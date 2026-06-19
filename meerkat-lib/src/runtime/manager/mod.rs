use super::ast::{ActionStmt, Decl, Expr, Value};
use super::interpreter::{eval, execute, EvalContext, EvalError, ExecuteEffect};
use super::semantic_analysis::var_analysis::{calc_dep_srv, DependAnalysis};
use crate::net::network_layer::NetworkLayer;
use crate::net::{Address, MeerkatMessage, NetworkActor, NetworkCommand, NetworkEvent, ServiceId};
use crate::runtime::txn::{Transaction, TxnId, VarState};
use std::collections::{HashMap, HashSet};
use tokio::sync::oneshot;
use tokio::time::Duration;

pub struct Service {
    /// Globally unique identity of this service (address-based when networked).
    pub id: ServiceId,
    pub name: String,
    /// Per-variable state: value, lock, and latest write transaction in one place
    pub vars: HashMap<String, VarState>,
    pub defs: HashMap<String, Expr>, // original def expressions for re-evaluation
    pub dep: DependAnalysis,         // dependency graph + topo order
    /// #24: who depends on each of this service's members, keyed uniformly by
    /// listener identity (ServiceId, def name) whether local or on another node.
    /// member -> set of (listener service, listener def).
    pub listeners: HashMap<String, HashSet<(ServiceId, String)>>,
    /// #24: cached values of each local def's direct cross-service deps, so a
    /// reactive recompute resolves a reference like s1.y from here instead of
    /// going to the network. def -> ((source service, member) -> value).
    pub dep_cache: HashMap<String, HashMap<(ServiceId, String), Value>>,
    /// #24: each local def's direct cross-service deps as (service, member),
    /// extracted from its expression at construction (free_var omits these).
    pub dep_remote: HashMap<String, HashSet<(String, String)>>,
}

/// A remote request parked on a variable's wait queue because the requesting
/// transaction is older than the current lock holder (wait-die wait). It holds
/// everything needed to re-dispatch the request and send its deferred reply
/// once the contended lock frees.
pub enum ParkedRequest {
    Action {
        request_id: u64,
        reply_to: String,
        service: String,
        stmts: Vec<ActionStmt>,
        env: Vec<(String, Value)>,
        tid: TxnId,
    },
    Lookup {
        request_id: u64,
        reply_to: String,
        service: String,
        member: String,
        tid: TxnId,
    },
}

impl ParkedRequest {
    /// The transaction this parked request belongs to. Its age decides serve
    /// order, and identifies it for purging when that transaction aborts.
    pub fn tid(&self) -> &TxnId {
        match self {
            ParkedRequest::Action { tid, .. } => tid,
            ParkedRequest::Lookup { tid, .. } => tid,
        }
    }
}

pub struct Manager {
    pub services: HashMap<String, Service>,
    /// Maps service name to remote address (for distributed services)
    pub remote_services: HashMap<String, Address>,
    /// Network actor for distributed communication
    pub network: Option<NetworkActor>,
    /// Pending reply channels keyed by request_id
    pub pending_replies: HashMap<u64, oneshot::Sender<MeerkatMessage>>,
    /// (Probabilistically) unique identifier of this node, used in transaction
    /// ids so ids minted on different nodes never collide.
    pub node_id: u64,
    /// Distributed transactions this node is participating in: actions composed
    /// by a remote originator, executed under a shared id and held (locks +
    /// buffered writes) until a Commit or Abort arrives.
    pub pending_txns: HashMap<TxnId, Transaction>,
    /// Requests parked because the requesting transaction is older than a lock
    /// holder (wait-die wait), keyed by the contended (service, var). Drained
    /// oldest-first when that variable's lock frees on commit or abort.
    pub wait_queue: HashMap<(ServiceId, String), Vec<ParkedRequest>>,
    /// This node's canonical, dialable address, set once after the network is
    /// listening. Service identities are derived from it, so they are stable for
    /// the life of the process (never empty-then-populated) and match the URL
    /// under which the node advertises its services.
    local_address: Option<String>,
    /// Enable local loopback mode
    pub local: bool,
}

impl Manager {
    pub fn new() -> Self {
        Manager {
            services: HashMap::new(),
            remote_services: HashMap::new(),
            network: None,
            pending_replies: HashMap::new(),
            node_id: Self::random_node_id(),
            pending_txns: HashMap::new(),
            wait_queue: HashMap::new(),
            local_address: None,
            local: false,
        }
    }

    /// Park a request on the wait queue for the contended (service, var). It
    /// receives no reply until that variable's lock frees and it is re-dispatched.
    pub fn park_request(&mut self, service: &str, var: String, parked: ParkedRequest) {
        let key = (self.id_for_service(service), var);
        self.wait_queue.entry(key).or_default().push(parked);
    }

    /// After a holder releases locks on commit or abort, return the oldest
    /// parked request waiting on each freed (service, var), removing it from the
    /// queue. Serving the oldest first is what keeps an older transaction from
    /// being starved by a stream of younger requests.
    pub fn take_ready_waiters(
        &mut self,
        freed: &HashSet<(ServiceId, String)>,
    ) -> Vec<ParkedRequest> {
        let mut ready = Vec::new();
        for key in freed {
            if let Some(waiters) = self.wait_queue.get_mut(key) {
                if let Some(idx) = waiters
                    .iter()
                    .enumerate()
                    .min_by(|(_, a), (_, b)| a.tid().cmp(b.tid()))
                    .map(|(i, _)| i)
                {
                    ready.push(waiters.remove(idx));
                    if waiters.is_empty() {
                        self.wait_queue.remove(key);
                    }
                }
            }
        }
        ready
    }

    /// Remove and return all parked requests belonging to a transaction, used
    /// when it aborts so its waiters do not later wake and prepare locks for a
    /// transaction the originator has abandoned.
    pub fn purge_parked_txn(&mut self, tid: &TxnId) -> Vec<ParkedRequest> {
        let mut removed = Vec::new();
        for waiters in self.wait_queue.values_mut() {
            let mut i = 0;
            while i < waiters.len() {
                if waiters[i].tid() == tid {
                    removed.push(waiters.remove(i));
                } else {
                    i += 1;
                }
            }
        }
        self.wait_queue.retain(|_, v| !v.is_empty());
        removed
    }

    /// (request_id, reply_to) for every currently parked request, so the owner
    /// can periodically reassure waiting originators that they are still queued
    /// (keepalive), keeping the wait from hitting the reply timeout.
    pub fn parked_keepalive_targets(&self) -> Vec<(u64, String)> {
        let mut out = Vec::new();
        for waiters in self.wait_queue.values() {
            for p in waiters {
                let pair = match p {
                    ParkedRequest::Action {
                        request_id,
                        reply_to,
                        ..
                    } => (*request_id, reply_to.clone()),
                    ParkedRequest::Lookup {
                        request_id,
                        reply_to,
                        ..
                    } => (*request_id, reply_to.clone()),
                };
                out.push(pair);
            }
        }
        out
    }

    /// Record this node's canonical address once the network is listening, so
    /// service identities are stable and consistent with the advertised URL.
    pub fn set_local_address(&mut self, addr: String) {
        self.local_address = Some(addr);
    }

    /// Compute the global identity of a service owned by this node. When the
    /// node has a network address, the identity is that address plus the service
    /// slug; otherwise it falls back to the bare name for local-only execution.
    fn service_identity(&self, name: &str) -> ServiceId {
        match &self.local_address {
            Some(addr) if !addr.is_empty() => ServiceId::new(format!("{}/{}", addr, name)),
            // No network address: fall back to the bare name. On a single node
            // names are unambiguous, and because local_address is fixed at
            // startup this choice never changes mid-run.
            _ => ServiceId::new(name),
        }
    }

    pub async fn create_service(
        &mut self,
        name: String,
        decls: Vec<Decl>,
    ) -> Result<(), EvalError> {
        let dep = calc_dep_srv(&decls);

        // #24: extract each def's direct cross-service deps now, while we still
        // own decls. free_var drops MemberAccess, so this is the only place a
        // reference like s1.y becomes visible to the runtime.
        let mut dep_remote: HashMap<String, HashSet<(String, String)>> = HashMap::new();
        for decl in &decls {
            if let Decl::DefDecl { name, val, .. } = decl {
                let refs = val.cross_service_deps();
                if !refs.is_empty() {
                    dep_remote.insert(name.clone(), refs);
                }
            }
        }

        let id = self.service_identity(&name);
        // Register the service (with its real ServiceId) before evaluating any
        // declarations, so action closures built during initialization are
        // stamped with the correct ServiceId instead of id_for_service's
        // bare-name fallback.
        self.services.insert(
            name.clone(),
            Service {
                id,
                name: name.clone(),
                vars: HashMap::new(),
                defs: HashMap::new(),
                dep,
                listeners: HashMap::new(),
                dep_cache: HashMap::new(),
                dep_remote,
            },
        );

        let mut env: Vec<(String, Value)> = vec![];
        let svc_name = name.clone();

        for decl in decls {
            match decl {
                Decl::VarDecl { name, val } => {
                    let value = eval(
                        &val,
                        &env,
                        &mut EvalContext {
                            manager: self,
                            service_name: &svc_name,
                            txn: None,
                        },
                    )
                    .await?;
                    env.push((name.clone(), value.clone()));
                    if let Some(service) = self.services.get_mut(&svc_name) {
                        service.vars.insert(name, VarState::new(value));
                    }
                }
                Decl::DefDecl { name, val, .. } => {
                    let value = eval(
                        &val,
                        &env,
                        &mut EvalContext {
                            manager: self,
                            service_name: &svc_name,
                            txn: None,
                        },
                    )
                    .await?;
                    env.push((name.clone(), value.clone()));
                    if let Some(service) = self.services.get_mut(&svc_name) {
                        service.vars.insert(name.clone(), VarState::new(value));
                        service.defs.insert(name, val); // store original expr
                    }
                }
                Decl::TableDecl { .. } => {
                    return Err(EvalError::NotImplemented);
                }
            }
        }

        Ok(())
    }

    pub async fn lookup(
        &mut self,
        ident: &str,
        service_name: &str,
        mut txn: Option<&mut Transaction>,
    ) -> Result<Value, EvalError> {
        // Check if service is remote
        if self.remote_services.contains_key(service_name) {
            return self.remote_lookup(service_name, ident, txn).await;
        }

        // If it's a def, re-evaluate from stored expression for freshness.
        // The transaction flows through so the def's underlying vars are locked.
        let def_expr = self
            .services
            .get(service_name)
            .and_then(|s| s.defs.get(ident))
            .cloned();

        if let Some(expr) = def_expr {
            // Evaluate the def with an empty env so its dependencies resolve
            // through lookup (acquiring read locks and populating the cache)
            // rather than being pre-seeded from current service var values.
            let env: Vec<(String, Value)> = Vec::new();
            return eval(
                &expr,
                &env,
                &mut EvalContext {
                    manager: self,
                    service_name,
                    txn: txn.as_deref_mut(),
                },
            )
            .await;
        }

        // Local var read. If inside a transaction, return the cached value if
        // present, otherwise acquire a read lock lazily and cache the value.
        // Transaction state is keyed by (service id, variable) so the same name
        // in different services never collides.
        let key = (self.id_for_service(service_name), ident.to_string());
        let mut need_read_lock: Option<TxnId> = None;
        if let Some(t) = txn.as_deref() {
            if let Some(cached) = t.read_cache.get(&key) {
                return Ok(cached.clone());
            }
            if !t.locked.contains(&key) {
                need_read_lock = Some(t.id.clone());
            }
        }
        if let Some(txn_id) = need_read_lock {
            self.acquire_read_lock(service_name, ident, &txn_id)?;
            if let Some(t) = txn.as_deref_mut() {
                t.locked.insert(key.clone());
            }
        }

        // Return stored var value (and cache it for the transaction)
        if let Some(service) = self.services.get(service_name) {
            if let Some(var_state) = service.vars.get(ident) {
                let value = var_state.value.clone();
                if let Some(t) = txn {
                    t.read_cache.insert(key, value.clone());
                }
                return Ok(value);
            }
        }
        Err(EvalError::LookupError(format!(
            "Variable '{}' not found in service '{}'",
            ident, service_name
        )))
    }

    pub async fn assign(
        &mut self,
        service_name: &str,
        var: &str,
        value: Value,
        txn: Option<&mut Transaction>,
    ) -> Result<(), EvalError> {
        // Inside a transaction: acquire the write lock lazily (upgrading from a
        // read lock for read-then-write patterns like x = x + 1) and buffer the
        // write. The buffered value is applied to the service only at commit, so
        // a transaction that fails partway leaves no partial writes behind.
        if txn.is_some() {
            let key = (self.id_for_service(service_name), var.to_string());
            enum LockAction {
                Acquire,
                Upgrade,
            }
            let (txn_id, kind) = {
                let t = txn.as_deref().unwrap();
                let kind = if t.locked.contains(&key) {
                    LockAction::Upgrade
                } else {
                    LockAction::Acquire
                };
                (t.id.clone(), kind)
            };
            match kind {
                LockAction::Upgrade => self.upgrade_to_write_lock(service_name, var, &txn_id)?,
                LockAction::Acquire => self.acquire_write_lock(service_name, var, &txn_id)?,
            }
            if let Some(t) = txn {
                t.locked.insert(key.clone());
                t.written.insert(key.clone(), value.clone());
                // Reads later in the same transaction see the buffered write
                t.read_cache.insert(key, value);
            }
            return Ok(());
        }

        // Non-transactional path: apply the write immediately and propagate.
        if let Some(service) = self.services.get_mut(service_name) {
            if let Some(var_state) = service.vars.get_mut(var) {
                var_state.value = value;
            } else {
                return Err(EvalError::LookupError(format!(
                    "Variable '{}' not found in service '{}'",
                    var, service_name
                )));
            }
        } else {
            return Err(EvalError::LookupError(format!(
                "Service '{}' not found",
                service_name
            )));
        }

        // propagate: re-evaluate defs that depend on this var in topo order
        self.propagate(service_name, var).await;
        Ok(())
    }

    async fn propagate(&mut self, service_name: &str, changed_var: &str) {
        // collect defs that need re-evaluation in topo order
        let topo_order: Vec<String> = self
            .services
            .get(service_name)
            .map(|s| s.dep.topo_order.clone())
            .unwrap_or_default();

        for def_name in topo_order {
            let needs_update = self
                .services
                .get(service_name)
                .and_then(|s| s.dep.dep_vars.get(&def_name))
                .map(|dep_vars| dep_vars.contains(changed_var))
                .unwrap_or(false);

            let is_def = self
                .services
                .get(service_name)
                .map(|s| s.defs.contains_key(&def_name))
                .unwrap_or(false);

            if needs_update && is_def {
                // build env from current var values
                let expr = self
                    .services
                    .get(service_name)
                    .and_then(|s| s.defs.get(&def_name))
                    .cloned();

                if let Some(expr) = expr {
                    let env: Vec<(String, Value)> = self
                        .services
                        .get(service_name)
                        .map(|s| {
                            s.vars
                                .iter()
                                .map(|(k, v)| (k.clone(), v.value.clone()))
                                .collect()
                        })
                        .unwrap_or_default();

                    let value = match eval(
                        &expr,
                        &env,
                        &mut EvalContext {
                            manager: self,
                            service_name,
                            txn: None,
                        },
                    )
                    .await
                    {
                        Ok(v) => v,
                        Err(e) => {
                            // Propagation is best-effort; durable retry of failed
                            // updates is tracked under issue #24 (async updates).
                            log::warn!("propagation of def '{}' failed: {}", def_name, e);
                            continue;
                        }
                    };

                    if let Some(service) = self.services.get_mut(service_name) {
                        if let Some(var_state) = service.vars.get_mut(&def_name) {
                            var_state.value = value;
                        }
                    }
                }
            }
        }
    }

    /// Drain all pending network events and dispatch each to the matching
    /// oneshot channel in pending_replies. Non-matching events are dropped.
    pub fn dispatch_network_events(&mut self) {
        while let Some(n) = self.network.as_mut() {
            let event = n.try_recv_event();
            match event {
                Some(NetworkEvent::MessageReceived { msg, .. }) => {
                    let rid = match &msg {
                        MeerkatMessage::LookupResponse { request_id, .. } => Some(*request_id),
                        MeerkatMessage::LookupError { request_id, .. } => Some(*request_id),
                        MeerkatMessage::ActionResponse { request_id, .. } => Some(*request_id),
                        MeerkatMessage::CommitResponse { request_id, .. } => Some(*request_id),
                        MeerkatMessage::AbortResponse { request_id, .. } => Some(*request_id),
                        MeerkatMessage::WaitParked { request_id } => Some(*request_id),
                        _ => None,
                    };
                    if let Some(id) = rid {
                        if let Some(tx) = self.pending_replies.remove(&id) {
                            let _ = tx.send(msg);
                        }
                    }
                }
                Some(_) => {}
                None => break,
            }
        }
    }

    /// Send a message and await a reply using tokio::select! for timeout.
    /// Encapsulates the duplicated send + register channel + await pattern
    /// shared by remote_lookup and remote_action.
    async fn send_and_await_reply(
        &mut self,
        addr: Address,
        msg: MeerkatMessage,
        request_id: u64,
        timeout_msg: String,
    ) -> Result<MeerkatMessage, EvalError> {
        // Send the message
        let net = self
            .network
            .as_mut()
            .ok_or_else(|| EvalError::NetworkError("No network layer available".to_string()))?;
        net.handle_command(NetworkCommand::SendMessage { addr, msg })
            .await;

        // Register oneshot channel for this request
        let (tx, mut rx) = oneshot::channel::<MeerkatMessage>();
        self.pending_replies.insert(request_id, tx);

        // Loop with pinned timeout + tokio::select!. Each iteration dispatches
        // pending network events then checks for reply, timeout, or yields 10ms.
        // The loop is required until the tokio::join! background message loop
        // architecture is implemented as a follow-up.
        let timeout = tokio::time::sleep(Duration::from_secs(15));
        tokio::pin!(timeout);

        loop {
            self.dispatch_network_events();
            tokio::select! {
                biased;
                result = &mut rx => {
                    match result {
                        // Owner parked our request (wait-die wait): it is alive
                        // and still queued, so reset the timeout, re-register a
                        // fresh reply channel, and keep waiting.
                        Ok(MeerkatMessage::WaitParked { .. }) => {
                            let (ntx, nrx) = oneshot::channel::<MeerkatMessage>();
                            self.pending_replies.insert(request_id, ntx);
                            rx = nrx;
                            timeout
                                .as_mut()
                                .reset(tokio::time::Instant::now() + Duration::from_secs(15));
                        }
                        Ok(msg) => return Ok(msg),
                        Err(_) => {
                            return Err(EvalError::NetworkError(
                                "Reply channel closed".to_string(),
                            ))
                        }
                    }
                }
                _ = &mut timeout => {
                    self.pending_replies.remove(&request_id);
                    return Err(EvalError::NetworkError(timeout_msg));
                }
                _ = tokio::time::sleep(Duration::from_millis(10)) => {}
            }
        }
    }

    /// Get the network address for a remote service (strips the slug)
    fn remote_addr(&self, service: &str) -> Result<Address, EvalError> {
        let full_url = self.remote_services.get(service).ok_or_else(|| {
            EvalError::LookupError(format!("Remote service '{}' not found", service))
        })?;
        let addr_str = full_url.0.trim_end_matches(&format!("/{}", service));
        Ok(Address::new(addr_str))
    }

    /// Get our local address with peer ID for use as reply_to
    /// Replaces loopback/unspecified with the actual outbound IP
    async fn local_reply_addr(&mut self) -> String {
        if let Some(addr) = &self.local_address {
            return addr.clone();
        }
        let net = match self.network.as_mut() {
            Some(n) => n,
            None => return String::new(),
        };
        let peer_id = net.local_peer_id();
        let reply = net.handle_command(NetworkCommand::GetLocalAddresses).await;
        let node_ip = self.get_node_ip();
        match reply {
            crate::net::NetworkReply::LocalAddresses { addrs } => {
                if let Some(addr) = addrs.first() {
                    let addr_str = addr
                        .0
                        .replace("0.0.0.0", &node_ip)
                        .replace("127.0.0.1", &node_ip);
                    format!("{}/p2p/{}", addr_str, peer_id)
                } else {
                    String::new()
                }
            }
            _ => String::new(),
        }
    }

    /// Generate a probabilistically-unique node id with no extra dependency.
    /// RandomState is OS-seeded on native targets; combining it with the current
    /// time gives a value that is distinct across nodes with high probability.
    fn random_node_id() -> u64 {
        use std::collections::hash_map::RandomState;
        use std::hash::{BuildHasher, Hasher};
        use std::time::{SystemTime, UNIX_EPOCH};
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0);
        let mut h = RandomState::new().build_hasher();
        h.write_u128(nanos);
        h.finish()
    }

    /// Get the local machine's outbound IP address (non-loopback) or loopback fallback
    pub fn get_node_ip(&self) -> String {
        if self.local {
            return "127.0.0.1".to_string();
        }
        use std::net::UdpSocket;
        UdpSocket::bind("0.0.0.0:0")
            .and_then(|s| {
                s.connect("8.8.8.8:80")?;
                s.local_addr()
            })
            .map(|addr| addr.ip().to_string())
            .unwrap_or_else(|_| "127.0.0.1".to_string())
    }

    pub async fn remote_lookup(
        &mut self,
        service: &str,
        member: &str,
        txn: Option<&mut Transaction>,
    ) -> Result<Value, EvalError> {
        use std::sync::atomic::{AtomicU64, Ordering};
        static NEXT_ID: AtomicU64 = AtomicU64::new(1);

        // Remote reads are always served by the owning node, which holds this
        // transaction's buffered writes and read locks. We deliberately do not
        // cache the result on the requesting side: a def's value can change
        // later in the same transaction when a composed action writes one of
        // its dependencies on the owner, so a cached copy would go stale and
        // the def would "stop updating". Re-fetching keeps reads consistent
        // with the owner's buffered state. (Caching provably-immutable reads to
        // save round-trips could be a later optimization.)
        let addr = self.remote_addr(service)?;
        let request_id = NEXT_ID.fetch_add(1, Ordering::SeqCst);
        let reply_to = self.local_reply_addr().await;
        let shared_tid = txn.as_ref().map(|t| t.id.clone());

        // Inside a transaction, the owning node will acquire and hold a read lock
        // under the shared id. Pre-register it as a participant so commit/abort
        // releases that lock even if the reply is lost.
        if shared_tid.is_some() {
            if let Some(t) = txn {
                t.participants.insert(addr.clone());
            }
        }

        let msg = MeerkatMessage::LookupRequest {
            request_id,
            service: service.to_string(),
            member: member.to_string(),
            reply_to,
            txn_id: shared_tid,
        };

        let reply = self
            .send_and_await_reply(
                addr,
                msg,
                request_id,
                format!(
                    "Timeout waiting for remote lookup of {}.{}",
                    service, member
                ),
            )
            .await?;

        match reply {
            MeerkatMessage::LookupResponse { value, .. } => {
                let val: Value = serde_json::from_str(&value)
                    .map_err(|e| EvalError::NetworkError(e.to_string()))?;
                Ok(val)
            }
            MeerkatMessage::LookupError { error, .. } => Err(EvalError::LookupError(error)),
            _ => Err(EvalError::NetworkError(
                "Unexpected reply to lookup request".to_string(),
            )),
        }
    }

    /// Participant side: serve a transactional remote read by acquiring and
    /// holding a read lock on the member under the shared transaction id (kept
    /// in pending_txns until commit/abort), accumulating into any state this
    /// node already prepared for the same transaction.
    pub async fn remote_read_participant(
        &mut self,
        service: &str,
        member: &str,
        tid: TxnId,
    ) -> Result<Value, EvalError> {
        let mut txn = self
            .pending_txns
            .remove(&tid)
            .unwrap_or_else(|| Transaction::new(tid.clone()));
        match self.lookup(member, service, Some(&mut txn)).await {
            Ok(v) => {
                self.pending_txns.insert(tid, txn);
                Ok(v)
            }
            Err(e) => {
                // Wait-die wait: preserve the transaction so the parked read can
                // resume on release; any other failure releases and drops it.
                if matches!(e, EvalError::WaitOn(_, _)) {
                    self.pending_txns.insert(tid, txn);
                    return Err(e);
                }
                // Could not acquire the read lock (e.g. conflict): release any
                // locks taken and do not keep this transaction prepared.
                self.release_locks(&txn.locked, &txn.id);
                Err(e)
            }
        }
    }

    pub async fn remote_action(
        &mut self,
        service_id: &ServiceId,
        stmts: Vec<ActionStmt>,
        env: Vec<(String, Value)>,
        txn: Option<&mut Transaction>,
    ) -> Result<(), EvalError> {
        use std::sync::atomic::{AtomicU64, Ordering};
        static NEXT_ACTION_ID: AtomicU64 = AtomicU64::new(1);

        // Dial the node address embedded in the ServiceId; send the slug as the
        // service name the remote node uses to find its local service. This works
        // even if the service was never imported into the current scope (#40).
        let (addr, slug) = Self::split_service_id(service_id);
        let request_id = NEXT_ACTION_ID.fetch_add(1, Ordering::SeqCst);
        let reply_to = self.local_reply_addr().await;

        // When part of a transaction, ship its id so the remote node executes
        // under the shared transaction and holds (does not commit) until our
        // commit/abort. Standalone (no txn) keeps the old commit-immediately path.
        let shared_tid = txn.as_ref().map(|t| t.id.clone());

        // Pre-register the participant BEFORE sending. If the request times out
        // or the response is lost after the remote already prepared and grabbed
        // locks, the originator's abort path still iterates txn.participants and
        // reaches this node to release them. If the remote never received the
        // request, the Abort it gets is a harmless no-op.
        if shared_tid.is_some() {
            if let Some(t) = txn {
                t.participants.insert(addr.clone());
            }
        }

        let msg = MeerkatMessage::ActionRequest {
            request_id,
            service: slug.clone(),
            stmts,
            env,
            reply_to,
            txn_id: shared_tid,
        };

        let reply = self
            .send_and_await_reply(
                addr.clone(),
                msg,
                request_id,
                format!("Timeout waiting for remote action on service '{}'", slug),
            )
            .await?;

        match reply {
            MeerkatMessage::ActionResponse { success, error, .. } => {
                if success {
                    // Participant already registered above; nothing more to do.
                    Ok(())
                } else {
                    Err(EvalError::NetworkError(
                        error.unwrap_or_else(|| "Remote action failed".to_string()),
                    ))
                }
            }
            _ => Err(EvalError::NetworkError(
                "Unexpected reply to action request".to_string(),
            )),
        }
    }

    /// Resolve an in-scope service name to its global ServiceId. Callers only
    /// resolve names of local services here (remote reads and actions are routed
    /// before reaching this), so this returns the service's stored, stable id.
    /// The bare-name fallback is a defensive default for an unknown name and is
    /// not used for genuine remote services, whose identities travel embedded in
    /// their ActionClosures.
    pub fn id_for_service(&self, service_name: &str) -> ServiceId {
        self.services
            .get(service_name)
            .map(|s| s.id.clone())
            .unwrap_or_else(|| ServiceId::new(service_name))
    }

    /// Find a local service (mutably) by its ServiceId.
    fn service_by_id_mut(&mut self, id: &ServiceId) -> Option<&mut Service> {
        self.services.values_mut().find(|s| &s.id == id)
    }

    /// Find the in-scope name of a local service from its ServiceId.
    pub fn name_for_id(&self, id: &ServiceId) -> Option<String> {
        self.services
            .iter()
            .find(|(_, s)| &s.id == id)
            .map(|(n, _)| n.clone())
    }

    /// Split a service identity into the dialable node address and the service
    /// slug (its trailing name segment). Lets remote_action use the address
    /// embedded in an ActionClosure's ServiceId rather than requiring the
    /// service to be imported into the current scope.
    fn split_service_id(id: &ServiceId) -> (Address, String) {
        match id.0.rfind('/') {
            Some(i) => (Address::new(&id.0[..i]), id.0[i + 1..].to_string()),
            None => (Address::new(String::new()), id.0.clone()),
        }
    }

    /// Try to acquire a write lock on a service variable.
    /// Returns LockConflict if the variable is already locked.
    fn acquire_write_lock(
        &mut self,
        service_name: &str,
        var: &str,
        txn_id: &TxnId,
    ) -> Result<(), EvalError> {
        let service = self.services.get_mut(service_name).ok_or_else(|| {
            EvalError::LookupError(format!("Service '{}' not found", service_name))
        })?;
        let var_state = service
            .vars
            .get_mut(var)
            .ok_or_else(|| EvalError::LookupError(format!("Variable '{}' not found", var)))?;
        if var_state.lock.try_write(txn_id) {
            Ok(())
        } else {
            match var_state.lock.wait_die(txn_id) {
                crate::runtime::txn::WaitDie::Die => Err(EvalError::WaitDieAbort(format!(
                    "transaction died contending for write lock on '{}'",
                    var
                ))),
                crate::runtime::txn::WaitDie::Wait => {
                    Err(EvalError::WaitOn(service_name.to_string(), var.to_string()))
                }
            }
        }
    }

    /// Try to acquire a read lock on a service variable.
    /// Returns LockConflict if a write lock is held.
    fn acquire_read_lock(
        &mut self,
        service_name: &str,
        var: &str,
        txn_id: &TxnId,
    ) -> Result<(), EvalError> {
        let service = self.services.get_mut(service_name).ok_or_else(|| {
            EvalError::LookupError(format!("Service '{}' not found", service_name))
        })?;
        let var_state = service
            .vars
            .get_mut(var)
            .ok_or_else(|| EvalError::LookupError(format!("Variable '{}' not found", var)))?;
        if var_state.lock.try_read(txn_id) {
            Ok(())
        } else {
            match var_state.lock.wait_die(txn_id) {
                crate::runtime::txn::WaitDie::Die => Err(EvalError::WaitDieAbort(format!(
                    "transaction died contending for read lock on '{}'",
                    var
                ))),
                crate::runtime::txn::WaitDie::Wait => {
                    Err(EvalError::WaitOn(service_name.to_string(), var.to_string()))
                }
            }
        }
    }

    /// Upgrade a read lock to a write lock on a service variable.
    /// Used for read-then-write within the same transaction (e.g. x = x + 1).
    fn upgrade_to_write_lock(
        &mut self,
        service_name: &str,
        var: &str,
        txn_id: &TxnId,
    ) -> Result<(), EvalError> {
        let service = self.services.get_mut(service_name).ok_or_else(|| {
            EvalError::LookupError(format!("Service '{}' not found", service_name))
        })?;
        let var_state = service
            .vars
            .get_mut(var)
            .ok_or_else(|| EvalError::LookupError(format!("Variable '{}' not found", var)))?;
        if var_state.lock.upgrade_to_write(txn_id) {
            Ok(())
        } else {
            match var_state.lock.wait_die(txn_id) {
                crate::runtime::txn::WaitDie::Die => Err(EvalError::WaitDieAbort(format!(
                    "transaction died contending to upgrade lock on '{}'",
                    var
                ))),
                crate::runtime::txn::WaitDie::Wait => {
                    Err(EvalError::WaitOn(service_name.to_string(), var.to_string()))
                }
            }
        }
    }

    /// Release all locks held by txn_id on the given variables.
    fn release_locks(&mut self, locked: &HashSet<(ServiceId, String)>, txn_id: &TxnId) {
        for (sid, var) in locked {
            if let Some(service) = self.service_by_id_mut(sid) {
                if let Some(var_state) = service.vars.get_mut(var) {
                    var_state.lock.release(txn_id);
                }
            }
        }
    }

    /// Execute action statements as a transaction with lazy lock acquisition:
    ///
    /// Locks are acquired on demand as each variable is first read or written
    /// during execution (inside `lookup` and `assign`), rather than upfront.
    /// This handles actions invoked via function calls and conditional branches,
    /// where the set of accessed variables can't be determined statically.
    /// Read values are cached in the transaction to avoid re-fetching (which
    /// also avoids redundant network round-trips for remote reads).
    ///
    /// On completion: commit records latest_write_txn for written variables,
    /// then all locks are released (always, even on error).
    ///
    /// Deadlock prevention (wait-die) is deferred to a follow-up issue.
    /// If a lock cannot be acquired, the transaction fails immediately.
    pub async fn execute_action_with_txn(
        &mut self,
        service_name: &str,
        stmts: &[ActionStmt],
        initial_env: &[(String, Value)],
    ) -> Result<(), EvalError> {
        // Wait-die: a transaction that dies on a lock conflict (an older
        // transaction holds the lock) aborts and retries with a higher
        // iteration but the same age, bounded so a permanently held lock
        // cannot loop forever. True blocking for the "wait" case (the older
        // transaction holding its place) is tracked separately under #30
        // stage 2.
        const MAX_WAIT_DIE_RETRIES: u32 = 10;
        let mut txn_id = TxnId::new(self.node_id);

        loop {
            // The transaction owns all its state and is passed down through
            // execution; nothing transaction-specific lives on the Manager.
            let mut txn = Transaction::new(txn_id.clone());

            // Execute statements; read/write locks are acquired lazily inside
            // lookup/assign as variables are accessed
            let mut env: Vec<(String, Value)> = initial_env.to_vec();
            let mut exec_error: Option<EvalError> = None;
            for stmt in stmts {
                match execute(stmt, &env, self, service_name, Some(&mut txn)).await {
                    Ok(ExecuteEffect::Binding(name, val)) => env.push((name, val)),
                    Ok(_) => {}
                    Err(e) => {
                        exec_error = Some(e);
                        break;
                    }
                }
            }

            // Wait-die abort: discard this attempt, abort participants, release
            // locks, and retry with a higher iteration up to the bound. A died
            // attempt never applies its buffered writes, so re-running from
            // scratch is safe.
            if matches!(exec_error, Some(EvalError::WaitDieAbort(_))) {
                for addr in txn.participants.iter().cloned().collect::<Vec<_>>() {
                    self.send_abort(addr, &txn.id).await;
                }
                self.release_locks(&txn.locked, &txn.id);
                if txn_id.iteration < MAX_WAIT_DIE_RETRIES {
                    txn_id = txn_id.retry();
                    continue;
                }
                return Err(exec_error.unwrap());
            }

            // The commit/abort decision depends only on whether execution
            // succeeded. Once execution succeeds the writes are applied and
            // become visible, so commit messaging to participants is
            // best-effort and never turns a successful transaction into a
            // failed one (commit retries are tracked separately under issue
            // #54).
            if exec_error.is_none() {
                self.apply_committed_writes(&txn).await;
                for addr in txn.participants.iter().cloned().collect::<Vec<_>>() {
                    let _ = self.send_commit(addr, &txn.id).await;
                }
            } else {
                // Execution failed: discard buffered writes and abort
                // participants.
                for addr in txn.participants.iter().cloned().collect::<Vec<_>>() {
                    self.send_abort(addr, &txn.id).await;
                }
            }

            // Release all locks held locally (always, even on error)
            self.release_locks(&txn.locked, &txn.id);

            return match exec_error {
                Some(e) => Err(e),
                None => Ok(()),
            };
        }
    }

    /// Apply a transaction's buffered writes to the owning services, record the
    /// writing transaction, and propagate to dependent defs. Shared by local
    /// commit and by a participant committing on a remote Commit message.
    /// Infallible: once we are applying writes the transaction is committed, so
    /// there is no going back. Propagation is best-effort (retries: issue #24).
    async fn apply_committed_writes(&mut self, txn: &Transaction) {
        let writes: Vec<((ServiceId, String), Value)> = txn
            .written
            .iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        let txn_id = txn.id.clone();
        for ((sid, var), value) in &writes {
            if let Some(service) = self.service_by_id_mut(sid) {
                if let Some(var_state) = service.vars.get_mut(var) {
                    var_state.value = value.clone();
                    var_state.latest_write_txn = Some(txn_id.clone());
                }
            }
        }
        // Propagate after all writes are applied so defs see a consistent state.
        for ((sid, var), _) in &writes {
            if let Some(name) = self.name_for_id(sid) {
                self.propagate(&name, var).await;
            }
        }
    }

    /// Participant side: execute a composed action under a shared transaction id
    /// received from the originator, then hold the transaction (locks + buffered
    /// writes) in `pending_txns` until a Commit or Abort arrives. Does not commit.
    pub async fn execute_action_participant(
        &mut self,
        service_name: &str,
        stmts: &[ActionStmt],
        initial_env: &[(String, Value)],
        tid: TxnId,
    ) -> Result<(), EvalError> {
        // Reuse an already-prepared transaction for this id if this node was
        // already touched by the same distributed transaction (two services on
        // one host, or transitive re-entry); otherwise start fresh. Pulling it
        // out of pending_txns gives ownership so we can borrow &mut self below,
        // and lets repeated actions accumulate into one prepared state.
        let mut txn = self
            .pending_txns
            .remove(&tid)
            .unwrap_or_else(|| Transaction::new(tid.clone()));
        let mut env: Vec<(String, Value)> = initial_env.to_vec();
        let mut exec_error: Option<EvalError> = None;
        for stmt in stmts {
            match execute(stmt, &env, self, service_name, Some(&mut txn)).await {
                Ok(ExecuteEffect::Binding(name, val)) => env.push((name, val)),
                Ok(_) => {}
                Err(e) => {
                    exec_error = Some(e);
                    break;
                }
            }
        }
        if let Some(e) = exec_error {
            // Wait-die wait: this transaction is older than a current holder and
            // must wait for the contended variable to free. Preserve its partial
            // locks and buffered writes in pending_txns so that a re-dispatch on
            // release skips the locks it already holds (guarded by txn.locked)
            // and resumes at the contended variable. The owner parks the
            // request; nothing is released here.
            if matches!(e, EvalError::WaitOn(_, _)) {
                self.pending_txns.insert(tid, txn);
                return Err(e);
            }
            // Any other failure: release all locks held by this (possibly merged)
            // transaction; do not keep it prepared. The originator's abort for
            // this tid will then be a safe no-op here.
            self.release_locks(&txn.locked, &txn.id);
            return Err(e);
        }
        // Prepared: hold the accumulated locks and buffered writes until commit/abort.
        self.pending_txns.insert(tid, txn);
        Ok(())
    }

    /// Participant side: apply and release a held transaction on Commit.
    pub async fn commit_participant(
        &mut self,
        tid: &TxnId,
    ) -> Result<HashSet<(ServiceId, String)>, EvalError> {
        if let Some(txn) = self.pending_txns.remove(tid) {
            // The originator decided to commit, so applying is infallible.
            let freed = txn.locked.clone();
            self.apply_committed_writes(&txn).await;
            self.release_locks(&txn.locked, &txn.id);
            // Forward the commit down the chain to any sub-participants this node
            // composed (transitive composition: s1 -> s2 -> s3 ...). Forwarding
            // failures are reported back but cannot undo the local commit.
            let mut forward_err = None;
            for addr in txn.participants.iter().cloned().collect::<Vec<_>>() {
                if let Err(e) = self.send_commit(addr, tid).await {
                    forward_err = Some(e);
                }
            }
            match forward_err {
                Some(e) => Err(e),
                None => Ok(freed),
            }
        } else {
            Ok(HashSet::new())
        }
    }

    /// Participant side: discard and release a held transaction on Abort, and
    /// forward the abort down the chain to any sub-participants.
    pub async fn abort_participant(&mut self, tid: &TxnId) -> HashSet<(ServiceId, String)> {
        if let Some(txn) = self.pending_txns.remove(tid) {
            let freed = txn.locked.clone();
            self.release_locks(&txn.locked, &txn.id);
            for addr in txn.participants.iter().cloned().collect::<Vec<_>>() {
                self.send_abort(addr, tid).await;
            }
            freed
        } else {
            HashSet::new()
        }
    }

    /// Originator side: ask a participant to commit, awaiting its acknowledgement.
    async fn send_commit(&mut self, addr: Address, tid: &TxnId) -> Result<(), EvalError> {
        use std::sync::atomic::{AtomicU64, Ordering};
        static NEXT_COMMIT_ID: AtomicU64 = AtomicU64::new(1);
        let request_id = NEXT_COMMIT_ID.fetch_add(1, Ordering::SeqCst);
        let reply_to = self.local_reply_addr().await;
        let msg = MeerkatMessage::Commit {
            request_id,
            txn_id: tid.clone(),
            reply_to,
        };
        let reply = self
            .send_and_await_reply(
                addr,
                msg,
                request_id,
                "Timeout waiting for commit acknowledgement".to_string(),
            )
            .await?;
        match reply {
            MeerkatMessage::CommitResponse { success, error, .. } => {
                if success {
                    Ok(())
                } else {
                    Err(EvalError::NetworkError(
                        error.unwrap_or_else(|| "Participant commit failed".to_string()),
                    ))
                }
            }
            _ => Err(EvalError::NetworkError(
                "Unexpected reply to commit".to_string(),
            )),
        }
    }

    /// Originator side: tell a participant to abort, awaiting acknowledgement
    /// so its locks are released before we return (and the process may exit).
    async fn send_abort(&mut self, addr: Address, tid: &TxnId) {
        use std::sync::atomic::{AtomicU64, Ordering};
        static NEXT_ABORT_ID: AtomicU64 = AtomicU64::new(1);
        let request_id = NEXT_ABORT_ID.fetch_add(1, Ordering::SeqCst);
        let reply_to = self.local_reply_addr().await;
        let msg = MeerkatMessage::Abort {
            request_id,
            txn_id: tid.clone(),
            reply_to,
        };
        // We await the ack so that in the normal case the participant's locks
        // are released before we return. If the ack times out the participant
        // may still hold locks; durable abort retries and error reporting are
        // tracked under issue #54.
        let _ = self
            .send_and_await_reply(
                addr,
                msg,
                request_id,
                "Timeout waiting for abort acknowledgement".to_string(),
            )
            .await;
    }

    pub async fn execute_action(
        &mut self,
        service_name: &str,
        stmts: &[ActionStmt],
    ) -> Result<(), EvalError> {
        self.execute_action_with_txn(service_name, stmts, &[]).await
    }

    pub async fn execute_action_with_env(
        &mut self,
        service_name: &str,
        stmts: &[ActionStmt],
        initial_env: &[(String, Value)],
    ) -> Result<(), EvalError> {
        self.execute_action_with_txn(service_name, stmts, initial_env)
            .await
    }
}

impl Default for Manager {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Decl, Expr, Value};

    #[tokio::test]
    async fn test_create_service_with_var() {
        let mut manager = Manager::new();
        let decls = vec![Decl::VarDecl {
            name: "x".to_string(),
            val: Expr::Literal {
                val: Value::Number { val: 1 },
            },
        }];
        manager
            .create_service("foo".to_string(), decls)
            .await
            .unwrap();
        let result = manager.lookup("x", "foo", None).await.unwrap();
        assert_eq!(result, Value::Number { val: 1 });
    }

    #[tokio::test]
    async fn test_create_service_with_def() {
        let mut manager = Manager::new();
        let decls = vec![
            Decl::VarDecl {
                name: "x".to_string(),
                val: Expr::Literal {
                    val: Value::Number { val: 2 },
                },
            },
            Decl::DefDecl {
                name: "f".to_string(),
                val: Expr::Binop {
                    op: crate::ast::BinOp::Add,
                    expr1: Box::new(Expr::Variable {
                        ident: "x".to_string(),
                    }),
                    expr2: Box::new(Expr::Literal {
                        val: Value::Number { val: 3 },
                    }),
                },
                is_pub: true,
            },
        ];
        manager
            .create_service("foo".to_string(), decls)
            .await
            .unwrap();
        let result = manager.lookup("f", "foo", None).await.unwrap();
        assert_eq!(result, Value::Number { val: 5 });
    }

    #[tokio::test]
    async fn test_lookup_missing_var_returns_error() {
        let mut manager = Manager::new();
        manager
            .create_service("foo".to_string(), vec![])
            .await
            .unwrap();
        let result = manager.lookup("nonexistent", "foo", None).await;
        assert!(result.is_err());
    }

    #[tokio::test]
    async fn test_def_updates_after_var_change() {
        let mut manager = Manager::new();
        // service foo { var x = 1; def f = x + 10; }
        let decls = vec![
            Decl::VarDecl {
                name: "x".to_string(),
                val: Expr::Literal {
                    val: Value::Number { val: 1 },
                },
            },
            Decl::DefDecl {
                name: "f".to_string(),
                val: Expr::Binop {
                    op: crate::ast::BinOp::Add,
                    expr1: Box::new(Expr::Variable {
                        ident: "x".to_string(),
                    }),
                    expr2: Box::new(Expr::Literal {
                        val: Value::Number { val: 10 },
                    }),
                },
                is_pub: true,
            },
        ];
        manager
            .create_service("foo".to_string(), decls)
            .await
            .unwrap();

        // f should be 11 initially
        let result = manager.lookup("f", "foo", None).await.unwrap();
        assert_eq!(result, Value::Number { val: 11 });

        // update x to 5, f should become 15
        manager
            .assign("foo", "x", Value::Number { val: 5 }, None)
            .await
            .unwrap();
        let result = manager.lookup("f", "foo", None).await.unwrap();
        assert_eq!(result, Value::Number { val: 15 });
    }

    // Helper: service with a single var x = 0
    async fn manager_with_x() -> Manager {
        let mut manager = Manager::new();
        let decls = vec![Decl::VarDecl {
            name: "x".to_string(),
            val: Expr::Literal {
                val: Value::Number { val: 0 },
            },
        }];
        manager
            .create_service("foo".to_string(), decls)
            .await
            .unwrap();
        manager
    }

    fn x_state(manager: &Manager) -> &VarState {
        manager.services.get("foo").unwrap().vars.get("x").unwrap()
    }

    fn assert_x_unlocked(manager: &Manager) {
        assert!(matches!(
            &x_state(manager).lock,
            crate::runtime::txn::VarLock::Unlocked
        ));
    }

    // x = x + 1 reads x (read lock) then writes x (must upgrade to write lock).
    // This is the read-then-write pattern that the old upfront analysis mishandled.
    #[tokio::test]
    async fn test_txn_read_then_write_upgrades_lock() {
        let mut manager = manager_with_x().await;
        let stmts = vec![ActionStmt::Assign {
            var: "x".to_string(),
            expr: Expr::Binop {
                op: crate::ast::BinOp::Add,
                expr1: Box::new(Expr::Variable {
                    ident: "x".to_string(),
                }),
                expr2: Box::new(Expr::Literal {
                    val: Value::Number { val: 1 },
                }),
            },
        }];
        manager.execute_action("foo", &stmts).await.unwrap();
        let result = manager.lookup("x", "foo", None).await.unwrap();
        assert_eq!(result, Value::Number { val: 1 });
    }

    // Locks must be released after a transaction, so a second transaction
    // can acquire them. Running x = x + 1 twice should yield x == 2.
    #[tokio::test]
    async fn test_txn_locks_released_between_transactions() {
        let mut manager = manager_with_x().await;
        let stmts = vec![ActionStmt::Assign {
            var: "x".to_string(),
            expr: Expr::Binop {
                op: crate::ast::BinOp::Add,
                expr1: Box::new(Expr::Variable {
                    ident: "x".to_string(),
                }),
                expr2: Box::new(Expr::Literal {
                    val: Value::Number { val: 1 },
                }),
            },
        }];
        manager.execute_action("foo", &stmts).await.unwrap();
        manager.execute_action("foo", &stmts).await.unwrap();
        let result = manager.lookup("x", "foo", None).await.unwrap();
        assert_eq!(result, Value::Number { val: 2 });
    }

    // After a transaction completes, the variable's lock should be Unlocked.
    #[tokio::test]
    async fn test_txn_var_unlocked_after_commit() {
        let mut manager = manager_with_x().await;
        let stmts = vec![ActionStmt::Assign {
            var: "x".to_string(),
            expr: Expr::Literal {
                val: Value::Number { val: 42 },
            },
        }];
        manager.execute_action("foo", &stmts).await.unwrap();
        assert_x_unlocked(&manager);
    }

    // A successful transaction commits its buffered write and records the
    // transaction as the latest writer for that variable.
    #[tokio::test]
    async fn test_txn_successful_write_updates_value_and_latest_write_txn() {
        let mut manager = manager_with_x().await;
        let stmts = vec![ActionStmt::Assign {
            var: "x".to_string(),
            expr: Expr::Literal {
                val: Value::Number { val: 42 },
            },
        }];

        manager.execute_action("foo", &stmts).await.unwrap();

        let state = x_state(&manager);
        assert_eq!(state.value, Value::Number { val: 42 });
        assert!(state.latest_write_txn.is_some());
    }

    // A nested `do` (an action invoking another action) must reuse the same
    // transaction, not start a fresh one. The inner write to x should commit and
    // all locks should be released afterward. This guards the bug where nested
    // execution clobbered the outer transaction's lock tracking.
    #[tokio::test]
    async fn test_txn_nested_do_reuses_transaction() {
        let mut manager = manager_with_x().await;
        // outer action: do (action { x = x + 1; });
        let inner = Expr::Action(vec![ActionStmt::Assign {
            var: "x".to_string(),
            expr: Expr::Binop {
                op: crate::ast::BinOp::Add,
                expr1: Box::new(Expr::Variable {
                    ident: "x".to_string(),
                }),
                expr2: Box::new(Expr::Literal {
                    val: Value::Number { val: 1 },
                }),
            },
        }]);
        let stmts = vec![ActionStmt::Do(inner)];
        manager.execute_action("foo", &stmts).await.unwrap();

        // inner write took effect
        let result = manager.lookup("x", "foo", None).await.unwrap();
        assert_eq!(result, Value::Number { val: 1 });
        // and the lock was released
        assert_x_unlocked(&manager);
    }

    // A transaction that fails partway must leave no partial writes: writes are
    // buffered and applied only on a successful commit. Here the first statement
    // writes x, the second fails (asserting false), so x must stay unchanged.
    #[tokio::test]
    async fn test_txn_failed_transaction_leaves_no_partial_writes() {
        let mut manager = manager_with_x().await;
        let stmts = vec![
            ActionStmt::Assign {
                var: "x".to_string(),
                expr: Expr::Literal {
                    val: Value::Number { val: 99 },
                },
            },
            ActionStmt::Assert(Expr::Literal {
                val: Value::Bool { val: false },
            }),
        ];
        let result = manager.execute_action("foo", &stmts).await;
        assert!(result.is_err());
        // x must remain 0 — the buffered write to 99 was never committed
        let x = manager.lookup("x", "foo", None).await.unwrap();
        assert_eq!(x, Value::Number { val: 0 });
        // and the lock was released
        assert_x_unlocked(&manager);
    }

    // A failed transaction must not update either committed state field: the
    // value and latest writer should remain from the last successful commit.
    #[tokio::test]
    async fn test_txn_failed_transaction_preserves_previous_latest_write_txn() {
        let mut manager = manager_with_x().await;
        let successful_write = vec![ActionStmt::Assign {
            var: "x".to_string(),
            expr: Expr::Literal {
                val: Value::Number { val: 1 },
            },
        }];
        manager
            .execute_action("foo", &successful_write)
            .await
            .unwrap();
        let previous_txn = x_state(&manager).latest_write_txn.clone();
        assert!(previous_txn.is_some());

        let failing_write = vec![
            ActionStmt::Assign {
                var: "x".to_string(),
                expr: Expr::Literal {
                    val: Value::Number { val: 99 },
                },
            },
            ActionStmt::Assert(Expr::Literal {
                val: Value::Bool { val: false },
            }),
        ];

        let result = manager.execute_action("foo", &failing_write).await;

        assert!(result.is_err());
        let state = x_state(&manager);
        assert_eq!(state.value, Value::Number { val: 1 });
        assert_eq!(state.latest_write_txn, previous_txn);
        assert_x_unlocked(&manager);
    }

    // If a transaction fails after a read, its read lock must still be released.
    #[tokio::test]
    async fn test_txn_read_lock_released_after_failure() {
        let mut manager = manager_with_x().await;
        let stmts = vec![ActionStmt::Assert(Expr::Variable {
            ident: "x".to_string(),
        })];

        let result = manager.execute_action("foo", &stmts).await;

        assert!(result.is_err());
        assert_eq!(x_state(&manager).value, Value::Number { val: 0 });
        assert!(x_state(&manager).latest_write_txn.is_none());
        assert_x_unlocked(&manager);
    }

    // A transaction beginning in s1 composes an action defined in s2 (the
    // example from issue #44). Both services' writes must commit under the one
    // transaction, and the (service id, var) keying must keep them distinct.
    #[tokio::test]
    async fn test_txn_cross_service_composition() {
        let mut manager = Manager::new();
        // s2 owns w and an action that bumps it.
        let bump = Expr::Action(vec![ActionStmt::Assign {
            var: "w".to_string(),
            expr: Expr::Binop {
                op: crate::ast::BinOp::Add,
                expr1: Box::new(Expr::Variable {
                    ident: "w".to_string(),
                }),
                expr2: Box::new(Expr::Literal {
                    val: Value::Number { val: 5 },
                }),
            },
        }]);
        manager
            .create_service(
                "s2".to_string(),
                vec![
                    Decl::VarDecl {
                        name: "w".to_string(),
                        val: Expr::Literal {
                            val: Value::Number { val: 10 },
                        },
                    },
                    Decl::DefDecl {
                        name: "bump".to_string(),
                        val: bump,
                        is_pub: true,
                    },
                ],
            )
            .await
            .unwrap();
        // s1 owns x.
        manager
            .create_service(
                "s1".to_string(),
                vec![Decl::VarDecl {
                    name: "x".to_string(),
                    val: Expr::Literal {
                        val: Value::Number { val: 0 },
                    },
                }],
            )
            .await
            .unwrap();

        // Transaction on s1: x = x + 1; do s2.bump;
        let stmts = vec![
            ActionStmt::Assign {
                var: "x".to_string(),
                expr: Expr::Binop {
                    op: crate::ast::BinOp::Add,
                    expr1: Box::new(Expr::Variable {
                        ident: "x".to_string(),
                    }),
                    expr2: Box::new(Expr::Literal {
                        val: Value::Number { val: 1 },
                    }),
                },
            },
            ActionStmt::Do(Expr::MemberAccess {
                service: "s2".to_string(),
                member: "bump".to_string(),
            }),
        ];
        manager.execute_action("s1", &stmts).await.unwrap();

        // Both services' writes committed.
        assert_eq!(
            manager.lookup("x", "s1", None).await.unwrap(),
            Value::Number { val: 1 }
        );
        assert_eq!(
            manager.lookup("w", "s2", None).await.unwrap(),
            Value::Number { val: 15 }
        );
        // Locks released on both services.
        assert!(matches!(
            manager
                .services
                .get("s1")
                .unwrap()
                .vars
                .get("x")
                .unwrap()
                .lock,
            crate::runtime::txn::VarLock::Unlocked
        ));
        assert!(matches!(
            manager
                .services
                .get("s2")
                .unwrap()
                .vars
                .get("w")
                .unwrap()
                .lock,
            crate::runtime::txn::VarLock::Unlocked
        ));
    }

    // Wait-die: a younger transaction contending for a lock held by an older
    // transaction dies (abort) rather than acquiring it.
    #[tokio::test]
    async fn test_wait_die_younger_dies_at_acquire() {
        let mut manager = Manager::new();
        manager
            .create_service(
                "s1".to_string(),
                vec![Decl::VarDecl {
                    name: "x".to_string(),
                    val: Expr::Literal {
                        val: Value::Number { val: 0 },
                    },
                }],
            )
            .await
            .unwrap();
        let older = crate::runtime::txn::TxnId {
            timestamp: 1,
            node_id: 1,
            iteration: 0,
        };
        manager
            .services
            .get_mut("s1")
            .unwrap()
            .vars
            .get_mut("x")
            .unwrap()
            .lock = crate::runtime::txn::VarLock::WriteLocked(older);
        let younger = crate::runtime::txn::TxnId {
            timestamp: u128::MAX,
            node_id: 1,
            iteration: 0,
        };
        let result = manager.acquire_write_lock("s1", "x", &younger);
        assert!(matches!(result, Err(EvalError::WaitDieAbort(_))));
    }

    // Wait-die: an older transaction contending for a lock held by a younger
    // transaction takes the wait path, surfaced as WaitOn carrying the
    // contended (service, var) so the owner can park the request.
    #[tokio::test]
    async fn test_wait_die_older_takes_wait_path() {
        let mut manager = Manager::new();
        manager
            .create_service(
                "s1".to_string(),
                vec![Decl::VarDecl {
                    name: "x".to_string(),
                    val: Expr::Literal {
                        val: Value::Number { val: 0 },
                    },
                }],
            )
            .await
            .unwrap();
        let younger = crate::runtime::txn::TxnId {
            timestamp: u128::MAX,
            node_id: 1,
            iteration: 0,
        };
        manager
            .services
            .get_mut("s1")
            .unwrap()
            .vars
            .get_mut("x")
            .unwrap()
            .lock = crate::runtime::txn::VarLock::WriteLocked(younger);
        let older = crate::runtime::txn::TxnId {
            timestamp: 1,
            node_id: 1,
            iteration: 0,
        };
        let result = manager.acquire_write_lock("s1", "x", &older);
        assert!(matches!(result, Err(EvalError::WaitOn(_, _))));
    }

    // Wait-die end to end: an action whose variable is held by an older
    // transaction dies and retries, and after exhausting the bounded retries
    // returns WaitDieAbort without disturbing the older holder's lock.
    #[tokio::test]
    async fn test_wait_die_action_dies_and_retries() {
        let mut manager = Manager::new();
        manager
            .create_service(
                "s1".to_string(),
                vec![Decl::VarDecl {
                    name: "x".to_string(),
                    val: Expr::Literal {
                        val: Value::Number { val: 0 },
                    },
                }],
            )
            .await
            .unwrap();
        let older = crate::runtime::txn::TxnId {
            timestamp: 1,
            node_id: 1,
            iteration: 0,
        };
        manager
            .services
            .get_mut("s1")
            .unwrap()
            .vars
            .get_mut("x")
            .unwrap()
            .lock = crate::runtime::txn::VarLock::WriteLocked(older);
        let stmts = vec![ActionStmt::Assign {
            var: "x".to_string(),
            expr: Expr::Binop {
                op: crate::ast::BinOp::Add,
                expr1: Box::new(Expr::Variable {
                    ident: "x".to_string(),
                }),
                expr2: Box::new(Expr::Literal {
                    val: Value::Number { val: 1 },
                }),
            },
        }];
        let result = manager.execute_action("s1", &stmts).await;
        assert!(matches!(result, Err(EvalError::WaitDieAbort(_))));
        assert!(matches!(
            manager
                .services
                .get("s1")
                .unwrap()
                .vars
                .get("x")
                .unwrap()
                .lock,
            crate::runtime::txn::VarLock::WriteLocked(_)
        ));
    }

    // Wait-die: a participant action that conflicts mid-execution parks by
    // preserving its partial transaction (locks already taken stay held) in
    // pending_txns, so a later re-dispatch can resume rather than restart.
    #[tokio::test]
    async fn test_wait_die_participant_preserves_partial_txn() {
        let mut manager = Manager::new();
        manager
            .create_service(
                "s1".to_string(),
                vec![
                    Decl::VarDecl {
                        name: "y".to_string(),
                        val: Expr::Literal {
                            val: Value::Number { val: 0 },
                        },
                    },
                    Decl::VarDecl {
                        name: "x".to_string(),
                        val: Expr::Literal {
                            val: Value::Number { val: 0 },
                        },
                    },
                ],
            )
            .await
            .unwrap();
        // A younger transaction holds a write lock on x.
        let younger = crate::runtime::txn::TxnId {
            timestamp: u128::MAX,
            node_id: 1,
            iteration: 0,
        };
        manager
            .services
            .get_mut("s1")
            .unwrap()
            .vars
            .get_mut("x")
            .unwrap()
            .lock = crate::runtime::txn::VarLock::WriteLocked(younger);
        // Older transaction: write y (acquires y), then touch x (conflict, waits).
        let older = crate::runtime::txn::TxnId {
            timestamp: 1,
            node_id: 1,
            iteration: 0,
        };
        let stmts = vec![
            ActionStmt::Assign {
                var: "y".to_string(),
                expr: Expr::Literal {
                    val: Value::Number { val: 5 },
                },
            },
            ActionStmt::Assign {
                var: "x".to_string(),
                expr: Expr::Binop {
                    op: crate::ast::BinOp::Add,
                    expr1: Box::new(Expr::Variable {
                        ident: "x".to_string(),
                    }),
                    expr2: Box::new(Expr::Literal {
                        val: Value::Number { val: 1 },
                    }),
                },
            },
        ];
        let result = manager
            .execute_action_participant("s1", &stmts, &[], older.clone())
            .await;
        // Parked: returns WaitOn, and the partial transaction is preserved.
        assert!(matches!(result, Err(EvalError::WaitOn(_, _))));
        assert!(manager.pending_txns.contains_key(&older));
        // The lock it already took on y is still held (not released on park).
        assert!(matches!(
            manager
                .services
                .get("s1")
                .unwrap()
                .vars
                .get("y")
                .unwrap()
                .lock,
            crate::runtime::txn::VarLock::WriteLocked(_)
        ));
    }

    // Wait-die: parked requests on a variable are served oldest-first when the
    // lock frees, and a transaction's waiters are purged when it aborts.
    #[tokio::test]
    async fn test_wait_queue_oldest_first_and_purge() {
        let mut manager = Manager::new();
        manager
            .create_service(
                "s1".to_string(),
                vec![Decl::VarDecl {
                    name: "x".to_string(),
                    val: Expr::Literal {
                        val: Value::Number { val: 0 },
                    },
                }],
            )
            .await
            .unwrap();
        let make = |rid: u64, tid: crate::runtime::txn::TxnId| ParkedRequest::Action {
            request_id: rid,
            reply_to: String::new(),
            service: "s1".to_string(),
            stmts: vec![],
            env: vec![],
            tid,
        };
        let old = crate::runtime::txn::TxnId {
            timestamp: 1,
            node_id: 1,
            iteration: 0,
        };
        let mid = crate::runtime::txn::TxnId {
            timestamp: 5,
            node_id: 1,
            iteration: 0,
        };
        manager.park_request("s1", "x".to_string(), make(1, mid.clone()));
        manager.park_request("s1", "x".to_string(), make(2, old.clone()));
        // Freeing x yields the oldest waiter first; the other stays parked.
        let mut freed = std::collections::HashSet::new();
        freed.insert((manager.id_for_service("s1"), "x".to_string()));
        let ready = manager.take_ready_waiters(&freed);
        assert_eq!(ready.len(), 1);
        assert!(ready[0].tid() == &old);
        // The remaining (mid) waiter is purged when its transaction aborts.
        let removed = manager.purge_parked_txn(&mid);
        assert_eq!(removed.len(), 1);
        assert!(manager.wait_queue.is_empty());
    }

    // Wait-die end to end (single node, no network): an older transaction parks
    // on a variable held by a younger one; when the younger aborts and frees the
    // lock, the parked request is taken oldest-first and its re-run resumes from
    // the preserved transaction and now succeeds.
    #[tokio::test]
    async fn test_wait_die_parked_request_resumes_after_release() {
        let mut manager = Manager::new();
        manager
            .create_service(
                "s1".to_string(),
                vec![Decl::VarDecl {
                    name: "x".to_string(),
                    val: Expr::Literal {
                        val: Value::Number { val: 0 },
                    },
                }],
            )
            .await
            .unwrap();

        // A younger transaction holds a write lock on x, prepared in pending_txns.
        let younger = crate::runtime::txn::TxnId {
            timestamp: u128::MAX,
            node_id: 1,
            iteration: 0,
        };
        manager
            .services
            .get_mut("s1")
            .unwrap()
            .vars
            .get_mut("x")
            .unwrap()
            .lock = crate::runtime::txn::VarLock::WriteLocked(younger.clone());
        let mut younger_txn = crate::runtime::txn::Transaction::new(younger.clone());
        younger_txn
            .locked
            .insert((manager.id_for_service("s1"), "x".to_string()));
        manager.pending_txns.insert(younger.clone(), younger_txn);

        // Older transaction: x = x + 1 conflicts -> WaitOn -> park it.
        let older = crate::runtime::txn::TxnId {
            timestamp: 1,
            node_id: 1,
            iteration: 0,
        };
        let stmts = vec![ActionStmt::Assign {
            var: "x".to_string(),
            expr: Expr::Binop {
                op: crate::ast::BinOp::Add,
                expr1: Box::new(Expr::Variable {
                    ident: "x".to_string(),
                }),
                expr2: Box::new(Expr::Literal {
                    val: Value::Number { val: 1 },
                }),
            },
        }];
        let r1 = manager
            .execute_action_participant("s1", &stmts, &[], older.clone())
            .await;
        assert!(matches!(r1, Err(EvalError::WaitOn(_, _))));
        manager.park_request(
            "s1",
            "x".to_string(),
            ParkedRequest::Action {
                request_id: 1,
                reply_to: String::new(),
                service: "s1".to_string(),
                stmts: stmts.clone(),
                env: vec![],
                tid: older.clone(),
            },
        );

        // The younger holder aborts, freeing x.
        let freed = manager.abort_participant(&younger).await;
        assert!(matches!(
            manager
                .services
                .get("s1")
                .unwrap()
                .vars
                .get("x")
                .unwrap()
                .lock,
            crate::runtime::txn::VarLock::Unlocked
        ));

        // Wake: take the oldest waiter and re-run it; it should now succeed.
        let ready = manager.take_ready_waiters(&freed);
        assert_eq!(ready.len(), 1);
        if let ParkedRequest::Action {
            service,
            stmts,
            env,
            tid,
            ..
        } = &ready[0]
        {
            let r2 = manager
                .execute_action_participant(service, stmts, env, tid.clone())
                .await;
            assert!(r2.is_ok());
        } else {
            panic!("expected an Action waiter");
        }

        // The older transaction now holds x's write lock and is prepared.
        assert!(matches!(
            manager
                .services
                .get("s1")
                .unwrap()
                .vars
                .get("x")
                .unwrap()
                .lock,
            crate::runtime::txn::VarLock::WriteLocked(_)
        ));
        assert!(manager.pending_txns.contains_key(&older));
    }
}
