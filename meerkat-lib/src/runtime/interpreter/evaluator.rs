use crate::ast::{BinOp, Expr, UnOp, Value};
use crate::runtime::manager::Manager;
use crate::runtime::txn::Transaction;
use std::collections::HashSet;

#[derive(Debug)]
pub enum EvalError {
    TypeError(String),
    NetworkError(String),
    LookupError(String),
    NotImplemented,
    LockConflict(String),
    /// A transaction lost a wait-die contest (an older transaction holds the
    /// lock) and must abort and retry with a higher iteration.
    WaitDieAbort(String),
    /// Wait-die wait: the requester is older than the current holder and should
    /// wait for the lock to free. Carries the contended (service, var) so the
    /// owner can park the request on that variable's wait queue.
    WaitOn(String, String),
}

impl std::fmt::Display for EvalError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            EvalError::TypeError(s) => write!(f, "Type error: {}", s),
            EvalError::NetworkError(s) => write!(f, "Network error: {}", s),
            EvalError::LookupError(s) => write!(f, "Lookup error: {}", s),
            EvalError::NotImplemented => write!(f, "Not yet implemented"),
            EvalError::LockConflict(s) => write!(f, "Lock conflict: {}", s),
            EvalError::WaitDieAbort(s) => write!(f, "Wait-die abort: {}", s),
            EvalError::WaitOn(service, var) => write!(f, "Wait-die wait on {}::{}", service, var),
        }
    }
}

impl std::error::Error for EvalError {}

/// Evaluation context: holds the stable execution state that doesn't
/// change per call frame. Passed as &mut so manager can be updated.
/// env is kept separate since it changes at each function call boundary.
pub struct EvalContext<'a> {
    pub manager: &'a mut Manager,
    pub service_name: &'a str,
    /// Active transaction, if evaluation is happening inside one.
    pub txn: Option<&'a mut Transaction>,
}

#[async_recursion::async_recursion]
pub async fn eval(
    expr: &Expr,
    env: &[(String, Value)],
    ctx: &mut EvalContext<'_>,
) -> Result<Value, EvalError> {
    match expr {
        Expr::Literal { val } => Ok(val.clone()),

        Expr::Call { func, args } => {
            let func_val = eval(func, env, ctx).await?;
            let mut arg_vals = Vec::new();
            for arg in args {
                arg_vals.push(eval(arg, env, ctx).await?);
            }
            match func_val {
                Value::Closure {
                    params,
                    body,
                    env: closure_env,
                    service_name: closure_svc,
                } => {
                    let mut new_env = closure_env.clone();
                    for (param, arg_val) in params.iter().zip(arg_vals) {
                        new_env.push((param.clone(), arg_val));
                    }
                    eval(
                        &body,
                        &new_env,
                        &mut EvalContext {
                            manager: ctx.manager,
                            service_name: &closure_svc,
                            txn: ctx.txn.as_deref_mut(),
                        },
                    )
                    .await
                }
                _ => Err(EvalError::TypeError(
                    "Attempting to call a non-function value".to_string(),
                )),
            }
        }

        Expr::Variable { ident } => {
            for (var_name, var_val) in env.iter().rev() {
                if var_name == ident {
                    return Ok(var_val.clone());
                }
            }
            ctx.manager
                .lookup(ident, ctx.service_name, ctx.txn.as_deref_mut())
                .await
        }

        Expr::Binop { op, expr1, expr2 } => {
            let val1 = eval(expr1, env, ctx).await?;
            let val2 = eval(expr2, env, ctx).await?;
            match (op, val1, val2) {
                (BinOp::Add, Value::Number { val: v1 }, Value::Number { val: v2 }) => {
                    Ok(Value::Number { val: v1 + v2 })
                }
                (BinOp::Sub, Value::Number { val: v1 }, Value::Number { val: v2 }) => {
                    Ok(Value::Number { val: v1 - v2 })
                }
                (BinOp::Mul, Value::Number { val: v1 }, Value::Number { val: v2 }) => {
                    Ok(Value::Number { val: v1 * v2 })
                }
                (BinOp::Div, Value::Number { val: v1 }, Value::Number { val: v2 }) => {
                    Ok(Value::Number { val: v1 / v2 })
                }
                (BinOp::Eq, Value::Number { val: v1 }, Value::Number { val: v2 }) => {
                    Ok(Value::Bool { val: v1 == v2 })
                }
                (BinOp::Lt, Value::Number { val: v1 }, Value::Number { val: v2 }) => {
                    Ok(Value::Bool { val: v1 < v2 })
                }
                (BinOp::Gt, Value::Number { val: v1 }, Value::Number { val: v2 }) => {
                    Ok(Value::Bool { val: v1 > v2 })
                }
                (BinOp::And, Value::Bool { val: v1 }, Value::Bool { val: v2 }) => {
                    Ok(Value::Bool { val: v1 && v2 })
                }
                (BinOp::Or, Value::Bool { val: v1 }, Value::Bool { val: v2 }) => {
                    Ok(Value::Bool { val: v1 || v2 })
                }
                _ => Err(EvalError::TypeError(
                    "Type error in binary operation".to_string(),
                )),
            }
        }

        Expr::Unop { op, expr } => {
            let val = eval(expr, env, ctx).await?;
            match (op, val) {
                (UnOp::Neg, Value::Number { val: v }) => Ok(Value::Number { val: -v }),
                (UnOp::Not, Value::Bool { val: v }) => Ok(Value::Bool { val: !v }),
                _ => Err(EvalError::TypeError(
                    "Type error in unary operation".to_string(),
                )),
            }
        }

        Expr::If { cond, expr1, expr2 } => {
            let cond_val = eval(cond, env, ctx).await?;
            match cond_val {
                Value::Bool { val: true } => eval(expr1, env, ctx).await,
                Value::Bool { val: false } => eval(expr2, env, ctx).await,
                _ => Err(EvalError::TypeError(
                    "Condition must be boolean".to_string(),
                )),
            }
        }

        Expr::Func { params, body } => {
            let var_binded: HashSet<String> = params.iter().cloned().collect();
            let free_vars = body.free_var(&HashSet::new(), &var_binded);
            let captured_env: Vec<(String, Value)> = env
                .iter()
                .filter(|(name, _)| {
                    free_vars.contains(name)
                        && !ctx
                            .manager
                            .services
                            .get(ctx.service_name)
                            .map(|s| {
                                s.vars.contains_key(name.as_str())
                                    || s.defs.contains_key(name.as_str())
                            })
                            .unwrap_or(false)
                })
                .cloned()
                .collect();
            Ok(Value::Closure {
                params: params.clone(),
                body: body.clone(),
                env: captured_env,
                service_name: ctx.service_name.to_string(),
            })
        }

        Expr::Action(stmts) => {
            // Use free_var on the Action expression itself to find free variables
            // Service vars/defs are looked up fresh via the manager at execution time
            let action_expr = Expr::Action(stmts.clone());
            let free_vars = action_expr.free_var(
                &std::collections::HashSet::new(),
                &std::collections::HashSet::new(),
            );
            let captured_env: Vec<(String, Value)> = env
                .iter()
                .filter(|(name, _)| {
                    free_vars.contains(name)
                        && !ctx
                            .manager
                            .services
                            .get(ctx.service_name)
                            .map(|s| {
                                s.vars.contains_key(name.as_str())
                                    || s.defs.contains_key(name.as_str())
                            })
                            .unwrap_or(false)
                })
                .cloned()
                .collect();
            Ok(Value::ActionClosure {
                stmts: stmts.clone(),
                env: captured_env,
                // Stamp the action with its owning service's identity (which
                // embeds this node's address), so it stays executable wherever
                // the closure travels.
                service: ctx.manager.id_for_service(ctx.service_name),
            })
        }

        Expr::MemberAccess { service, member } => {
            // #24: a reactive recompute pre-seeds env with each cross-service
            // dep's cached value under its qualified name "service.member" (the
            // dot keeps it from colliding with any real identifier), so the
            // recompute resolves from cache instead of a network round-trip.
            let qualified = format!("{}.{}", service, member);
            for (name, val) in env.iter().rev() {
                if name == &qualified {
                    return Ok(val.clone());
                }
            }
            // Manager figures out whether service is local or remote
            ctx.manager
                .lookup(member, service, ctx.txn.as_deref_mut())
                .await
        }
        _ => Err(EvalError::NotImplemented),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{ActionStmt, BinOp, Expr, Value};
    use crate::runtime::Manager;

    #[tokio::test]
    async fn test_literal() {
        let mut manager = Manager::default();
        let mut ctx = EvalContext {
            manager: &mut manager,
            service_name: "",
            txn: None,
        };
        let expr = Expr::Literal {
            val: Value::Number { val: 42 },
        };
        let result = eval(&expr, &[], &mut ctx).await.unwrap();
        assert_eq!(result, Value::Number { val: 42 });
    }

    #[tokio::test]
    async fn test_binop_add() {
        let mut manager = Manager::default();
        let mut ctx = EvalContext {
            manager: &mut manager,
            service_name: "",
            txn: None,
        };
        let expr = Expr::Binop {
            op: BinOp::Add,
            expr1: Box::new(Expr::Literal {
                val: Value::Number { val: 2 },
            }),
            expr2: Box::new(Expr::Literal {
                val: Value::Number { val: 3 },
            }),
        };
        let result = eval(&expr, &[], &mut ctx).await.unwrap();
        assert_eq!(result, Value::Number { val: 5 });
    }

    #[tokio::test]
    async fn test_func_and_call() {
        let mut manager = Manager::default();
        let mut ctx = EvalContext {
            manager: &mut manager,
            service_name: "",
            txn: None,
        };
        let func_expr = Expr::Func {
            params: vec!["x".to_string()],
            body: Box::new(Expr::Binop {
                op: BinOp::Add,
                expr1: Box::new(Expr::Variable {
                    ident: "x".to_string(),
                }),
                expr2: Box::new(Expr::Literal {
                    val: Value::Number { val: 10 },
                }),
            }),
        };
        let call_expr = Expr::Call {
            func: Box::new(func_expr),
            args: vec![Expr::Literal {
                val: Value::Number { val: 5 },
            }],
        };
        let result = eval(&call_expr, &[], &mut ctx).await.unwrap();
        assert_eq!(result, Value::Number { val: 15 });
    }

    #[tokio::test]
    async fn test_action_creation() {
        let mut manager = Manager::default();
        let mut ctx = EvalContext {
            manager: &mut manager,
            service_name: "",
            txn: None,
        };
        let action_expr = Expr::Action(vec![ActionStmt::Assign {
            var: "x".to_string(),
            expr: Expr::Literal {
                val: Value::Number { val: 5 },
            },
        }]);
        let result = eval(&action_expr, &[], &mut ctx).await.unwrap();
        match result {
            Value::ActionClosure { stmts, .. } => assert_eq!(stmts.len(), 1),
            _ => panic!("Expected ActionClosure"),
        }
    }

    #[tokio::test]
    async fn test_closure_captures_only_free_vars() {
        let mut manager = Manager::default();
        let mut ctx = EvalContext {
            manager: &mut manager,
            service_name: "",
            txn: None,
        };
        let env = vec![
            ("a".to_string(), Value::Number { val: 1 }),
            ("b".to_string(), Value::Number { val: 2 }),
            ("c".to_string(), Value::Number { val: 3 }),
        ];
        let func_expr = Expr::Func {
            params: vec!["x".to_string()],
            body: Box::new(Expr::Binop {
                op: BinOp::Add,
                expr1: Box::new(Expr::Variable {
                    ident: "x".to_string(),
                }),
                expr2: Box::new(Expr::Variable {
                    ident: "a".to_string(),
                }),
            }),
        };
        let result = eval(&func_expr, &env, &mut ctx).await.unwrap();
        match result {
            Value::Closure {
                params,
                body: _,
                env: captured_env,
                ..
            } => {
                assert_eq!(params.len(), 1);
                assert_eq!(captured_env.len(), 1);
                assert_eq!(captured_env[0].0, "a");
                assert_eq!(captured_env[0].1, Value::Number { val: 1 });
            }
            _ => panic!("Expected Closure"),
        }
    }
}
