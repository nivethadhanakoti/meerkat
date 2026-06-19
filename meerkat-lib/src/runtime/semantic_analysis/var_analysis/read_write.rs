use crate::ast::{ActionStmt, Expr};
use std::collections::HashSet;

impl Expr {
    /// Collect every cross-service reference (service, member) appearing
    /// anywhere in this expression. This is the cross-service counterpart to
    /// free_var: free_var deliberately drops MemberAccess (returning no local
    /// free vars for s1.y), so without this pass a def's dependencies on other
    /// services are invisible to the dependency analysis. Issue #24 uses it to
    /// learn which remote members a def must subscribe to for change updates.
    pub fn cross_service_deps(&self) -> HashSet<(String, String)> {
        match self {
            Expr::Literal { .. } | Expr::Table { .. } | Expr::Variable { .. } => HashSet::new(),
            Expr::MemberAccess { service, member } => {
                HashSet::from([(service.clone(), member.clone())])
            }
            Expr::KeyVal { value, .. } => value.cross_service_deps(),
            Expr::Tuple { val } => {
                let mut deps = HashSet::new();
                for item in val {
                    deps.extend(item.cross_service_deps());
                }
                deps
            }
            Expr::Unop { expr, .. } => expr.cross_service_deps(),
            Expr::Binop { expr1, expr2, .. } => {
                let mut deps = expr1.cross_service_deps();
                deps.extend(expr2.cross_service_deps());
                deps
            }
            Expr::If { cond, expr1, expr2 } => {
                let mut deps = cond.cross_service_deps();
                deps.extend(expr1.cross_service_deps());
                deps.extend(expr2.cross_service_deps());
                deps
            }
            Expr::Func { body, .. } => body.cross_service_deps(),
            Expr::Call { func, args } => {
                let mut deps = func.cross_service_deps();
                for arg in args {
                    deps.extend(arg.cross_service_deps());
                }
                deps
            }
            Expr::Action(stmts) => {
                let mut deps = HashSet::new();
                for stmt in stmts {
                    match stmt {
                        ActionStmt::Assign { expr, .. } => deps.extend(expr.cross_service_deps()),
                        ActionStmt::Do(expr) => deps.extend(expr.cross_service_deps()),
                        ActionStmt::Assert(expr) => deps.extend(expr.cross_service_deps()),
                        ActionStmt::Let { expr, .. } => deps.extend(expr.cross_service_deps()),
                        ActionStmt::Expr(expr) => deps.extend(expr.cross_service_deps()),
                        ActionStmt::Insert { row, .. } => deps.extend(row.cross_service_deps()),
                    }
                }
                deps
            }
            Expr::Select { where_clause, .. } => where_clause.cross_service_deps(),
            Expr::Fold {
                operation,
                identity,
                ..
            } => {
                let mut deps = operation.cross_service_deps();
                deps.extend(identity.cross_service_deps());
                deps
            }
        }
    }

    /// return free variables in expr wrt var_binded, used for
    /// 1. for extracting dependency of each def declaration
    /// 2. for evaluation a expression (substitution based evaluation)
    pub fn free_var(
        &self,
        reactive_names: &HashSet<String>,
        var_binded: &HashSet<String>,
    ) -> HashSet<String> {
        match self {
            Expr::Literal { .. } | Expr::Table { .. } => HashSet::new(),
            Expr::Variable { ident } => {
                if var_binded.contains(ident) {
                    HashSet::new()
                } else {
                    HashSet::from([ident.clone()])
                }
            }
            Expr::KeyVal { value, .. } => value.free_var(reactive_names, var_binded),
            Expr::Tuple { val } => {
                let mut free_vars = HashSet::new();
                for item in val {
                    free_vars.extend(item.free_var(reactive_names, var_binded));
                }
                free_vars
            }
            Expr::Unop { op: _, expr } => expr.free_var(reactive_names, var_binded),
            Expr::Binop {
                op: _,
                expr1,
                expr2,
            } => {
                let mut free_vars = expr1.free_var(reactive_names, var_binded);
                free_vars.extend(expr2.free_var(reactive_names, var_binded));
                free_vars
            }
            Expr::If { cond, expr1, expr2 } => {
                let mut free_vars = cond.free_var(reactive_names, var_binded);
                free_vars.extend(expr1.free_var(reactive_names, var_binded));
                free_vars.extend(expr2.free_var(reactive_names, var_binded));
                free_vars
            }
            Expr::Func { params, body } => {
                let mut new_binds = var_binded.clone();
                new_binds.extend(params.iter().cloned());
                body.free_var(reactive_names, &new_binds)
            }
            Expr::Call { func, args } => {
                let mut free_vars = func.free_var(reactive_names, var_binded);
                for arg in args {
                    free_vars.extend(arg.free_var(reactive_names, var_binded));
                }
                free_vars
            }
            Expr::Action(stmts) => {
                let mut free_vars = HashSet::new();
                for stmt in stmts {
                    match stmt {
                        ActionStmt::Assign { var: _, expr } => {
                            free_vars.extend(expr.free_var(reactive_names, var_binded));
                        }
                        ActionStmt::Do(expr) => {
                            free_vars.extend(expr.free_var(reactive_names, var_binded));
                        }
                        ActionStmt::Assert(expr) => {
                            free_vars.extend(expr.free_var(reactive_names, var_binded));
                        }
                        ActionStmt::Let { name: _, expr } => {
                            free_vars.extend(expr.free_var(reactive_names, var_binded));
                        }
                        ActionStmt::Expr(expr) => {
                            free_vars.extend(expr.free_var(reactive_names, var_binded));
                        }
                        ActionStmt::Insert { row, .. } => {
                            free_vars.extend(row.free_var(reactive_names, var_binded));
                        }
                    }
                }
                free_vars.difference(reactive_names).cloned().collect()
            }
            Expr::MemberAccess { .. } => {
                // member access on another service - no local free vars
                HashSet::new()
            }
            Expr::Select {
                table_name,
                where_clause,
                ..
            } => {
                let mut free_vars = where_clause.free_var(reactive_names, var_binded);
                free_vars.insert(table_name.clone());
                free_vars
            }
            Expr::Fold {
                operation,
                identity,
                ..
            } => {
                let mut free_vars = HashSet::new();
                free_vars.extend(operation.free_var(reactive_names, var_binded));
                free_vars.extend(identity.free_var(reactive_names, var_binded));
                free_vars
            }
        }
    }
}

#[cfg(test)]
mod cross_service_deps_tests {
    use crate::ast::Expr;
    use std::collections::HashSet;

    fn member(service: &str, member: &str) -> Expr {
        Expr::MemberAccess {
            service: service.to_string(),
            member: member.to_string(),
        }
    }

    #[test]
    fn collects_member_access_in_a_def_body() {
        // mirrors: pub def inc_delegate = fn n => s1.inc_x;
        let expr = Expr::Func {
            params: vec!["n".to_string()],
            body: Box::new(member("s1", "inc_x")),
        };
        assert_eq!(
            expr.cross_service_deps(),
            HashSet::from([("s1".to_string(), "inc_x".to_string())])
        );
    }

    #[test]
    fn recurses_into_nesting_and_ignores_local_names() {
        // s1.y and s2.w buried at different depths, with a local variable x
        // that must not be collected (it is not a cross-service reference).
        let expr = Expr::Tuple {
            val: vec![
                member("s1", "y"),
                Expr::Variable {
                    ident: "x".to_string(),
                },
                Expr::Func {
                    params: vec![],
                    body: Box::new(member("s2", "w")),
                },
            ],
        };
        assert_eq!(
            expr.cross_service_deps(),
            HashSet::from([
                ("s1".to_string(), "y".to_string()),
                ("s2".to_string(), "w".to_string()),
            ])
        );
    }

    #[test]
    fn a_purely_local_def_has_no_cross_service_deps() {
        // mirrors: pub def y = x + 1;  (no MemberAccess anywhere)
        let expr = Expr::Variable {
            ident: "x".to_string(),
        };
        assert!(expr.cross_service_deps().is_empty());
    }
}
