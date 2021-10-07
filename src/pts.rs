//! Pure type system type-checking algorithm.

use std::{
    collections::HashMap,
    fmt::{Debug, Display},
    hash::Hash,
};

use crate::{
    ast::{self, Def, ExprEnum},
    Env, Expr, TypeCheckError,
};

pub struct PureTypeSystem<S> {
    pub axioms: HashMap<S, S>,
    pub rules: HashMap<(S, S), S>,
}

impl<S: Clone + Display + Debug + Hash + Eq> PureTypeSystem<S> {
    pub fn check_expr(&self, env: &Env<S>, expr: &Expr<S>) -> Result<Expr<S>, TypeCheckError<S>> {
        Ok(match expr.inner() {
            ExprEnum::ConstSort(s) => {
                if let Some(meta) = self.axioms.get(s) {
                    ast::sort(meta.clone())
                } else {
                    return Err(TypeCheckError::UntypedSort(s.clone()));
                }
            }
            ExprEnum::Var(v) => {
                if let Some(v_ty) = env.get(v) {
                    v_ty.clone()
                } else {
                    return Err(TypeCheckError::UndeclaredVar(v.clone()));
                }
            }
            ExprEnum::Pi(x, x_ty, body_ty) => {
                let x_sort = match self.check_expr(env, x_ty)?.inner() {
                    ExprEnum::ConstSort(s) => s.clone(),
                    _ => {
                        return Err(TypeCheckError::InvalidPiParameterType(
                            expr.clone(),
                            x_ty.clone(),
                        ))
                    }
                };
                let body_ty_ty = self.check_expr(&env.with(x.clone(), x_ty.clone()), body_ty)?;
                let body_sort = match body_ty_ty.inner() {
                    ExprEnum::ConstSort(s) => s.clone(),
                    _ => {
                        return Err(TypeCheckError::InvalidPiReturnType(
                            expr.clone(),
                            body_ty.clone(),
                        ))
                    }
                };
                if let Some(s) = self.rules.get(&(x_sort.clone(), body_sort.clone())) {
                    ast::sort(s.clone())
                } else {
                    return Err(TypeCheckError::InvalidPiSorts(
                        expr.clone(),
                        x_sort,
                        body_sort,
                    ));
                }
            }
            ExprEnum::Apply(f, arg) => {
                let f_ty = self.check_expr(env, f)?;
                if let ExprEnum::Pi(x, expected_arg_ty, body_ty_expr) = f_ty.inner() {
                    let actual_arg_ty: Expr<S> = self.check_expr(env, arg)?;
                    let expected_arg_ty: Expr<S> = expected_arg_ty.clone();
                    if actual_arg_ty != expected_arg_ty {
                        return Err(TypeCheckError::ArgumentTypeMismatch(
                            expr.clone(),
                            expected_arg_ty,
                            actual_arg_ty,
                        ));
                    }
                    body_ty_expr.subst(x, &actual_arg_ty)
                } else {
                    return Err(TypeCheckError::FunctionExpected(
                        expr.clone(),
                        f.clone(),
                        f_ty,
                    ));
                }
            }
            ExprEnum::Lambda(p, p_ty, body) => {
                let body_ty = self.check_expr(&env.with(p.clone(), p_ty.clone()), body)?;
                let product_ty = ast::pi(p.clone(), p_ty.clone(), body_ty);
                let _product_ty_ty = self.check_expr(env, &product_ty)?;
                product_ty
            }
            ExprEnum::Blank => {
                return Err(TypeCheckError::Blank);
            }
        })
    }

    pub fn check_program(
        &self,
        env: &Env<S>,
        program: Vec<Def<S>>,
    ) -> Result<Env<S>, TypeCheckError<S>> {
        let mut env = env.clone();
        for def in program {
            let ty = if let Some(defined_ty) = def.ty {
                // There's a defined type; type-check to make sure it's not nonsense.
                self.check_expr(&env, &defined_ty)?;

                if let Some(term) = def.term {
                    let actual_ty = self.check_expr(&env, &term)?;
                    assert_eq!(actual_ty, defined_ty); // unify
                }
                defined_ty
            } else {
                let term = def.term.expect("def must have a term or type");
                self.check_expr(&env, &term)?
            };
            env.push(def.id, ty);
        }
        Ok(env)
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Context;

    #[cfg(test)]
    use pretty_assertions::assert_eq;

    use super::*;
    use crate::ast::*;
    use crate::parser::{ProgramParser, TermParser};
    use USort::*;

    fn system_u() -> PureTypeSystem<USort> {
        PureTypeSystem {
            axioms: vec![(Type, Kind), (Kind, Triangle)].into_iter().collect(),
            rules: vec![
                ((Type, Type), Type),
                ((Kind, Type), Type),
                ((Kind, Kind), Kind),
                ((Triangle, Type), Type),
                ((Triangle, Kind), Kind),
            ]
            .into_iter()
            .collect(),
        }
    }

    #[allow(dead_code)]
    fn u_env() -> Env<USort> {
        vec![
            (Id::from("Type"), ast::sort(Type)),
            (Id::from("Kind"), ast::sort(Kind)),
        ]
        .into_iter()
        .collect()
    }

    fn parse(s: &'static str) -> Expr<USort> {
        TermParser::new().parse(s).context("parse error").unwrap()
    }

    fn parse_program(s: &'static str) -> Vec<Def<USort>> {
        ProgramParser::new()
            .parse(s)
            .context("parse error")
            .unwrap()
    }

    #[test]
    fn test_id() {
        let u = system_u();

        // λ (t : *), λ (x : t), x
        let id_expr = lambda("t", sort(Type), lambda("x", var("t"), var("x")));
        let id_type = u.check_expr(&Env::new(), &id_expr).unwrap();
        println!("The type of `{}` is `{}`", id_expr, id_type);

        // Π (t : *), Π (x : t), t
        assert_eq!(id_type, pi("t", sort(Type), pi("x", var("t"), var("t"))),);
    }

    #[test]
    fn test_girard() {
        let expr = parse("λ (k : Kind) . λ (α : k -> k) . λ (β : k) . (α (α β))");
        let ty = parse("Π (k : Kind) . Π (α : k -> k) . Π (β : k) . k");

        let u = system_u();
        assert_eq!(u.check_expr(&Env::new(), &expr).unwrap(), ty);
    }

    #[test]
    fn test_parser() {
        assert_eq!(parse("Type"), sort(Type));
        assert_eq!(parse("Kind"), sort(Kind));

        assert_eq!(parse("a b c"), apply(apply(var("a"), var("b")), var("c")));
        assert_eq!(
            parse("a -> b -> c"),
            arrow(var("a"), arrow(var("b"), var("c")))
        );

        assert_eq!(
            parse("λ (t : Type) . λ (x : t) . x"),
            lambda("t", sort(Type), lambda("x", var("t"), var("x"))),
        );

        assert_eq!(
            parse("λ (k : Kind) . λ (α : k -> k) . λ (β : k) . (α (α β))"),
            lambda(
                "k",
                sort(Kind),
                lambda(
                    "α",
                    arrow(var("k"), var("k")),
                    lambda("β", var("k"), apply(var("α"), apply(var("α"), var("β"))))
                )
            )
        );
    }

    #[test]
    fn test_program_parser() {
        let u = system_u();
        let base_env = u_env();
        let actual_env = u
            .check_program(
                &base_env,
                parse_program(
                    "
                axiom true : Type;
                axiom trivial : true;
                def tx : Π (p : Type) . p -> true := λ (p : Type) . λ (_ : p) . trivial;
                axiom false : Type;
                axiom ffs : Π (p : Type) . false -> p;
                ",
                ),
            )
            .unwrap();

        let mut expected_env = base_env;
        expected_env.push(Id::from("true"), sort(Type));
        expected_env.push(Id::from("trivial"), var("true"));
        expected_env.push(
            Id::from("ffs"),
            pi("p", sort(Type), arrow(var("false"), var("p"))),
        );
        expected_env.push(Id::from("false"), sort(Type));
        expected_env.push(
            Id::from("tx"),
            pi("p", sort(Type), arrow(var("p"), var("true"))),
        );

        assert_eq!(actual_env, expected_env);
    }
}
