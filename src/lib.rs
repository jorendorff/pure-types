use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;

use lalrpop_util::lalrpop_mod;

pub mod ast;
lalrpop_mod!(pub parser);

pub use ast::{Expr, USort, Var};

pub struct PureTypeSystem<S> {
    pub axioms: HashMap<S, S>,
    pub rules: HashMap<(S, S), S>,
}

pub enum Env<'a, S> {
    Empty,
    Bind(Var, &'a Expr<S>, &'a Env<'a, S>),
}

impl<'a, S> Env<'a, S> {
    fn get(&self, x: Var) -> Option<&'a Expr<S>> {
        let mut current = self;
        while let Env::Bind(bind_key, bind_value, tail) = current {
            if *bind_key == x {
                return Some(*bind_value);
            }
            current = tail;
        }
        None
    }
}

impl<S: Clone + Debug + Hash + Eq> PureTypeSystem<S> {
    pub fn typeck(&self, env: &Env<S>, expr: &Expr<S>) -> Box<Expr<S>> {
        match expr {
            Expr::ConstSort(s) => {
                if let Some(meta) = self.axioms.get(s) {
                    ast::sort(meta.clone())
                } else {
                    panic!(
                        "{:?} can't be used as an expression in code; it has no type",
                        expr
                    );
                }
            }
            Expr::Var(v) => {
                if let Some(v_ty) = env.get(*v) {
                    Box::new(v_ty.clone())
                } else {
                    panic!("can't find value `{:?}` in this scope", *v);
                }
            }
            Expr::Product(x, x_ty, body_ty) => {
                let x_sort = match *self.typeck(env, x_ty) {
                    Expr::ConstSort(s) => s,
                    _ => panic!(
                        "invalid type: {:?} (because the type of {:?} is not a sort)",
                        expr, x_ty
                    ),
                };
                let env2 = Env::Bind(*x, x_ty, env);
                let body_sort = match *self.typeck(&env2, body_ty) {
                    Expr::ConstSort(s) => s,
                    _ => panic!(
                        "invalid type: {:?} (because the type of {:?} is not a sort)",
                        expr, body_ty
                    ),
                };
                if let Some(s) = self.rules.get(&(x_sort.clone(), body_sort.clone())) {
                    ast::sort(s.clone())
                } else {
                    panic!(
                        "invalid type: {:?} (because {:?} is a {:?} and {:?} is a {:?})",
                        expr, x_ty, x_sort, body_ty, body_sort
                    );
                }
            }
            Expr::Apply(f, arg) => {
                if let Expr::Product(x, expected_arg_ty, body_ty_expr) = *self.typeck(env, f) {
                    let actual_arg_ty: Box<Expr<S>> = self.typeck(env, arg);
                    let expected_arg_ty: Box<Expr<S>> = expected_arg_ty;
                    assert_eq!(actual_arg_ty, expected_arg_ty); // unify
                    body_ty_expr.subst(x, &actual_arg_ty)
                } else {
                    panic!("function expected; got {:?}", f);
                }
            }
            Expr::Lambda(p, p_ty, body) => {
                let body_ty = self.typeck(&Env::Bind(*p, p_ty, env), body);
                let product_ty = Expr::Product(*p, p_ty.clone(), body_ty);
                let _product_ty_ty = self.typeck(env, &product_ty);
                Box::new(product_ty)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Context;

    use super::*;
    use crate::ast::*;
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
    static U_ENV: Env<'static, USort> = {
        static E0: Env<'static, USort> = Env::Empty;
        static E1: Env<'static, USort> = Env::Bind(Var("Type"), &Expr::ConstSort(Type), &E0);
        Env::Bind(Var("Kind"), &Expr::ConstSort(Kind), &E0)
    };

    fn parse(s: &'static str) -> Box<Expr<USort>> {
        Box::new(
            parser::TermParser::new()
                .parse(s)
                .context("parse error")
                .unwrap(),
        )
    }

    #[test]
    fn test_id() {
        let u = system_u();

        // λ (t : *), λ (x : t), x
        let id_expr = lambda("t", sort(Type), lambda("x", var("t"), var("x")));
        let id_type = u.typeck(&Env::Empty, &id_expr);
        println!("The type of `{}` is `{}`", id_expr, id_type);

        // Π (t : *), Π (x : t), t
        assert_eq!(id_type, pi("t", sort(Type), pi("x", var("t"), var("t"))),);
    }

    #[test]
    fn test_girard() {
        let expr = parse("λ (k : Kind) . λ (α : k -> k) . λ (β : k) . (α (α β))");
        let ty = parse("Π (k : Kind) . Π (α : k -> k) . Π (β : k) . k");

        let u = system_u();
        assert_eq!(u.typeck(&Env::Empty, &expr), ty);
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
}
