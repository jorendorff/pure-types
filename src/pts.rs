//! Pure type system type-checking algorithm.
use std::fmt::{self, Debug, Formatter};
use std::hash::Hash;
use std::rc::Rc;
use std::{collections::HashMap, iter::FromIterator};

use crate::ast::{self, Def, Expr, ExprEnum, Id};

pub struct PureTypeSystem<S> {
    pub axioms: HashMap<S, S>,
    pub rules: HashMap<(S, S), S>,
}

#[derive(Debug, PartialEq)]
struct EnvCons<S> {
    id: Id,
    term: Expr<S>,
    tail: Env<S>,
}

#[derive(Clone, PartialEq)]
pub struct Env<S>(Option<Rc<EnvCons<S>>>);

impl<'a, S> Iterator for &'a Env<S> {
    type Item = (&'a Id, &'a Expr<S>);

    fn next(&mut self) -> Option<Self::Item> {
        let cons = self.0.as_ref()?;
        let entry = (&cons.id, &cons.term);
        *self = &cons.tail;
        Some(entry)
    }
}

impl<S: Debug> Debug for Env<S> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_list().entries(self).finish()
    }
}

impl<S> Env<S> {
    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        Env(None)
    }

    pub fn get(&self, x: &Id) -> Option<&Expr<S>> {
        let mut current = self;
        while let Env(Some(cell)) = current {
            if cell.id == *x {
                return Some(&cell.term);
            }
            current = &cell.tail;
        }
        None
    }

    pub fn cons(id: Id, term: Expr<S>, tail: Env<S>) -> Env<S> {
        Env(Some(Rc::new(EnvCons { id, term, tail })))
    }

    pub fn push(&mut self, id: Id, term: Expr<S>) {
        let mut tmp = Env(None);
        std::mem::swap(&mut tmp, self);
        *self = Self::cons(id, term, tmp);
    }
}

impl<S> FromIterator<(Id, Expr<S>)> for Env<S> {
    fn from_iter<T: IntoIterator<Item = (Id, Expr<S>)>>(iter: T) -> Self {
        let mut env = Env(None);
        for (id, term) in iter {
            env.push(id, term);
        }
        env
    }
}

impl<S: Clone + Debug + Hash + Eq> PureTypeSystem<S> {
    pub fn typeck(&self, env: &Env<S>, expr: &Expr<S>) -> Expr<S> {
        match expr.inner() {
            ExprEnum::ConstSort(s) => {
                if let Some(meta) = self.axioms.get(s) {
                    ast::sort(meta.clone())
                } else {
                    panic!(
                        "{:?} can't be used as an expression in code; it has no type",
                        expr
                    );
                }
            }
            ExprEnum::Var(v) => {
                if let Some(v_ty) = env.get(v) {
                    v_ty.clone()
                } else {
                    panic!("can't find value `{:?}` in this scope", *v);
                }
            }
            ExprEnum::Pi(x, x_ty, body_ty) => {
                let x_sort = match self.typeck(env, x_ty).inner() {
                    ExprEnum::ConstSort(s) => s.clone(),
                    _ => panic!(
                        "invalid type: {:?} (because the type of {:?} is not a sort)",
                        expr, x_ty
                    ),
                };
                let env2 = Env::cons(x.clone(), x_ty.clone(), env.clone());
                let body_sort = match self.typeck(&env2, body_ty).inner() {
                    ExprEnum::ConstSort(s) => s.clone(),
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
            ExprEnum::Apply(f, arg) => {
                if let ExprEnum::Pi(x, expected_arg_ty, body_ty_expr) =
                    &self.typeck(env, f).0 as &ExprEnum<S>
                {
                    let actual_arg_ty: Expr<S> = self.typeck(env, arg);
                    let expected_arg_ty: Expr<S> = expected_arg_ty.clone();
                    assert_eq!(actual_arg_ty, expected_arg_ty); // unify
                    body_ty_expr.subst(x, &actual_arg_ty)
                } else {
                    panic!("function expected; got {:?}", f);
                }
            }
            ExprEnum::Lambda(p, p_ty, body) => {
                let body_ty = self.typeck(&Env::cons(p.clone(), p_ty.clone(), env.clone()), body);
                let product_ty = ast::pi(p.clone(), p_ty.clone(), body_ty);
                let _product_ty_ty = self.typeck(env, &product_ty);
                product_ty
            }
        }
    }

    pub fn typeck_program(&self, env: &Env<S>, program: Vec<Def<S>>) -> Env<S> {
        let mut env = env.clone();
        for def in program {
            let ty = if let Some(defined_ty) = def.ty {
                // There's a defined type; type-check to make sure it's not nonsense.
                self.typeck(&env, &defined_ty);

                if let Some(term) = def.term {
                    let actual_ty = self.typeck(&env, &term);
                    assert_eq!(actual_ty, defined_ty); // unify
                }
                defined_ty
            } else {
                let term = def.term.expect("def must have a term or type");
                self.typeck(&env, &term)
            };
            env.push(def.id, ty);
        }
        env
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
        let id_type = u.typeck(&Env(None), &id_expr);
        println!("The type of `{}` is `{}`", id_expr, id_type);

        // Π (t : *), Π (x : t), t
        assert_eq!(id_type, pi("t", sort(Type), pi("x", var("t"), var("t"))),);
    }

    #[test]
    fn test_girard() {
        let expr = parse("λ (k : Kind) . λ (α : k -> k) . λ (β : k) . (α (α β))");
        let ty = parse("Π (k : Kind) . Π (α : k -> k) . Π (β : k) . k");

        let u = system_u();
        assert_eq!(u.typeck(&Env::new(), &expr), ty);
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
        let result = u.typeck_program(
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
        );

        let actual_env = result
            .into_iter()
            .map(|(id, ty)| (id.clone(), ty.clone()))
            .collect::<BTreeMap<Id, Expr<USort>>>();

        use std::collections::BTreeMap;
        let expected_env = base_env
            .into_iter()
            .map(|(a, b)| (a.clone(), b.clone()))
            .chain(vec![
                (Id::from("true"), sort(Type)),
                (Id::from("trivial"), var("true")),
                (
                    Id::from("ffs"),
                    pi("p", sort(Type), arrow(var("false"), var("p"))),
                ),
                (Id::from("false"), sort(Type)),
                (
                    Id::from("tx"),
                    pi("p", sort(Type), arrow(var("p"), var("true"))),
                ),
            ])
            .collect::<BTreeMap<Id, Expr<USort>>>();

        assert_eq!(actual_env, expected_env);
    }
}
