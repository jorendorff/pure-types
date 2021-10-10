//! Pure type system type-checking algorithm.

use std::{
    collections::HashMap,
    fmt::{Debug, Display},
    hash::Hash,
};

use crate::{
    ast::{self, Def, ExprEnum},
    Env, Expr, Thunk, TypeCheckError,
};

pub struct PureTypeSystem<S> {
    pub axioms: HashMap<S, S>,
    pub rules: HashMap<(S, S), S>,
}

impl<S: Clone + Display + Debug + Hash + Eq> PureTypeSystem<S> {
    pub fn check_expr(&self, expr: &Thunk<S>) -> Result<Thunk<S>, TypeCheckError<S>> {
        let env = expr.env.clone();
        Ok(match expr.term.inner() {
            ExprEnum::ConstSort(s) => {
                if let Some(meta) = self.axioms.get(s) {
                    Thunk {
                        term: ast::sort(meta.clone()),
                        env,
                    }
                } else {
                    return Err(TypeCheckError::UntypedSort(s.clone()));
                }
            }
            ExprEnum::Var(v) => {
                if let Some(v_ty) = expr.env.get(v) {
                    v_ty.clone()
                } else {
                    return Err(TypeCheckError::UndeclaredVar(v.clone()));
                }
            }
            ExprEnum::Pi(param, param_ty, body_ty) => {
                let param_ty_thunk = Thunk {
                    term: param_ty.clone(),
                    env: env.clone(),
                };
                let param_ty_ty_thunk = self.check_expr(&param_ty_thunk)?;
                let body_ty_thunk = Thunk {
                    term: body_ty.clone(),
                    env: env.with(param.clone(), param_ty_thunk),
                };
                let sort = self.check_pi_type(
                    param_ty_ty_thunk,
                    body_ty_thunk,
                    &|| TypeCheckError::InvalidPiParameterType(expr.term.clone(), param_ty.clone()),
                    &|| TypeCheckError::InvalidPiReturnType(expr.term.clone(), body_ty.clone()),
                    &|s1, s2| TypeCheckError::InvalidPiSorts(expr.term.clone(), s1, s2),
                )?;
                Thunk {
                    term: ast::sort(sort),
                    env,
                }
            }
            ExprEnum::Apply(f, arg) => {
                let f_thunk = Thunk {
                    term: f.clone(),
                    env: env.clone(),
                };
                let arg_thunk = Thunk {
                    term: arg.clone(),
                    env,
                };
                let f_ty = self.check_expr(&f_thunk)?;
                println!("it seems the type of {} is {}", f.clone(), f_ty.term);
                if let ExprEnum::Pi(x, expected_arg_ty, body_ty_expr) = f_ty.term.inner() {
                    let actual_arg_ty: Thunk<S> = self.check_expr(&arg_thunk)?;
                    let expected_arg_ty: Expr<S> = expected_arg_ty.clone();
                    // XXX FIXME bug
                    if actual_arg_ty.term != expected_arg_ty {
                        println!(
                            "{}",
                            TypeCheckError::ArgumentTypeMismatch(
                                expr.term.clone(),
                                expected_arg_ty.clone(),
                                actual_arg_ty.term.clone(),
                            )
                        );
                        return Err(TypeCheckError::ArgumentTypeMismatch(
                            expr.term.clone(),
                            expected_arg_ty,
                            actual_arg_ty.term,
                        ));
                    }
                    Thunk {
                        term: body_ty_expr.clone(),
                        env: f_ty.env.with(x.clone(), arg_thunk),
                    }
                } else {
                    return Err(TypeCheckError::FunctionExpected(
                        expr.term.clone(),
                        f.clone(),
                        f_ty.term,
                    ));
                }
            }
            ExprEnum::Lambda(param, param_ty, body) => {
                let param_ty_thunk = Thunk {
                    term: param_ty.clone(),
                    env: env.clone(),
                };
                let param_ty_ty_thunk = self.check_expr(&param_ty_thunk)?;

                let body_env = env.with(param.clone(), param_ty_thunk);
                let body_thunk = Thunk {
                    env: body_env,
                    term: body.clone(),
                };
                let body_ty_thunk = self.check_expr(&body_thunk)?;
                let body_ty = body_ty_thunk.term.clone();

                self.check_pi_type(
                    param_ty_ty_thunk,
                    body_ty_thunk,
                    &|| {
                        TypeCheckError::InvalidLambdaParameterType(
                            expr.term.clone(),
                            param_ty.clone(),
                        )
                    },
                    &|| TypeCheckError::InvalidLambdaReturnType(expr.term.clone(), body_ty.clone()),
                    &|s1, s2| TypeCheckError::InvalidLambdaSorts(expr.term.clone(), s1, s2),
                )?;

                // XXX TODO: hopeless environment confusion here
                Thunk {
                    term: ast::pi(param, param_ty.clone(), body_ty),
                    env,
                }
            }
            ExprEnum::Blank => {
                return Err(TypeCheckError::Blank);
            }
        })
    }

    pub fn thunk_as_sort(&self, thunk: Thunk<S>) -> Option<S> {
        match thunk.term.inner() {
            ExprEnum::ConstSort(s) => Some(s.clone()),
            _ => None,
        }
    }

    pub fn check_pi_type(
        &self,
        param_ty_ty_thunk: Thunk<S>,
        body_ty_thunk: Thunk<S>,
        parameter_error: &dyn Fn() -> TypeCheckError<S>,
        return_error: &dyn Fn() -> TypeCheckError<S>,
        sort_error: &dyn Fn(S, S) -> TypeCheckError<S>,
    ) -> Result<S, TypeCheckError<S>> {
        let param_sort = match self.thunk_as_sort(param_ty_ty_thunk) {
            Some(sort) => sort,
            None => return Err(parameter_error()),
        };
        let body_ty_ty = self.check_expr(&body_ty_thunk)?;
        let body_sort = match self.thunk_as_sort(body_ty_ty) {
            Some(sort) => sort,
            None => return Err(return_error()),
        };
        if let Some(sort) = self.rules.get(&(param_sort.clone(), body_sort.clone())) {
            Ok(sort.clone())
        } else {
            Err(sort_error(param_sort, body_sort))
        }
    }

    //pub fn check_sort() -> Result<S, TypeCheckError<S>> {
    //
    //}

    pub fn check_program(
        &self,
        env: &Env<S>,
        program: Vec<Def<S>>,
    ) -> Result<Env<S>, TypeCheckError<S>> {
        let mut env = env.clone();
        for def in program {
            let ty = if let Some(defined_ty) = def.ty {
                // There's a defined type; type-check to make sure it's not nonsense.
                self.check_expr(&Thunk {
                    env: env.clone(),
                    term: defined_ty.clone(),
                })?;

                if let Some(term) = def.term {
                    let env = env.clone();
                    let actual_ty = self.check_expr(&Thunk { env, term })?;
                    assert_eq!(actual_ty.term, defined_ty); // TODO unify
                    actual_ty
                } else {
                    // XXX hopeless env confusion
                    Thunk {
                        term: defined_ty,
                        env: env.clone(),
                    }
                }
            } else {
                let env = env.clone();
                let term = def.term.expect("def must have a term or type");
                self.check_expr(&Thunk { env, term })?
            };
            env = env.with(def.id, ty);
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
        let cst = TermParser::new().parse(s).context("parse error").unwrap();
        Expr::from_cst(cst)
    }

    fn parse_program(s: &'static str) -> Vec<Def<USort>> {
        let program_cst = ProgramParser::new()
            .parse(s)
            .context("parse error")
            .unwrap();
        ast::program_from_cst(program_cst)
    }

    #[test]
    fn test_binder_shorthands() {
        // binder shorthands
        assert_eq!(parse("λ a : b c . a"), parse("λ (a : b c) . a"));
        assert_eq!(parse("λ a b . a b"), parse("λ (a : _) . λ (b : _) . a b"));
        assert_eq!(
            parse("λ (a b c : _) . a"),
            parse("λ (a : _) . (λ (b : _) . (λ (c : _) . a))"),
        );

        assert_eq!(
            parse("Π (p q : Prop) . p -> q -> and p q"),
            parse("Π (p : Prop) . (Π (q : Prop) . (p -> (q -> (and p q))))"),
        );
    }

    #[test]
    fn test_id() {
        let u = system_u();

        // λ (t : *), λ (x : t), x
        let id_expr = lambda("t", sort(Type), lambda("x", var("t"), var("x")));
        let id_type = u
            .check_expr(&Thunk {
                term: id_expr.clone(),
                env: Env::new(),
            })
            .unwrap();
        println!("The type of `{}` is `{}`", id_expr, id_type.term);

        // Π (t : *), Π (x : t), t
        assert_eq!(
            id_type.term,
            pi("t", sort(Type), pi("x", var("t"), var("t"))),
        );
    }

    #[test]
    fn test_girard() {
        let expr = parse("λ (k : Kind) . λ (α : k -> k) . λ (β : k) . (α (α β))");
        let ty = parse("Π (k : Kind) . Π (α : k -> k) . Π (β : k) . k");

        let u = system_u();
        assert_eq!(
            u.check_expr(&Thunk {
                term: expr,
                env: Env::new()
            })
            .unwrap()
            .term,
            ty
        );
    }

    #[test]
    fn test_check_program() {
        let u = system_u();
        let base_env = u_env();
        let actual_env = u
            .check_program(
                &base_env,
                parse_program(
                    "
                axiom true : Type;
                axiom true_intro : true;
                def tx : Π (p : Type) . p -> true := λ (p : Type) . λ (_ : p) . true_intro;
                axiom false : Type;
                axiom false_elim : Π (p : Type) . false -> p;
                ",
                ),
            )
            .unwrap();

        let get = |s| &actual_env.get(&Id::from(s)).unwrap().term;

        assert_eq!(get("true"), &sort(Type));
        assert_eq!(get("true_intro"), &var("true"));
        assert_eq!(
            get("tx"),
            &pi("p", sort(Type), arrow(var("p"), var("true"))),
        );
        assert_eq!(get("false"), &sort(Type));
        assert_eq!(
            get("false_elim"),
            &pi("p", sort(Type), arrow(var("false"), var("p"))),
        );
    }

    fn assert_checks_in_system_u(program: &'static str) {
        let u = system_u();
        let base_env = u_env();
        u.check_program(&base_env, parse_program(program)).unwrap();
    }

    #[test]
    fn no_dependent_types_in_system_u() {
        // The `eq` type takes a type and two values as parameters. This is possible
        // in System U, but the return type would have to be another value, not
        // a type.
        let u = system_u();
        let program = parse_program("axiom eq : Π (t : Type) . t -> t -> Type;");
        assert!(u.check_program(&u_env(), program).is_err());

        let program = parse_program("axiom nat : Type; axiom vect : Type -> nat -> Type;");
        assert!(u.check_program(&u_env(), program).is_err());
    }

    #[test]
    fn imp_trans() {
        assert_checks_in_system_u(
            "
            def imp_trans :
              Π (a b c : Type) (ab : a -> b) (bc : b -> c) (h : a) . c :=
                λ (a b c : Type) (ab : a -> b) (bc : b -> c) (h : a) . bc (ab h);
            ",
        );
    }

    #[test]
    #[ignore]
    fn not_false() {
        assert_checks_in_system_u(
            "
            axiom true : Type;
            axiom true_intro : true;

            axiom false : Type;
            axiom false_elim : Π (x : Type) . false -> x;

            def not : Type -> Type := λ (p : Type) . p -> false;
            def not_false : not false := λ (f : false) . f;
            ",
        );
    }
}
