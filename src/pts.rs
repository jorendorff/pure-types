//! Pure type system type-checking algorithm.

use std::{
    collections::HashMap,
    fmt::{Debug, Display},
    hash::Hash,
};

use crate::{
    ast::{self, Def, ExprEnum},
    Binding, Env, Expr, Id, Thunk, TypeCheckError,
};

#[derive(Clone)]
pub struct PureTypeSystem<S> {
    pub axioms: HashMap<S, S>,
    pub rules: HashMap<(S, S), S>,
}

#[derive(Clone)]
struct Context<S> {
    system: PureTypeSystem<S>,
    blanks: Vec<Option<Thunk<S>>>,
    next_undefined: usize,
    next_gensym: usize,
}

impl<S: Clone + Display + Debug + Hash + Eq> PureTypeSystem<S> {
    fn new_context(&self) -> Context<S> {
        Context {
            system: self.clone(),
            blanks: vec![],
            next_undefined: 0,
            next_gensym: 0,
        }
    }

    pub fn check_expr(&self, expr: &Thunk<S>) -> Result<Thunk<S>, TypeCheckError<S>> {
        self.new_context().check_expr(expr)
    }

    pub fn check_program(
        &self,
        env: &Env<S>,
        program: Vec<Def<S>>,
    ) -> Result<Env<S>, TypeCheckError<S>> {
        self.new_context().check_program(env, program)
    }
}

impl<S: Clone + Display + Debug + Hash + Eq + 'static> Context<S> {
    fn new_blank(&mut self) -> Expr<S> {
        let n = self.blanks.len();
        self.blanks.push(None);
        ast::blank(n)
    }

    fn undefined(&mut self, message: &str) -> Thunk<S> {
        let id = self.next_undefined;
        self.next_undefined += 1;
        println!("defining #undef{} for {}", id, message);
        Thunk {
            term: ast::undefined(id),
            env: Env::new(),
        }
    }

    fn shorten_chain(&mut self, mut start: usize, end: usize) {
        let stamp = Some(Thunk {
            env: Env::new(),
            term: ast::blank(end),
        });
        while end != start {
            if let ExprEnum::Blank(next) = self.blanks[start].as_mut().unwrap().term.inner() {
                start = *next;
                self.blanks[start] = stamp.clone();
            } else {
                unreachable!();
            }
        }
    }

    fn lookup_blank(&mut self, i: usize) -> Thunk<S> {
        let mut c = i;
        loop {
            match &mut self.blanks[c] {
                Some(expr) => {
                    if let ExprEnum::Blank(j) = expr.term.inner() {
                        c = *j;
                    } else {
                        self.shorten_chain(i, c);
                        return self.blanks[c].clone().unwrap();
                    }
                }
                None => {
                    self.shorten_chain(i, c);
                    return Thunk {
                        term: ast::blank(c),
                        env: Env::new(),
                    };
                }
            }
        }
    }

    fn fill_blank(&mut self, i: usize, thunk: &Thunk<S>) {
        assert!(self.blanks[i].is_none());
        self.blanks[i] = Some(thunk.clone());
    }

    fn reduce_to_lambda(
        &mut self,
        value: Thunk<S>,
    ) -> Result<(Id, Expr<S>, Expr<S>, Env<S>), TypeCheckError<S>> {
        match value.term.inner() {
            ExprEnum::Lambda(id, ty, body) => {
                Ok((id.clone(), ty.clone(), body.clone(), value.env.clone()))
            }
            ExprEnum::Blank(i) => {
                let value = self.lookup_blank(*i);
                if value.term.is_blank() {
                    return Err(TypeCheckError::ReduceBlank);
                }
                self.reduce_to_lambda(value)
            }
            ExprEnum::Var(x) => {
                let value = value.env.get(x).unwrap().def.clone();
                self.reduce_to_lambda(value)
            }
            ExprEnum::Apply(fun, arg) => {
                let value = self.reduce_app(fun, arg, &value.env)?;
                self.reduce_to_lambda(value)
            }
            _ => {
                return Err(TypeCheckError::ExpectedLambda(format!("{}", value.term)));
            }
        }
    }

    fn unify(
        &mut self,
        mut actual: Thunk<S>,
        mut expected: Thunk<S>,
    ) -> Result<(), TypeCheckError<S>> {
        use ExprEnum::*;

        if let Blank(i) = actual.term.inner() {
            actual = self.lookup_blank(*i);
        }
        if let Blank(j) = expected.term.inner() {
            expected = self.lookup_blank(*j);
        }

        // If either thunk is still Blank, we really know nothing about its
        // structure.

        match (actual.term.inner(), expected.term.inner()) {
            // XXX BUG: since `actual.env != expected.env`, we may be filling
            // with an expression that means something else on the other side.
            (Blank(i), _) => self.fill_blank(*i, &expected),
            (_, Blank(j)) => self.fill_blank(*j, &actual),
            (Var(x), _) => {
                let defn = actual.env.get(x).unwrap().def.clone();
                self.unify(defn, expected)?;
            }
            (_, Var(y)) => {
                let defn = expected.env.get(y).unwrap().def.clone();
                self.unify(actual, defn)?;
            }
            (Undefined(u), Undefined(v)) => {
                // XXX TODO improve error message, ew
                if u != v {
                    return Err(TypeCheckError::UnifyMismatch(expected.term, actual.term));
                }
            }
            (ConstSort(u), ConstSort(v)) => {
                if u != v {
                    return Err(TypeCheckError::UnifyMismatch(expected.term, actual.term));
                }
            }
            (Lambda(p, p_ty, a), Lambda(q, q_ty, b)) | (Pi(p, p_ty, a), Pi(q, q_ty, b)) => {
                self.unify(
                    Thunk {
                        term: p_ty.clone(),
                        env: actual.env.clone(),
                    },
                    Thunk {
                        term: q_ty.clone(),
                        env: expected.env.clone(),
                    },
                )?;

                let param_binding = Binding {
                    def: self.undefined(&format!("param {}/{}", p, q)),
                    ty: Thunk {
                        term: q_ty.clone(),
                        env: expected.env.clone(),
                    },
                };
                self.unify(
                    Thunk {
                        term: a.clone(),
                        env: actual.env.with(p.clone(), param_binding.clone()),
                    },
                    Thunk {
                        term: b.clone(),
                        env: expected.env.with(q.clone(), param_binding),
                    },
                )?;
            }
            (Apply(f, a), Apply(g, b)) => {
                if !self.try_naive_unification(f, a, &actual.env, g, b, &expected.env) {
                    if let Some(new_actual) = self.try_reduce_app(f, a, &actual.env) {
                        self.unify(new_actual, expected)?;
                    } else {
                        let new_expected = self.reduce_app(g, b, &expected.env)?;
                        self.unify(actual, new_expected)?;
                    }
                }
            }
            (Apply(f, a), _) => {
                // Reduce `actual` and retry.
                let new_actual = self.reduce_app(f, a, &actual.env)?;
                self.unify(new_actual, expected)?;
            }
            (_, Apply(g, b)) => {
                // Reduce `expected` and retry.
                let new_expected = self.reduce_app(g, b, &expected.env)?;
                self.unify(actual, new_expected)?;
            }
            (_, _) => return Err(TypeCheckError::UnifyMismatch(expected.term, actual.term)),
        }

        Ok(())
    }

    fn try_reduce_app(&mut self, fun: &Expr<S>, arg: &Expr<S>, env: &Env<S>) -> Option<Thunk<S>> {
        let saved_state = self.clone();
        if let Ok(thunk) = self.reduce_app(fun, arg, env) {
            Some(thunk)
        } else {
            *self = saved_state;
            println!(
                "reduce failed, rolled back to {} undefined bindings",
                self.next_undefined
            );
            None
        }
    }

    fn reduce_app(
        &mut self,
        fun: &Expr<S>,
        arg: &Expr<S>,
        env: &Env<S>,
    ) -> Result<Thunk<S>, TypeCheckError<S>> {
        println!("reducing {}", ast::apply(fun.clone(), arg.clone()));
        let (param, param_ty, body, lambda_env) = self.reduce_to_lambda(Thunk {
            term: fun.clone(),
            env: env.clone(),
        })?;

        let param_binding = Binding {
            def: Thunk {
                term: arg.clone(),
                env: env.clone(),
            },
            ty: Thunk {
                term: param_ty,
                env: lambda_env.clone(),
            },
        };
        Ok(Thunk {
            term: body,
            env: lambda_env.with(param, param_binding),
        })
    }

    /// Attempt to unify `f a = g b` by unifying `f = g` and `a = b`.
    /// Returns true on success; rolls back the failed inferences on failure.
    ///
    /// Of course this will fail in many cases where in fact the two
    /// expressions are definitionally equivalent. But it is necessary to cover
    /// some important cases like `list t = list t`, where the function has no
    /// known definition as a lambda. It's a nice optimization too: this will
    /// succeed or fail faster than fully reducing the two expressions.
    fn try_naive_unification(
        &mut self,
        f: &Expr<S>,
        a: &Expr<S>,
        fa_env: &Env<S>,
        g: &Expr<S>,
        b: &Expr<S>,
        gb_env: &Env<S>,
    ) -> bool {
        let saved_state = self.clone();

        let f = Thunk {
            term: f.clone(),
            env: fa_env.clone(),
        };
        let g = Thunk {
            term: g.clone(),
            env: gb_env.clone(),
        };
        let a = Thunk {
            term: a.clone(),
            env: fa_env.clone(),
        };
        let b = Thunk {
            term: b.clone(),
            env: gb_env.clone(),
        };

        if let Ok(()) = self.unify(f, g).and_then(|()| self.unify(a, b)) {
            true
        } else {
            *self = saved_state;
            println!(
                "naive unification failed, rolled back to {} undefined bindings",
                self.next_undefined
            );
            false
        }
    }

    fn check_expr(&mut self, expr: &Thunk<S>) -> Result<Thunk<S>, TypeCheckError<S>> {
        let env = expr.env.clone();
        Ok(match expr.term.inner() {
            ExprEnum::ConstSort(s) => {
                if let Some(meta) = self.system.axioms.get(s) {
                    Thunk {
                        term: ast::sort(meta.clone()),
                        env,
                    }
                } else {
                    return Err(TypeCheckError::UntypedSort(s.clone()));
                }
            }
            ExprEnum::Var(v) => {
                if let Some(binding) = expr.env.get(v) {
                    binding.ty.clone()
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
                    env: env.with(
                        param.clone(),
                        Binding {
                            ty: param_ty_thunk,
                            def: self.undefined(&format!("Π parameter {}", param)),
                        },
                    ),
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
                if let ExprEnum::Pi(param, expected_arg_ty, body_ty_expr) = f_ty.term.inner() {
                    let actual_arg_ty: Thunk<S> = self.check_expr(&arg_thunk)?;
                    let expected_arg_ty = Thunk {
                        term: expected_arg_ty.clone(),
                        env: f_ty.env.clone(),
                    };
                    if let Err(err) = self.unify(actual_arg_ty.clone(), expected_arg_ty.clone()) {
                        return Err(TypeCheckError::ArgumentTypeMismatch(
                            expr.term.clone(),
                            expected_arg_ty.term,
                            actual_arg_ty.term,
                            Box::new(err),
                        ));
                    }
                    Thunk {
                        term: body_ty_expr.clone(),
                        env: f_ty.env.with(
                            param.clone(),
                            Binding {
                                ty: actual_arg_ty,
                                def: arg_thunk,
                            },
                        ),
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

                let body_env = env.with(
                    param.clone(),
                    Binding {
                        ty: param_ty_thunk,
                        def: self.undefined(&format!("λ parameter {}", param)),
                    },
                );
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
            ExprEnum::Blank(_) | ExprEnum::Undefined(_) => {
                return Err(TypeCheckError::Blank);
            }
        })
    }

    /// This is used when we need to check the sorts of a function type.
    ///
    /// Suppose we have `def m : Type -> Kind;`. To find out if this function
    /// type is valid, we must first determine whether `Type` and `Kind` are
    /// definitionally equivalent to some statically known sort. This function
    /// is called once for each expression; it determines that, for example,
    /// `Type` is bound to `ast::sort(Type)`.
    fn thunk_as_sort(&self, thunk: Thunk<S>) -> Option<S> {
        match thunk.term.inner() {
            ExprEnum::ConstSort(s) => Some(s.clone()),
            ExprEnum::Var(id) => match thunk.env.get(id) {
                Some(Binding { def, .. }) => self.thunk_as_sort(def.clone()),
                _ => None,
            },
            _ => None,
        }
    }

    fn check_pi_type(
        &mut self,
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
        if let Some(sort) = self
            .system
            .rules
            .get(&(param_sort.clone(), body_sort.clone()))
        {
            Ok(sort.clone())
        } else {
            Err(sort_error(param_sort, body_sort))
        }
    }

    fn check_program(
        &mut self,
        env: &Env<S>,
        program: Vec<Def<S>>,
    ) -> Result<Env<S>, TypeCheckError<S>> {
        let mut env = env.clone();
        for def in program {
            let ty = if let Some(defined_ty) = &def.ty {
                // There's a defined type; type-check to make sure it's not nonsense.
                let defined_ty_thunk = Thunk {
                    env: env.clone(),
                    term: defined_ty.clone(),
                };
                self.check_expr(&defined_ty_thunk)?;

                if let Some(term) = &def.term {
                    let actual_thunk = Thunk {
                        env: env.clone(),
                        term: term.clone(),
                    };
                    let actual_ty = self.check_expr(&actual_thunk)?;
                    if let Err(err) = self.unify(actual_ty.clone(), defined_ty_thunk.clone()) {
                        return Err(TypeCheckError::DefinedTypeMismatch(
                            def.id,
                            defined_ty_thunk.term,
                            actual_thunk.term,
                            actual_ty.term,
                            Box::new(err),
                        ));
                    }

                    actual_ty
                } else {
                    // XXX hopeless env confusion
                    Thunk {
                        term: defined_ty.clone(),
                        env: env.clone(),
                    }
                }
            } else {
                let env = env.clone();
                let term = def
                    .term
                    .as_ref()
                    .expect("def must have a term or type")
                    .clone();
                self.check_expr(&Thunk { env, term })?
            };
            let def_thunk = match def.term {
                Some(term) => Thunk {
                    term,
                    env: env.clone(),
                },
                None => self.undefined(&format!("axiom {}", def.id)),
            };
            env = env.with(def.id, Binding { def: def_thunk, ty });
        }
        Ok(env)
    }
}

#[cfg(test)]
mod tests {
    use std::error::Error;

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
        let sort = |s| Thunk {
            env: Env::new(),
            term: ast::sort(s),
        };
        Env::new()
            .with(
                Id::from("Type"),
                Binding {
                    def: sort(Type),
                    ty: sort(Kind),
                },
            )
            .with(
                Id::from("Kind"),
                Binding {
                    def: sort(Kind),
                    ty: sort(Triangle),
                },
            )
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
                term: id_expr,
                env: Env::new(),
            })
            .unwrap();

        // Π (t : *), Π (x : t), t
        assert_eq!(
            id_type.term,
            pi("t", sort(Type), pi("x", var("t"), var("t"))),
        );
    }

    #[test]
    fn test_girard() {
        let term = parse("λ (k : Kind) . λ (α : k -> k) . λ (β : k) . (α (α β))");
        let ty = parse("Π (k : Kind) . Π (α : k -> k) . Π (β : k) . k");

        let u = system_u();
        let env = u_env();
        assert_eq!(u.check_expr(&Thunk { term, env }).unwrap().term, ty);
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

        let get = |s| &actual_env.get(&Id::from(s)).unwrap().ty.term;

        assert_eq!(get("true"), &var("Type"));
        assert_eq!(get("true_intro"), &var("true"));
        assert_eq!(
            get("tx"),
            &pi("p", var("Type"), arrow(var("p"), var("true"))),
        );
        assert_eq!(get("false"), &var("Type"));
        assert_eq!(
            get("false_elim"),
            &pi("p", var("Type"), arrow(var("false"), var("p"))),
        );
    }

    fn dump<E: Error>(err: E) {
        let mut s: Option<&dyn Error> = Some(&err);
        while let Some(err) = s {
            eprintln!("{}", err);
            s = err.source();
        }
    }

    #[track_caller]
    fn assert_checks_in_system_u(program: &'static str) {
        let u = system_u();
        let base_env = u_env();
        if let Err(err) = u.check_program(&base_env, parse_program(program)) {
            dump(err);
            panic!("failed to type-check program");
        }
    }

    #[track_caller]
    fn assert_unify_in_system_u(actual: &'static str, expected: &'static str) {
        let u = system_u();
        let base_env = u_env();
        let actual = Thunk {
            term: parse(actual),
            env: base_env.clone(),
        };
        let expected = Thunk {
            term: parse(expected),
            env: base_env,
        };
        if let Err(err) = u.new_context().unify(actual, expected) {
            dump(err);
            panic!("failed to unify");
        }
    }

    #[test]
    fn no_dependent_types_in_system_u() {
        let u = system_u();

        // The `eq` type takes a type and two values as parameters. This is possible
        // in System U, but the return type would have to be another value, not
        // a type.
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
              Π (a b c : Type) . (a -> b) -> (b -> c) -> a -> c :=
                λ (a b c : Type) (ab : a -> b) (bc : b -> c) (h : a) . bc (ab h);
            ",
        );
    }

    #[test]
    fn test_unify() {
        // simple alpha-equivalence
        assert_unify_in_system_u("λ x : Type . x -> x", "λ y : Type . y -> y");
        // beta-equivalence
        assert_unify_in_system_u(
            "λ t : Type . λ v : t . (λ x : t . x) v",
            "λ t : Type . λ v : t . v",
        );

        // another flavor of beta-equivalence
        assert_unify_in_system_u(
            "λ (list : Type -> Type) (nat : Type) .
                     list (list nat)",
            "λ (list : Type -> Type) (nat : Type) .
                     (λ (f : Type -> Type) (x : Type) . f (f x)) list nat",
        );
    }

    #[test]
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
