//! Pure type system type-checking algorithm.

use std::rc::Rc;

use crate::{
    ast::{self, Def, TermEnum},
    env::PureTypeSystem,
    Binding, Env, Id, Term, TypeCheckError,
};

/// Returns a term in normal form.
pub fn type_check(env: &Env, term: &Term) -> Result<Term, TypeCheckError> {
    match term.inner() {
        TermEnum::Constant(c) => env.system.get_constant_type(c),
        TermEnum::Variable(id) => Ok(env
            .get(id)
            .ok_or_else(|| TypeCheckError::UndeclaredVar(id.clone()))?
            .ty
            .clone()),
        TermEnum::Lambda(param, param_ty, body) => {
            let param_sort = type_check(env, param_ty)?;
            let param_ty = env.eval(param_ty)?;

            let body_env = env.with_param(param.clone(), param_ty.clone());
            let body_ty = type_check(&body_env, body)?;
            let body_sort = type_check(&body_env, &body_ty)?;
            get_function_sort(env, term, &param_ty, param_sort, &body_ty, body_sort)?;
            Ok(ast::pi(param, param_ty, body_ty))
        }
        TermEnum::Pi(param, param_ty, body_ty) => {
            let param_sort = type_check(env, param_ty)?;
            let body_sort = type_check(&env.with_param(param, param_ty.clone()), body_ty)?;
            let fn_sort = get_function_sort(env, term, param_ty, param_sort, body_ty, body_sort)?;
            Ok(ast::constant(fn_sort))
        }
        TermEnum::Apply(fun, arg) => {
            let fun_ty = type_check(env, fun)?;
            let arg_ty = type_check(env, arg)?;
            if let TermEnum::Pi(param, param_ty, body_ty) = fun_ty.inner() {
                check_judgmental_eq(&env.system, &arg_ty, param_ty)?;
                env.with(
                    param,
                    Binding {
                        ty: arg_ty,
                        def: Some(arg.clone()),
                    },
                )
                .eval(body_ty)
            } else {
                Err(TypeCheckError::FunctionExpected(
                    term.clone(),
                    fun.clone(),
                    fun_ty,
                ))
            }
        }
        TermEnum::Subst(id, binding, body) => type_check(&env.with(id, binding.clone()), body),
    }
}

fn get_function_sort<'env>(
    env: &'env Env,
    term: &Term,
    param_ty: &Term,
    param_sort: Term,
    body_ty: &Term,
    body_sort: Term,
) -> Result<&'env Id, TypeCheckError> {
    use TypeCheckError::*;

    let is_pi = matches!(term.inner(), TermEnum::Pi(..));

    let param_sort = match param_sort.inner() {
        TermEnum::Constant(c) => c,
        _ => {
            let err = if is_pi {
                InvalidPiParameterType
            } else {
                InvalidLambdaParameterType
            };

            return Err(err(term.clone(), param_ty.clone()));
        }
    };

    let body_sort = match body_sort.inner() {
        TermEnum::Constant(c) => c,
        _ => {
            let err = if is_pi {
                InvalidPiReturnType
            } else {
                InvalidLambdaParameterType
            };
            return Err(err(term.clone(), body_ty.clone()));
        }
    };

    env.system
        .get_function_sort(param_sort, body_sort)
        .ok_or_else(|| {
            let err = if is_pi {
                InvalidPiSorts
            } else {
                InvalidLambdaSorts
            };
            err(term.clone(), param_sort.clone(), body_sort.clone())
        })
}

/// a and b must already be in normal form. No free variables with known
/// definitions.
///
/// Unfortunately normal form means inlining all function calls. I'm sure this
/// isn't how real systems work. There's a more efficient way to do this that
/// also doesn't require them to be in normal form first. It would involve
/// environments.
fn check_judgmental_eq(
    system: &Rc<PureTypeSystem>,
    a: &Term,
    b: &Term,
) -> Result<(), TypeCheckError> {
    match (a.inner(), b.inner()) {
        (TermEnum::Constant(c), TermEnum::Constant(d)) if *c == *d => Ok(()),
        (TermEnum::Variable(a), TermEnum::Variable(b)) if *a == *b => Ok(()),
        (TermEnum::Lambda(v1, t1, b1), TermEnum::Lambda(v2, t2, b2)) => {
            check_judgmental_eq(system, t1, t2)?;
            if *v1 == *v2 {
                check_judgmental_eq(system, b1, b2)
            } else {
                let env = Env::new(Rc::clone(system)).with(
                    v2,
                    Binding {
                        ty: t2.clone(),
                        def: Some(ast::var(v1)),
                    },
                );
                let b2 = env.eval(b2)?;
                check_judgmental_eq(system, b1, &b2)
            }
        }
        (TermEnum::Pi(v1, t1, b1), TermEnum::Pi(v2, t2, b2)) => check_judgmental_eq(
            system,
            &ast::lambda(v1, t1.clone(), b1.clone()),
            &ast::lambda(v2, t2.clone(), b2.clone()),
        ),
        (TermEnum::Apply(f, a), TermEnum::Apply(g, b)) => {
            check_judgmental_eq(system, f, g)?;
            check_judgmental_eq(system, a, b)
        }
        _ => Err(TypeCheckError::UnifyMismatch(a.clone(), b.clone())),
    }
}

pub fn type_check_program(env: &Env, program: &[Def]) -> Result<Env, TypeCheckError> {
    program.iter().try_fold(env.clone(), |env, def| {
        let def_ty = def
            .ty
            .as_ref()
            .ok_or_else(|| TypeCheckError::MissingType(def.id.clone()))?;
        let def_ty = env.eval(def_ty)?;
        type_check(&env, &def_ty)?;

        let def_term = match &def.term {
            None => None,
            Some(term) => {
                let actual_ty = type_check(&env, term)?;
                check_judgmental_eq(&env.system, &actual_ty, &def_ty)?;
                Some(env.eval(term)?)
            }
        };
        let binding = Binding {
            ty: def_ty,
            def: def_term,
        };
        Ok(env.with(def.id.clone(), binding))
    })
}

#[allow(dead_code)]
fn dump<E: std::error::Error>(err: E) {
    let mut s: Option<&dyn std::error::Error> = Some(&err);
    while let Some(err) = s {
        eprintln!("{}", err);
        s = err.source();
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Context;

    use super::*;
    use crate::ast::*;
    use crate::parser::{ProgramParser, TermParser};

    #[derive(Copy, Clone, PartialEq, Eq, Debug)]
    enum SystemUSort {
        Type,
        Kind,
        Triangle,
    }

    use SystemUSort::*;

    impl SystemUSort {
        fn id(self) -> Id {
            Id::from(match self {
                SystemUSort::Type => "∗",
                SystemUSort::Kind => "◻",
                SystemUSort::Triangle => "△",
            })
        }
    }

    fn sort(s: SystemUSort) -> Term {
        constant(s.id())
    }

    fn system_u() -> Rc<PureTypeSystem> {
        let ty = || Type.id();
        let kind = || Kind.id();
        let triangle = || Triangle.id();

        Rc::new(PureTypeSystem {
            axioms: vec![(ty(), kind()), (kind(), triangle())]
                .into_iter()
                .collect(),
            function_sorts: vec![
                ((ty(), ty()), ty()),
                ((kind(), ty()), ty()),
                ((kind(), kind()), kind()),
                ((triangle(), ty()), ty()),
                ((triangle(), kind()), kind()),
            ]
            .into_iter()
            .collect(),
        })
    }

    fn u_env() -> Env {
        system_u()
            .env()
            .with(
                Id::from("Type"),
                Binding {
                    def: Some(sort(Type)),
                    ty: sort(Kind),
                },
            )
            .with(
                Id::from("Kind"),
                Binding {
                    def: Some(sort(Kind)),
                    ty: sort(Triangle),
                },
            )
    }

    fn parse(s: &str) -> Term {
        let cst = TermParser::new().parse(s).unwrap();
        Term::from_cst(cst)
    }

    fn parse_program(s: &'static str) -> Vec<Def> {
        let program_cst = ProgramParser::new()
            .parse(s)
            .context("parse error")
            .unwrap();
        ast::program_from_cst(program_cst)
    }

    #[track_caller]
    fn assert_parse_eq(a: &str, b: &str) {
        let a = format!("{:?}", parse(a));
        let b = format!("{:?}", parse(b));
        assert_eq!(a, b);
    }

    #[test]
    fn test_binder_shorthands() {
        // binder shorthands
        assert_parse_eq("λ a : b c . a", "λ (a : b c) . a");

        // Commented out because blanks aren't supported.
        //
        // assert_parse_eq("λ a b . a b", "λ (a : _) . λ (b : _) . a b");

        // This test is a little broken. Parameters assigned the same blank as
        // a type should still have the same type (not three different blanks)
        // after conversion to the core language.
        //
        // assert_parse_eq(
        //     "λ (a b c : _) . a",
        //     "λ (a : _) . (λ (b : _) . (λ (c : _) . a))",
        // );

        assert_parse_eq(
            "Π (p q : Prop) . p -> q -> and p q",
            "Π (p : Prop) . (Π (q : Prop) . (p -> (q -> (and p q))))",
        );
    }

    /// Assert two terms are judgmentally equivalent.
    #[track_caller]
    fn assert_jeq(system: &Rc<PureTypeSystem>, left: &Term, right: &Term) {
        if let Err(err) = check_judgmental_eq(system, left, right) {
            dump(err);
            panic!("assertion failed");
        }
    }

    #[test]
    fn test_id() {
        let u = system_u();

        // λ (t : Type) . λ (x : t) . x
        let id_expr = lambda("t", sort(Type), lambda("x", var("t"), var("x")));

        let id_type = type_check(&u.env(), &id_expr).unwrap();

        // Π (t : Type) . Π (x : t) . t
        assert_jeq(
            &u,
            &id_type,
            &pi("t", sort(Type), pi("x", var("t"), var("t"))),
        );
    }

    #[test]
    fn test_girard() {
        let env = u_env();

        let term = parse("λ (k : Kind) . λ (α : k -> k) . λ (β : k) . (α (α β))");
        let actual_ty = type_check(&env, &term).unwrap();

        let expected_ty = env
            .eval(&parse("Π (k : Kind) . Π (α : k -> k) . Π (β : k) . k"))
            .unwrap();

        assert_jeq(&env.system, &actual_ty, &expected_ty);
    }

    #[test]
    fn test_check_program() {
        let env = type_check_program(
            &u_env(),
            &parse_program(
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

        let get = |s| env.get(&Id::from(s)).unwrap().ty.clone();
        assert_jeq(&env.system, &get("true"), &sort(Type));
        assert_jeq(&env.system, &get("true_intro"), &var("true"));
        assert_jeq(
            &env.system,
            &get("tx"),
            &pi("p", sort(Type), arrow(var("p"), var("true"))),
        );
        assert_jeq(&env.system, &get("false"), &sort(Type));
        assert_jeq(
            &env.system,
            &get("false_elim"),
            &pi("p", sort(Type), arrow(var("false"), var("p"))),
        );
    }

    #[test]
    fn no_dependent_types_in_system_u() {
        // The `eq` type takes a type and two values as parameters. This is possible
        // in System U, but the return type would have to be another value, not
        // a type.
        let program = parse_program("axiom eq : Π (t : Type) . t -> t -> Type;");
        assert!(type_check_program(&u_env(), &program).is_err());

        let program = parse_program("axiom nat : Type; axiom vect : Type -> nat -> Type;");
        assert!(type_check_program(&u_env(), &program).is_err());
    }

    #[track_caller]
    fn assert_checks_in_system_u(program: &'static str) {
        if let Err(err) = type_check_program(&u_env(), &parse_program(program)) {
            dump(err);
            panic!("failed to type-check program");
        }
    }

    #[test]
    fn test_basic_application() {
        // end-to-end test of a function application
        assert_checks_in_system_u(
            "
            axiom R : Type;
            axiom Z : Type;
            axiom floor : R -> Z;
            axiom pi : R;
            def three : Z := floor pi;
            ",
        );
    }

    #[test]
    fn test_call_id() {
        assert_checks_in_system_u(
            "
            def id : Π (t : Type) . t -> t := λ (t : Type) . λ (x : t) . x;

            axiom nat : Type;
            axiom zero : nat;
            def very_zero : nat := id nat zero;
            ",
        );
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

    fn eval(env: &Env, term: Term) -> Term {
        env.eval(&term).unwrap_or_else(|err| {
            dump(err);
            panic!("assertion failed");
        })
    }

    #[track_caller]
    fn assert_jeq_in_system_u(actual: &str, expected: &str) {
        let env = u_env();
        let actual = eval(&env, parse(actual));
        let expected = eval(&env, parse(expected));
        assert_jeq(&env.system, &actual, &expected);
    }

    #[test]
    fn test_alpha() {
        // simple α-equivalence
        assert_jeq_in_system_u("λ x : Type . x -> x", "λ y : Type . y -> y");
    }

    #[test]
    fn test_beta() {
        // β-equivalence
        assert_jeq_in_system_u(
            "λ t : Type . λ v : t . (λ x : t . x) v",
            "λ t : Type . λ v : t . v",
        );

        // another flavor of β-equivalence
        assert_jeq_in_system_u(
            "λ (list : Type -> Type) (nat : Type) .
                     (λ (f : Type -> Type) (x : Type) . f (f x)) list nat",
            "λ (list : Type -> Type) (nat : Type) .
                     list (list nat)",
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

    /* TODO - enable when we have a system that can deal with dependent types
    #[test]
    fn test_eq_in_system() {
        assert_checks_in_system_u(
            "
            axiom eq : Π t : Type . t -> t -> Type;
            axiom refl : Π (t : Type) (a : t) . eq a a;

            axiom congr_arg : Π (t u : Type) (f : t -> u) (a b : t) .
              eq a b -> eq (f a) (f b);

            axiom replace : Π (a b : Type) (f : Type -> Type) .
              eq a b -> f a -> f b;
            ",
        );
    }
     */

    #[test]
    fn test_nat_axioms_look_ok() {
        // Does not include the full inductor because System U doesn't have
        // depedent types.
        assert_checks_in_system_u(
            "
            axiom nat : Type;
            axiom zero : nat;
            axiom succ : nat -> nat;
            axiom nat_rec : Π a : Type . nat -> a -> (nat -> a) -> a;
            ",
        );

        // axiom nat_ind : Π p : nat -> Type .
        //   p zero ->
        //   (Π n : nat . p n -> p (succ n)) ->
        //   Π n : nat . p n;
    }
}
