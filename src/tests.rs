use std::rc::Rc;

use crate::ast::{self, *};
use crate::env::{Binding, Env, PureTypeSystem};
use crate::parser::{ProgramParser, TermParser};
use crate::pts::{check_judgmental_eq, type_check, type_check_program};

/// A sort of "read-eval-assert loop" for playing with pure type systems.
struct Test {
    env: Env,
}

fn dump<E: std::error::Error>(err: E) {
    let mut s: Option<&dyn std::error::Error> = Some(&err);
    while let Some(err) = s {
        eprintln!("{}", err);
        s = err.source();
    }
}

impl Test {
    fn stlc() -> Test {
        Test { env: stlc_env() }
    }

    fn system_u() -> Test {
        Test { env: u_env() }
    }

    fn add(&mut self, code: &'static str) {
        match type_check_program(&self.env, &parse_program(code)) {
            Ok(env) => {
                self.env = env;
            }
            Err(err) => {
                dump(err);
                panic!("failed to type-check `{}`", code);
            }
        }
    }

    fn err(&mut self, code: &'static str) {
        if let Ok(_) = type_check_program(&self.env, &parse_program(code)) {
            panic!("expected error type-checking: `{}`", code);
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum SystemUSort {
    Type,
    Kind,
    Triangle,
}

// The simply typed lambda calculus.
fn system_stlc() -> Rc<PureTypeSystem> {
    // The type of all types "∗" needs to have a type so that it can be
    // named in programs. All bindings must have types.
    PureTypeSystem::new(&[("∗", "◻")], &[("∗", "∗", "∗")])
}

fn stlc_env() -> Env {
    system_stlc().env().with(
        Id::from("Type"),
        Binding {
            def: Some(constant(Id::from("∗"))),
            ty: constant(Id::from("◻")),
        },
    )
}

#[track_caller]
fn assert_checks_in_stlc(program: &'static str) {
    if let Err(err) = type_check_program(&stlc_env(), &parse_program(program)) {
        dump(err);
        panic!("failed to type-check program");
    }
}

#[test]
fn test_church_numerals() {
    assert_checks_in_stlc(
        "
            axiom nat : Type;
            axiom zero : nat;
            axiom succ : nat -> nat;
            def num : Type := (nat -> nat) -> (nat -> nat);
            axiom nat_ind : num -> (num -> num) -> nat -> num;

            def zero_num : num := λ (f : nat -> nat) (x : nat) . x;

            def succ_num : num -> num :=
              λ (a : num) (f : nat -> nat) (x : nat) . f (a f x);

            def nat_to_num : nat -> num :=
              λ n : nat . nat_ind zero_num succ_num n;

            def num_to_nat : num -> nat :=
              λ a : num . a succ zero;
            ",
    );
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
    PureTypeSystem::new(
        &[("∗", "◻"), ("◻", "△")],
        &[
            ("∗", "∗", "∗"),
            ("◻", "∗", "∗"),
            ("◻", "◻", "◻"),
            ("△", "∗", "∗"),
            ("△", "◻", "◻"),
        ],
    )
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

fn parse_program(s: &str) -> Vec<Def> {
    match ProgramParser::new().parse(s) {
        Ok(cst) => ast::program_from_cst(cst),
        Err(err) => {
            dump(err);
            panic!("failed to parse program: `{}`", s);
        }
    }
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
#[ignore] // test currently fails due to a bug
fn bad_types() {
    // Not all terms are types! Declared types need to actually be types.
    let mut t = Test::stlc();
    t.add("axiom nat : Type; axiom three : nat;");
    t.err("axiom weird : three;");

    // TODO:
    // - try `def`ined names as well as axioms like `three`
    // - other expression forms, including those involving reduction
    // - other places types are used
    // - terms that actually don't have a type at all (they fail type-checking)
}

#[test]
fn no_dependent_types_in_system_u() {
    // The `eq` type takes a type and two values as parameters. This is possible
    // in System U, but the return type would have to be another value, not
    // a type.
    let mut t = Test::system_u();
    t.err("axiom eq : Π (t : Type) . t -> t -> Type;");
    t.add("axiom nat : Type;");
    t.err("axiom vect : Type -> nat -> Type;");
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

#[test]
fn test_swap() {
    assert_checks_in_system_u(
        "
            def swap : Π (a b c : Type) . (a -> b -> c) -> b -> a -> c :=
              λ (a b c : Type) (f : a -> b -> c) (y : b) (x : a) . f x y;

            axiom and : Type -> Type -> Type;
            axiom and_intro : Π (a b : Type) . a -> b -> and a b;
            def and_retro : Π (a b : Type) . b -> a -> and a b :=
              λ (a b : Type) . swap a b (and a b) (and_intro a b);
            ",
    );
}

#[test]
#[ignore] // test currently fails due to a bug
fn test_and_or() {
    let mut t = Test::system_u();
    t.add(
        "
        axiom true : Type;
        axiom true_intro : true;
        axiom false : Type;
        def not : Type -> Type := λ t : Type . t -> false;
        ",
    );
    t.add(
        "
        axiom and : Type -> Type -> Type;
        axiom and_intro : Π (a b : Type) . a -> b -> and a b;
        axiom and_ind : Π (a b motive : Type) .
          (a -> b -> motive) -> and a b -> motive;
    ",
    );
    t.add(
        // currently fails
        "
        def and_comm :
          Π (a b : Type) . and a b -> and b a :=
          λ (a b : Type) (hab : and a b) .
            and_ind a b (and b a)
              (λ (ha : a) (hb : b) . and_intro b a hb ha)
              hab;
        ",
    );

    t.add(
        // currently fails
        "
        def and_assoc :
          Π (a b c : Type) . and (and a b) c -> and a (and b c) :=
          λ (a b c : Type) (habc : and (and a b) c) .
            and_ind (and a b) c
              (λ (hab : and a b) (hc : c) . and_ind a b
                 (λ (ha : a) (hb : b) . and_intro ha (and_intro hb hc))
                 hab)
              habc;
        ",
    );

    t.add(
        "
        axiom or : Type -> Type -> Type;
        axiom or_intro_left : Π (a b : Type) . a -> and a b;
        axiom or_intro_right : Π (a b : Type) . b -> and a b;
        axiom or_ind : Π (a b motive : Type) .
          (a -> motive) -> (b -> motive) -> or a b -> motive;
        ",
    );

    // XXX TODO - prove something interesting :)
}
