#![cfg(test)]

use anyhow::Context;

use crate::cst::*;
use crate::parser::{ProgramParser, TermParser};

fn parse(s: &'static str) -> Expr {
    TermParser::new().parse(s).context("parse error").unwrap()
}

fn no_parse(s: &'static str) {
    assert!(TermParser::new().parse(s).is_err())
}

#[test]
fn test_parser() {
    assert_eq!(
        parse("λ (t : Type) . λ (x : t) . x"),
        lambda(("t", var("Type")), lambda(("x", var("t")), var("x"))),
    );

    assert_eq!(
        parse("λ (k : Kind) . λ (α : k -> k) . λ (β : k) . (α (α β))"),
        lambda(
            ("k", var("Kind")),
            lambda(
                ("α", arrow(var("k"), var("k"))),
                lambda(("β", var("k")), apply(var("α"), apply(var("α"), var("β"))))
            )
        )
    );

    // operator precedence and associativity
    assert_eq!(parse("a b c"), apply(apply(var("a"), var("b")), var("c")));
    assert_eq!(
        parse("a -> b -> c"),
        arrow(var("a"), arrow(var("b"), var("c")))
    );
    assert_eq!(parse("a b -> c d"), parse("(a b) -> (c d)"));
}

fn parse_program(s: &'static str) -> Vec<Def> {
    ProgramParser::new()
        .parse(s)
        .context("parse error")
        .unwrap()
}

#[test]
fn test_program_parser() {
    assert_eq!(
        parse_program(
            "
                axiom true : Type;
                axiom true_intro : true;
                def tx : Π (p : Type) . p -> true := λ (p : Type) . λ (_ : p) . trivial;
                axiom false : Type;
                axiom false_elim : Π (p : Type) . false -> p;
            ",
        ),
        vec![
            def("true", Some(var("Type")), None,),
            def("true_intro", Some(var("true")), None,),
            def(
                "tx",
                Some(pi(("p", var("Type")), arrow(var("p"), var("true")))),
                Some(lambda(
                    ("p", var("Type")),
                    lambda(("_", var("p")), var("trivial"))
                )),
            ),
            def("false", Some(var("Type")), None,),
            def(
                "false_elim",
                Some(pi(("p", var("Type")), arrow(var("false"), var("p")))),
                None,
            ),
        ],
    );
}

#[test]
fn binder_shorthand_limits() {
    // a binder with type can be unparenthesized, as in `λ a : t . x`,
    // but only when the lambda has a single argument.
    no_parse("λ a : Type b : Type . a");
    no_parse("λ (a : Type) b : Type . a");
    no_parse("λ a : Type (b : Type) . a");
    no_parse("Π a : Type b : Type . a");
    no_parse("Π (a : Type) b : Type . a");
    no_parse("Π a : Type (b : Type) . a");
    no_parse("Π a b : Type . a");
    assert_eq!(parse("Π a : t b . a"), parse("Π (a : (t b)) . a"));
}
