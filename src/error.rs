//! The error type.

use thiserror::Error;

use crate::{Id, Term};

/// An error in type checking.
#[derive(Error, Debug)]
pub enum TypeCheckError {
    #[error("unrecognized or untyped constant")]
    UnrecognizedConstant,

    #[error("can't find value {0:?} in this scope")]
    UndeclaredVar(Id),

    #[error("invalid function type `{0}`: the type of the argument type `{1}` is not a sort")]
    InvalidPiParameterType(Term, Term),

    #[error("invalid function type `{0}`: the type of the return type `{1}` is not a sort")]
    InvalidPiReturnType(Term, Term),

    #[error(
        "invalid function type `{0}`: the argument type is a {1} and the return type is a {2}"
    )]
    InvalidPiSorts(Term, Id, Id),

    #[error("invalid lambda `{0}`: the type of the argument type `{1}` is not a sort")]
    InvalidLambdaParameterType(Term, Term),

    #[error("invalid lambda `{0}`: the body is of type `{1}`, and that type's type is not a sort")]
    InvalidLambdaReturnType(Term, Term),

    #[error("invalid lambda `{0}`: the argument type is a {1} and the return type is a {2}")]
    InvalidLambdaSorts(Term, Id, Id),

    #[error("type error in function call `{0}`: function expected, type of `{1}` is `{2}`")]
    FunctionExpected(Term, Term, Term),

    #[error("argument is the wrong type in `{0}`: expected `{1}`, got `{2}`")]
    ArgumentTypeMismatch(Term, Term, Term, #[source] Box<dyn std::error::Error>),

    #[error(
        "in definition of `{0}`, the defined type is `{1}`, but the expression `{2}` has type `{3}`"
    )]
    DefinedTypeMismatch(Id, Term, Term, Term, #[source] Box<dyn std::error::Error>),

    #[error("type mismatch: expected `{0}`, got `{1}`")]
    UnifyMismatch(Term, Term),

    #[error("can't type-check expressions containing blanks")]
    Blank,

    #[error("missing type in definition of `{0}`")]
    MissingType(Id),

    #[error("can't reduce blank")]
    ReduceBlank,

    #[error("expected lambda, got `{0}`")]
    ExpectedLambda(String),

    #[error("internal error: tried to evaluate an application that should not have type-checked; `{0}` is not a function")]
    EvalApplyPi(Term),

    #[error("internal error: tried to evaluate a variable `{0}` that isn't in scope")]
    EvalUndefined(Id),
}
