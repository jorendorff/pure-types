//! The error type.

use thiserror::Error;

use crate::{Expr, Id};

/// An error in type checking.
#[derive(Error, Debug)]
pub enum TypeCheckError<S> {
    #[error("`{0:?}` can't be used as an expression in code; it has no type")]
    UntypedSort(S),

    #[error("can't find value {0:?} in this scope")]
    UndeclaredVar(Id),

    #[error("invalid function type `{0}`: the type of the argument type `{1}` is not a sort")]
    InvalidPiParameterType(Expr<S>, Expr<S>),

    #[error("invalid function type `{0}`: the type of the return type `{1}` is not a sort")]
    InvalidPiReturnType(Expr<S>, Expr<S>),

    #[error(
        "invalid function type `{0}`: the argument type is a {1:?} and the return type is a {2:?}"
    )]
    InvalidPiSorts(Expr<S>, S, S),

    #[error("invalid lambda `{0}`: the type of the argument type `{1}` is not a sort")]
    InvalidLambdaParameterType(Expr<S>, Expr<S>),

    #[error("invalid lambda `{0}`: the body is of type `{1}`, and that type's type is not a sort")]
    InvalidLambdaReturnType(Expr<S>, Expr<S>),

    #[error("invalid lambda `{0}`: the argument type is a {1:?} and the return type is a {2:?}")]
    InvalidLambdaSorts(Expr<S>, S, S),

    #[error("type error in function call `{0}`: function expected, type of `{1}` is `{2}`")]
    FunctionExpected(Expr<S>, Expr<S>, Expr<S>),

    #[error("argument is the wrong type in `{0}`: expected `{1}`, got `{2}`")]
    ArgumentTypeMismatch(Expr<S>, Expr<S>, Expr<S>),

    #[error("type mismatch: expected `{0}`, got `{1}`")]
    UnifyMismatch(Expr<S>, Expr<S>),

    #[error("can't type-check expressions containing blanks")]
    Blank,
}
