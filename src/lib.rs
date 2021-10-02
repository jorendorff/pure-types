use lalrpop_util::lalrpop_mod;

pub mod ast;
lalrpop_mod!(pub parser);
pub mod pts;

pub use ast::{Expr, USort, Var};
