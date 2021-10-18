//! Abstract syntax trees.

use std::{
    fmt::{self, Debug, Display, Formatter},
    rc::Rc,
};

use crate::cst;

/// The type of identifiers.
pub type Id = string_cache::DefaultAtom;

/// Expressions.
#[derive(PartialEq)]
pub struct Expr<S>(pub(crate) Rc<ExprEnum<S>>);

#[derive(Clone, PartialEq, Debug)]
pub(crate) enum ExprEnum<S> {
    ConstSort(S),
    Var(Id),
    Pi(Id, Expr<S>, Expr<S>),
    Apply(Expr<S>, Expr<S>),
    Lambda(Id, Expr<S>, Expr<S>),

    /// A placeholder.
    Blank(usize),

    /// Used for bindings that are not defined as equivalent to particular
    /// expressions, like lambda bindings and axioms.
    Undefined(usize),
}

// Manual implementation, as `#[derive(Clone)]` derives an unwanted `S: Clone` bound.
impl<S> Clone for Expr<S> {
    fn clone(&self) -> Self {
        Expr(self.0.clone())
    }
}

impl<S: Display> Display for Expr<S> {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        <ExprEnum<S> as Display>::fmt(&self.0, f)
    }
}

impl<S: Debug> Debug for Expr<S> {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        <ExprEnum<S> as Debug>::fmt(&self.0, f)
    }
}

impl<S: Display> Display for ExprEnum<S> {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        match self {
            ExprEnum::ConstSort(s) => write!(f, "{}", *s),
            ExprEnum::Var(v) => write!(f, "{}", v),
            ExprEnum::Pi(p, p_ty, body) => write!(f, "Π ({} : {}) . {}", p, p_ty, body),
            ExprEnum::Apply(fun, arg) => {
                match fun.inner() {
                    ExprEnum::Pi(..) | ExprEnum::Lambda(..) => write!(f, "({})", fun)?,
                    _ => write!(f, "{}", fun)?,
                }
                write!(f, " ")?;
                match arg.inner() {
                    ExprEnum::Pi(..) | ExprEnum::Lambda(..) | ExprEnum::Apply(..) => {
                        write!(f, "({})", arg)
                    }
                    _ => write!(f, "{}", arg),
                }
            }
            ExprEnum::Lambda(p, p_ty, body) => write!(f, "λ ({} : {}) . {}", p, p_ty, body),
            ExprEnum::Blank(n) => write!(f, "#_{}", n),
            ExprEnum::Undefined(n) => write!(f, "#undef{}", n),
        }
    }
}

impl<S> Expr<S> {
    pub(crate) fn from_cst(expr: cst::Expr) -> Self {
        match *expr.0 {
            cst::ExprEnum::Var(id) => var(id),
            cst::ExprEnum::Pi(binders, body) => desugar_binders(ExprEnum::Pi, binders, body),
            cst::ExprEnum::Arrow(arg_ty, ret_ty) => {
                arrow(Self::from_cst(arg_ty), Self::from_cst(ret_ty))
            }
            cst::ExprEnum::Lambda(binders, body) => {
                desugar_binders(ExprEnum::Lambda, binders, body)
            }
            cst::ExprEnum::Apply(fun, arg) => apply(Self::from_cst(fun), Self::from_cst(arg)),
            cst::ExprEnum::Blank => blank(0),
        }
    }

    pub(crate) fn inner(&self) -> &ExprEnum<S> {
        &self.0
    }

    pub fn is_blank(&self) -> bool {
        matches!(self.inner(), ExprEnum::Blank(_))
    }
}

fn desugar_binders<S>(
    construct: fn(Id, Expr<S>, Expr<S>) -> ExprEnum<S>,
    binders: Vec<cst::Binder>,
    body: cst::Expr,
) -> Expr<S> {
    binders
        .into_iter()
        .flat_map(|binder| {
            let ty = match binder.ty {
                Some(ty) => Expr::from_cst(ty),
                None => blank(0),
            };
            binder.ids.into_iter().map(move |id| (id, ty.clone()))
        })
        .rev()
        .fold(Expr::from_cst(body), |body, (id, ty)| {
            Expr(Rc::new(construct(id, ty, body)))
        })
}

#[derive(Debug)]
pub struct Def<S> {
    pub id: Id,
    pub ty: Option<Expr<S>>,
    pub term: Option<Expr<S>>,
}

impl<S> Def<S> {
    fn from_cst(cst: cst::Def) -> Self {
        Def {
            id: cst.id,
            ty: cst.ty.map(Expr::from_cst),
            term: cst.term.map(Expr::from_cst),
        }
    }
}

pub fn program_from_cst<S>(cst: Vec<cst::Def>) -> Vec<Def<S>> {
    cst.into_iter().map(Def::from_cst).collect()
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum USort {
    Type,
    Kind,
    Triangle,
}

impl Display for USort {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        let c = match self {
            USort::Type => '∗',
            USort::Kind => '◻',
            USort::Triangle => '△',
        };
        write!(f, "{}", c)
    }
}

// *** Convenience constructors

pub fn var<S>(x: impl Into<Id>) -> Expr<S> {
    Expr(Rc::new(ExprEnum::Var(x.into())))
}

pub fn apply<S>(f: Expr<S>, a: Expr<S>) -> Expr<S> {
    Expr(Rc::new(ExprEnum::Apply(f, a)))
}

pub fn lambda<S>(p: impl Into<Id>, ty: Expr<S>, b: Expr<S>) -> Expr<S> {
    Expr(Rc::new(ExprEnum::Lambda(p.into(), ty, b)))
}

pub fn pi<S>(p: impl Into<Id>, ty: Expr<S>, b: Expr<S>) -> Expr<S> {
    Expr(Rc::new(ExprEnum::Pi(p.into(), ty, b)))
}

pub fn arrow<S>(f: Expr<S>, a: Expr<S>) -> Expr<S> {
    pi("_", f, a)
}

pub fn sort<S>(s: S) -> Expr<S> {
    Expr(Rc::new(ExprEnum::ConstSort(s)))
}

pub fn blank<S>(index: usize) -> Expr<S> {
    Expr(Rc::new(ExprEnum::Blank(index)))
}

pub fn undefined<S>(undefined_id: usize) -> Expr<S> {
    Expr(Rc::new(ExprEnum::Undefined(undefined_id)))
}

pub fn var_or_blank<S>(x: impl Into<Id>) -> Expr<S> {
    let x = x.into();
    if x == Id::from("_") {
        blank(0)
    } else {
        var(x)
    }
}

pub fn def<S>(id: Id, ty: Option<Expr<S>>, term: Option<Expr<S>>) -> Def<S> {
    Def { id, ty, term }
}
