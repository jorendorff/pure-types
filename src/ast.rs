//! Abstract syntax trees.

use std::{
    fmt::{self, Debug, Display, Formatter},
    rc::Rc,
};

/// The type of identifiers.
pub type Id = string_cache::DefaultAtom;

/// Expressions.
#[derive(Clone, PartialEq)]
pub struct Expr<S>(pub(crate) Rc<ExprEnum<S>>);

#[derive(Clone, PartialEq, Debug)]
pub(crate) enum ExprEnum<S> {
    ConstSort(S),
    Var(Id),
    Pi(Id, Expr<S>, Expr<S>),
    Apply(Expr<S>, Expr<S>),
    Lambda(Id, Expr<S>, Expr<S>),
    Blank,
}

pub(crate) struct Binder<S> {
    pub(crate) id: Id,
    pub(crate) ty: Expr<S>,
}

pub fn var<S>(x: impl Into<Id>) -> Expr<S> {
    Expr(Rc::new(ExprEnum::Var(x.into())))
}

pub fn apply<S>(f: Expr<S>, a: Expr<S>) -> Expr<S> {
    Expr(Rc::new(ExprEnum::Apply(f, a)))
}

pub fn lambda<S>(p: impl Into<Id>, ty: Expr<S>, b: Expr<S>) -> Expr<S> {
    Expr(Rc::new(ExprEnum::Lambda(p.into(), ty, b)))
}

pub(crate) fn binders_to_lambda<S>(binders: Vec<Binder<S>>, b: Expr<S>) -> Expr<S> {
    binders
        .into_iter()
        .rev()
        .fold(b, |b, Binder { id, ty }| lambda(id, ty, b))
}

pub fn pi<S>(p: impl Into<Id>, ty: Expr<S>, b: Expr<S>) -> Expr<S> {
    Expr(Rc::new(ExprEnum::Pi(p.into(), ty, b)))
}

pub(crate) fn binders_to_pi<S>(binders: Vec<Binder<S>>, b: Expr<S>) -> Expr<S> {
    binders
        .into_iter()
        .rev()
        .fold(b, |b, Binder { id, ty }| pi(id, ty, b))
}

pub fn arrow<S>(f: Expr<S>, a: Expr<S>) -> Expr<S> {
    Expr(Rc::new(ExprEnum::Pi(Id::from("_"), f, a)))
}

pub fn sort<S>(s: S) -> Expr<S> {
    Expr(Rc::new(ExprEnum::ConstSort(s)))
}

pub fn blank<S>() -> Expr<S> {
    Expr(Rc::new(ExprEnum::Blank))
}

pub fn var_or_blank<S>(x: impl Into<Id>) -> Expr<S> {
    let x = x.into();
    if x == Id::from("_") {
        blank()
    } else {
        var(x)
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
            ExprEnum::Blank => write!(f, "_"),
        }
    }
}

impl<S> Expr<S> {
    pub(crate) fn inner(&self) -> &ExprEnum<S> {
        &self.0
    }
}

impl<S: Clone> Expr<S> {
    pub fn subst(&self, x: &Id, y: &Expr<S>) -> Expr<S> {
        match self.inner() {
            ExprEnum::ConstSort(s) => sort(s.clone()),
            ExprEnum::Var(v) => {
                if *v == *x {
                    y.clone()
                } else {
                    self.clone()
                }
            }
            ExprEnum::Pi(v, v_ty, body) => pi(
                v.clone(),
                v_ty.subst(x, y),
                if *v == *x {
                    body.clone()
                } else {
                    body.subst(x, y)
                },
            ),
            ExprEnum::Apply(f, arg) => apply(f.subst(x, y), arg.subst(x, y)),
            ExprEnum::Lambda(v, v_ty, body) => lambda(
                v.clone(),
                v_ty.subst(x, y),
                if *v == *x {
                    body.clone()
                } else {
                    body.subst(x, y)
                },
            ),
            ExprEnum::Blank => self.clone(),
        }
    }
}

#[derive(Debug)]
pub struct Def<S> {
    pub id: Id,
    pub ty: Option<Expr<S>>,
    pub term: Option<Expr<S>>,
}

pub fn def<S>(id: Id, ty: Option<Expr<S>>, term: Option<Expr<S>>) -> Def<S> {
    Def { id, ty, term }
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
