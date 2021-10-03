use std::fmt::{self, Debug, Display, Formatter};
use std::rc::Rc;

pub type Id = string_cache::DefaultAtom;

#[derive(Clone, PartialEq)]
pub struct Expr<S>(pub(crate) Rc<ExprEnum<S>>);

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
    Expr(Rc::new(ExprEnum::Pi(Id::from("_"), f, a)))
}

pub fn sort<S>(s: S) -> Expr<S> {
    Expr(Rc::new(ExprEnum::ConstSort(s)))
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

#[derive(Clone, PartialEq, Debug)]
pub(crate) enum ExprEnum<S> {
    ConstSort(S),
    Var(Id),
    Pi(Id, Expr<S>, Expr<S>),
    Apply(Expr<S>, Expr<S>),
    Lambda(Id, Expr<S>, Expr<S>),
}

impl<S: Display> Display for ExprEnum<S> {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        match self {
            ExprEnum::ConstSort(s) => write!(f, "{}", *s),
            ExprEnum::Var(v) => write!(f, "{}", v),
            ExprEnum::Pi(p, p_ty, body) => write!(f, "Π ({} : {}) . {}", p, p_ty, body),
            ExprEnum::Apply(fun, arg) => write!(f, "({})({})", fun, arg),
            ExprEnum::Lambda(p, p_ty, body) => write!(f, "λ ({} : {}) . {}", p, p_ty, body),
        }
    }
}

impl<S: Clone> Expr<S> {
    pub(crate) fn inner(&self) -> &ExprEnum<S> {
        &self.0
    }

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
        }
    }
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
