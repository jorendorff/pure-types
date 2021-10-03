use std::fmt::{self, Display, Formatter};

pub type Id = string_cache::DefaultAtom;

#[derive(Clone, PartialEq, Debug)]
pub enum Expr<S> {
    ConstSort(S),
    Var(Id),
    Product(Id, Box<Expr<S>>, Box<Expr<S>>),
    Apply(Box<Expr<S>>, Box<Expr<S>>),
    Lambda(Id, Box<Expr<S>>, Box<Expr<S>>),
}

impl<S: Display> Display for Expr<S> {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        match self {
            Expr::ConstSort(s) => write!(f, "{}", *s),
            Expr::Var(v) => write!(f, "{}", v),
            Expr::Product(p, p_ty, body) => write!(f, "Π ({} : {}) . {}", p, p_ty, body),
            Expr::Apply(fun, arg) => write!(f, "({})({})", fun, arg),
            Expr::Lambda(p, p_ty, body) => write!(f, "λ ({} : {}) . {}", p, p_ty, body),
        }
    }
}

impl<S: Clone> Expr<S> {
    pub fn subst(self, x: &Id, y: &Expr<S>) -> Box<Expr<S>> {
        match self {
            Expr::ConstSort(s) => Box::new(Expr::ConstSort(s)),
            Expr::Var(v) => {
                if v == *x {
                    Box::new(y.clone())
                } else {
                    Box::new(Expr::Var(v))
                }
            }
            Expr::Product(v, v_ty, body) => Box::new(Expr::Product(
                v.clone(),
                v_ty.subst(x, y),
                if v == *x { body } else { body.subst(x, y) },
            )),
            Expr::Apply(f, arg) => Box::new(Expr::Apply(f.subst(x, y), arg.subst(x, y))),
            Expr::Lambda(v, v_ty, body) => Box::new(Expr::Lambda(
                v.clone(),
                v_ty.subst(x, y),
                if v == *x { body } else { body.subst(x, y) },
            )),
        }
    }
}

pub fn var<S>(x: &str) -> Box<Expr<S>> {
    Box::new(Expr::Var(Id::from(x)))
}

pub fn apply<S>(f: Box<Expr<S>>, a: Box<Expr<S>>) -> Box<Expr<S>> {
    Box::new(Expr::Apply(f, a))
}

pub fn lambda<S>(p: &str, ty: Box<Expr<S>>, b: Box<Expr<S>>) -> Box<Expr<S>> {
    Box::new(Expr::Lambda(Id::from(p), ty, b))
}

pub fn pi<S>(p: &str, ty: Box<Expr<S>>, b: Box<Expr<S>>) -> Box<Expr<S>> {
    Box::new(Expr::Product(Id::from(p), ty, b))
}

pub fn arrow<S>(f: Box<Expr<S>>, a: Box<Expr<S>>) -> Box<Expr<S>> {
    Box::new(Expr::Product(Id::from("_"), f, a))
}

pub fn sort<S>(s: S) -> Box<Expr<S>> {
    Box::new(Expr::ConstSort(s))
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
