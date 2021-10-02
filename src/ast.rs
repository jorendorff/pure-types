use std::fmt::{self, Display, Formatter};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Var(pub &'static str);

impl Var {
    pub fn new(s: &str) -> Var {
        Var(Box::leak(s.to_string().into_boxed_str()))
    }
}

impl Display for Var {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", self.0)
    }
}

#[derive(Clone, PartialEq, Debug)]
pub enum Expr<S> {
    ConstSort(S),
    Var(Var),
    Product(Var, Box<Expr<S>>, Box<Expr<S>>),
    Apply(Box<Expr<S>>, Box<Expr<S>>),
    Lambda(Var, Box<Expr<S>>, Box<Expr<S>>),
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
    pub fn subst(self, x: Var, y: &Expr<S>) -> Box<Expr<S>> {
        match self {
            Expr::ConstSort(s) => Box::new(Expr::ConstSort(s)),
            Expr::Var(v) => {
                if v == x {
                    Box::new(y.clone())
                } else {
                    Box::new(Expr::Var(v))
                }
            }
            Expr::Product(v, v_ty, body) => Box::new(Expr::Product(
                v,
                v_ty.subst(x, y),
                if v == x { body } else { body.subst(x, y) },
            )),
            Expr::Apply(f, arg) => Box::new(Expr::Apply(f.subst(x, y), arg.subst(x, y))),
            Expr::Lambda(v, v_ty, body) => Box::new(Expr::Lambda(
                v,
                v_ty.subst(x, y),
                if v == x { body } else { body.subst(x, y) },
            )),
        }
    }
}

pub fn var<S>(x: &'static str) -> Box<Expr<S>> {
    Box::new(Expr::Var(Var(x)))
}

pub fn apply<S>(f: Box<Expr<S>>, a: Box<Expr<S>>) -> Box<Expr<S>> {
    Box::new(Expr::Apply(f, a))
}

pub fn lambda<S>(p: &'static str, ty: Box<Expr<S>>, b: Box<Expr<S>>) -> Box<Expr<S>> {
    Box::new(Expr::Lambda(Var(p), ty, b))
}

pub fn pi<S>(p: &'static str, ty: Box<Expr<S>>, b: Box<Expr<S>>) -> Box<Expr<S>> {
    Box::new(Expr::Product(Var(p), ty, b))
}

pub fn arrow<S>(f: Box<Expr<S>>, a: Box<Expr<S>>) -> Box<Expr<S>> {
    Box::new(Expr::Product(Var("_"), f, a))
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
