use std::fmt::{self, Display, Formatter};
use std::rc::Rc;

pub type Id = string_cache::DefaultAtom;

#[derive(Clone, PartialEq, Debug)]
pub enum Expr<S> {
    ConstSort(S),
    Var(Id),
    Product(Id, Rc<Expr<S>>, Rc<Expr<S>>),
    Apply(Rc<Expr<S>>, Rc<Expr<S>>),
    Lambda(Id, Rc<Expr<S>>, Rc<Expr<S>>),
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
    pub fn subst(&self, x: &Id, y: &Rc<Expr<S>>) -> Rc<Expr<S>> {
        match self {
            Expr::ConstSort(s) => Rc::new(Expr::ConstSort(s.clone())),
            Expr::Var(v) => {
                if *v == *x {
                    Rc::clone(y)
                } else {
                    Rc::new(Expr::Var(v.clone()))
                }
            }
            Expr::Product(v, v_ty, body) => Rc::new(Expr::Product(
                v.clone(),
                v_ty.subst(x, y),
                if *v == *x {
                    Rc::clone(body)
                } else {
                    body.subst(x, y)
                },
            )),
            Expr::Apply(f, arg) => Rc::new(Expr::Apply(f.subst(x, y), arg.subst(x, y))),
            Expr::Lambda(v, v_ty, body) => Rc::new(Expr::Lambda(
                v.clone(),
                v_ty.subst(x, y),
                if *v == *x {
                    Rc::clone(body)
                } else {
                    body.subst(x, y)
                },
            )),
        }
    }
}

pub fn var<S>(x: &str) -> Rc<Expr<S>> {
    Rc::new(Expr::Var(Id::from(x)))
}

pub fn apply<S>(f: Rc<Expr<S>>, a: Rc<Expr<S>>) -> Rc<Expr<S>> {
    Rc::new(Expr::Apply(f, a))
}

pub fn lambda<S>(p: &str, ty: Rc<Expr<S>>, b: Rc<Expr<S>>) -> Rc<Expr<S>> {
    Rc::new(Expr::Lambda(Id::from(p), ty, b))
}

pub fn pi<S>(p: &str, ty: Rc<Expr<S>>, b: Rc<Expr<S>>) -> Rc<Expr<S>> {
    Rc::new(Expr::Product(Id::from(p), ty, b))
}

pub fn arrow<S>(f: Rc<Expr<S>>, a: Rc<Expr<S>>) -> Rc<Expr<S>> {
    Rc::new(Expr::Product(Id::from("_"), f, a))
}

pub fn sort<S>(s: S) -> Rc<Expr<S>> {
    Rc::new(Expr::ConstSort(s))
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
