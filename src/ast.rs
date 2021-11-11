//! Abstract syntax trees.

use std::{
    fmt::{self, Debug, Display, Formatter},
    rc::Rc,
};

use crate::{cst, Binding};

/// The type of identifiers.
pub type Id = string_cache::DefaultAtom;

#[derive(Clone)]
pub struct Term(pub(crate) Rc<TermEnum>);

#[derive(Debug)]
pub enum TermEnum {
    Constant(Id),
    Variable(Id),
    Apply(Term, Term),
    Lambda(Id, Term, Term),
    Pi(Id, Term, Term),
    Subst(Id, Binding, Term),
}

impl Display for Term {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        <TermEnum as Display>::fmt(&self.0, f)
    }
}

impl Debug for Term {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        <TermEnum as Debug>::fmt(&self.0, f)
    }
}

impl Display for TermEnum {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        match self {
            TermEnum::Constant(c) => write!(f, "#c{}", *c),
            TermEnum::Variable(v) => write!(f, "{}", v),
            TermEnum::Pi(p, p_ty, body) => write!(f, "Π ({} : {}) . {}", p, p_ty, body),
            TermEnum::Apply(fun, arg) => {
                match fun.inner() {
                    TermEnum::Pi(..) | TermEnum::Lambda(..) => write!(f, "({})", fun)?,
                    _ => write!(f, "{}", fun)?,
                }
                write!(f, " ")?;
                match arg.inner() {
                    TermEnum::Pi(..) | TermEnum::Lambda(..) | TermEnum::Apply(..) => {
                        write!(f, "({})", arg)
                    }
                    _ => write!(f, "{}", arg),
                }
            }
            TermEnum::Lambda(p, p_ty, body) => write!(f, "λ ({} : {}) . {}", p, p_ty, body),
            TermEnum::Subst(id, binding, body) => write!(f, "({})[{} {}]", body, id, binding),
        }
    }
}

impl Term {
    pub(crate) fn from_cst(expr: cst::Term) -> Self {
        match *expr.0 {
            cst::TermEnum::Var(id) => var(id),
            cst::TermEnum::Pi(binders, body) => desugar_binders(TermEnum::Pi, binders, body),
            cst::TermEnum::Arrow(arg_ty, ret_ty) => {
                arrow(Self::from_cst(arg_ty), Self::from_cst(ret_ty))
            }
            cst::TermEnum::Lambda(binders, body) => {
                desugar_binders(TermEnum::Lambda, binders, body)
            }
            cst::TermEnum::Apply(fun, arg) => apply(Self::from_cst(fun), Self::from_cst(arg)),
            cst::TermEnum::Blank => blank(0),
        }
    }

    pub(crate) fn inner(&self) -> &TermEnum {
        &self.0
    }
}

fn desugar_binders(
    construct: fn(Id, Term, Term) -> TermEnum,
    binders: Vec<cst::Binder>,
    body: cst::Term,
) -> Term {
    binders
        .into_iter()
        .flat_map(|binder| {
            let ty = match binder.ty {
                Some(ty) => Term::from_cst(ty),
                None => blank(0),
            };
            binder.ids.into_iter().map(move |id| (id, ty.clone()))
        })
        .rev()
        .fold(Term::from_cst(body), |body, (id, ty)| {
            Term(Rc::new(construct(id, ty, body)))
        })
}

#[derive(Debug)]
pub struct Def {
    pub id: Id,
    pub ty: Option<Term>,
    pub term: Option<Term>,
}

impl Def {
    fn from_cst(cst: cst::Def) -> Self {
        Def {
            id: cst.id,
            ty: cst.ty.map(Term::from_cst),
            term: cst.term.map(Term::from_cst),
        }
    }
}

pub fn program_from_cst(cst: Vec<cst::Def>) -> Vec<Def> {
    cst.into_iter().map(Def::from_cst).collect()
}

// *** Convenience constructors

pub fn constant(c: impl Into<Id>) -> Term {
    Term(Rc::new(TermEnum::Constant(c.into())))
}

pub fn var(x: impl Into<Id>) -> Term {
    Term(Rc::new(TermEnum::Variable(x.into())))
}

pub fn apply(f: Term, a: Term) -> Term {
    Term(Rc::new(TermEnum::Apply(f, a)))
}

pub fn lambda(p: impl Into<Id>, ty: Term, b: Term) -> Term {
    Term(Rc::new(TermEnum::Lambda(p.into(), ty, b)))
}

pub fn pi(p: impl Into<Id>, ty: Term, b: Term) -> Term {
    Term(Rc::new(TermEnum::Pi(p.into(), ty, b)))
}

pub fn arrow(f: Term, a: Term) -> Term {
    pi("_", f, a)
}

pub fn blank(_index: usize) -> Term {
    panic!("no blanks please")
}

pub fn var_or_blank(x: impl Into<Id>) -> Term {
    let x = x.into();
    if x == Id::from("_") {
        blank(0)
    } else {
        var(x)
    }
}

pub fn def(id: Id, ty: Option<Term>, term: Option<Term>) -> Def {
    Def { id, ty, term }
}
