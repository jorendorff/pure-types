//! Concrete syntax trees.

use std::fmt::{self, Debug, Display, Formatter};

/// The type of identifiers.
pub type Id = string_cache::DefaultAtom;

/// Expressions.
#[derive(PartialEq)]
pub struct Expr(pub(crate) Box<ExprEnum>);

#[derive(Debug, PartialEq)]
pub(crate) enum ExprEnum {
    Var(Id),
    Pi(Vec<Binder>, Expr),
    Arrow(Expr, Expr),
    Lambda(Vec<Binder>, Expr),
    Apply(Expr, Expr),
    Blank,
}

#[derive(Debug, PartialEq)]
pub struct Binder {
    pub ids: Vec<Id>,
    pub ty: Option<Expr>,
}

#[derive(Debug, PartialEq)]
pub struct Def {
    pub id: Id,
    pub ty: Option<Expr>,
    pub term: Option<Expr>,
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        <ExprEnum as Display>::fmt(&self.0, f)
    }
}

impl Debug for Expr {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        <ExprEnum as Debug>::fmt(&self.0, f)
    }
}

impl Display for ExprEnum {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        use ExprEnum::*;
        match self {
            Var(v) => write!(f, "{}", v),
            Pi(binders, body) => {
                write!(f, "Π")?;
                write_binders(f, binders)?;
                write!(f, " . {}", body)
            }
            Arrow(arg_ty, out_ty) => {
                match arg_ty.inner() {
                    Var(_) | Apply(..) | Blank => write!(f, "{}", arg_ty)?,
                    _ => write!(f, "({})", arg_ty)?,
                }
                write!(f, " -> ")?;
                match out_ty.inner() {
                    Var(_) | Apply(..) | Arrow(..) | Blank => write!(f, "{}", out_ty),
                    _ => write!(f, "({})", out_ty),
                }
            }
            Apply(fun, arg) => {
                match fun.inner() {
                    Var(_) | Apply(..) | Blank => write!(f, "{}", fun)?,
                    _ => write!(f, "({})", fun)?,
                }
                write!(f, " ")?;
                match arg.inner() {
                    Var(_) | Blank => write!(f, "{}", arg),
                    _ => write!(f, "({})", arg),
                }
            }
            Lambda(binders, body) => {
                write!(f, "λ")?;
                write_binders(f, binders)?;
                write!(f, " . {}", body)
            }
            Blank => write!(f, "_"),
        }
    }
}

fn write_binders(f: &mut Formatter, binders: &[Binder]) -> Result<(), fmt::Error> {
    match binders {
        [Binder { ids, ty: Some(ty) }] => {
            let strs: Vec<&str> = ids.iter().map(|id| id as &str).collect();
            write!(f, " {} : {}", strs.join(" "), ty)?
        }
        _ => {
            write!(f, "Π")?;
            for b in binders {
                let strs: Vec<&str> = b.ids.iter().map(|id| id as &str).collect();
                if let Some(ty) = &b.ty {
                    write!(f, " ({} : {})", strs.join(" "), ty)?;
                } else {
                    assert_eq!(strs.len(), 1);
                    write!(f, " {}", strs.join(" "))?;
                }
            }
        }
    }
    Ok(())
}

impl Expr {
    pub(crate) fn inner(&self) -> &ExprEnum {
        &self.0
    }
}

// *** DbgInto trait for convenience constructors

/// Alternative version of Into for binders, since coherence rules are too
/// strict to use Into.
pub trait DbgInto<T> {
    fn dbg_into(self) -> T;
}

impl DbgInto<Vec<Id>> for Id {
    fn dbg_into(self) -> Vec<Id> {
        vec![self]
    }
}

impl<T> DbgInto<T> for T {
    fn dbg_into(self) -> T {
        self
    }
}

impl<T> DbgInto<Option<T>> for T {
    fn dbg_into(self) -> Option<T> {
        Some(self)
    }
}

impl<'s> DbgInto<Id> for &'s str {
    fn dbg_into(self) -> Id {
        self.into()
    }
}

impl<'s> DbgInto<Vec<Id>> for &'s str {
    fn dbg_into(self) -> Vec<Id> {
        vec![self.into()]
    }
}

impl<Ids: DbgInto<Vec<Id>>, Ty: DbgInto<Option<Expr>>> DbgInto<Vec<Binder>> for (Ids, Ty) {
    fn dbg_into(self) -> Vec<Binder> {
        Binder {
            ids: self.0.dbg_into(),
            ty: self.1.dbg_into(),
        }
        .dbg_into()
    }
}

impl DbgInto<Vec<Binder>> for Binder {
    fn dbg_into(self) -> Vec<Binder> {
        vec![self]
    }
}

impl DbgInto<Vec<Binder>> for Vec<Id> {
    fn dbg_into(self) -> Vec<Binder> {
        Binder {
            ids: self,
            ty: None,
        }
        .dbg_into()
    }
}

impl DbgInto<Vec<Binder>> for Id {
    fn dbg_into(self) -> Vec<Binder> {
        vec![self].dbg_into()
    }
}

impl<'s> DbgInto<Vec<Binder>> for &'s str {
    fn dbg_into(self) -> Vec<Binder> {
        Binder {
            ids: vec![Id::from(self)],
            ty: None,
        }
        .dbg_into()
    }
}

// *** Convenience constructors

pub fn var(x: impl DbgInto<Id>) -> Expr {
    Expr(Box::new(ExprEnum::Var(x.dbg_into())))
}

pub fn binder(id: impl DbgInto<Vec<Id>>, ty: impl DbgInto<Option<Expr>>) -> Binder {
    Binder {
        ids: id.dbg_into(),
        ty: ty.dbg_into(),
    }
}

pub fn pi(binders: impl DbgInto<Vec<Binder>>, body: Expr) -> Expr {
    Expr(Box::new(ExprEnum::Pi(binders.dbg_into(), body)))
}

pub fn arrow(a: Expr, b: Expr) -> Expr {
    Expr(Box::new(ExprEnum::Arrow(a, b)))
}

pub fn lambda(binders: impl DbgInto<Vec<Binder>>, body: Expr) -> Expr {
    Expr(Box::new(ExprEnum::Lambda(binders.dbg_into(), body)))
}

pub fn apply(f: Expr, a: Expr) -> Expr {
    Expr(Box::new(ExprEnum::Apply(f, a)))
}

pub fn blank() -> Expr {
    Expr(Box::new(ExprEnum::Blank))
}

pub fn var_or_blank(x: impl Into<Id>) -> Expr {
    let x = x.into();
    if x == Id::from("_") {
        blank()
    } else {
        var(x)
    }
}

pub fn def(
    id: impl DbgInto<Id>,
    ty: impl DbgInto<Option<Expr>>,
    term: impl DbgInto<Option<Expr>>,
) -> Def {
    Def {
        id: id.dbg_into(),
        ty: ty.dbg_into(),
        term: term.dbg_into(),
    }
}
