//! Static environments.

use std::fmt::{self, Debug, Display, Formatter};
use std::rc::Rc;

use rpds::HashTrieMap;

use crate::{ast, ast::TermEnum, Id, Term, TypeCheckError};

pub struct PureTypeSystem {
    pub axioms: HashTrieMap<Id, Id>,
    pub function_sorts: HashTrieMap<(Id, Id), Id>,
}

/// A static environment, mapping identifiers to type-expressions.
#[derive(Clone)]
pub struct Env {
    bindings: HashTrieMap<Id, Binding>,
    pub system: Rc<PureTypeSystem>,
}

/// An axiom, definition, or parameter.
///
/// If we have `def foo : A := b;` then `foo` has type `A` and definition `b`.
/// A function parameter has a type but its definition is None.
///
/// `ty` and `def` may contain free variables (?). The interpretation of these
/// is tricky.
#[derive(Debug, Clone)]
pub struct Binding {
    /// Type of the binding.
    pub ty: Term,

    /// Definition of the binding.
    ///
    /// In the case of a function application like `f 0`, given `def f := λ i :
    /// nat . i + 1`, when trying to figure out if it's definitionally
    /// equivalent to something else, we can reduce terms at typecheck time,
    /// with the result that the binding `i` contains the definition `0`.
    ///
    /// Otherwise, we generally don't know what's in a parameter binding,
    /// so the `def` will be `None`.
    pub def: Option<Term>,
}

impl Debug for Env {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let mut entries: Vec<(&Id, &Binding)> = self.bindings.iter().collect();
        entries.sort_by_key(|(id, _binding)| id.clone());
        f.debug_list().entries(entries).finish()
    }
}

impl Display for Binding {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        write!(f, ": {}", self.ty)?;
        if let Some(def) = &self.def {
            write!(f, ":= {}", def)?;
        }
        Ok(())
    }
}

impl Env {
    pub fn new(system: Rc<PureTypeSystem>) -> Self {
        Env {
            bindings: HashTrieMap::new(),
            system,
        }
    }

    pub fn get(&self, x: &Id) -> Option<&Binding> {
        self.bindings.get(x)
    }

    pub fn with(&self, id: impl Into<Id>, binding: Binding) -> Env {
        Env {
            bindings: self.bindings.insert(id.into(), binding),
            system: Rc::clone(&self.system),
        }
    }

    pub fn with_param(&self, id: impl Into<Id>, ty: Term) -> Env {
        self.with(id.into(), Binding { ty, def: None })
    }

    pub fn with_definition(&self, id: impl Into<Id>, ty: Term, definition: Term) -> Env {
        self.with(
            id.into(),
            Binding {
                ty,
                def: Some(definition),
            },
        )
    }

    /// Reduce `term` to a canonical form. This leaves variables unevaluated
    /// where they occur free.
    pub fn eval(&self, term: &Term) -> Result<Term, TypeCheckError> {
        Ok(match term.inner() {
            TermEnum::Constant(_) => term.clone(),
            TermEnum::Variable(v) => match self.get(v) {
                None => term.clone(),
                Some(binding) => match &binding.def {
                    None => term.clone(),
                    Some(value) => value.clone(),
                },
            },
            TermEnum::Apply(fun, arg) => {
                let fun = self.eval(fun)?;
                let arg = self.eval(arg)?;
                if let TermEnum::Lambda(param, param_ty, body) = fun.inner() {
                    self.with_definition(param.clone(), param_ty.clone(), arg)
                        .eval(body)?
                } else {
                    ast::apply(fun, arg)
                }
            }
            TermEnum::Lambda(param, param_ty, body) => {
                // Note: Evaluates the body on purpose. The point of `eval` is
                // to perform substitutions (from `self`, on `term`). Since the
                // result does not contain those substitutions in any other
                // form, we have to push them through now.
                let param_ty = self.eval(param_ty)?;
                let body = self.with_param(param, param_ty.clone()).eval(body)?;
                ast::lambda(param, param_ty, body)
            }
            TermEnum::Pi(param, param_ty, body) => {
                let param_ty = self.eval(param_ty)?;
                let body = self.with_param(param, param_ty.clone()).eval(body)?;
                ast::pi(param, param_ty, body)
            }
            TermEnum::Subst(id, binding, body) => self.with(id, binding.clone()).eval(body)?,
        })
    }
}

impl PureTypeSystem {
    /// Return the empty environment.
    pub fn env(self: &Rc<Self>) -> Env {
        Env {
            bindings: HashTrieMap::new(),
            system: Rc::clone(self),
        }
    }

    pub fn get_constant_type(&self, c: &Id) -> Result<Term, TypeCheckError> {
        if let Some(t) = self.axioms.get(c) {
            Ok(ast::constant(t.clone()))
        } else {
            Err(TypeCheckError::UnrecognizedConstant)
        }
    }

    pub fn get_function_sort<'env>(
        &'env self,
        param_sort: &Id,
        body_sort: &Id,
    ) -> Option<&'env Id> {
        let param_sort = param_sort.clone();
        let body_sort = body_sort.clone();
        self.function_sorts.get(&(param_sort, body_sort))
    }
}
