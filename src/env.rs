//! Static environments.

use std::fmt::{self, Debug, Formatter};

use rpds::HashTrieMap;

use crate::{ast, Expr, Id};

/// A static environment, mapping identifiers to type-expressions.
#[derive(Clone)]
pub struct Env<S>(HashTrieMap<Id, Binding<S>>);

#[derive(Debug, Clone)]
pub struct Thunk<S> {
    pub env: Env<S>,
    pub term: Expr<S>,
}

/// An axiom, definition, or parameter.
///
/// If we have `def foo : A := b;` then `foo` has type `A` and definition `b`.
/// A function parameter has a type but no definition.
#[derive(Debug, Clone)]
pub struct Binding<S> {
    /// Type of the binding.
    pub ty: Thunk<S>,

    /// Definition of the binding.
    ///
    /// In the case of a function application like `f 0`, given `def f := λ i :
    /// nat . i + 1`, when trying to figure out if it's definitionally
    /// equivalent to something else, we can reduce terms at typecheck time,
    /// with the result that the binding `i` contains the definition `0`.
    ///
    /// Otherwise, we generally don't know what's in a parameter binding,
    /// so the `def` will be `Undefined`.
    pub def: Thunk<S>,
}

impl<S: Debug> Debug for Env<S> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let mut entries: Vec<(&Id, &Binding<S>)> = self.0.iter().collect();
        entries.sort_by_key(|(_id, binding)| binding.ty.env.0.size());
        f.debug_list()
            .entries(
                entries
                    .into_iter()
                    .map(|(id, binding)| (id, &binding.ty.term)),
            )
            .finish()
    }
}

impl<S> Env<S> {
    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        Env(HashTrieMap::new())
    }

    pub fn get(&self, x: &Id) -> Option<&Binding<S>> {
        self.0.get(x)
    }

    pub fn with(&self, id: Id, binding: Binding<S>) -> Env<S> {
        Env(self.0.insert(id, binding))
    }
}
