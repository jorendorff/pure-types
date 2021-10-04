//! Static environments.

use std::{
    fmt::{self, Debug, Formatter},
    iter::FromIterator,
};

use rpds::HashTrieMap;

use crate::{Expr, Id};

/// A static environment, mapping identifiers to type-expressions.
///
/// XXX FIXME: A type-expression may contain an identifier. This identifier
/// should be interpreted with reference to the immediately enclosing
/// environment. But we don't store anything that would make it possible to
/// figure out what the environment is.
///
/// Generally the meaning of identifiers is broken everywhere.
#[derive(Clone, PartialEq)]
pub struct Env<S>(HashTrieMap<Id, Expr<S>>);

impl<S: Debug> Debug for Env<S> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_list().entries(&self.0).finish()
    }
}

impl<S> Env<S> {
    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        Env(HashTrieMap::new())
    }

    pub fn get(&self, x: &Id) -> Option<&Expr<S>> {
        self.0.get(x)
    }

    pub fn with(&self, id: Id, term: Expr<S>) -> Env<S> {
        Env(self.0.insert(id, term))
    }

    pub fn push(&mut self, id: Id, term: Expr<S>) {
        self.0 = self.0.insert(id, term);
    }
}

impl<S> FromIterator<(Id, Expr<S>)> for Env<S> {
    fn from_iter<T: IntoIterator<Item = (Id, Expr<S>)>>(iter: T) -> Self {
        Env(iter.into_iter().collect())
    }
}
