//! Static environments.

use std::{
    fmt::{self, Debug, Formatter},
    iter::FromIterator,
};

use rpds::HashTrieMap;

use crate::{Expr, Id};

/// A static environment, mapping identifiers to type-expressions.
#[derive(Clone)]
pub struct Env<S>(HashTrieMap<Id, Thunk<S>>);

#[derive(Debug, Clone)]
pub struct Thunk<S> {
    pub env: Env<S>,
    pub term: Expr<S>,
}

impl<S: Debug> Debug for Env<S> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let mut entries: Vec<(&Id, &Thunk<S>)> = self.0.iter().collect();
        entries.sort_by_key(|(_id, thunk)| thunk.env.0.size());
        f.debug_list()
            .entries(entries.into_iter().map(|(id, thunk)| (id, &thunk.term)))
            .finish()
    }
}

impl<S> Env<S> {
    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        Env(HashTrieMap::new())
    }

    pub fn get(&self, x: &Id) -> Option<&Thunk<S>> {
        self.0.get(x)
    }

    pub fn with(&self, id: Id, term: Thunk<S>) -> Env<S> {
        Env(self.0.insert(id, term))
    }
}

impl<S: Clone> Env<S> {
    pub fn push(&mut self, id: Id, term: Expr<S>) {
        self.0 = self.0.insert(
            id,
            Thunk {
                env: self.clone(),
                term,
            },
        );
    }
}

impl<S: Clone> FromIterator<(Id, Expr<S>)> for Env<S> {
    fn from_iter<T: IntoIterator<Item = (Id, Expr<S>)>>(iter: T) -> Self {
        let mut env = Env::new();
        for (id, term) in iter {
            env.push(id, term);
        }
        env
    }
}
