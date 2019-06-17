// MIT License
//
// Copyright (c) 2019 Gregory Meyer
//
// Permission is hereby granted, free of charge, to any person
// obtaining a copy of this software and associated documentation files
// (the "Software"), to deal in the Software without restriction,
// including without limitation the rights to use, copy, modify, merge,
// publish, distribute, sublicense, and/or sell copies of the Software,
// and to permit persons to whom the Software is furnished to do so,
// subject to the following conditions:
//
// The above copyright notice and this permission notice shall be
// included in all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
// NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
// BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
// ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
// CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

use crate::map::HashMap;

use std::{
    borrow::Borrow,
    hash::{BuildHasher, Hash},
};

use fxhash::FxBuildHasher;

pub struct HashSet<T: Hash + Eq, S: BuildHasher> {
    map: HashMap<T, (), S>,
}

impl<T: Hash + Eq> HashSet<T, FxBuildHasher> {
    pub fn new() -> HashSet<T, FxBuildHasher> {
        HashSet::with_capacity_and_hasher(0, FxBuildHasher::default())
    }

    pub fn with_capacity(capacity: usize) -> HashSet<T, FxBuildHasher> {
        HashSet::with_capacity_and_hasher(capacity, FxBuildHasher::default())
    }
}

impl<T: Hash + Eq, S: BuildHasher> HashSet<T, S> {
    pub fn with_hasher(hash_builder: S) -> HashSet<T, S> {
        HashSet::with_capacity_and_hasher(0, hash_builder)
    }

    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> HashSet<T, S> {
        HashSet {
            map: HashMap::with_capacity_and_hasher(capacity, hash_builder),
        }
    }

    pub fn capacity(&self) -> usize {
        self.map.capacity()
    }

    pub fn len(&self) -> usize {
        self.map.len()
    }

    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    pub fn contains<Q: ?Sized + Hash + Eq>(&self, value: &Q) -> bool
    where
        T: Borrow<Q>,
    {
        self.map.get_and(value, |_| ()).is_some()
    }

    pub fn get<Q: ?Sized + Hash + Eq>(&self, value: &Q) -> Option<T>
    where
        T: Borrow<Q> + Clone,
    {
        self.map.get_key_value(value).map(|(k, _)| k)
    }

    pub fn insert(&self, value: T) -> bool {
        self.map.insert_and(value, (), |_| ()).is_none()
    }

    pub fn replace(&self, value: T) -> Option<T>
    where
        T: Clone,
    {
        self.map.insert_entry(value, ()).map(|(k, _)| k)
    }

    pub fn remove<Q: ?Sized + Hash + Eq>(&self, value: &Q) -> bool
    where
        T: Borrow<Q> + Clone,
    {
        self.map.remove_and(value, |_| ()).is_some()
    }
}
