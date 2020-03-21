// MIT License
//
// Copyright (c) 2020 Gregory Meyer
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

use super::{MutateResult, MutateVisitResult, MutateVisitor, Table};

use crate::common::Bucket;

use std::borrow::Borrow;

use crossbeam_epoch::{Guard, Shared};

impl<'g, K: 'g + Eq, V: 'g> Table<K, V> {
    pub(crate) fn remove_if<Q: ?Sized + Eq, F: FnMut(&K, &V) -> bool>(
        &self,
        guard: &'g Guard,
        hash: u64,
        key: &'g Q,
        condition: F,
    ) -> Result<Shared<'g, Bucket<K, V>>, F>
    where
        K: Borrow<Q>,
    {
        match self.mutate(guard, hash, Visitor { key, condition }) {
            MutateResult::Returned(r) => r.map_err(|visitor| visitor.condition),
            MutateResult::LoopEnded(visitor) | MutateResult::FoundSentinelTag(visitor) => {
                Err(visitor.condition)
            }
        }
    }
}

struct Visitor<'a, Q: ?Sized, F> {
    key: &'a Q,
    condition: F,
}

impl<'g, 'a: 'g, K: 'a, V: 'a, Q: ?Sized, F: FnMut(&K, &V) -> bool> MutateVisitor<'g, K, V>
    for Visitor<'a, Q, F>
{
    type Memento = Self;
    type Pointer = Shared<'g, Bucket<K, V>>;
    type Key = Q;

    fn key(&self) -> &Q {
        self.key
    }

    fn on_filled(
        mut self,
        bucket_ptr: Shared<'g, Bucket<K, V>>,
        key: &K,
        value: &V,
    ) -> MutateVisitResult<'g, K, V, Self> {
        if !(self.condition)(key, value) {
            Ok(None)
        } else {
            let bucket = Bucket::to_tombstone(bucket_ptr);

            Ok(Some((bucket, self)))
        }
    }

    fn on_tombstone(self, _: Shared<'_, Bucket<K, V>>, _: &K) -> MutateVisitResult<'g, K, V, Self> {
        Ok(None)
    }

    fn on_null(self) -> MutateVisitResult<'g, K, V, Self> {
        Ok(None)
    }

    fn from_pointer(_: Self::Pointer, visitor: Self) -> Self {
        visitor
    }
}
