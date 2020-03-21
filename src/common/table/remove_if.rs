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

use super::{BucketLike, MutateBucketResult, Table};

use crate::common::Bucket;

use std::borrow::Borrow;

use crossbeam_epoch::{Guard, Shared};

impl<'g, K: 'g + Eq, V: 'g, Q: 'g + Eq + ?Sized> BucketLike<K, V, Q> for &'g Q
where
    K: Borrow<Q>,
{
    type Memento = &'g Q;
    type Pointer = Shared<'g, Bucket<K, V>>;

    fn key_like(&self) -> &Q {
        *self
    }

    fn from_pointer(_: Shared<'g, Bucket<K, V>>, bucket_like: Self) -> Self {
        bucket_like
    }
}

impl<'g, K: 'g + Eq, V: 'g> Table<K, V> {
    pub(crate) fn remove_if<Q: ?Sized + Eq, F: FnMut(&K, &V) -> bool>(
        &self,
        guard: &'g Guard,
        hash: u64,
        key: &Q,
        mut condition: F,
    ) -> Result<Shared<'g, Bucket<K, V>>, F>
    where
        K: Borrow<Q>,
    {
        match self.mutate_bucket(
            guard,
            hash,
            key,
            |key, this_bucket_ptr, this_key, this_value| {
                if !condition(this_key, this_value) {
                    None
                } else {
                    Some((Bucket::to_tombstone(this_bucket_ptr), key))
                }
            },
            |_, _| None,
            |_| Ok(None),
        ) {
            MutateBucketResult::Returned(r) => r.map_err(|_| condition),
            MutateBucketResult::LoopEnded(_) | MutateBucketResult::FoundSentinelTag(_) => {
                Err(condition)
            }
        }
    }
}
