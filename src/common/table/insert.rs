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

use super::{BucketLike, BucketResult, MutateBucketResult, Table};

use crate::common::Bucket;

use std::sync::atomic::Ordering;

use crossbeam_epoch::{Guard, Owned};

impl<K: Eq, V> BucketLike<K, V, K> for Owned<Bucket<K, V>> {
    type Memento = ();
    type Pointer = Self;

    fn key_like(&self) -> &K {
        &self.key
    }

    fn from_pointer(pointer: Self::Pointer, _: Self::Memento) -> Self {
        pointer
    }
}

impl<'g, K: 'g + Eq, V: 'g> Table<K, V> {
    pub(crate) fn insert(
        &self,
        guard: &'g Guard,
        hash: u64,
        bucket_ptr: Owned<Bucket<K, V>>,
    ) -> BucketResult<'g, K, V, Owned<Bucket<K, V>>> {
        match self.mutate_bucket(
            guard,
            hash,
            bucket_ptr,
            |bucket_ptr, _, _, _| Some((bucket_ptr, ())),
            |bucket_ptr, _| Some((bucket_ptr, ())),
            |bucket_ptr| {
                if self.num_nonnull_buckets.load(Ordering::Relaxed) < self.capacity() {
                    Ok(Some((bucket_ptr, ())))
                } else {
                    Err(bucket_ptr)
                }
            },
        ) {
            MutateBucketResult::Returned(r) => r,
            MutateBucketResult::LoopEnded(b) | MutateBucketResult::FoundSentinelTag(b) => Err(b),
        }
    }
}
