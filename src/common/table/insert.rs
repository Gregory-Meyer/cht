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

use super::{BucketResult, MutateResult, MutateVisitResult, MutateVisitor, Table};

use crate::common::Bucket;

use std::sync::atomic::Ordering;

use crossbeam_epoch::{Guard, Owned, Shared};

impl<'g, K: 'g + Eq, V: 'g> Table<K, V> {
    pub(crate) fn insert(
        &self,
        guard: &'g Guard,
        hash: u64,
        bucket: Owned<Bucket<K, V>>,
    ) -> BucketResult<'g, K, V, Owned<Bucket<K, V>>> {
        match self.mutate(
            guard,
            hash,
            Visitor {
                bucket,
                table: self,
            },
        ) {
            MutateResult::Returned(r) => r.map_err(|visitor| visitor.bucket),
            MutateResult::LoopEnded(vistor) | MutateResult::FoundSentinelTag(vistor) => {
                Err(vistor.bucket)
            }
        }
    }
}

struct Visitor<'a, K, V> {
    bucket: Owned<Bucket<K, V>>,
    table: &'a Table<K, V>,
}

impl<'a, K, V> Visitor<'a, K, V> {
    fn into_bucket_table<'g>(self) -> MutateVisitResult<'g, K, V, Self> {
        Ok(Some((self.bucket, self.table)))
    }
}

impl<'g, 'a, K, V> MutateVisitor<'g, K, V> for Visitor<'a, K, V> {
    type Memento = &'a Table<K, V>;
    type Pointer = Owned<Bucket<K, V>>;
    type Key = K;

    fn key(&self) -> &K {
        &self.bucket.key
    }

    fn on_filled(
        self,
        _: Shared<'_, Bucket<K, V>>,
        _: &K,
        _: &V,
    ) -> MutateVisitResult<'g, K, V, Self> {
        self.into_bucket_table()
    }

    fn on_tombstone(self, _: Shared<'_, Bucket<K, V>>, _: &K) -> MutateVisitResult<'g, K, V, Self> {
        self.into_bucket_table()
    }

    fn on_null(self) -> MutateVisitResult<'g, K, V, Self> {
        if self.table.can_insert() {
            self.into_bucket_table()
        } else {
            Err(self)
        }
    }

    fn from_pointer(bucket: Self::Pointer, table: &'a Table<K, V>) -> Self {
        Self { bucket, table }
    }
}
