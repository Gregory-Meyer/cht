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

use crossbeam_epoch::{Guard, Owned, Shared};

impl<'g, K: 'g + Eq, V: 'g> Table<K, V> {
    pub(crate) fn modify<F: FnMut(&K, &V) -> V>(
        &self,
        guard: &'g Guard,
        hash: u64,
        key_or_owned_bucket: KeyOrBucket<K, V>,
        modifier: F,
    ) -> BucketResult<'g, K, V, (KeyOrBucket<K, V>, F)> {
        match self.mutate(
            guard,
            hash,
            Visitor {
                key_or_owned_bucket,
                modifier,
            },
        ) {
            MutateResult::Returned(r) => r.map_err(Visitor::into_tuple),
            MutateResult::LoopEnded(visitor) | MutateResult::FoundSentinelTag(visitor) => {
                Err(visitor.into_tuple())
            }
        }
    }
}

pub(crate) enum KeyOrBucket<K, V> {
    Key(K),
    Bucket(Owned<Bucket<K, V>>),
}

struct Visitor<K, V, F: FnMut(&K, &V) -> V> {
    key_or_owned_bucket: KeyOrBucket<K, V>,
    modifier: F,
}

impl<K, V, F: FnMut(&K, &V) -> V> Visitor<K, V, F> {
    fn into_tuple(self) -> (KeyOrBucket<K, V>, F) {
        let Self {
            key_or_owned_bucket,
            modifier,
        } = self;

        (key_or_owned_bucket, modifier)
    }
}

impl<'g, K, V, F: FnMut(&K, &V) -> V> MutateVisitor<'g, K, V> for Visitor<K, V, F> {
    type Memento = F;
    type Pointer = Owned<Bucket<K, V>>;
    type Key = K;

    fn key(&self) -> &K {
        match &self.key_or_owned_bucket {
            KeyOrBucket::Key(key) => &key,
            KeyOrBucket::Bucket(bucket) => &bucket.key,
        }
    }

    fn on_filled(
        self,
        _: Shared<'g, Bucket<K, V>>,
        key: &K,
        value: &V,
    ) -> MutateVisitResult<'g, K, V, Self> {
        let Visitor {
            key_or_owned_bucket,
            mut modifier,
        } = self;

        let new_value = modifier(key, value);
        let bucket = match key_or_owned_bucket {
            KeyOrBucket::Key(k) => Bucket::new(k, new_value),
            KeyOrBucket::Bucket(b) => Bucket::with_value(b, new_value).0,
        };

        Ok(Some((bucket, modifier)))
    }

    fn on_tombstone(self, _: Shared<'_, Bucket<K, V>>, _: &K) -> MutateVisitResult<'g, K, V, Self> {
        Ok(None)
    }

    fn on_null(self) -> MutateVisitResult<'g, K, V, Self> {
        Ok(None)
    }

    fn from_pointer(bucket: Owned<Bucket<K, V>>, modifier: F) -> Self {
        Self {
            key_or_owned_bucket: KeyOrBucket::Bucket(bucket),
            modifier,
        }
    }
}
