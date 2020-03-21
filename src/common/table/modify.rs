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

use crossbeam_epoch::{Guard, Owned};

impl<'g, K: 'g + Eq, V: 'g> Table<K, V> {
    pub(crate) fn modify<F: FnMut(&K, &V) -> V>(
        &self,
        guard: &'g Guard,
        hash: u64,
        key_or_owned_bucket: KeyOrOwnedBucket<K, V>,
        mut modifier: F,
    ) -> BucketResult<'g, K, V, (KeyOrOwnedBucket<K, V>, F)> {
        match self.mutate_bucket(
            guard,
            hash,
            key_or_owned_bucket,
            |key_or_owned_bucket, _, this_key, this_value| {
                Some((
                    key_or_owned_bucket.into_bucket(modifier(this_key, this_value)),
                    (),
                ))
            },
            |_, _| None,
            |_| Ok(None),
        ) {
            MutateBucketResult::Returned(r) => r.map_err(|k_or_ob| (k_or_ob, modifier)),
            MutateBucketResult::LoopEnded(k_or_ob)
            | MutateBucketResult::FoundSentinelTag(k_or_ob) => Err((k_or_ob, modifier)),
        }
    }
}

pub(crate) enum KeyOrOwnedBucket<K, V> {
    Key(K),
    OwnedBucket(Owned<Bucket<K, V>>),
}

impl<K, V> KeyOrOwnedBucket<K, V> {
    fn into_bucket(self, value: V) -> Owned<Bucket<K, V>> {
        match self {
            Self::Key(k) => Bucket::new(k, value),
            Self::OwnedBucket(b) => Bucket::with_value(b, value).0,
        }
    }
}

impl<K: Eq, V> BucketLike<K, V, K> for KeyOrOwnedBucket<K, V> {
    type Memento = ();
    type Pointer = Owned<Bucket<K, V>>;

    fn key_like(&self) -> &K {
        match self {
            Self::Key(k) => k,
            Self::OwnedBucket(b) => &b.key,
        }
    }

    fn from_pointer(bucket: Owned<Bucket<K, V>>, _: ()) -> Self {
        Self::OwnedBucket(bucket)
    }
}
