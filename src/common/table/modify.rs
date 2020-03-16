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

use super::*;

use crate::common::{Bucket, BucketRef};

impl<'g, K: 'g + Eq, V: 'g> Table<K, V> {
    pub(crate) fn modify<F: FnMut(&K, &V) -> V>(
        &self,
        guard: &'g Guard,
        hash: u64,
        key_or_owned_bucket: KeyOrOwnedBucket<K, V>,
        mut modifier: F,
    ) -> BucketResult<'g, K, V, (KeyOrOwnedBucket<K, V>, F)> {
        let mut maybe_key_or_owned_bucket = Some(key_or_owned_bucket);

        match self.probe_loop(hash, |_, _, _, _, expected, this_bucket| {
            let key_or_owned_bucket = maybe_key_or_owned_bucket.take().unwrap();

            if expected == 0 {
                return ProbeLoopAction::Return(Ok(Shared::null()));
            }

            let this_bucket_ptr = this_bucket.load_consume(guard);

            let new_value = match unsafe { Bucket::as_ref(this_bucket_ptr) } {
                BucketRef::Filled(this_key, this_value)
                    if this_key == key_or_owned_bucket.key() =>
                {
                    modifier(this_key, this_value)
                }
                BucketRef::Tombstone(this_key) if this_key == key_or_owned_bucket.key() => {
                    return ProbeLoopAction::Return(Ok(Shared::null()));
                }
                BucketRef::Filled(_, _) | BucketRef::Tombstone(_) => {
                    maybe_key_or_owned_bucket = Some(key_or_owned_bucket);

                    return ProbeLoopAction::Continue;
                }
                BucketRef::Null => {
                    assert_eq!(expected, 0);

                    return ProbeLoopAction::Return(Ok(Shared::null()));
                }
                BucketRef::Sentinel => return ProbeLoopAction::Return(Err(key_or_owned_bucket)),
            };

            let new_bucket_ptr = key_or_owned_bucket.into_bucket(new_value);

            if let Err(CompareAndSetError { new, .. }) = this_bucket.compare_and_set_weak(
                this_bucket_ptr,
                new_bucket_ptr,
                (Ordering::Release, Ordering::Relaxed),
                guard,
            ) {
                maybe_key_or_owned_bucket = Some(KeyOrOwnedBucket::OwnedBucket(new));

                ProbeLoopAction::Reload
            } else {
                ProbeLoopAction::Return(Ok(this_bucket_ptr))
            }
        }) {
            ProbeLoopResult::Returned(result) => {
                result.map_err(|key_or_owned_bucket| (key_or_owned_bucket, modifier))
            }
            ProbeLoopResult::LoopEnded => Ok(Shared::null()),
            ProbeLoopResult::FoundSentinelTag => {
                Err((maybe_key_or_owned_bucket.unwrap(), modifier))
            }
        }
    }
}

pub(crate) enum KeyOrOwnedBucket<K, V> {
    Key(K),
    OwnedBucket(Owned<Bucket<K, V>>),
}

impl<K, V> KeyOrOwnedBucket<K, V> {
    fn key(&self) -> &K {
        match self {
            Self::Key(k) => k,
            Self::OwnedBucket(b) => &b.key,
        }
    }

    fn into_bucket(self, value: V) -> Owned<Bucket<K, V>> {
        match self {
            Self::Key(k) => Bucket::new(k, value),
            Self::OwnedBucket(b) => Bucket::with_value(b, value).0,
        }
    }
}
