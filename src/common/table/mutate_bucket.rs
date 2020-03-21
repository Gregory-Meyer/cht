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

use super::{ProbeLoopAction, ProbeLoopResult, ProbeLoopState, Table};

use crate::common::{Bucket, BucketRef};

use std::{borrow::Borrow, result::Result as StdResult, sync::atomic::Ordering};

use crossbeam_epoch::{CompareAndSetError, Guard, Pointer, Shared};

impl<'g, K: 'g + Eq, V: 'g> Table<K, V> {
    pub(super) fn mutate_bucket<B: BucketLike<K, V, Q>, Q: ?Sized + Eq>(
        &self,
        guard: &'g Guard,
        hash: u64,
        bucket_like: B,
        mut on_filled: impl FnMut(
            B,
            Shared<'g, Bucket<K, V>>,
            &K,
            &V,
        ) -> Option<(B::Pointer, B::Memento)>,
        mut on_tombstone: impl FnMut(B, &K) -> Option<(B::Pointer, B::Memento)>,
        mut on_null: impl FnMut(B) -> StdResult<Option<(B::Pointer, B::Memento)>, B>,
    ) -> Result<Shared<'g, Bucket<K, V>>, B>
    where
        K: Borrow<Q>,
    {
        let mut maybe_bucket_like = Some(bucket_like);

        match self.probe_loop(hash, |loop_state| {
            let ProbeLoopState {
                current_control_byte,
                this_bucket,
                ..
            } = loop_state;

            let bucket_like = maybe_bucket_like.take().unwrap();
            let this_bucket_ptr = this_bucket.load_consume(guard);

            let (new_bucket_ptr, memento) = match unsafe { Bucket::as_ref(this_bucket_ptr) } {
                BucketRef::Filled(this_key, this_value)
                    if this_key.borrow() == bucket_like.key_like() =>
                {
                    if let Some(t) = on_filled(bucket_like, this_bucket_ptr, this_key, this_value) {
                        t
                    } else {
                        return ProbeLoopAction::Return(Ok(Shared::null()));
                    }
                }
                BucketRef::Tombstone(this_key) if this_key.borrow() == bucket_like.key_like() => {
                    if let Some(t) = on_tombstone(bucket_like, this_key) {
                        t
                    } else {
                        return ProbeLoopAction::Return(Ok(Shared::null()));
                    }
                }
                BucketRef::Filled(_, _) | BucketRef::Tombstone(_) => {
                    maybe_bucket_like = Some(bucket_like);

                    return ProbeLoopAction::Continue;
                }
                BucketRef::Null => {
                    assert_eq!(current_control_byte, 0);

                    match on_null(bucket_like) {
                        Ok(Some(t)) => t,
                        Ok(None) => return ProbeLoopAction::Return(Ok(Shared::null())),
                        Err(bucket_like) => return ProbeLoopAction::Return(Err(bucket_like)),
                    }
                }
                BucketRef::Sentinel => {
                    return ProbeLoopAction::Return(Err(bucket_like));
                }
            };

            if let Err(CompareAndSetError { new, .. }) = this_bucket.compare_and_set_weak(
                this_bucket_ptr,
                new_bucket_ptr,
                (Ordering::Release, Ordering::Relaxed),
                guard,
            ) {
                maybe_bucket_like = Some(B::from_pointer(new, memento));

                ProbeLoopAction::Reload
            } else {
                loop_state.set_control_byte();

                if this_bucket_ptr.is_null() {
                    self.num_nonnull_buckets.fetch_add(1, Ordering::Relaxed);
                }

                ProbeLoopAction::Return(Ok(this_bucket_ptr))
            }
        }) {
            ProbeLoopResult::Returned(t) => Result::Returned(t),
            ProbeLoopResult::LoopEnded => Result::LoopEnded(maybe_bucket_like.unwrap()),
            ProbeLoopResult::FoundSentinelTag => {
                Result::FoundSentinelTag(maybe_bucket_like.unwrap())
            }
        }
    }
}

pub(super) trait BucketLike<K, V, Q: ?Sized + Eq>
where
    K: Borrow<Q>,
{
    type Memento;
    type Pointer: Pointer<Bucket<K, V>>;

    fn key_like(&self) -> &Q;
    fn from_pointer(pointer: Self::Pointer, memento: Self::Memento) -> Self;
}

pub(super) enum Result<T, B> {
    Returned(StdResult<T, B>),
    LoopEnded(B),
    FoundSentinelTag(B),
}
