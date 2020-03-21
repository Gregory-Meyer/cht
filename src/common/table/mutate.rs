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

use std::{borrow::Borrow, sync::atomic::Ordering};

use crossbeam_epoch::{CompareAndSetError, Guard, Pointer, Shared};

impl<'g, K: 'g + Eq, V: 'g> Table<K, V> {
    pub(super) fn mutate<B: Visitor<'g, K, V>>(
        &self,
        guard: &'g Guard,
        hash: u64,
        visitor: B,
    ) -> MutateResult<Shared<'g, Bucket<K, V>>, B>
    where
        B::Key: Eq,
        K: Borrow<B::Key>,
    {
        let mut maybe_visitor = Some(visitor);

        match self.probe_loop(hash, |loop_state| {
            let ProbeLoopState {
                current_control_byte,
                this_bucket,
                ..
            } = loop_state;

            let visitor = maybe_visitor.take().unwrap();
            let this_bucket_ptr = this_bucket.load_consume(guard);

            let result = match unsafe { Bucket::as_ref(this_bucket_ptr) } {
                BucketRef::Filled(this_key, this_value) if this_key.borrow() == visitor.key() => {
                    visitor.on_filled(this_bucket_ptr, this_key, this_value)
                }
                BucketRef::Tombstone(this_key) if this_key.borrow() == visitor.key() => {
                    visitor.on_tombstone(this_bucket_ptr, this_key)
                }
                BucketRef::Filled(_, _) | BucketRef::Tombstone(_) => {
                    maybe_visitor = Some(visitor);

                    return ProbeLoopAction::Continue;
                }
                BucketRef::Null => {
                    assert_eq!(current_control_byte, 0);

                    visitor.on_null()
                }
                BucketRef::Sentinel => {
                    return ProbeLoopAction::Return(Err(visitor));
                }
            };

            let (new_bucket_ptr, memento) = match result {
                Ok(Some((new_bucket_ptr, memento))) => (new_bucket_ptr, memento),
                Ok(None) => return ProbeLoopAction::Return(Ok(Shared::null())),
                Err(visitor) => return ProbeLoopAction::Return(Err(visitor)),
            };

            if let Err(CompareAndSetError {
                new: new_bucket_ptr,
                ..
            }) = this_bucket.compare_and_set_weak(
                this_bucket_ptr,
                new_bucket_ptr,
                (Ordering::Release, Ordering::Relaxed),
                guard,
            ) {
                maybe_visitor = Some(B::from_pointer(new_bucket_ptr, memento));

                ProbeLoopAction::Reload
            } else {
                loop_state.set_control_byte();

                if this_bucket_ptr.is_null() {
                    self.num_nonnull_buckets.fetch_add(1, Ordering::Relaxed);
                }

                ProbeLoopAction::Return(Ok(this_bucket_ptr))
            }
        }) {
            ProbeLoopResult::Returned(t) => MutateResult::Returned(t),
            ProbeLoopResult::LoopEnded => MutateResult::LoopEnded(maybe_visitor.unwrap()),
            ProbeLoopResult::FoundSentinelTag => {
                MutateResult::FoundSentinelTag(maybe_visitor.unwrap())
            }
        }
    }
}

pub(super) trait Visitor<'g, K, V>: Sized {
    type Memento;
    type Pointer: Pointer<Bucket<K, V>>;
    type Key: ?Sized;

    fn key(&self) -> &Self::Key;
    fn on_filled(
        self,
        bucket_ptr: Shared<'g, Bucket<K, V>>,
        key: &K,
        value: &V,
    ) -> VisitResult<'g, K, V, Self>;
    fn on_tombstone(
        self,
        bucket_ptr: Shared<'_, Bucket<K, V>>,
        key: &K,
    ) -> VisitResult<'g, K, V, Self>;
    fn on_null(self) -> VisitResult<'g, K, V, Self>;
    fn from_pointer(pointer: Self::Pointer, memento: Self::Memento) -> Self;
}

pub(super) type VisitResult<'g, K, V, B> = Result<
    Option<(
        <B as Visitor<'g, K, V>>::Pointer,
        <B as Visitor<'g, K, V>>::Memento,
    )>,
    B,
>;

pub(super) enum MutateResult<T, B> {
    Returned(Result<T, B>),
    LoopEnded(B),
    FoundSentinelTag(B),
}
