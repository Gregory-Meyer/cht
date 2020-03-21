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

use super::{BucketResult, ProbeLoopAction, ProbeLoopResult, ProbeLoopState, Table};

use crate::common::{Bucket, BucketRef};

use std::sync::atomic::Ordering;

use crossbeam_epoch::{CompareAndSetError, Guard, Owned};

impl<'g, K: 'g + Eq, V: 'g> Table<K, V> {
    pub(crate) fn insert(
        &self,
        guard: &'g Guard,
        hash: u64,
        bucket_ptr: Owned<Bucket<K, V>>,
    ) -> BucketResult<'g, K, V, Owned<Bucket<K, V>>> {
        let mut maybe_bucket_ptr = Some(bucket_ptr);

        match self.probe_loop(hash, |loop_state| {
            let ProbeLoopState {
                current_control_byte,
                this_bucket,
                ..
            } = loop_state;

            let bucket_ptr = maybe_bucket_ptr.take().unwrap();
            let this_bucket_ptr = this_bucket.load_consume(guard);

            match unsafe { Bucket::as_ref(this_bucket_ptr) } {
                BucketRef::Filled(this_key, _) | BucketRef::Tombstone(this_key)
                    if this_key != &bucket_ptr.key =>
                {
                    maybe_bucket_ptr = Some(bucket_ptr);

                    return ProbeLoopAction::Continue;
                }
                BucketRef::Null => {
                    if self.num_nonnull_buckets.load(Ordering::Relaxed) >= self.capacity() {
                        return ProbeLoopAction::Return(Err(bucket_ptr));
                    }

                    assert_eq!(current_control_byte, 0);
                }
                BucketRef::Sentinel => return ProbeLoopAction::Return(Err(bucket_ptr)),
                _ => (),
            }

            match this_bucket.compare_and_set_weak(
                this_bucket_ptr,
                bucket_ptr,
                (Ordering::Release, Ordering::Relaxed),
                guard,
            ) {
                Ok(_) => {
                    loop_state.set_control_byte();

                    if this_bucket_ptr.is_null() {
                        self.num_nonnull_buckets.fetch_add(1, Ordering::Relaxed);
                    }

                    ProbeLoopAction::Return(Ok(this_bucket_ptr))
                }
                Err(CompareAndSetError { new, .. }) => {
                    maybe_bucket_ptr = Some(new);

                    ProbeLoopAction::Reload
                }
            }
        }) {
            ProbeLoopResult::Returned(r) => r,
            ProbeLoopResult::LoopEnded | ProbeLoopResult::FoundSentinelTag => {
                Err(maybe_bucket_ptr.unwrap())
            }
        }
    }
}
