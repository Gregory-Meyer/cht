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

use crossbeam_epoch::{Guard, Shared};

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
        match self.probe_loop(
            hash,
            |ProbeLoopState {
                 current_control_byte,
                 this_bucket,
                 ..
             }| {
                if current_control_byte == 0 {
                    return ProbeLoopAction::Return(Ok(Shared::null()));
                }

                let this_bucket_ptr = this_bucket.load_consume(guard);

                match unsafe { Bucket::as_ref(this_bucket_ptr) } {
                    BucketRef::Filled(this_key, this_value) if this_key.borrow() == key => {
                        if !condition(this_key, this_value) {
                            return ProbeLoopAction::Return(Ok(Shared::null()));
                        }
                    }
                    BucketRef::Tombstone(this_key) if this_key.borrow() == key => {
                        return ProbeLoopAction::Return(Ok(Shared::null()));
                    }
                    BucketRef::Filled(_, _) | BucketRef::Tombstone(_) => {
                        return ProbeLoopAction::Continue;
                    }
                    BucketRef::Null => unreachable!(),
                    BucketRef::Sentinel => return ProbeLoopAction::Return(Err(())),
                }

                let tombstone_ptr = Bucket::to_tombstone(this_bucket_ptr);

                if this_bucket
                    .compare_and_set_weak(
                        this_bucket_ptr,
                        tombstone_ptr,
                        (Ordering::Release, Ordering::Relaxed),
                        guard,
                    )
                    .is_ok()
                {
                    ProbeLoopAction::Return(Ok(this_bucket_ptr))
                } else {
                    ProbeLoopAction::Reload
                }
            },
        ) {
            ProbeLoopResult::Returned(Ok(previous_bucket_ptr)) => Ok(previous_bucket_ptr),
            ProbeLoopResult::LoopEnded => Ok(Shared::null()),
            ProbeLoopResult::FoundSentinelTag | ProbeLoopResult::Returned(Err(_)) => Err(condition),
        }
    }
}
