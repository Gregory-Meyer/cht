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

use std::borrow::Borrow;

impl<'g, K: 'g + Eq, V: 'g> Table<K, V> {
    pub(crate) fn get<Q: ?Sized + Eq>(
        &self,
        guard: &'g Guard,
        hash: u64,
        key: &Q,
    ) -> BucketResult<'g, K, V, RelocatedError>
    where
        K: Borrow<Q>,
    {
        match self.probe_loop(hash, |_, _, _, _, expected, this_bucket| {
            if expected == 0 {
                return ProbeLoopAction::Return(Ok(Shared::null()));
            }

            let this_bucket_ptr = this_bucket.load_consume(guard);

            match unsafe { Bucket::as_ref(this_bucket_ptr) } {
                BucketRef::Filled(this_key, _) if this_key.borrow() == key => {
                    ProbeLoopAction::Return(Ok(this_bucket_ptr))
                }
                BucketRef::Tombstone(this_key) if this_key.borrow() == key => {
                    ProbeLoopAction::Return(Ok(Shared::null()))
                }
                BucketRef::Filled(_, _) | BucketRef::Tombstone(_) => ProbeLoopAction::Continue,
                BucketRef::Null => ProbeLoopAction::Return(Ok(Shared::null())),
                BucketRef::Sentinel => ProbeLoopAction::Return(Err(RelocatedError)),
            }
        }) {
            ProbeLoopResult::LoopEnded => Ok(Shared::null()),
            ProbeLoopResult::FoundSentinelTag => Err(RelocatedError),
            ProbeLoopResult::Returned(r) => r,
        }
    }
}

pub(crate) struct RelocatedError;
