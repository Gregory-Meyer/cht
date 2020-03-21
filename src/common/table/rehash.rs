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

use crate::common::{self, Bucket, BucketRef};

use std::{
    hash::{BuildHasher, Hash},
    sync::atomic::Ordering,
};

use crossbeam_epoch::{CompareAndSetError, Guard, Shared};

impl<'g, K: 'g + Hash + Eq, V: 'g> Table<K, V> {
    pub(crate) fn rehash<H: BuildHasher>(
        &self,
        guard: &'g Guard,
        build_hasher: &H,
    ) -> &'g Table<K, V> {
        let next_array = self.next_array(guard);
        assert!(self.groups.len() <= next_array.groups.len());

        for (these_control_bytes, this_group) in self.control_bytes.iter().zip(self.groups.iter()) {
            for (j, this_bucket) in this_group.buckets.iter().enumerate() {
                let mut maybe_state: Option<(usize, usize, Shared<'g, Bucket<K, V>>)> = None;
                let mut printed = false;

                loop {
                    let this_bucket_ptr = this_bucket.load_consume(guard);

                    if Bucket::is_sentinel(this_bucket_ptr) {
                        these_control_bytes.set_sentinel(j);

                        break;
                    }

                    if let Some((group_index, group_offset, mut next_bucket_ptr)) = maybe_state {
                        assert!(!this_bucket_ptr.is_null());
                        assert!(Bucket::is_borrowed(next_bucket_ptr));
                        let to_put_ptr = Bucket::to_borrowed(this_bucket_ptr);

                        let next_bucket =
                            &next_array.groups[group_index].buckets[group_offset as usize];

                        while Bucket::is_borrowed(next_bucket_ptr) {
                            if !printed {
                                println!("{:p}: CASing [{}, {}]", self, group_index, group_offset);
                                printed = true;
                            }

                            if let Err(CompareAndSetError { current, .. }) = next_bucket
                                .compare_and_set_weak(
                                    next_bucket_ptr,
                                    to_put_ptr,
                                    (Ordering::Release, Ordering::Relaxed),
                                    guard,
                                )
                            {
                                // *next_bucket_ptr is never inspected; relaxed load is fine
                                if current == to_put_ptr {
                                    break;
                                }

                                next_bucket_ptr = current;
                            } else {
                                break;
                            }
                        }
                    } else {
                        match unsafe { Bucket::as_ref(this_bucket_ptr) } {
                            BucketRef::Filled(this_key, _) => {
                                let hash = common::hash(build_hasher, this_key);
                                let to_put_ptr = Bucket::to_borrowed(this_bucket_ptr);

                                if let Some((group_index, group_offset)) =
                                    next_array.rehash_insert(guard, hash, to_put_ptr)
                                {
                                    maybe_state = Some((group_index, group_offset, to_put_ptr));
                                }
                            }
                            BucketRef::Tombstone(_) => (),
                            BucketRef::Null => (),
                            BucketRef::Sentinel => unreachable!(),
                        }
                    }

                    if this_bucket
                        .compare_and_set_weak(
                            this_bucket_ptr,
                            Bucket::sentinel(),
                            (Ordering::Release, Ordering::Relaxed),
                            guard,
                        )
                        .is_ok()
                    {
                        if !this_bucket_ptr.is_null()
                            && Bucket::is_tombstone(this_bucket_ptr)
                            && maybe_state.is_none()
                        {
                            unsafe { guard.defer_destroy(this_bucket_ptr) };
                        }

                        these_control_bytes.set_sentinel(j);

                        break;
                    }
                }
            }
        }

        next_array
    }
}

impl<'g, K: 'g + Eq, V: 'g> Table<K, V> {
    fn rehash_insert(
        &self,
        guard: &'g Guard,
        hash: u64,
        bucket_ptr: Shared<'g, Bucket<K, V>>,
    ) -> Option<(usize, usize)> {
        assert!(!bucket_ptr.is_null());
        assert!(!Bucket::is_sentinel(bucket_ptr));
        assert!(!Bucket::is_tombstone(bucket_ptr));
        assert!(Bucket::is_borrowed(bucket_ptr));

        let key = &unsafe { bucket_ptr.deref() }.key;

        let loop_result = self.probe_loop(hash, |loop_state| {
            let ProbeLoopState {
                group_index,
                group_offset,
                this_bucket,
                ..
            } = loop_state;

            let this_bucket_ptr = this_bucket.load_consume(guard);

            if !this_bucket_ptr.is_null() && this_bucket_ptr == bucket_ptr {
                return ProbeLoopAction::Return(None);
            }

            match unsafe { Bucket::as_ref(this_bucket_ptr) } {
                BucketRef::Filled(this_key, _) | BucketRef::Tombstone(this_key)
                    if this_key != key =>
                {
                    return ProbeLoopAction::Continue;
                }
                BucketRef::Filled(_, _) | BucketRef::Tombstone(_)
                    if !Bucket::is_borrowed(this_bucket_ptr) =>
                {
                    return ProbeLoopAction::Return(None);
                }
                _ => (),
            }

            if this_bucket
                .compare_and_set_weak(
                    this_bucket_ptr,
                    bucket_ptr,
                    (Ordering::Release, Ordering::Relaxed),
                    guard,
                )
                .is_ok()
            {
                loop_state.set_control_byte();

                if this_bucket_ptr.is_null() {
                    self.num_non_null_buckets.fetch_add(1, Ordering::Relaxed);
                }

                ProbeLoopAction::Return(Some((group_index, group_offset)))
            } else {
                ProbeLoopAction::Reload
            }
        });

        if let ProbeLoopResult::Returned(t) = loop_result {
            t
        } else {
            None
        }
    }
}
