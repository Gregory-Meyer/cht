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

pub(crate) mod get;
pub(crate) mod insert;
pub(crate) mod insert_or_modify;
pub(crate) mod modify;
pub(crate) mod remove_if;

#[cfg(all(
    target_feature = "avx2",
    any(target_arch = "x86", target_arch = "x86_64")
))]
#[path = "table/arch/avx2.rs"]
mod arch;

#[cfg(all(
    all(target_feature = "sse2", not(target_feature = "avx2")),
    any(target_arch = "x86", target_arch = "x86_64")
))]
#[path = "table/arch/sse2.rs"]
mod arch;

#[cfg(not(all(
    any(target_feature = "sse2", target_feature = "avx2"),
    any(target_arch = "x86", target_arch = "x86_64")
)))]
#[path = "table/arch/generic.rs"]
mod arch;

mod facade;

pub(crate) use facade::Facade;
pub(crate) use insert_or_modify::InsertOrModifyState;
pub(crate) use modify::KeyOrOwnedBucket;

use std::hash::BuildHasher;
use std::hash::Hash;

use arch::{ControlByteGroup, Searcher};

use super::{Bucket, BucketRef};

use std::{
    env, ptr,
    sync::atomic::{AtomicU64, Ordering},
};

use crossbeam_epoch::{Atomic, CompareAndSetError, Guard, Owned, Shared};

pub(crate) struct Table<K, V> {
    groups: Box<[BucketPointerGroup<K, V>]>,
    control_bytes: Box<[ControlByteGroup]>,
    next: Atomic<Table<K, V>>,
    epoch: usize,
    modulo_mask: usize,
}

pub(crate) type BucketResult<'g, K, V, E> = Result<Shared<'g, Bucket<K, V>>, E>;

pub(crate) struct BucketPointerGroup<K, V> {
    buckets: [Atomic<Bucket<K, V>>; arch::BUCKETS_PER_GROUP],
}

const SENTINEL_CONTROL_BYTE: u8 = 0b0111_1111;

impl<K, V> Table<K, V> {
    pub(crate) fn with_capacity(capacity: usize) -> Self {
        let num_buckets = (capacity as f64 / max_load_factor()).ceil() as usize;

        let length = if num_buckets % arch::BUCKETS_PER_GROUP != 0 {
            num_buckets / arch::BUCKETS_PER_GROUP + 1
        } else {
            num_buckets / arch::BUCKETS_PER_GROUP
        }
        .next_power_of_two();

        Self::with_length(0, length)
    }

    fn with_length(epoch: usize, length: usize) -> Self {
        assert!(length.is_power_of_two());

        let groups = unsafe { boxed_zeroed_slice(length) };
        let control_bytes = unsafe { boxed_zeroed_slice(length) };
        let next = Atomic::null();
        let modulo_mask = length - 1;

        Self {
            groups,
            control_bytes,
            next,
            epoch,
            modulo_mask,
        }
    }

    pub(crate) fn capacity(&self) -> usize {
        assert_eq!(self.groups.len(), self.control_bytes.len());
        assert!(self.groups.len().is_power_of_two());

        ((self.groups.len() * arch::BUCKETS_PER_GROUP) as f64 * max_load_factor()).floor() as usize
    }
}

impl<'g, K: 'g + Eq, V: 'g> Table<K, V> {
    fn insert_for_grow(
        &self,
        guard: &'g Guard,
        hash: u64,
        bucket_ptr: Shared<'g, Bucket<K, V>>,
    ) -> Option<(usize, u32)> {
        assert!(!bucket_ptr.is_null());
        assert!(!Bucket::is_sentinel(bucket_ptr));
        assert!(!Bucket::is_tombstone(bucket_ptr));
        assert!(Bucket::is_borrowed(bucket_ptr));

        let key = &unsafe { bucket_ptr.deref() }.key;

        let loop_result = self.probe_loop(
            hash,
            |i, j, these_control_bytes, control, expected, this_bucket| {
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
                    these_control_bytes.set(expected, j, control);

                    ProbeLoopAction::Return(Some((i, j)))
                } else {
                    ProbeLoopAction::Reload
                }
            },
        );

        loop_result.returned().flatten()
    }
}

impl<'g, K: 'g, V: 'g> Table<K, V> {
    fn probe_loop<
        F: FnMut(usize, u32, &ControlByteGroup, u8, u8, &Atomic<Bucket<K, V>>) -> ProbeLoopAction<T>,
        T,
    >(
        &self,
        hash: u64,
        mut f: F,
    ) -> ProbeLoopResult<T> {
        let (control, index) = split_hash(hash);
        let offset = index & self.modulo_mask;

        let searcher = Searcher::new(control);

        for i in (0..self.control_bytes.len()).map(|i| i.wrapping_add(offset) & self.modulo_mask) {
            let this_group = &self.groups[i];
            let these_control_bytes = &self.control_bytes[i];

            let (mut zero_move_mask, mut query_move_mask) =
                if let Some((z, q)) = searcher.search(these_control_bytes.load()) {
                    (z, q)
                } else {
                    return ProbeLoopResult::FoundSentinelTag;
                };

            match (zero_move_mask, query_move_mask) {
                (0, 0) => continue, // no zeros and no matches; keep probing
                _ => {
                    while query_move_mask != 0 || zero_move_mask != 0 {
                        let query_tz = query_move_mask.trailing_zeros();
                        let zeros_tz = zero_move_mask.trailing_zeros();

                        assert_ne!(zeros_tz, query_tz);

                        let (j, expected) = if zeros_tz < query_tz {
                            zero_move_mask &= !(1 << zeros_tz);

                            (zeros_tz, 0)
                        } else {
                            query_move_mask &= !(1 << query_tz);

                            (query_tz, control)
                        };

                        loop {
                            match f(
                                i,
                                j,
                                these_control_bytes,
                                control,
                                expected,
                                &this_group.buckets[j as usize],
                            ) {
                                ProbeLoopAction::Continue => break,
                                ProbeLoopAction::Reload => (),
                                ProbeLoopAction::Return(t) => return ProbeLoopResult::Returned(t),
                            }
                        }
                    }
                }
            }
        }

        ProbeLoopResult::LoopEnded
    }

    pub(crate) fn rehash<H: BuildHasher>(
        &self,
        guard: &'g Guard,
        build_hasher: &H,
    ) -> &'g Table<K, V>
    where
        K: Hash + Eq,
    {
        let next_array = self.next_array(guard);
        assert!(self.groups.len() <= next_array.groups.len());

        for (these_control_bytes, this_group) in self.control_bytes.iter().zip(self.groups.iter()) {
            for (j, this_bucket) in this_group.buckets.iter().enumerate() {
                let mut maybe_state: Option<(usize, u32, Shared<'g, Bucket<K, V>>)> = None;

                loop {
                    let this_bucket_ptr = this_bucket.load_consume(guard);

                    if Bucket::is_sentinel(this_bucket_ptr) {
                        these_control_bytes.set_sentinel(j);

                        break;
                    }

                    if let Some((group_index, group_offset, mut next_bucket_ptr)) = maybe_state {
                        assert!(!this_bucket_ptr.is_null());
                        let to_put_ptr = Bucket::to_borrowed(this_bucket_ptr);

                        let next_bucket =
                            &next_array.groups[group_index].buckets[group_offset as usize];

                        while Bucket::is_borrowed(next_bucket_ptr)
                            && next_bucket
                                .compare_and_set_weak(
                                    next_bucket_ptr,
                                    to_put_ptr,
                                    (Ordering::Release, Ordering::Relaxed),
                                    guard,
                                )
                                .is_err()
                        {
                            next_bucket_ptr = next_bucket.load_consume(guard);
                        }
                    } else {
                        match unsafe { Bucket::as_ref(this_bucket_ptr) } {
                            BucketRef::Filled(this_key, _) => {
                                let hash = super::hash(build_hasher, this_key);
                                let to_put_ptr = Bucket::to_borrowed(this_bucket_ptr);

                                if let Some((group_index, group_offset)) =
                                    next_array.insert_for_grow(guard, hash, to_put_ptr)
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

    fn next_array(&self, guard: &'g Guard) -> &'g Table<K, V> {
        let mut maybe_new_next = None;

        loop {
            let next_ptr = self.next.load_consume(guard);

            if let Some(next_ref) = unsafe { next_ptr.as_ref() } {
                return next_ref;
            }

            let new_next = maybe_new_next.unwrap_or_else(|| {
                Owned::new(Table::with_length(self.epoch + 1, self.groups.len() * 2))
            });

            match self.next.compare_and_set_weak(
                Shared::null(),
                new_next,
                (Ordering::Release, Ordering::Relaxed),
                guard,
            ) {
                Ok(p) => return unsafe { p.deref() },
                Err(CompareAndSetError { new, .. }) => {
                    maybe_new_next = Some(new);
                }
            }
        }
    }
}

enum ProbeLoopAction<T> {
    Continue,
    Reload,
    Return(T),
}

enum ProbeLoopResult<T> {
    LoopEnded,
    FoundSentinelTag,
    Returned(T),
}

impl<T> ProbeLoopResult<T> {
    fn returned(self) -> Option<T> {
        match self {
            Self::Returned(t) => Some(t),
            Self::LoopEnded | Self::FoundSentinelTag => None,
        }
    }
}

fn split_hash(hash: u64) -> (u8, usize) {
    (
        (hash & 0b0111_1111) as u8 | 0b1000_0000,
        (hash >> 7) as usize,
    )
}

fn max_load_factor() -> f64 {
    const DEFAULT_MAX_LOAD_FACTOR: f64 = 0.9375;
    static STORAGE: AtomicU64 = AtomicU64::new(u64::MAX);

    let mut storage = STORAGE.load(Ordering::Relaxed);

    if storage == u64::MAX {
        storage = env::var("MAX_LOAD_FACTOR")
            .ok()
            .as_deref()
            .and_then(|s| s.parse().ok())
            .unwrap_or(DEFAULT_MAX_LOAD_FACTOR)
            .to_bits();

        STORAGE
            .compare_exchange_weak(u64::MAX, storage, Ordering::Relaxed, Ordering::Relaxed)
            .ok();
    }

    f64::from_bits(storage)
}

unsafe fn boxed_zeroed_slice<T>(length: usize) -> Box<[T]> {
    let mut vec = Vec::with_capacity(length);
    ptr::write_bytes(vec.as_mut_ptr(), 0, length);
    vec.set_len(length);

    vec.into_boxed_slice()
}
