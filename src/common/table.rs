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
mod get;
mod insert;
mod insert_or_modify;
mod modify;
mod mutate_bucket;
mod probe_loop;
mod rehash;
mod remove_if;

pub(crate) use facade::Facade;
pub(crate) use insert_or_modify::InsertOrModifyState;
pub(crate) use modify::KeyOrOwnedBucket;

use arch::{ControlByteGroup, Searcher};

use probe_loop::{Action as ProbeLoopAction, Result as ProbeLoopResult, State as ProbeLoopState};

use mutate_bucket::{BucketLike, Result as MutateBucketResult};

use super::Bucket;

use std::{
    env, ptr,
    sync::atomic::{AtomicU64, AtomicUsize, Ordering},
    u64,
};

use crossbeam_epoch::{Atomic, CompareAndSetError, Guard, Owned, Shared};

pub(crate) struct Table<K, V> {
    groups: Box<[BucketPointerGroup<K, V>]>,
    control_bytes: Box<[ControlByteGroup]>,
    next: Atomic<Table<K, V>>,
    epoch: usize,
    modulo_mask: usize,
    num_nonnull_buckets: AtomicUsize,
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
        let num_nonnull_buckets = AtomicUsize::new(0);

        Self {
            groups,
            control_bytes,
            next,
            epoch,
            modulo_mask,
            num_nonnull_buckets,
        }
    }

    pub(crate) fn capacity(&self) -> usize {
        assert_eq!(self.groups.len(), self.control_bytes.len());
        assert!(self.groups.len().is_power_of_two());

        ((self.groups.len() * arch::BUCKETS_PER_GROUP) as f64 * max_load_factor()).floor() as usize
    }
}

impl<'g, K: 'g, V: 'g> Table<K, V> {
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
