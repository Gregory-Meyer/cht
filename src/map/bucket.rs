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
    target_feature = "sse2",
    any(target_arch = "x86", target_arch = "x86_64")
))]
#[path = "bucket/arch/x86.rs"]
mod arch;

#[cfg(not(all(
    target_feature = "sse2",
    any(target_arch = "x86", target_arch = "x86_64")
)))]
#[path = "bucket/arch/generic.rs"]
mod arch;

use arch::{ControlBytes, Searcher};

use std::{
    borrow::Borrow,
    hash::{BuildHasher, Hash, Hasher},
    mem::{self, MaybeUninit},
    ptr,
    sync::atomic::{self, Ordering},
    u64, u8,
};

use crossbeam_epoch::{Atomic, CompareAndSetError, Guard, Owned, Shared};

pub(crate) struct BucketPointerGroup<K, V> {
    pub(crate) buckets: [Atomic<Bucket<K, V>>; arch::BUCKETS_PER_GROUP],
}

const SENTINEL_CONTROL_BYTE: u8 = 0b0111_1111;

fn split_hash(hash: u64) -> (u8, usize) {
    (
        (hash & 0b0111_1111) as u8 | 0b1000_0000,
        (hash >> 7) as usize,
    )
}

pub(crate) struct BucketPointerArray<K, V> {
    pub(crate) groups: Box<[BucketPointerGroup<K, V>]>,
    control_bytes: Box<[ControlBytes]>,
    pub(crate) next: Atomic<BucketPointerArray<K, V>>,
    pub(crate) epoch: usize,
    pub(crate) modulo_mask: usize,
}

impl<K, V> BucketPointerArray<K, V> {
    pub(crate) fn with_capacity(capacity: usize) -> Self {
        let num_buckets = capacity * 2;

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

        self.groups.len() * arch::BUCKETS_PER_GROUP / 2
    }
}

unsafe fn boxed_zeroed_slice<T>(length: usize) -> Box<[T]> {
    let mut vec = Vec::with_capacity(length);
    ptr::write_bytes(vec.as_mut_ptr(), 0, length);
    vec.set_len(length);

    vec.into_boxed_slice()
}

impl<'g, K: 'g + Eq, V: 'g> BucketPointerArray<K, V> {
    pub(crate) fn get<Q: ?Sized + Eq>(
        &self,
        guard: &'g Guard,
        hash: u64,
        key: &Q,
    ) -> Result<Shared<'g, Bucket<K, V>>, RelocatedError>
    where
        K: Borrow<Q>,
    {
        let (control, index) = split_hash(hash);
        let offset = index & self.modulo_mask;

        let searcher = Searcher::new(control);

        for i in (0..self.control_bytes.len()).map(|i| i.wrapping_add(offset) & self.modulo_mask) {
            let this_group = &self.groups[i];
            let these_control_bytes = self.control_bytes[i].load();

            let (mut zero_move_mask, mut query_move_mask) =
                if let Some((z, q)) = searcher.search(these_control_bytes) {
                    (z, q)
                } else {
                    return Err(RelocatedError);
                };

            match (zero_move_mask, query_move_mask) {
                (0, 0) => continue,                  // no zeros and no matches; keep probing
                (_, 0) => return Ok(Shared::null()), // zeros, but no matches; key not inserted
                _ => {
                    while query_move_mask != 0 {
                        let query_tz = query_move_mask.trailing_zeros();
                        let zeros_tz = zero_move_mask.trailing_zeros();

                        assert_ne!(zeros_tz, query_tz);

                        let j = if zeros_tz < query_tz {
                            zero_move_mask &= !(1 << zeros_tz);

                            zeros_tz as usize
                        } else {
                            query_move_mask &= !(1 << query_tz);

                            query_tz as usize
                        };

                        let this_bucket_ptr = this_group.buckets[j].load_consume(guard);

                        if this_bucket_ptr.tag() & SENTINEL_TAG != 0 {
                            assert!(this_bucket_ptr.is_null());

                            return Err(RelocatedError);
                        }

                        assert!(!this_bucket_ptr.is_null());
                        let this_bucket_ref = unsafe { this_bucket_ptr.deref() };

                        if this_bucket_ref.key.borrow() != key {
                            continue;
                        }

                        if this_bucket_ptr.tag() & TOMBSTONE_TAG != 0 {
                            return Ok(Shared::null());
                        }

                        return Ok(this_bucket_ptr);
                    }

                    if zero_move_mask != 0 {
                        return Ok(Shared::null());
                    }
                }
            }
        }

        Ok(Shared::null())
    }

    pub(crate) fn insert(
        &self,
        guard: &'g Guard,
        hash: u64,
        mut bucket_ptr: Owned<Bucket<K, V>>,
    ) -> Result<Shared<'g, Bucket<K, V>>, Owned<Bucket<K, V>>> {
        let (control, index) = split_hash(hash);
        let offset = index & self.modulo_mask;

        let searcher = Searcher::new(control);

        for i in (0..self.control_bytes.len()).map(|i| i.wrapping_add(offset) & self.modulo_mask) {
            let this_group = &self.groups[i];
            let these_control_bytes = self.control_bytes[i].load();

            let (mut zero_move_mask, mut query_move_mask) =
                if let Some((z, q)) = searcher.search(these_control_bytes) {
                    (z, q)
                } else {
                    return Err(bucket_ptr);
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

                            (zeros_tz as usize, 0)
                        } else {
                            query_move_mask &= !(1 << query_tz);

                            (query_tz as usize, control)
                        };

                        loop {
                            let this_bucket_ptr = this_group.buckets[j].load_consume(guard);

                            if this_bucket_ptr.tag() & SENTINEL_TAG != 0 {
                                assert!(this_bucket_ptr.is_null());

                                return Err(bucket_ptr);
                            }

                            if let Some(this_bucket_ref) = unsafe { this_bucket_ptr.as_ref() } {
                                if this_bucket_ref.key != bucket_ptr.key {
                                    break;
                                }
                            } else {
                                assert_eq!(this_bucket_ptr.tag() & TOMBSTONE_TAG, 0);
                            }

                            match this_group.buckets[j].compare_and_set_weak(
                                this_bucket_ptr,
                                bucket_ptr,
                                (Ordering::Release, Ordering::Relaxed),
                                guard,
                            ) {
                                Ok(_) => {
                                    self.control_bytes[i].set(expected, j as u32, control);

                                    return Ok(this_bucket_ptr);
                                }
                                Err(CompareAndSetError { new, .. }) => {
                                    bucket_ptr = new;
                                }
                            }
                        }
                    }
                }
            }
        }

        Err(bucket_ptr)
    }

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
        let (control, index) = split_hash(hash);
        let offset = index & self.modulo_mask;

        let searcher = Searcher::new(control);

        for i in (0..self.control_bytes.len()).map(|i| i.wrapping_add(offset) & self.modulo_mask) {
            let this_group = &self.groups[i];
            let these_control_bytes = self.control_bytes[i].load();

            let (mut zero_move_mask, mut query_move_mask) =
                if let Some((z, q)) = searcher.search(these_control_bytes) {
                    (z, q)
                } else {
                    return Err(condition);
                };

            match (zero_move_mask, query_move_mask) {
                (0, 0) => continue,                  // no zeros and no matches; keep probing
                (_, 0) => return Ok(Shared::null()), // zeros, but no matches; key not inserted
                _ => {
                    while query_move_mask != 0 {
                        let query_tz = query_move_mask.trailing_zeros();
                        let zeros_tz = zero_move_mask.trailing_zeros();

                        assert_ne!(zeros_tz, query_tz);

                        let j = if zeros_tz < query_tz {
                            zero_move_mask &= !(1 << zeros_tz);

                            zeros_tz as usize
                        } else {
                            query_move_mask &= !(1 << query_tz);

                            query_tz as usize
                        };

                        loop {
                            let this_bucket_ptr = this_group.buckets[j].load_consume(guard);

                            if this_bucket_ptr.tag() & SENTINEL_TAG != 0 {
                                assert!(this_bucket_ptr.is_null());

                                return Err(condition);
                            }

                            assert!(!this_bucket_ptr.is_null());
                            let this_bucket_ref = unsafe { this_bucket_ptr.deref() };

                            if this_bucket_ref.key.borrow() != key {
                                break;
                            }

                            if this_bucket_ptr.tag() & TOMBSTONE_TAG != 0 {
                                return Ok(Shared::null());
                            }

                            let value = unsafe { &*this_bucket_ref.maybe_value.as_ptr() };

                            if !condition(&this_bucket_ref.key, value) {
                                return Ok(Shared::null());
                            }

                            if this_group.buckets[j]
                                .compare_and_set_weak(
                                    this_bucket_ptr,
                                    this_bucket_ptr.with_tag(TOMBSTONE_TAG),
                                    (Ordering::Release, Ordering::Relaxed),
                                    guard,
                                )
                                .is_ok()
                            {
                                unsafe {
                                    defer_destroy_tombstone(
                                        guard,
                                        this_bucket_ptr.with_tag(TOMBSTONE_TAG),
                                    )
                                };

                                return Ok(this_bucket_ptr.with_tag(TOMBSTONE_TAG));
                            }
                        }
                    }

                    if zero_move_mask != 0 {
                        return Ok(Shared::null());
                    }
                }
            }
        }

        Ok(Shared::null())
    }

    pub(crate) fn modify<F: FnMut(&K, &V) -> V>(
        &self,
        guard: &'g Guard,
        hash: u64,
        key_or_owned_bucket: KeyOrOwnedBucket<K, V>,
        mut modifier: F,
    ) -> Result<Shared<'g, Bucket<K, V>>, (KeyOrOwnedBucket<K, V>, F)> {
        unimplemented!()
    }

    pub(crate) fn insert_or_modify<F: FnOnce() -> V, G: FnMut(&K, &V) -> V>(
        &self,
        guard: &'g Guard,
        hash: u64,
        state: InsertOrModifyState<K, V, F>,
        mut modifier: G,
    ) -> Result<Shared<'g, Bucket<K, V>>, (InsertOrModifyState<K, V, F>, G)> {
        unimplemented!()
    }

    fn insert_for_grow(
        &self,
        guard: &'g Guard,
        hash: u64,
        bucket_ptr: Shared<'g, Bucket<K, V>>,
    ) -> Option<usize> {
        unimplemented!()
    }
}

impl<'g, K: 'g, V: 'g> BucketPointerArray<K, V> {
    pub(crate) fn rehash<H: BuildHasher>(
        &self,
        guard: &'g Guard,
        build_hasher: &H,
    ) -> &'g BucketPointerArray<K, V>
    where
        K: Hash + Eq,
    {
        unimplemented!()
    }

    fn next_array(&self, guard: &'g Guard) -> &'g BucketPointerArray<K, V> {
        let mut maybe_new_next = None;

        loop {
            let next_ptr = self.next.load_consume(guard);

            if let Some(next_ref) = unsafe { next_ptr.as_ref() } {
                return next_ref;
            }

            let new_next = maybe_new_next.unwrap_or_else(|| {
                Owned::new(BucketPointerArray::with_length(
                    self.epoch + 1,
                    self.groups.len() * 2,
                ))
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

#[repr(align(8))]
#[derive(Debug)]
pub(crate) struct Bucket<K, V> {
    pub(crate) key: K,
    pub(crate) maybe_value: MaybeUninit<V>,
}

impl<K, V> Bucket<K, V> {
    pub(crate) fn new(key: K, value: V) -> Bucket<K, V> {
        Bucket {
            key,
            maybe_value: MaybeUninit::new(value),
        }
    }
}

#[derive(Debug, Eq, PartialEq)]
pub(crate) struct RelocatedError;

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
            Self::Key(k) => Owned::new(Bucket::new(k, value)),
            Self::OwnedBucket(mut b) => {
                unsafe {
                    mem::drop(
                        mem::replace(&mut b.maybe_value, MaybeUninit::new(value)).assume_init(),
                    )
                };

                b
            }
        }
    }
}

pub(crate) enum InsertOrModifyState<K, V, F: FnOnce() -> V> {
    New(K, F),
    AttemptedInsertion(Owned<Bucket<K, V>>),
    AttemptedModification(Owned<Bucket<K, V>>, ValueOrFunction<V, F>),
}

impl<K, V, F: FnOnce() -> V> InsertOrModifyState<K, V, F> {
    fn from_bucket_value(
        bucket: Owned<Bucket<K, V>>,
        value_or_function: Option<ValueOrFunction<V, F>>,
    ) -> Self {
        if let Some(value_or_function) = value_or_function {
            Self::AttemptedModification(bucket, value_or_function)
        } else {
            Self::AttemptedInsertion(bucket)
        }
    }

    fn key(&self) -> &K {
        match self {
            InsertOrModifyState::New(k, _) => &k,
            InsertOrModifyState::AttemptedInsertion(b)
            | InsertOrModifyState::AttemptedModification(b, _) => &b.key,
        }
    }

    fn into_insert_bucket(self) -> Owned<Bucket<K, V>> {
        match self {
            InsertOrModifyState::New(k, f) => Owned::new(Bucket::new(k, f())),
            InsertOrModifyState::AttemptedInsertion(b) => b,
            InsertOrModifyState::AttemptedModification(mut b, v_or_f) => {
                unsafe {
                    mem::drop(
                        mem::replace(&mut b.maybe_value, MaybeUninit::new(v_or_f.into_value()))
                            .assume_init(),
                    )
                };

                b
            }
        }
    }

    fn into_modify_bucket(self, value: V) -> (Owned<Bucket<K, V>>, ValueOrFunction<V, F>) {
        match self {
            InsertOrModifyState::New(k, f) => (
                Owned::new(Bucket::new(k, value)),
                ValueOrFunction::Function(f),
            ),
            InsertOrModifyState::AttemptedInsertion(mut b) => {
                let insert_value = unsafe {
                    mem::replace(&mut b.maybe_value, MaybeUninit::new(value)).assume_init()
                };

                (b, ValueOrFunction::Value(insert_value))
            }
            InsertOrModifyState::AttemptedModification(mut b, v_or_f) => {
                unsafe {
                    mem::drop(
                        mem::replace(&mut b.maybe_value, MaybeUninit::new(value)).assume_init(),
                    )
                };

                (b, v_or_f)
            }
        }
    }
}

pub(crate) enum ValueOrFunction<V, F: FnOnce() -> V> {
    Value(V),
    Function(F),
}

impl<V, F: FnOnce() -> V> ValueOrFunction<V, F> {
    fn into_value(self) -> V {
        match self {
            ValueOrFunction::Value(v) => v,
            ValueOrFunction::Function(f) => f(),
        }
    }
}

pub(crate) fn hash<K: ?Sized + Hash, H: BuildHasher>(build_hasher: &H, key: &K) -> u64 {
    let mut hasher = build_hasher.build_hasher();
    key.hash(&mut hasher);

    hasher.finish()
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

pub(crate) unsafe fn defer_destroy_bucket<'g, K, V>(
    guard: &'g Guard,
    mut ptr: Shared<'g, Bucket<K, V>>,
) {
    assert!(!ptr.is_null());

    guard.defer_unchecked(move || {
        atomic::fence(Ordering::Acquire);

        if ptr.tag() & TOMBSTONE_TAG == 0 {
            ptr::drop_in_place(ptr.deref_mut().maybe_value.as_mut_ptr());
        }

        mem::drop(ptr.into_owned());
    });
}

pub(crate) unsafe fn defer_destroy_tombstone<'g, K, V>(
    guard: &'g Guard,
    mut ptr: Shared<'g, Bucket<K, V>>,
) {
    assert!(!ptr.is_null());
    assert_ne!(ptr.tag() & TOMBSTONE_TAG, 0);

    atomic::fence(Ordering::Acquire);
    // read the value now, but defer its destruction for later
    let value = ptr::read(ptr.deref_mut().maybe_value.as_ptr());

    // to be entirely honest, i don't know what order deferred functions are
    // called in crossbeam-epoch. in the case that the deferred functions are
    // called out of order, this prevents that from being an issue.
    guard.defer_unchecked(move || mem::drop(value));
}

pub(crate) unsafe fn defer_acquire_destroy<'g, T>(guard: &'g Guard, ptr: Shared<'g, T>) {
    assert!(!ptr.is_null());

    guard.defer_unchecked(move || {
        atomic::fence(Ordering::Acquire);
        mem::drop(ptr.into_owned());
    });
}

pub(crate) const SENTINEL_TAG: usize = 0b001; // set on old table buckets when copied into a new table
pub(crate) const TOMBSTONE_TAG: usize = 0b010; // set when the value has been destroyed
pub(crate) const BORROWED_TAG: usize = 0b100; // set on new table buckets when copied from an old table

#[cfg(test)]
mod tests {
    use super::*;

    use ahash::RandomState;

    #[test]
    fn get_insert_remove() {
        let build_hasher = RandomState::new();
        let buckets = BucketPointerArray::with_length(0, 16);
        let guard = unsafe { &crossbeam_epoch::unprotected() };

        let k1 = "foo";
        let h1 = hash(&build_hasher, k1);
        let v1 = 5;

        let k2 = "bar";
        let h2 = hash(&build_hasher, k2);
        let v2 = 10;

        let k3 = "baz";
        let h3 = hash(&build_hasher, k3);
        let v3 = 15;

        assert_eq!(buckets.get(guard, h1, k1), Ok(Shared::null()));
        assert_eq!(buckets.get(guard, h2, k2), Ok(Shared::null()));
        assert_eq!(buckets.get(guard, h3, k3), Ok(Shared::null()));

        let b1 = Owned::new(Bucket::new(k1, v1)).into_shared(guard);
        assert!(is_ok_null(
            buckets.insert(guard, h1, unsafe { b1.into_owned() })
        ));

        assert_eq!(buckets.get(guard, h1, k1), Ok(b1));
        assert_eq!(buckets.get(guard, h2, k2), Ok(Shared::null()));
        assert_eq!(buckets.get(guard, h3, k3), Ok(Shared::null()));

        let b2 = Owned::new(Bucket::new(k2, v2)).into_shared(guard);
        assert!(is_ok_null(
            buckets.insert(guard, h2, unsafe { b2.into_owned() })
        ));

        assert_eq!(buckets.get(guard, h1, k1), Ok(b1));
        assert_eq!(buckets.get(guard, h2, k2), Ok(b2));
        assert_eq!(buckets.get(guard, h3, k3), Ok(Shared::null()));

        let b3 = Owned::new(Bucket::new(k3, v3)).into_shared(guard);
        assert!(is_ok_null(
            buckets.insert(guard, h3, unsafe { b3.into_owned() })
        ));

        assert_eq!(buckets.get(guard, h1, k1), Ok(b1));
        assert_eq!(buckets.get(guard, h2, k2), Ok(b2));
        assert_eq!(buckets.get(guard, h3, k3), Ok(b3));

        assert_eq!(
            buckets.remove_if(guard, h1, k1, |_, _| true).ok().unwrap(),
            b1.with_tag(TOMBSTONE_TAG)
        );
        unsafe { defer_destroy_tombstone(guard, b1.with_tag(TOMBSTONE_TAG)) };
        assert_eq!(
            buckets.remove_if(guard, h2, k2, |_, _| true).ok().unwrap(),
            b2.with_tag(TOMBSTONE_TAG)
        );
        unsafe { defer_destroy_tombstone(guard, b2.with_tag(TOMBSTONE_TAG)) };
        assert_eq!(
            buckets.remove_if(guard, h3, k3, |_, _| true).ok().unwrap(),
            b3.with_tag(TOMBSTONE_TAG)
        );
        unsafe { defer_destroy_tombstone(guard, b3.with_tag(TOMBSTONE_TAG)) };

        assert_eq!(buckets.get(guard, h1, k1), Ok(Shared::null()));
        assert_eq!(buckets.get(guard, h2, k2), Ok(Shared::null()));
        assert_eq!(buckets.get(guard, h3, k3), Ok(Shared::null()));

        for this_bucket in buckets.groups.iter().map(|g| g.buckets.iter()).flatten() {
            let this_bucket_ptr = this_bucket.swap(Shared::null(), Ordering::Relaxed, guard);

            if this_bucket_ptr.is_null() {
                continue;
            }

            unsafe {
                defer_destroy_bucket(guard, this_bucket_ptr);
            }
        }
    }

    fn is_ok_null<'g, K, V, E>(maybe_bucket_ptr: Result<Shared<'g, Bucket<K, V>>, E>) -> bool {
        if let Ok(bucket_ptr) = maybe_bucket_ptr {
            bucket_ptr.is_null()
        } else {
            false
        }
    }
}
