// MIT License
//
// Copyright (c) 2019 Gregory Meyer
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

use std::{
    borrow::Borrow,
    hash::{BuildHasher, Hash, Hasher},
    mem,
    sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    },
};

use crossbeam_epoch::{self, Atomic, Guard, Owned, Shared};
use fxhash::FxBuildHasher;

#[derive(Default)]
pub struct HashMap<K: Hash + Eq, V, S: BuildHasher> {
    buckets: Atomic<BucketArray<K, V, S>>,
    len: AtomicUsize,
    hash_builder: Arc<S>,
}

impl<K: Hash + Eq, V> HashMap<K, V, FxBuildHasher> {
    pub fn new() -> HashMap<K, V, FxBuildHasher> {
        HashMap::with_capacity_and_hasher(0, FxBuildHasher::default())
    }

    pub fn with_capacity(capacity: usize) -> HashMap<K, V, FxBuildHasher> {
        HashMap::with_capacity_and_hasher(capacity, FxBuildHasher::default())
    }
}

impl<K: Hash + Eq, V, S: BuildHasher> HashMap<K, V, S> {
    pub fn with_hasher(hash_builder: S) -> HashMap<K, V, S> {
        HashMap::with_capacity_and_hasher(0, hash_builder)
    }

    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> HashMap<K, V, S> {
        let hash_builder = Arc::new(hash_builder);

        if capacity == 0 {
            HashMap {
                buckets: Atomic::null(),
                hash_builder,
                len: AtomicUsize::new(0),
            }
        } else {
            HashMap {
                buckets: Atomic::new(BucketArray::with_capacity_and_hasher(
                    capacity,
                    hash_builder.clone(),
                )),
                hash_builder,
                len: AtomicUsize::new(0),
            }
        }
    }

    pub fn len(&self) -> usize {
        self.len.load(Ordering::SeqCst)
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn capacity(&self) -> usize {
        let guard = &crossbeam_epoch::pin();
        let buckets_ptr = self.buckets.load(Ordering::SeqCst, guard);

        if buckets_ptr.is_null() {
            return 0;
        }

        let buckets_ref = unsafe { buckets_ptr.deref() };

        buckets_ref.buckets.len() / 2
    }

    pub fn get<Q: ?Sized + Hash + Eq>(&self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        V: Clone,
    {
        let guard = &crossbeam_epoch::pin();

        self.get_bucket(key, guard)
            .and_then(|b| match &b.maybe_value {
                Some(v) => Some(v.clone()),
                None => None,
            })
    }

    pub fn get_key_value<Q: ?Sized + Hash + Eq>(&self, key: &Q) -> Option<(K, V)>
    where
        K: Borrow<Q> + Clone,
        V: Clone,
    {
        let guard = &crossbeam_epoch::pin();

        self.get_bucket(key, guard)
            .and_then(|b| match &b.maybe_value {
                Some(v) => Some((b.key.clone(), v.clone())),
                None => None,
            })
    }

    pub fn get_and<Q: ?Sized + Hash + Eq, F: FnOnce(&V) -> T, T>(
        &self,
        key: &Q,
        func: F,
    ) -> Option<T>
    where
        K: Borrow<Q>,
    {
        let guard = &crossbeam_epoch::pin();

        self.get_bucket(key, guard)
            .and_then(move |b| match &b.maybe_value {
                Some(v) => Some(func(v)),
                None => None,
            })
    }

    pub fn get_key_value_and<Q: ?Sized + Hash + Eq, F: FnOnce(&K, &V) -> T, T>(
        &self,
        key: &Q,
        func: F,
    ) -> Option<T>
    where
        K: Borrow<Q>,
    {
        let guard = &crossbeam_epoch::pin();

        self.get_bucket(key, guard)
            .and_then(move |b| match &b.maybe_value {
                Some(v) => Some(func(&b.key, v)),
                None => None,
            })
    }

    pub fn insert(&self, k: K, v: V) -> Option<V>
    where
        V: Clone,
    {
        let guard = &crossbeam_epoch::pin();

        self.do_insert(k, v, guard)
            .and_then(|bucket| bucket.maybe_value.as_ref().cloned())
    }

    pub fn insert_entry(&self, k: K, v: V) -> Option<(K, V)>
    where
        K: Clone,
        V: Clone,
    {
        let guard = &crossbeam_epoch::pin();

        self.do_insert(k, v, guard).and_then(|bucket| {
            bucket
                .maybe_value
                .as_ref()
                .map(|v| (bucket.key.clone(), v.clone()))
        })
    }

    pub fn insert_and<F: FnOnce(&V) -> T, T>(&self, k: K, v: V, func: F) -> Option<T> {
        let guard = &crossbeam_epoch::pin();

        self.do_insert(k, v, guard)
            .and_then(|bucket| bucket.maybe_value.as_ref().map(func))
    }

    pub fn insert_entry_and<F: FnOnce(&K, &V) -> T, T>(&self, k: K, v: V, func: F) -> Option<T> {
        let guard = &crossbeam_epoch::pin();

        self.do_insert(k, v, guard)
            .and_then(|bucket| bucket.maybe_value.as_ref().map(|v| func(&bucket.key, v)))
    }
}

impl<K: Hash + Eq + Clone, V, S: BuildHasher> HashMap<K, V, S> {
    pub fn remove<Q: Hash + Eq + ?Sized>(&self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        V: Clone,
    {
        let guard = &crossbeam_epoch::pin();

        self.do_remove(key, guard)
            .and_then(|bucket| bucket.maybe_value.as_ref().cloned())
    }

    pub fn remove_entry<Q: Hash + Eq + ?Sized>(&self, key: &Q) -> Option<(K, V)>
    where
        K: Borrow<Q>,
        V: Clone,
    {
        let guard = &crossbeam_epoch::pin();

        self.do_remove(key, guard).and_then(|bucket| {
            bucket
                .maybe_value
                .as_ref()
                .map(|v| (bucket.key.clone(), v.clone()))
        })
    }

    pub fn remove_and<Q: Hash + Eq + ?Sized, F: FnOnce(&V) -> T, T>(
        &self,
        key: &Q,
        func: F,
    ) -> Option<T>
    where
        K: Borrow<Q>,
    {
        let guard = &crossbeam_epoch::pin();

        self.do_remove(key, guard)
            .and_then(|bucket| bucket.maybe_value.as_ref().map(func))
    }

    pub fn remove_entry_and<Q: Hash + Eq + ?Sized, F: FnOnce(&K, &V) -> T, T>(
        &self,
        key: &Q,
        func: F,
    ) -> Option<T>
    where
        K: Borrow<Q>,
    {
        let guard = &crossbeam_epoch::pin();

        self.do_remove(key, guard)
            .and_then(|bucket| bucket.maybe_value.as_ref().map(|v| func(&bucket.key, v)))
    }
}

impl<'g, K: Hash + Eq, V, S: 'g + BuildHasher> HashMap<K, V, S> {
    fn get_bucket<Q: ?Sized + Hash + Eq>(
        &self,
        key: &Q,
        guard: &'g Guard,
    ) -> Option<&'g Bucket<K, V>>
    where
        K: Borrow<Q>,
    {
        let hash = self.get_hash(&key);

        let buckets_ptr = self.buckets.load(Ordering::SeqCst, guard);

        if buckets_ptr.is_null() {
            return None;
        }

        let buckets = unsafe { buckets_ptr.deref() };
        let BucketAndParentPtr {
            bucket_ptr: found_bucket_ptr,
            parent_ptr: new_buckets_ptr,
        } = buckets.get(key, hash, guard);

        if !new_buckets_ptr.is_null() {
            self.buckets
                .compare_and_set(buckets_ptr, new_buckets_ptr, Ordering::SeqCst, guard)
                .ok();
        }

        unsafe { found_bucket_ptr.as_ref() }
    }

    fn do_insert(&self, key: K, value: V, guard: &'g Guard) -> Option<&'g Bucket<K, V>> {
        let hash = self.get_hash(&key);

        let buckets_ptr = self.get_or_create_buckets(guard);
        assert!(!buckets_ptr.is_null());
        let buckets = unsafe { buckets_ptr.deref() };

        let new_bucket = Owned::new(Bucket {
            key,
            maybe_value: Some(value),
        })
        .into_shared(guard);

        let BucketAndParentPtr {
            bucket_ptr: previous_bucket_ptr,
            parent_ptr: new_buckets_ptr,
        } = buckets.insert(new_bucket, hash, guard);

        if let Some(previous_bucket) = unsafe { previous_bucket_ptr.as_ref() } {
            if previous_bucket.maybe_value.is_none() {
                self.len.fetch_add(1, Ordering::SeqCst);
            }
        } else {
            self.len.fetch_add(1, Ordering::SeqCst);
        }

        if !new_buckets_ptr.is_null() {
            self.buckets
                .compare_and_set(buckets_ptr, new_buckets_ptr, Ordering::SeqCst, guard)
                .ok();
        }

        unsafe { previous_bucket_ptr.as_ref() }
    }

    fn do_remove<Q: Hash + Eq + ?Sized>(
        &self,
        key: &Q,
        guard: &'g Guard,
    ) -> Option<&'g Bucket<K, V>>
    where
        K: Borrow<Q> + Clone,
    {
        let buckets_ptr = self.buckets.load(Ordering::SeqCst, guard);

        if buckets_ptr.is_null() {
            return None;
        }

        let buckets_ref = unsafe { buckets_ptr.deref() };
        let hash = self.get_hash(key);

        unsafe { buckets_ref.remove(key, hash, None, guard).as_ref() }.map(|b| {
            self.len.fetch_sub(1, Ordering::SeqCst);

            b
        })
    }

    fn get_hash<Q: ?Sized + Hash + Eq>(&self, key: &Q) -> u64 {
        let mut hasher = self.hash_builder.build_hasher();
        key.hash(&mut hasher);

        hasher.finish()
    }

    fn get_or_create_buckets(&self, guard: &'g Guard) -> Shared<'g, BucketArray<K, V, S>> {
        const DEFAULT_CAPACITY: usize = 64;

        let mut buckets_ptr = self.buckets.load(Ordering::SeqCst, guard);
        let mut maybe_new_buckets = None;

        loop {
            if buckets_ptr.is_null() {
                let new_buckets = match maybe_new_buckets.take() {
                    Some(b) => b,
                    None => Owned::new(BucketArray::with_capacity_and_hasher(
                        DEFAULT_CAPACITY,
                        self.hash_builder.clone(),
                    )),
                };

                match self.buckets.compare_and_set_weak(
                    buckets_ptr,
                    new_buckets,
                    Ordering::SeqCst,
                    guard,
                ) {
                    Ok(new_buckets) => return new_buckets,
                    Err(e) => {
                        maybe_new_buckets = Some(e.new);
                        buckets_ptr = e.current;
                    }
                }
            } else {
                return buckets_ptr;
            }
        }
    }
}

struct BucketArray<K: Hash + Eq, V, S: BuildHasher> {
    buckets: Vec<Atomic<Bucket<K, V>>>, // len() is a power of 2
    len: AtomicUsize,
    next_array: Atomic<BucketArray<K, V, S>>,
    hash_builder: Arc<S>,
}

impl<K: Hash + Eq, V, S: BuildHasher> BucketArray<K, V, S> {
    fn with_capacity_and_hasher(capacity: usize, hash_builder: Arc<S>) -> BucketArray<K, V, S> {
        BucketArray {
            buckets: vec![Atomic::null(); round_up_to_next_power_of_2(capacity * 2)],
            len: AtomicUsize::new(0),
            next_array: Atomic::null(),
            hash_builder,
        }
    }

    fn get_hash(&self, key: &K) -> u64 {
        let mut hasher = self.hash_builder.build_hasher();
        key.hash(&mut hasher);

        hasher.finish()
    }
}

const REDIRECT_TAG: usize = 1;

impl<'g, K: Hash + Eq, V, S: BuildHasher> BucketArray<K, V, S> {
    fn get<Q: ?Sized + Hash + Eq>(
        &self,
        key: &Q,
        hash: u64,
        guard: &'g Guard,
    ) -> BucketAndParentPtr<'g, K, V, S>
    where
        K: Borrow<Q>,
    {
        let capacity = self.buckets.len();
        let offset = (hash & (self.buckets.len() - 1) as u64) as usize;

        for this_bucket_ptr in (0..capacity)
            .map(|x| (x + offset) & (capacity - 1))
            .map(|i| &self.buckets[i])
            .map(|this_bucket| this_bucket.load(Ordering::SeqCst, guard))
        {
            if let Some(this_bucket_ref) = unsafe { this_bucket_ptr.as_ref() } {
                if this_bucket_ref.key.borrow() != key {
                    continue;
                } else if this_bucket_ptr.tag() != REDIRECT_TAG {
                    return BucketAndParentPtr::without_parent(this_bucket_ptr);
                }

                let next_array_ptr = self.next_array.load(Ordering::SeqCst, guard);
                assert!(!next_array_ptr.is_null());
                let next_array = unsafe { next_array_ptr.deref() };
                self.grow_into(next_array, guard);

                return next_array
                    .get(key, hash, guard)
                    .parent_ptr_or(next_array_ptr);
            } else {
                return BucketAndParentPtr::null();
            }
        }

        BucketAndParentPtr::null()
    }

    fn insert(
        &self,
        bucket_ptr: Shared<'g, Bucket<K, V>>,
        hash: u64,
        guard: &'g Guard,
    ) -> BucketAndParentPtr<'g, K, V, S> {
        assert!(!bucket_ptr.is_null());

        let bucket = unsafe { bucket_ptr.deref() };
        let capacity = self.buckets.len();
        let len = self.len.load(Ordering::SeqCst);

        let insert_into = |next_array_ptr: Shared<'g, BucketArray<K, V, S>>| {
            assert!(!next_array_ptr.is_null());
            let next_array = unsafe { next_array_ptr.deref() };

            next_array
                .insert(bucket_ptr, hash, guard)
                .parent_ptr_or(next_array_ptr)
        };

        // grow if inserting would push us over a load factor of 0.5
        if (len + 1) > (capacity / 2) {
            return insert_into(self.grow(guard));
        }

        let grow_into_next_if_and_insert_into_next = |have_seen_redirect| {
            let next_array_ptr = if have_seen_redirect {
                let next_array_ptr = self.next_array.load(Ordering::SeqCst, guard);
                assert!(!next_array_ptr.is_null());
                let next_array = unsafe { next_array_ptr.deref() };
                self.grow_into(next_array, guard);

                next_array_ptr
            } else {
                self.grow(guard)
            };

            insert_into(next_array_ptr)
        };

        let offset = (hash & (capacity - 1) as u64) as usize;
        let mut have_seen_redirect = false;

        for this_bucket in (0..capacity)
            .map(|x| (x + offset) & (capacity - 1))
            .map(|i| &self.buckets[i])
        {
            let mut this_bucket_ptr = this_bucket.load(Ordering::SeqCst, guard);

            loop {
                have_seen_redirect = have_seen_redirect || (this_bucket_ptr.tag() == REDIRECT_TAG);

                let should_increment_len =
                    if let Some(this_bucket_ref) = unsafe { this_bucket_ptr.as_ref() } {
                        if this_bucket_ref.key != bucket.key {
                            break;
                        }

                        this_bucket_ref.is_tombstone()
                    } else {
                        true
                    };

                if this_bucket_ptr.tag() == REDIRECT_TAG {
                    return grow_into_next_if_and_insert_into_next(true);
                }

                match this_bucket.compare_and_set_weak(
                    this_bucket_ptr,
                    bucket_ptr,
                    Ordering::SeqCst,
                    guard,
                ) {
                    Ok(_) => {
                        if should_increment_len {
                            // replaced a tombstone
                            self.len.fetch_add(1, Ordering::SeqCst);

                            return BucketAndParentPtr::null();
                        } else {
                            // swapped with something
                            return BucketAndParentPtr::without_parent(this_bucket_ptr);
                        }
                    }
                    Err(e) => this_bucket_ptr = e.current,
                }
            }
        }

        grow_into_next_if_and_insert_into_next(have_seen_redirect)
    }

    fn remove<Q: Hash + Eq + ?Sized>(
        &self,
        key: &Q,
        hash: u64,
        mut maybe_new_bucket: Option<Owned<Bucket<K, V>>>,
        guard: &'g Guard,
    ) -> Shared<'g, Bucket<K, V>>
    where
        K: Borrow<Q> + Clone,
    {
        let capacity = self.buckets.len();
        let offset = (hash & (capacity - 1) as u64) as usize;

        for this_bucket in (0..self.buckets.len())
            .map(|x| (x + offset) & (capacity - 1))
            .map(|i| &self.buckets[i])
        {
            let mut this_bucket_ptr = this_bucket.load(Ordering::SeqCst, guard);

            loop {
                if this_bucket_ptr.is_null() {
                    return Shared::null();
                }

                let this_bucket_ref = unsafe { this_bucket_ptr.deref() };

                if this_bucket_ref.key.borrow() != key {
                    // hash collision, keep probing
                    break;
                } else if this_bucket_ref.is_tombstone() {
                    return Shared::null();
                }

                let new_bucket = match maybe_new_bucket.take() {
                    Some(b) => b,
                    None => Owned::new(Bucket {
                        key: this_bucket_ref.key.clone(),
                        maybe_value: None,
                    }),
                };

                if this_bucket_ptr.tag() == REDIRECT_TAG {
                    let next_array = self.get_next(guard).unwrap();

                    return next_array.remove(key, hash, Some(new_bucket), guard);
                }

                match this_bucket.compare_and_set_weak(
                    this_bucket_ptr,
                    new_bucket,
                    Ordering::SeqCst,
                    guard,
                ) {
                    Ok(_) => {
                        self.len.fetch_sub(1, Ordering::SeqCst);

                        return this_bucket_ptr;
                    }
                    Err(e) => {
                        this_bucket_ptr = e.current;
                        maybe_new_bucket.replace(e.new);
                    }
                }
            }
        }

        Shared::null()
    }

    fn grow(&self, guard: &'g Guard) -> Shared<'g, BucketArray<K, V, S>> {
        let maybe_next_array_ptr = self.next_array.load(Ordering::SeqCst, guard);

        if !maybe_next_array_ptr.is_null() {
            let next_array = unsafe { maybe_next_array_ptr.deref() };
            self.grow_into(next_array, guard);

            return maybe_next_array_ptr;
        }

        let new_array_ptr = match self.next_array.compare_and_set(
            maybe_next_array_ptr,
            Owned::new(BucketArray::with_capacity_and_hasher(
                self.buckets.len() * 2,
                self.hash_builder.clone(),
            )),
            Ordering::SeqCst,
            guard,
        ) {
            Ok(new_array_ptr) => new_array_ptr,
            Err(e) => e.current,
        };

        assert!(!new_array_ptr.is_null());
        let new_array = unsafe { new_array_ptr.deref() };

        self.grow_into(new_array, guard);

        new_array_ptr
    }

    fn grow_into(&self, next_array: &'g BucketArray<K, V, S>, guard: &'g Guard) {
        for this_bucket in self.buckets.iter() {
            let mut this_bucket_ptr = this_bucket.load(Ordering::SeqCst, guard);

            loop {
                if this_bucket_ptr.tag() == REDIRECT_TAG {
                    // another thread already relocated this bucket
                    break;
                }

                if let Some(this_bucket_ref) = unsafe { this_bucket_ptr.as_ref() } {
                    if this_bucket_ref.is_tombstone() {
                        // set redirect tag and move on
                        match this_bucket.compare_and_set_weak(
                            this_bucket_ptr,
                            this_bucket_ptr.with_tag(REDIRECT_TAG),
                            Ordering::SeqCst,
                            guard,
                        ) {
                            Ok(_) => break,
                            Err(e) => {
                                this_bucket_ptr = e.current;

                                continue;
                            }
                        }
                    }

                    // insert into the next array
                    let this_key = &this_bucket_ref.key;
                    let hash = self.get_hash(this_key);

                    next_array.insert(this_bucket_ptr, hash, guard);

                    // strong CAS to avoid spurious insert/remove pairs
                    match this_bucket.compare_and_set(
                        this_bucket_ptr,
                        this_bucket_ptr.with_tag(REDIRECT_TAG),
                        Ordering::SeqCst,
                        guard,
                    ) {
                        Ok(_) => break,
                        Err(e) => {
                            // don't remove??? dunno what's going on here
                            // next_array.remove(this_key, hash, None, guard);
                            this_bucket_ptr = e.current;
                        }
                    }
                } else {
                    // set redirect tag and move on
                    match this_bucket.compare_and_set_weak(
                        Shared::null(),
                        Shared::null().with_tag(REDIRECT_TAG),
                        Ordering::SeqCst,
                        guard,
                    ) {
                        Ok(_) => break,
                        Err(e) => this_bucket_ptr = e.current,
                    }
                }
            }
        }
    }

    fn get_next(&self, guard: &'g Guard) -> Option<&'g BucketArray<K, V, S>> {
        unsafe { self.next_array.load(Ordering::SeqCst, guard).as_ref() }
    }
}

#[derive(Copy, Clone)]
struct BucketAndParentPtr<'g, K: Hash + Eq, V, S: BuildHasher> {
    bucket_ptr: Shared<'g, Bucket<K, V>>,
    parent_ptr: Shared<'g, BucketArray<K, V, S>>,
}

impl<'g, K: Hash + Eq, V, S: BuildHasher> BucketAndParentPtr<'g, K, V, S> {
    fn without_parent(bucket_ptr: Shared<'g, Bucket<K, V>>) -> BucketAndParentPtr<'g, K, V, S> {
        BucketAndParentPtr {
            bucket_ptr,
            parent_ptr: Shared::null(),
        }
    }

    fn null() -> BucketAndParentPtr<'g, K, V, S> {
        BucketAndParentPtr {
            bucket_ptr: Shared::null(),
            parent_ptr: Shared::null(),
        }
    }

    fn parent_ptr_or(
        mut self,
        parent_ptr: Shared<'g, BucketArray<K, V, S>>,
    ) -> BucketAndParentPtr<'g, K, V, S> {
        if self.parent_ptr.is_null() {
            self.parent_ptr = parent_ptr;
        }

        self
    }
}

#[repr(align(2))]
struct Bucket<K: Hash + Eq, V> {
    key: K,
    maybe_value: Option<V>,
}

impl<K: Hash + Eq, V> Bucket<K, V> {
    fn is_tombstone(&self) -> bool {
        self.maybe_value.is_none()
    }
}

fn round_up_to_next_power_of_2(x: usize) -> usize {
    if is_power_of_2(x) {
        return x;
    }

    let first_set = (mem::size_of::<usize>() * 8) as u32 - x.leading_zeros();

    1 << first_set
}

fn is_power_of_2(x: usize) -> bool {
    if x == 0 {
        false
    } else {
        (x & (x - 1)) == 0
    }
}
