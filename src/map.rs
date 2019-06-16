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
pub struct HashMap<K: Hash + Eq + Clone, V: Clone, S: BuildHasher> {
    buckets: Atomic<BucketArray<K, V, S>>,
    hash_builder: Arc<S>,
}

impl<K: Hash + Eq + Clone, V: Clone> HashMap<K, V, FxBuildHasher> {
    pub fn new() -> HashMap<K, V, FxBuildHasher> {
        HashMap::with_capacity_and_hasher(0, FxBuildHasher::default())
    }

    pub fn with_capacity(capacity: usize) -> HashMap<K, V, FxBuildHasher> {
        HashMap::with_capacity_and_hasher(capacity, FxBuildHasher::default())
    }
}

impl<K: Hash + Eq + Clone, V: Clone, S: BuildHasher> HashMap<K, V, S> {
    pub fn with_hasher(hash_builder: S) -> HashMap<K, V, S> {
        HashMap::with_capacity_and_hasher(0, hash_builder)
    }

    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> HashMap<K, V, S> {
        if capacity == 0 {
            HashMap {
                buckets: Atomic::null(),
                hash_builder: Arc::new(hash_builder),
            }
        } else {
            let hash_builder = Arc::new(hash_builder);

            HashMap {
                buckets: Atomic::new(BucketArray::with_capacity_and_hasher(
                    capacity,
                    hash_builder.clone(),
                )),
                hash_builder,
            }
        }
    }

    pub fn len(&self) -> usize {
        let guard = &crossbeam_epoch::pin();
        let buckets_ptr = self.buckets.load(Ordering::SeqCst, guard);

        if buckets_ptr.is_null() {
            return 0;
        }

        let buckets_ref = unsafe { buckets_ptr.deref() };

        buckets_ref.len.load(Ordering::SeqCst)
    }

    pub fn is_empty(&self) -> bool {
        let guard = &crossbeam_epoch::pin();
        let buckets_ptr = self.buckets.load(Ordering::SeqCst, guard);

        if buckets_ptr.is_null() {
            return true;
        }

        let buckets_ref = unsafe { buckets_ptr.deref() };

        buckets_ref.len.load(Ordering::SeqCst) == 0
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
        K: Borrow<Q>,
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

    pub fn insert(&self, k: K, v: V) -> Option<V> {
        let guard = &crossbeam_epoch::pin();
        let previous_bucket_ptr = self.do_insert(k, v, guard);

        if previous_bucket_ptr.is_null() {
            None
        } else {
            let previous_bucket_ref = unsafe { previous_bucket_ptr.deref() };

            previous_bucket_ref.maybe_value.as_ref().cloned()
        }
    }

    pub fn insert_entry(&self, k: K, v: V) -> Option<(K, V)> {
        let guard = &crossbeam_epoch::pin();
        let previous_bucket_ptr = self.do_insert(k, v, guard);

        if previous_bucket_ptr.is_null() {
            None
        } else {
            let previous_bucket_ref = unsafe { previous_bucket_ptr.deref() };

            previous_bucket_ref
                .maybe_value
                .as_ref()
                .map(|v| (previous_bucket_ref.key.clone(), v.clone()))
        }
    }

    pub fn insert_and<F: FnOnce(&V) -> T, T>(&self, k: K, v: V, func: F) -> Option<T> {
        let guard = &crossbeam_epoch::pin();
        let previous_bucket_ptr = self.do_insert(k, v, guard);

        if previous_bucket_ptr.is_null() {
            None
        } else {
            let previous_bucket_ref = unsafe { previous_bucket_ptr.deref() };

            previous_bucket_ref.maybe_value.as_ref().map(|v| func(&v))
        }
    }

    pub fn insert_entry_and<F: FnOnce(&K, &V) -> T, T>(&self, k: K, v: V, func: F) -> Option<T> {
        let guard = &crossbeam_epoch::pin();
        let previous_bucket_ptr = self.do_insert(k, v, guard);

        if previous_bucket_ptr.is_null() {
            None
        } else {
            let previous_bucket_ref = unsafe { previous_bucket_ptr.deref() };

            previous_bucket_ref
                .maybe_value
                .as_ref()
                .map(|v| func(&previous_bucket_ref.key, &v))
        }
    }

    pub fn remove<Q: Hash + Eq + ?Sized>(&self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
    {
        let guard = &crossbeam_epoch::pin();

        let buckets_ptr = self.buckets.load(Ordering::SeqCst, guard);

        if buckets_ptr.is_null() {
            return None;
        }

        let buckets_ref = unsafe { buckets_ptr.deref() };
        let hash = self.get_hash(key);

        let removed_bucket_ptr = buckets_ref.remove(key, hash, None, guard);

        if removed_bucket_ptr.is_null() {
            None
        } else {
            let removed_bucket_ref = unsafe { removed_bucket_ptr.deref() };

            removed_bucket_ref.maybe_value.as_ref().cloned()
        }
    }
}

impl<'g, K: Hash + Eq + Clone, V: Clone, S: BuildHasher> HashMap<K, V, S> {
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
        let (found_bucket_ptr, redirected) = buckets.get(key, hash, guard);

        if redirected {
            self.catch_up_buckets_ptr(buckets_ptr, guard);
        }

        if found_bucket_ptr.is_null() {
            None
        } else {
            Some(unsafe { found_bucket_ptr.deref() })
        }
    }

    fn do_insert(&self, key: K, value: V, guard: &'g Guard) -> Shared<'g, Bucket<K, V>> {
        let hash = self.get_hash(&key);

        let buckets_ptr = self.get_or_create_buckets(guard);
        assert!(!buckets_ptr.is_null());
        let buckets = unsafe { buckets_ptr.deref() };

        let new_bucket = Owned::new(Bucket {
            key,
            maybe_value: Some(value),
        })
        .into_shared(guard);

        let InsertReturn {
            previous_bucket_ptr,
            was_redirected,
        } = buckets.insert(new_bucket, hash, guard);

        if was_redirected {
            self.catch_up_buckets_ptr(buckets_ptr, guard);
        }

        previous_bucket_ptr
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

    fn catch_up_buckets_ptr(
        &self,
        mut buckets_ptr: Shared<'g, BucketArray<K, V, S>>,
        guard: &'g Guard,
    ) {
        assert!(!buckets_ptr.is_null());

        let mut next_ptr = unsafe { buckets_ptr.deref() }
            .next_array
            .load(Ordering::SeqCst, guard);
        assert!(!next_ptr.is_null());

        loop {
            if next_ptr.is_null() {
                return;
            }

            match self
                .buckets
                .compare_and_set_weak(buckets_ptr, next_ptr, Ordering::SeqCst, guard)
            {
                Ok(_) => {
                    buckets_ptr = next_ptr;

                    if !buckets_ptr.is_null() {
                        next_ptr = unsafe { buckets_ptr.deref() }
                            .next_array
                            .load(Ordering::SeqCst, guard);
                    }
                }
                Err(e) => {
                    buckets_ptr = e.current;
                    assert!(!buckets_ptr.is_null());
                    next_ptr = unsafe { buckets_ptr.deref() }
                        .next_array
                        .load(Ordering::SeqCst, guard);
                }
            }
        }
    }
}

struct BucketArray<K: Hash + Eq + Clone, V: Clone, S: BuildHasher> {
    buckets: Vec<Atomic<Bucket<K, V>>>, // must be a power of 2
    len: AtomicUsize,
    next_array: Atomic<BucketArray<K, V, S>>,
    hash_builder: Arc<S>,
}

impl<K: Hash + Eq + Clone, V: Clone, S: BuildHasher> BucketArray<K, V, S> {
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

impl<'g, K: Hash + Eq + Clone, V: Clone, S: BuildHasher> BucketArray<K, V, S> {
    fn get<Q: ?Sized + Hash + Eq>(
        &self,
        key: &Q,
        hash: u64,
        guard: &'g Guard,
    ) -> (Shared<'g, Bucket<K, V>>, bool)
    where
        K: Borrow<Q>,
    {
        let len = self.buckets.len();
        let offset = (hash & (len - 1) as u64) as usize;

        for i in (0..self.buckets.len()).map(|x| (x + offset) & (len - 1)) {
            let this_bucket = &self.buckets[i];
            let this_bucket_ptr = this_bucket.load(Ordering::SeqCst, guard);

            if this_bucket_ptr.is_null() {
                return (Shared::null(), false);
            } else {
                let this_bucket_ref = unsafe { this_bucket_ptr.deref() };

                if this_bucket_ref.key.borrow() == key {
                    if this_bucket_ptr.tag() == REDIRECT_TAG {
                        let next_array_ptr = self.next_array.load(Ordering::SeqCst, guard);
                        assert!(!next_array_ptr.is_null());
                        let next_array = unsafe { next_array_ptr.deref() };

                        let (new_bucket, _) = next_array.get(key, hash, guard);

                        return (new_bucket, true);
                    }

                    return (this_bucket_ptr, false);
                }
            }
        }

        (Shared::null(), false)
    }

    fn insert(
        &self,
        bucket_ptr: Shared<'g, Bucket<K, V>>,
        hash: u64,
        guard: &'g Guard,
    ) -> InsertReturn<'g, K, V> {
        assert!(!bucket_ptr.is_null());

        let bucket = unsafe { bucket_ptr.deref() };
        let capacity = self.buckets.len();
        let num_elements = self.len.load(Ordering::SeqCst);

        // grow if inserting would push us over a load factor of 0.5
        if (num_elements + 1) > (capacity / 2) {
            let next_array = self.grow(guard);

            let mut ret = next_array.insert(bucket_ptr, hash, guard);
            ret.was_redirected = true;

            return ret;
        }

        let offset = (hash & (capacity - 1) as u64) as usize;
        let mut have_seen_redirect = false;

        for i in (0..self.buckets.len()).map(|x| (x + offset) & (capacity - 1)) {
            let this_bucket = &self.buckets[i];
            let mut this_bucket_ptr = this_bucket.load(Ordering::SeqCst, guard);

            loop {
                have_seen_redirect = have_seen_redirect || (this_bucket_ptr.tag() == REDIRECT_TAG);

                if this_bucket_ptr.is_null() {
                    if this_bucket_ptr.tag() == REDIRECT_TAG {
                        let next_array_ptr = self.next_array.load(Ordering::SeqCst, guard);
                        assert!(!next_array_ptr.is_null());
                        let next_array = unsafe { next_array_ptr.deref() };

                        let mut ret = next_array.insert(bucket_ptr, hash, guard);
                        ret.was_redirected = true;

                        return ret;
                    }

                    match this_bucket.compare_and_set_weak(
                        this_bucket_ptr,
                        bucket_ptr,
                        Ordering::SeqCst,
                        guard,
                    ) {
                        Ok(_) => {
                            self.len.fetch_add(1, Ordering::SeqCst);

                            return InsertReturn {
                                previous_bucket_ptr: this_bucket_ptr,
                                was_redirected: false,
                            };
                        }
                        Err(e) => this_bucket_ptr = e.current,
                    };
                } else {
                    let this_bucket_ref = unsafe { this_bucket_ptr.deref() };

                    if this_bucket_ref.key == bucket.key {
                        if this_bucket_ptr.tag() == REDIRECT_TAG {
                            let next_array_ptr = self.next_array.load(Ordering::SeqCst, guard);
                            assert!(!next_array_ptr.is_null());
                            let next_array = unsafe { next_array_ptr.deref() };

                            let mut ret = next_array.insert(bucket_ptr, hash, guard);
                            ret.was_redirected = true;

                            return ret;
                        }

                        match this_bucket.compare_and_set_weak(
                            this_bucket_ptr,
                            bucket_ptr,
                            Ordering::SeqCst,
                            guard,
                        ) {
                            Ok(_) => {
                                // this was a swap
                                if this_bucket_ref.maybe_value.is_none() {
                                    self.len.fetch_add(1, Ordering::SeqCst);
                                }

                                return InsertReturn {
                                    previous_bucket_ptr: this_bucket_ptr,
                                    was_redirected: false,
                                };
                            }
                            Err(e) => this_bucket_ptr = e.current,
                        }
                    } else {
                        break;
                    }
                }
            }
        }

        let next_array = if have_seen_redirect {
            let next_array_ptr = self.next_array.load(Ordering::SeqCst, guard);
            assert!(!next_array_ptr.is_null());

            unsafe { next_array_ptr.deref() }
        } else {
            self.grow(guard)
        };

        let mut ret = next_array.insert(bucket_ptr, hash, guard);
        ret.was_redirected = true;

        ret
    }

    fn remove<Q: Hash + Eq + ?Sized>(
        &self,
        key: &Q,
        hash: u64,
        mut maybe_new_bucket: Option<Owned<Bucket<K, V>>>,
        guard: &'g Guard,
    ) -> Shared<'g, Bucket<K, V>>
    where
        K: Borrow<Q>,
    {
        let capacity = self.buckets.len();
        let offset = (hash & (capacity - 1) as u64) as usize;

        'outer: for i in (0..self.buckets.len()).map(|x| (x + offset) & (capacity - 1)) {
            let this_bucket = &self.buckets[i];
            let mut this_bucket_ptr = this_bucket.load(Ordering::SeqCst, guard);

            loop {
                if this_bucket_ptr.is_null() {
                    return Shared::null();
                }

                let this_bucket_ref = unsafe { this_bucket_ptr.deref() };

                if this_bucket_ref.key.borrow() != key {
                    continue 'outer;
                }

                let new_bucket = match maybe_new_bucket.take() {
                    Some(b) => b,
                    None => Owned::new(Bucket {
                        key: this_bucket_ref.key.clone(),
                        maybe_value: None,
                    }),
                };

                if this_bucket_ptr.tag() == REDIRECT_TAG {
                    let next_array_ptr = self.next_array.load(Ordering::SeqCst, guard);
                    assert!(!next_array_ptr.is_null());
                    let next_array = unsafe { next_array_ptr.deref() };

                    return next_array.remove(key, hash, Some(new_bucket), guard);
                }

                match this_bucket.compare_and_set_weak(
                    this_bucket_ptr,
                    new_bucket,
                    Ordering::SeqCst,
                    guard,
                ) {
                    Ok(_) => {
                        let prev_value = self.len.fetch_sub(1, Ordering::SeqCst);
                        let new_size = prev_value - 1;
                        assert!(new_size < prev_value);

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

    fn grow(&self, guard: &'g Guard) -> &'g BucketArray<K, V, S> {
        let maybe_next_array_ptr = self.next_array.load(Ordering::SeqCst, guard);

        if !maybe_next_array_ptr.is_null() {
            let next_array = unsafe { maybe_next_array_ptr.deref() };
            self.grow_into(next_array, guard);

            return next_array;
        }

        let owned_new_array_ptr = Owned::new(BucketArray::with_capacity_and_hasher(
            self.buckets.len() * 2,
            self.hash_builder.clone(),
        ));

        let new_array_ptr = match self.next_array.compare_and_set(
            maybe_next_array_ptr,
            owned_new_array_ptr,
            Ordering::SeqCst,
            guard,
        ) {
            Ok(new_array_ptr) => new_array_ptr,
            Err(e) => e.current,
        };

        assert!(!new_array_ptr.is_null());
        let new_array = unsafe { new_array_ptr.deref() };

        self.grow_into(new_array, guard);

        new_array
    }

    fn grow_into(&self, next_array: &'g BucketArray<K, V, S>, guard: &'g Guard) {
        'outer: for this_bucket in self.buckets.iter() {
            let mut this_bucket_ptr = this_bucket.load(Ordering::SeqCst, guard);

            loop {
                // if the tag is redirect, someone else moved it already
                if this_bucket_ptr.tag() == REDIRECT_TAG {
                    continue 'outer;
                }

                if this_bucket_ptr.is_null() {
                    match this_bucket.compare_and_set_weak(
                        this_bucket_ptr,
                        Shared::null().with_tag(REDIRECT_TAG),
                        Ordering::SeqCst,
                        guard,
                    ) {
                        Ok(_) => continue 'outer,
                        Err(e) => this_bucket_ptr = e.current,
                    }
                } else {
                    let this_bucket_ref = unsafe { this_bucket_ptr.deref() };

                    if this_bucket_ref.maybe_value.is_some() {
                        let hash = self.get_hash(&this_bucket_ref.key);

                        next_array.insert(this_bucket_ptr, hash, guard);

                        match this_bucket.compare_and_set(
                            this_bucket_ptr,
                            this_bucket_ptr.with_tag(REDIRECT_TAG),
                            Ordering::SeqCst,
                            guard,
                        ) {
                            Ok(_) => continue 'outer,
                            Err(e) => {
                                next_array.remove(&this_bucket_ref.key, hash, None, guard);
                                this_bucket_ptr = e.current;
                            }
                        }
                    } else {
                        // mark tombstones as redirect, but don't move them
                        match this_bucket.compare_and_set_weak(
                            this_bucket_ptr,
                            this_bucket_ptr.with_tag(REDIRECT_TAG),
                            Ordering::SeqCst,
                            guard,
                        ) {
                            Ok(_) => continue 'outer,
                            Err(e) => this_bucket_ptr = e.current,
                        }
                    }
                }
            }
        }
    }
}

struct InsertReturn<'g, K: Hash + Eq + Clone, V: Clone> {
    previous_bucket_ptr: Shared<'g, Bucket<K, V>>,
    was_redirected: bool,
}

struct Bucket<K: Hash + Eq + Clone, V: Clone> {
    key: K,
    maybe_value: Option<V>,
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
