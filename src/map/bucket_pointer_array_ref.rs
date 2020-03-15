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

use super::bucket::{self, Bucket, BucketPointerArray, InsertOrModifyState, KeyOrOwnedBucket};

use std::{
    borrow::Borrow,
    hash::{BuildHasher, Hash},
    sync::atomic::{AtomicUsize, Ordering},
};

use crossbeam_epoch::{Atomic, CompareAndSetError, Guard, Owned, Shared};

pub(crate) struct BucketPointerArrayRef<'a, K, V, S> {
    pub(crate) bucket_pointer_array: &'a Atomic<BucketPointerArray<K, V>>,
    pub(crate) build_hasher: &'a S,
    pub(crate) len: &'a AtomicUsize,
}

impl<'a, K: Hash + Eq, V, S: BuildHasher> BucketPointerArrayRef<'a, K, V, S> {
    pub(crate) fn get_key_value_and<Q: Hash + Eq + ?Sized, F: FnOnce(&K, &V) -> T, T>(
        &self,
        key: &Q,
        hash: u64,
        with_entry: F,
    ) -> Option<T>
    where
        K: Borrow<Q>,
    {
        let guard = &crossbeam_epoch::pin();
        let current_ref = self.get(guard);
        let mut bucket_pointer_array_ref = current_ref;

        let result;

        loop {
            match bucket_pointer_array_ref
                .get(guard, hash, key)
                .map(|p| unsafe { p.as_ref() })
            {
                Ok(Some(Bucket {
                    key,
                    maybe_value: value,
                })) => {
                    result = Some(with_entry(key, unsafe { &*value.as_ptr() }));

                    break;
                }
                Ok(None) => {
                    result = None;

                    break;
                }
                Err(_) => {
                    bucket_pointer_array_ref =
                        bucket_pointer_array_ref.rehash(guard, self.build_hasher);
                }
            }
        }

        self.swing(guard, current_ref, bucket_pointer_array_ref);

        result
    }

    pub(crate) fn insert_entry_and<F: FnOnce(&K, &V) -> T, T>(
        &self,
        key: K,
        hash: u64,
        value: V,
        with_previous_entry: F,
    ) -> Option<T> {
        let guard = &crossbeam_epoch::pin();
        let current_ref = self.get(guard);
        let mut bucket_pointer_array_ref = current_ref;
        let mut bucket_ptr = Owned::new(Bucket::new(key, value));

        let result;

        loop {
            while self.len.load(Ordering::Relaxed) > bucket_pointer_array_ref.capacity() {
                bucket_pointer_array_ref =
                    bucket_pointer_array_ref.rehash(guard, self.build_hasher);
            }

            match bucket_pointer_array_ref.insert(guard, hash, bucket_ptr) {
                Ok(previous_bucket_ptr) => {
                    if let Some(previous_bucket_ref) = unsafe { previous_bucket_ptr.as_ref() } {
                        if previous_bucket_ptr.tag() & bucket::TOMBSTONE_TAG != 0 {
                            self.len.fetch_add(1, Ordering::Relaxed);
                            result = None;
                        } else {
                            let Bucket {
                                key,
                                maybe_value: value,
                            } = previous_bucket_ref;
                            result = Some(with_previous_entry(key, unsafe { &*value.as_ptr() }));
                        }

                        unsafe { bucket::defer_destroy_bucket(guard, previous_bucket_ptr) };
                    } else {
                        self.len.fetch_add(1, Ordering::Relaxed);
                        result = None;
                    }

                    break;
                }
                Err(p) => {
                    bucket_ptr = p;
                    bucket_pointer_array_ref =
                        bucket_pointer_array_ref.rehash(guard, self.build_hasher);
                }
            }
        }

        self.swing(guard, current_ref, bucket_pointer_array_ref);

        result
    }

    pub(crate) fn remove_entry_if_and<
        Q: Hash + Eq + ?Sized,
        F: FnMut(&K, &V) -> bool,
        G: FnOnce(&K, &V) -> T,
        T,
    >(
        &self,
        key: &Q,
        hash: u64,
        mut condition: F,
        with_previous_entry: G,
    ) -> Option<T>
    where
        K: Borrow<Q>,
    {
        let guard = &crossbeam_epoch::pin();
        let current_ref = self.get(guard);
        let mut bucket_pointer_array_ref = current_ref;

        let result;

        loop {
            match bucket_pointer_array_ref.remove_if(guard, hash, key, condition) {
                Ok(previous_bucket_ptr) => {
                    if let Some(previous_bucket_ref) = unsafe { previous_bucket_ptr.as_ref() } {
                        let Bucket {
                            key,
                            maybe_value: value,
                        } = previous_bucket_ref;
                        self.len.fetch_sub(1, Ordering::Relaxed);
                        result = Some(with_previous_entry(key, unsafe { &*value.as_ptr() }));

                        unsafe { bucket::defer_destroy_tombstone(guard, previous_bucket_ptr) };
                    } else {
                        result = None;
                    }

                    break;
                }
                Err(c) => {
                    condition = c;
                    bucket_pointer_array_ref =
                        bucket_pointer_array_ref.rehash(guard, self.build_hasher);
                }
            }
        }

        self.swing(guard, current_ref, bucket_pointer_array_ref);

        result
    }

    pub(crate) fn insert_with_or_modify_entry_and<
        F: FnOnce() -> V,
        G: FnMut(&K, &V) -> V,
        H: FnOnce(&K, &V) -> T,
        T,
    >(
        &self,
        key: K,
        hash: u64,
        on_insert: F,
        mut on_modify: G,
        with_old_entry: H,
    ) -> Option<T> {
        let guard = &crossbeam_epoch::pin();
        let current_ref = self.get(guard);
        let mut bucket_pointer_array_ref = current_ref;
        let mut state = InsertOrModifyState::New(key, on_insert);

        let result;

        loop {
            while self.len.load(Ordering::Relaxed) > bucket_pointer_array_ref.capacity() {
                bucket_pointer_array_ref =
                    bucket_pointer_array_ref.rehash(guard, self.build_hasher);
            }

            match bucket_pointer_array_ref.insert_or_modify(guard, hash, state, on_modify) {
                Ok(previous_bucket_ptr) => {
                    if let Some(previous_bucket_ref) = unsafe { previous_bucket_ptr.as_ref() } {
                        if previous_bucket_ptr.tag() & bucket::TOMBSTONE_TAG != 0 {
                            self.len.fetch_add(1, Ordering::Relaxed);
                            result = None;
                        } else {
                            let Bucket {
                                key,
                                maybe_value: value,
                            } = previous_bucket_ref;
                            result = Some(with_old_entry(key, unsafe { &*value.as_ptr() }));
                        }

                        unsafe { bucket::defer_destroy_bucket(guard, previous_bucket_ptr) };
                    } else {
                        self.len.fetch_add(1, Ordering::Relaxed);
                        result = None;
                    }

                    break;
                }
                Err((s, f)) => {
                    state = s;
                    on_modify = f;
                    bucket_pointer_array_ref =
                        bucket_pointer_array_ref.rehash(guard, self.build_hasher);
                }
            }
        }

        self.swing(guard, current_ref, bucket_pointer_array_ref);

        result
    }

    pub(crate) fn modify_entry_and<F: FnMut(&K, &V) -> V, G: FnOnce(&K, &V) -> T, T>(
        &self,
        key: K,
        hash: u64,
        mut on_modify: F,
        with_old_entry: G,
    ) -> Option<T> {
        let guard = &crossbeam_epoch::pin();
        let current_ref = self.get(guard);
        let mut bucket_pointer_array_ref = current_ref;
        let mut key_or_owned_bucket = KeyOrOwnedBucket::Key(key);

        let result;

        loop {
            match bucket_pointer_array_ref.modify(guard, hash, key_or_owned_bucket, on_modify) {
                Ok(previous_bucket_ptr) => {
                    if let Some(previous_bucket_ref) = unsafe { previous_bucket_ptr.as_ref() } {
                        let Bucket {
                            key,
                            maybe_value: value,
                        } = previous_bucket_ref;
                        result = Some(with_old_entry(key, unsafe { &*value.as_ptr() }));

                        unsafe { bucket::defer_destroy_bucket(guard, previous_bucket_ptr) };
                    } else {
                        result = None;
                    }

                    break;
                }
                Err((kb, f)) => {
                    key_or_owned_bucket = kb;
                    on_modify = f;
                    bucket_pointer_array_ref =
                        bucket_pointer_array_ref.rehash(guard, self.build_hasher);
                }
            }
        }

        self.swing(guard, current_ref, bucket_pointer_array_ref);

        result
    }
}

impl<'a, 'g, K, V, S> BucketPointerArrayRef<'a, K, V, S> {
    fn get(&self, guard: &'g Guard) -> &'g BucketPointerArray<K, V> {
        const DEFAULT_CAPACITY: usize = 64;

        let mut maybe_new_bucket_pointer_array = None;

        loop {
            let bucket_pointer_array_ptr = self.bucket_pointer_array.load_consume(guard);

            if let Some(bucket_pointer_array_ref) = unsafe { bucket_pointer_array_ptr.as_ref() } {
                return bucket_pointer_array_ref;
            }

            let new_bucket_pointer_array = maybe_new_bucket_pointer_array
                .unwrap_or_else(|| Owned::new(BucketPointerArray::with_capacity(DEFAULT_CAPACITY)));

            match self.bucket_pointer_array.compare_and_set_weak(
                Shared::null(),
                new_bucket_pointer_array,
                (Ordering::Release, Ordering::Relaxed),
                guard,
            ) {
                Ok(b) => return unsafe { b.as_ref() }.unwrap(),
                Err(CompareAndSetError { new, .. }) => maybe_new_bucket_pointer_array = Some(new),
            }
        }
    }

    fn swing(
        &self,
        guard: &'g Guard,
        mut current_ref: &'g BucketPointerArray<K, V>,
        min_ref: &'g BucketPointerArray<K, V>,
    ) {
        let min_epoch = min_ref.epoch;

        let mut current_ptr = (current_ref as *const BucketPointerArray<K, V>).into();
        let min_ptr: Shared<'g, _> = (min_ref as *const BucketPointerArray<K, V>).into();

        loop {
            if current_ref.epoch >= min_epoch {
                return;
            }

            match self.bucket_pointer_array.compare_and_set_weak(
                current_ptr,
                min_ptr,
                (Ordering::Release, Ordering::Relaxed),
                guard,
            ) {
                Ok(_) => unsafe { bucket::defer_acquire_destroy(guard, current_ptr) },
                Err(_) => {
                    let new_ptr = self.bucket_pointer_array.load_consume(guard);
                    assert!(!new_ptr.is_null());

                    current_ptr = new_ptr;
                    current_ref = unsafe { new_ptr.as_ref() }.unwrap();
                }
            }
        }
    }
}
