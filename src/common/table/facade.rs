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

use super::{InsertOrModifyState, KeyOrBucket, Table};

use crate::common::{Bucket, BucketRef};

use std::{
    borrow::Borrow,
    hash::{BuildHasher, Hash},
    mem,
    sync::atomic::{self, AtomicUsize, Ordering},
};

use crossbeam_epoch::{Atomic, CompareAndSetError, Guard, Owned, Shared};

pub(crate) struct Facade<'a, K, V, S> {
    pub(crate) table: &'a Atomic<Table<K, V>>,
    pub(crate) build_hasher: &'a S,
    pub(crate) len: &'a AtomicUsize,
}

impl<'a, K: Hash + Eq, V, S: BuildHasher> Facade<'a, K, V, S> {
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
        let mut table_ref = current_ref;

        let result;

        loop {
            match table_ref.get(guard, hash, key) {
                Ok(bucket_ptr) => {
                    match unsafe { Bucket::as_ref(bucket_ptr) } {
                        BucketRef::Filled(key, value) => result = Some(with_entry(key, value)),
                        BucketRef::Tombstone(_) => unreachable!(),
                        BucketRef::Null => result = None,
                        BucketRef::Sentinel => unreachable!(),
                    }

                    break;
                }
                Err(_) => {
                    table_ref = table_ref.rehash(guard, self.build_hasher);
                }
            }
        }

        self.swing(guard, current_ref, table_ref);

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
        let mut table_ref = current_ref;
        let mut bucket_ptr = Bucket::new(key, value);

        let result;

        loop {
            match table_ref.insert(guard, hash, bucket_ptr) {
                Ok(previous_bucket_ptr) => {
                    match unsafe { Bucket::as_ref(previous_bucket_ptr) } {
                        BucketRef::Filled(previous_key, previous_value) => {
                            result = Some(with_previous_entry(previous_key, previous_value));
                            unsafe { Bucket::defer_destroy(guard, previous_bucket_ptr) };
                        }
                        BucketRef::Tombstone(_) => {
                            self.len.fetch_add(1, Ordering::Relaxed);
                            result = None;
                            unsafe { Bucket::defer_destroy(guard, previous_bucket_ptr) };
                        }
                        BucketRef::Null => {
                            self.len.fetch_add(1, Ordering::Relaxed);
                            result = None;
                        }
                        BucketRef::Sentinel => unreachable!(),
                    }

                    break;
                }
                Err(p) => {
                    bucket_ptr = p;
                    table_ref = table_ref.rehash(guard, self.build_hasher);
                }
            }
        }

        self.swing(guard, current_ref, table_ref);

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
        let mut table_ref = current_ref;

        let result;

        loop {
            match table_ref.remove_if(guard, hash, key, condition) {
                Ok(previous_bucket_ptr) => {
                    match unsafe { Bucket::as_ref(previous_bucket_ptr) } {
                        BucketRef::Filled(previous_key, previous_value) => {
                            self.len.fetch_sub(1, Ordering::Relaxed);
                            result = Some(with_previous_entry(previous_key, previous_value));

                            unsafe { Bucket::defer_destroy_value(guard, previous_bucket_ptr) };
                        }
                        BucketRef::Tombstone(_) => unreachable!(),
                        BucketRef::Null => result = None,
                        BucketRef::Sentinel => unreachable!(),
                    }

                    break;
                }
                Err(c) => {
                    condition = c;
                    table_ref = table_ref.rehash(guard, self.build_hasher);
                }
            }
        }

        self.swing(guard, current_ref, table_ref);

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
        let mut table_ref = current_ref;
        let mut state = InsertOrModifyState::New {
            key,
            insert_function: on_insert,
        };

        let result;

        loop {
            match table_ref.insert_or_modify(guard, hash, state, on_modify) {
                Ok(previous_bucket_ptr) => {
                    match unsafe { Bucket::as_ref(previous_bucket_ptr) } {
                        BucketRef::Filled(previous_key, previous_value) => {
                            result = Some(with_old_entry(previous_key, previous_value));
                            unsafe { Bucket::defer_destroy(guard, previous_bucket_ptr) };
                        }
                        BucketRef::Tombstone(_) => {
                            self.len.fetch_add(1, Ordering::Relaxed);
                            result = None;
                            unsafe { Bucket::defer_destroy(guard, previous_bucket_ptr) };
                        }
                        BucketRef::Null => {
                            self.len.fetch_add(1, Ordering::Relaxed);
                            result = None;
                        }
                        BucketRef::Sentinel => unreachable!(),
                    }

                    break;
                }
                Err((s, f)) => {
                    state = s;
                    on_modify = f;
                    table_ref = table_ref.rehash(guard, self.build_hasher);
                }
            }
        }

        self.swing(guard, current_ref, table_ref);

        result
    }

    pub(crate) fn modify_entry_and<F: FnMut(&K, &V) -> V, G: FnOnce(&K, &V) -> T, T>(
        &self,
        key: K,
        hash: u64,
        mut on_modify: F,
        with_previous_entry: G,
    ) -> Option<T> {
        let guard = &crossbeam_epoch::pin();
        let current_ref = self.get(guard);
        let mut table_ref = current_ref;
        let mut key_or_owned_bucket = KeyOrBucket::Key(key);

        let result;

        loop {
            match table_ref.modify(guard, hash, key_or_owned_bucket, on_modify) {
                Ok(previous_bucket_ptr) => {
                    match unsafe { Bucket::as_ref(previous_bucket_ptr) } {
                        BucketRef::Filled(previous_key, previous_value) => {
                            result = Some(with_previous_entry(previous_key, previous_value));

                            unsafe { Bucket::defer_destroy(guard, previous_bucket_ptr) };
                        }
                        BucketRef::Tombstone(_) => unreachable!(),
                        BucketRef::Null => {
                            result = None;
                        }
                        BucketRef::Sentinel => unreachable!(),
                    }

                    break;
                }
                Err((kb, f)) => {
                    key_or_owned_bucket = kb;
                    on_modify = f;
                    table_ref = table_ref.rehash(guard, self.build_hasher);
                }
            }
        }

        self.swing(guard, current_ref, table_ref);

        result
    }
}

impl<'a, 'g, K, V, S> Facade<'a, K, V, S> {
    pub(crate) unsafe fn drop(self) {
        let guard = &crossbeam_epoch::unprotected();

        let mut current_ptr = self.table.load(Ordering::Relaxed, guard);

        while let Some(current_ref) = current_ptr.as_ref() {
            let next_ptr = current_ref.next.load(Ordering::Relaxed, guard);

            for this_bucket_ptr in current_ref
                .groups
                .iter()
                .map(|g| g.buckets.iter())
                .flatten()
                .map(|b| b.load(Ordering::Relaxed, guard))
                .filter(|p| !p.is_null())
                .filter(|p| next_ptr.is_null() || !Bucket::is_tombstone(*p))
            {
                // only delete tombstones from the newest bucket array
                // the only way this becomes a memory leak is if there was a panic during a rehash,
                // in which case i'm going to say that running destructors and freeing memory is
                // best-effort, and my best effort is to not do it

                Bucket::drop(this_bucket_ptr);
            }

            mem::drop(current_ptr.into_owned());

            current_ptr = next_ptr;
        }
    }

    fn get(&self, guard: &'g Guard) -> &'g Table<K, V> {
        const DEFAULT_CAPACITY: usize = 64;

        let mut maybe_new_table = None;

        loop {
            let table_ptr = self.table.load_consume(guard);

            if let Some(table_ref) = unsafe { table_ptr.as_ref() } {
                return table_ref;
            }

            let new_table = maybe_new_table
                .unwrap_or_else(|| Owned::new(Table::with_capacity(DEFAULT_CAPACITY)));

            match self.table.compare_and_set_weak(
                Shared::null(),
                new_table,
                (Ordering::Release, Ordering::Relaxed),
                guard,
            ) {
                Ok(b) => return unsafe { b.as_ref() }.unwrap(),
                Err(CompareAndSetError { new, .. }) => maybe_new_table = Some(new),
            }
        }
    }

    fn swing(&self, guard: &'g Guard, mut current_ref: &'g Table<K, V>, min_ref: &'g Table<K, V>) {
        let min_epoch = min_ref.epoch;

        let mut current_ptr = (current_ref as *const Table<K, V>).into();
        let min_ptr: Shared<'g, _> = (min_ref as *const Table<K, V>).into();

        loop {
            if current_ref.epoch >= min_epoch {
                return;
            }

            match self.table.compare_and_set_weak(
                current_ptr,
                min_ptr,
                (Ordering::Release, Ordering::Relaxed),
                guard,
            ) {
                Ok(_) => unsafe {
                    guard.defer_unchecked(move || {
                        atomic::fence(Ordering::Acquire);
                        mem::drop(current_ptr.into_owned());
                    })
                },
                Err(_) => {
                    let new_ptr = self.table.load_consume(guard);
                    assert!(!new_ptr.is_null());

                    current_ptr = new_ptr;
                    current_ref = unsafe { new_ptr.as_ref() }.unwrap();
                }
            }
        }
    }
}
