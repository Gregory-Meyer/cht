// Copyright (C) 2020 Gregory Meyer
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Affero General Public License for more details.
//
// You should have received a copy of the GNU Affero General Public License
// along with this program.  If not, see <https://www.gnu.org/licenses/>.

//! A lockfree hash map implemented with bucket pointer arrays, open addressing,
//! and linear probing.

pub(crate) mod bucket;
pub(crate) mod bucket_array_ref;

use bucket::BucketArray;
use bucket_array_ref::BucketArrayRef;

use std::{
    borrow::Borrow,
    collections::hash_map::RandomState,
    error::Error,
    fmt::{self, Display, Formatter},
    hash::{BuildHasher, Hash},
    marker::PhantomData,
    sync::atomic::{self, AtomicUsize, Ordering},
};

use crossbeam_epoch::{self, Atomic, Guard};

#[cfg(feature = "serde")]
use serde::{
    de::{Deserialize, Deserializer, MapAccess, Visitor},
    ser::{Serialize, SerializeMap, Serializer},
};

/// Default hasher for `HashMap`.
pub type DefaultHashBuilder = RandomState;

/// A lockfree hash map implemented with bucket pointer arrays, open addressing,
/// and linear probing.
///
/// The default hashing algorithm is currently [`AHash`], though this is
/// subject to change at any point in the future. This hash function is very
/// fast for all types of keys, but this algorithm will typically *not* protect
/// against attacks such as HashDoS.
///
/// The hashing algorithm can be replaced on a per-`HashMap` basis using the
/// [`default`], [`with_hasher`], and [`with_capacity_and_hasher`] methods. Many
/// alternative algorithms are available on crates.io, such as the [`fnv`] crate.
///
/// It is required that the keys implement the [`Eq`] and [`Hash`] traits,
/// although this can frequently be achieved by using
/// `#[derive(PartialEq, Eq, Hash)]`. If you implement these yourself, it is
/// important that the following property holds:
///
/// ```text
/// k1 == k2 -> hash(k1) == hash(k2)
/// ```
///
/// In other words, if two keys are equal, their hashes must be equal.
///
/// It is a logic error for a key to be modified in such a way that the key's
/// hash, as determined by the [`Hash`] trait, or its equality, as determined by
/// the [`Eq`] trait, changes while it is in the map. This is normally only
/// possible through [`Cell`], [`RefCell`], global state, I/O, or unsafe code.
///
/// [`AHash`]: https://crates.io/crates/ahash
/// [`fnv`]: https://crates.io/crates/fnv
/// [`default`]: #method.default
/// [`with_hasher`]: #method.with_hasher
/// [`with_capacity_and_hasher`]: #method.with_capacity_and_hasher
/// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
/// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
/// [`Cell`]: https://doc.rust-lang.org/std/cell/struct.Ref.html
/// [`RefCell`]: https://doc.rust-lang.org/std/cell/struct.RefCell.html
#[derive(Default)]
pub struct HashMap<K, V, S = DefaultHashBuilder> {
    bucket_array: Atomic<bucket::BucketArray<K, V>>,
    build_hasher: S,
    len: AtomicUsize,
}

impl<K, V> HashMap<K, V, DefaultHashBuilder> {
    /// Creates an empty `HashMap`.
    ///
    /// The hash map is initially created with a capacity of 0, so it will not
    /// allocate a bucket pointer array until it is first inserted into.
    pub fn new() -> HashMap<K, V, DefaultHashBuilder> {
        HashMap::with_capacity_and_hasher(0, DefaultHashBuilder::default())
    }

    /// Creates an empty `HashMap` with the specified capacity.
    ///
    /// The hash map will be able to hold at least `capacity` elements without
    /// reallocating its bucket pointer array. If `capacity` is 0, the hash map
    /// will not allocate.
    pub fn with_capacity(capacity: usize) -> HashMap<K, V, DefaultHashBuilder> {
        HashMap::with_capacity_and_hasher(capacity, DefaultHashBuilder::default())
    }
}

impl<K, V, S> HashMap<K, V, S> {
    /// Creates an empty `HashMap` which will use the given hash builder to hash
    /// keys.
    ///
    /// The hash map is initially created with a capacity of 0, so it will not
    /// allocate a bucket pointer array until it is first inserted into.
    pub fn with_hasher(build_hasher: S) -> HashMap<K, V, S> {
        HashMap::with_capacity_and_hasher(0, build_hasher)
    }

    /// Creates an empty `HashMap` with the specified capacity, using
    /// `build_hasher` to hash the keys.
    ///
    /// The hash map will be able to hold at least `capacity` elements without
    /// reallocating its bucket pointer array. If `capacity` is 0, the hash map
    /// will not allocate.
    pub fn with_capacity_and_hasher(capacity: usize, build_hasher: S) -> HashMap<K, V, S> {
        let bucket_array = if capacity == 0 {
            Atomic::null()
        } else {
            Atomic::new(BucketArray::with_length(
                0,
                (capacity * 2).next_power_of_two(),
            ))
        };

        Self {
            bucket_array,
            build_hasher,
            len: AtomicUsize::new(0),
        }
    }

    /// Returns the number of elements in the map.
    ///
    /// # Safety
    ///
    /// This method on its own is safe, but other threads can add or remove
    /// elements at any time.
    pub fn len(&self) -> usize {
        self.len.load(Ordering::Relaxed)
    }

    /// Returns `true` if the map contains no elements.
    ///
    /// # Safety
    ///
    /// This method on its own is safe, but other threads can add or remove
    /// elements at any time.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the number of elements the map can hold without reallocating its
    /// bucket pointer array.
    ///
    /// Note that all mutating operations except removal will result in a bucket
    /// being allocated or reallocated.
    ///
    /// # Safety
    ///
    /// This method on its own is safe, but other threads can increase the
    /// capacity at any time by adding elements.
    pub fn capacity(&self) -> usize {
        let guard = &crossbeam_epoch::pin();

        let bucket_array_ptr = self.bucket_array.load_consume(guard);

        unsafe { bucket_array_ptr.as_ref() }
            .map(BucketArray::capacity)
            .unwrap_or(0)
    }

    pub fn raw_iter(&self) -> RawIter<K, V> {
        let guard = crossbeam_epoch::pin();

        let bucket_array_ptr = self.bucket_array.load_consume(&guard).as_raw();

        if bucket_array_ptr.is_null() {
            RawIter {
                inner: RawIterInner::Empty,
            }
        } else {
            RawIter {
                inner: RawIterInner::Referenced {
                    guard,
                    bucket_array_ptr,
                    index: 0,
                    phantom: PhantomData,
                },
            }
        }
    }
}

pub struct EntryRef<'a, K, V> {
    #[allow(dead_code)]
    guard: Guard,
    bucket_ptr: *const bucket::Bucket<K, V>,
    phantom: PhantomData<&'a HashMap<K, V>>,
}

impl<'a, K, V> EntryRef<'a, K, V> {
    pub fn key(&self) -> &K {
        let bucket_ref = unsafe { self.bucket_ptr.as_ref() }.unwrap();

        &bucket_ref.key
    }

    pub fn value(&self) -> &V {
        let bucket_ref = unsafe { self.bucket_ptr.as_ref() }.unwrap();

        unsafe { &*bucket_ref.maybe_value.as_ptr() }
    }

    pub fn entry(&self) -> (&K, &V) {
        let bucket_ref = unsafe { self.bucket_ptr.as_ref() }.unwrap();

        (&bucket_ref.key, unsafe {
            &*bucket_ref.maybe_value.as_ptr()
        })
    }
}

pub struct RawIter<'a, K, V> {
    inner: RawIterInner<'a, K, V>,
}

impl<'a, K, V> Iterator for RawIter<'a, K, V> {
    type Item = Result<EntryRef<'a, K, V>, RestartIterationError>;

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.inner {
            RawIterInner::Empty => None,
            RawIterInner::Referenced {
                bucket_array_ptr,
                index,
                ..
            } => {
                let guard = crossbeam_epoch::pin();
                let bucket_array_ref = unsafe { bucket_array_ptr.as_ref() }.unwrap();

                while *index < bucket_array_ref.buckets.len() {
                    match unsafe { bucket_array_ref.get_index_unchecked(&guard, *index) } {
                        Ok(bucket_ptr) if bucket_ptr.is_null() => {
                            *index += 1;

                            continue;
                        }
                        Ok(bucket_ptr) => {
                            let bucket_ptr = bucket_ptr.as_raw();
                            *index += 1;

                            return Some(Ok(EntryRef {
                                guard,
                                bucket_ptr,
                                phantom: PhantomData,
                            }));
                        }
                        Err(_) => {
                            self.inner = RawIterInner::Empty;

                            return Some(Err(RestartIterationError));
                        }
                    }
                }

                self.inner = RawIterInner::Empty;

                None
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match &self.inner {
            RawIterInner::Empty => (0, Some(0)),
            RawIterInner::Referenced {
                bucket_array_ptr,
                index,
                ..
            } => (
                0,
                Some(unsafe { bucket_array_ptr.as_ref() }.unwrap().buckets.len() - *index),
            ),
        }
    }
}

enum RawIterInner<'a, K, V> {
    Empty,
    Referenced {
        #[allow(dead_code)]
        guard: Guard,
        bucket_array_ptr: *const bucket::BucketArray<K, V>,
        index: usize,
        phantom: PhantomData<&'a HashMap<K, V>>,
    },
}

#[derive(Debug)]
pub struct RestartIterationError;

impl Display for RestartIterationError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.write_str("table resized while iterating")
    }
}

impl Error for RestartIterationError {}

impl<K: Hash + Eq, V, S: BuildHasher> HashMap<K, V, S> {
    /// Returns a clone of the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    #[inline]
    pub fn get<Q: Hash + Eq + ?Sized>(&self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        V: Clone,
    {
        self.get_key_value_and(key, |_, v| v.clone())
    }

    /// Returns a clone of the the key-value pair corresponding to the supplied
    /// key.
    ///
    /// The supplied key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for the key
    /// type.
    ///
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    #[inline]
    pub fn get_key_value<Q: Hash + Eq + ?Sized>(&self, key: &Q) -> Option<(K, V)>
    where
        K: Borrow<Q> + Clone,
        V: Clone,
    {
        self.get_key_value_and(key, |k, v| (k.clone(), v.clone()))
    }

    /// Returns the result of invoking a function with a reference to the value
    /// corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    #[inline]
    pub fn get_and<Q: Hash + Eq + ?Sized, F: FnOnce(&V) -> T, T>(
        &self,
        key: &Q,
        with_value: F,
    ) -> Option<T>
    where
        K: Borrow<Q>,
    {
        self.get_key_value_and(key, move |_, v| with_value(v))
    }

    /// Returns the result of invoking a function with a reference to the
    /// key-value pair corresponding to the supplied key.
    ///
    /// The supplied key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for the key
    /// type.
    ///
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    #[inline]
    pub fn get_key_value_and<Q: Hash + Eq + ?Sized, F: FnOnce(&K, &V) -> T, T>(
        &self,
        key: &Q,
        with_entry: F,
    ) -> Option<T>
    where
        K: Borrow<Q>,
    {
        let hash = bucket::hash(&self.build_hasher, &key);

        self.bucket_array_ref()
            .get_key_value_and(key, hash, with_entry)
    }

    /// Inserts a key-value pair into the map, returning a clone of the value
    /// previously corresponding to the key.
    ///
    /// If the map did have this key present, both the key and value are
    /// updated.
    #[inline]
    pub fn insert(&self, key: K, value: V) -> Option<V>
    where
        V: Clone,
    {
        self.insert_entry_and(key, value, |_, v| v.clone())
    }

    /// Inserts a key-value pair into the map, returning a clone of the
    /// key-value pair previously corresponding to the supplied key.
    ///
    /// If the map did have this key present, both the key and value are
    /// updated.
    #[inline]
    pub fn insert_entry(&self, key: K, value: V) -> Option<(K, V)>
    where
        K: Clone,
        V: Clone,
    {
        self.insert_entry_and(key, value, |k, v| (k.clone(), v.clone()))
    }

    /// Inserts a key-value pair into the map, returning the result of invoking
    /// a function with a reference to the value previously corresponding to the
    /// key.
    ///
    /// If the map did have this key present, both the key and value are
    /// updated.
    #[inline]
    pub fn insert_and<F: FnOnce(&V) -> T, T>(
        &self,
        key: K,
        value: V,
        with_previous_value: F,
    ) -> Option<T> {
        self.insert_entry_and(key, value, move |_, v| with_previous_value(v))
    }

    /// Inserts a key-value pair into the map, returning the result of invoking
    /// a function with a reference to the key-value pair previously
    /// corresponding to the supplied key.
    ///
    /// If the map did have this key present, both the key and value are
    /// updated.
    #[inline]
    pub fn insert_entry_and<F: FnOnce(&K, &V) -> T, T>(
        &self,
        key: K,
        value: V,
        with_previous_entry: F,
    ) -> Option<T> {
        let hash = bucket::hash(&self.build_hasher, &key);

        self.bucket_array_ref()
            .insert_entry_and(key, hash, value, with_previous_entry)
    }

    /// Removes a key from the map, returning a clone of the value previously
    /// corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    #[inline]
    pub fn remove<Q: Hash + Eq + ?Sized>(&self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        V: Clone,
    {
        self.remove_entry_if_and(key, |_, _| true, |_, v| v.clone())
    }

    /// Removes a key from the map, returning a clone of the key-value pair
    /// previously corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    #[inline]
    pub fn remove_entry<Q: Hash + Eq + ?Sized>(&self, key: &Q) -> Option<(K, V)>
    where
        K: Borrow<Q> + Clone,
        V: Clone,
    {
        self.remove_entry_if_and(key, |_, _| true, |k, v| (k.clone(), v.clone()))
    }

    /// Remove a key from the map, returning the result of invoking a function
    /// with a reference to the value previously corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    #[inline]
    pub fn remove_and<Q: Hash + Eq + ?Sized, F: FnOnce(&V) -> T, T>(
        &self,
        key: &Q,
        with_previous_value: F,
    ) -> Option<T>
    where
        K: Borrow<Q>,
    {
        self.remove_entry_if_and(key, |_, _| true, move |_, v| with_previous_value(v))
    }

    /// Removes a key from the map, returning the result of invoking a function
    /// with a reference to the key-value pair previously corresponding to the
    /// key.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    #[inline]
    pub fn remove_entry_and<Q: Hash + Eq + ?Sized, F: FnOnce(&K, &V) -> T, T>(
        &self,
        key: &Q,
        with_previous_entry: F,
    ) -> Option<T>
    where
        K: Borrow<Q>,
    {
        self.remove_entry_if_and(key, |_, _| true, with_previous_entry)
    }

    /// Removes a key from the map if a condition is met, returning a clone of
    /// the value previously corresponding to the key.
    ///
    /// `condition` will be invoked at least once if [`Some`] is returned. It
    /// may also be invoked one or more times if [`None`] is returned.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    /// [`Some`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.Some
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    pub fn remove_if<Q: Hash + Eq + ?Sized, F: FnMut(&K, &V) -> bool>(
        &self,
        key: &Q,
        condition: F,
    ) -> Option<V>
    where
        K: Borrow<Q>,
        V: Clone,
    {
        self.remove_entry_if_and(key, condition, move |_, v| v.clone())
    }

    /// Removes a key from the map if a condition is met, returning a clone of
    /// the key-value pair previously corresponding to the key.
    ///
    /// `condition` will be invoked at least once if [`Some`] is returned. It
    /// may also be invoked one or more times if [`None`] is returned.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    /// [`Some`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.Some
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    #[inline]
    pub fn remove_entry_if<Q: Hash + Eq + ?Sized, F: FnMut(&K, &V) -> bool>(
        &self,
        key: &Q,
        condition: F,
    ) -> Option<(K, V)>
    where
        K: Clone + Borrow<Q>,
        V: Clone,
    {
        self.remove_entry_if_and(key, condition, move |k, v| (k.clone(), v.clone()))
    }

    /// Remove a key from the map if a condition is met, returning the result of
    /// invoking a function with a reference to the value previously
    /// corresponding to the key.
    ///
    /// `condition` will be invoked at least once if [`Some`] is returned. It
    /// may also be invoked one or more times if [`None`] is returned.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    /// [`Some`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.Some
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    #[inline]
    pub fn remove_if_and<Q: Hash + Eq + ?Sized, F: FnMut(&K, &V) -> bool, G: FnOnce(&V) -> T, T>(
        &self,
        key: &Q,
        condition: F,
        with_previous_value: G,
    ) -> Option<T>
    where
        K: Borrow<Q>,
    {
        self.remove_entry_if_and(key, condition, move |_, v| with_previous_value(v))
    }

    /// Removes a key from the map if a condition is met, returning the result
    /// of invoking a function with a reference to the key-value pair previously
    /// corresponding to the key.
    ///
    /// `condition` will be invoked at least once if [`Some`] is returned. It
    /// may also be invoked one or more times if [`None`] is returned.
    ///
    /// The key may be any borrowed form of the map's key type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the key type.
    ///
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    /// [`Some`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.Some
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    #[inline]
    pub fn remove_entry_if_and<
        Q: Hash + Eq + ?Sized,
        F: FnMut(&K, &V) -> bool,
        G: FnOnce(&K, &V) -> T,
        T,
    >(
        &self,
        key: &Q,
        condition: F,
        with_previous_entry: G,
    ) -> Option<T>
    where
        K: Borrow<Q>,
    {
        let hash = bucket::hash(&self.build_hasher, &key);

        self.bucket_array_ref()
            .remove_entry_if_and(key, hash, condition, with_previous_entry)
    }

    /// If no value corresponds to the key, insert a new key-value pair into
    /// the map. Otherwise, modify the existing value and return a clone of the
    /// value previously corresponding to the key.
    ///
    /// `on_modify` will be invoked at least once if [`Some`] is returned. It
    /// may also be invoked one or more times if [`None`] is returned.
    ///
    /// [`Some`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.Some
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    #[inline]
    pub fn insert_or_modify<F: FnMut(&K, &V) -> V>(
        &self,
        key: K,
        value: V,
        on_modify: F,
    ) -> Option<V>
    where
        V: Clone,
    {
        self.insert_with_or_modify_entry_and(key, move || value, on_modify, |_, v| v.clone())
    }

    /// If no value corresponds to the key, insert a new key-value pair into
    /// the map. Otherwise, modify the existing value and return a clone of the
    /// key-value pair previously corresponding to the key.
    ///
    /// `on_modify` will be invoked at least once if [`Some`] is returned. It
    /// may also be invoked one or more times if [`None`] is returned.
    ///
    /// [`Some`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.Some
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    #[inline]
    pub fn insert_or_modify_entry<F: FnMut(&K, &V) -> V>(
        &self,
        key: K,
        value: V,
        on_modify: F,
    ) -> Option<(K, V)>
    where
        K: Clone,
        V: Clone,
    {
        self.insert_with_or_modify_entry_and(
            key,
            move || value,
            on_modify,
            |k, v| (k.clone(), v.clone()),
        )
    }

    /// If no value corresponds to the key, invoke a default function to insert
    /// a new key-value pair into the map. Otherwise, modify the existing value
    /// and return a clone of the value previously corresponding to the key.
    ///
    /// `on_insert` may be invoked, even if [`None`] is returned.
    ///
    /// `on_modify` will be invoked at least once if [`Some`] is returned. It
    /// may also be invoked one or more times if [`None`] is returned.
    ///
    /// [`Some`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.Some
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    #[inline]
    pub fn insert_with_or_modify<F: FnOnce() -> V, G: FnMut(&K, &V) -> V>(
        &self,
        key: K,
        on_insert: F,
        on_modify: G,
    ) -> Option<V>
    where
        V: Clone,
    {
        self.insert_with_or_modify_entry_and(key, on_insert, on_modify, |_, v| v.clone())
    }

    /// If no value corresponds to the key, invoke a default function to insert
    /// a new key-value pair into the map. Otherwise, modify the existing value
    /// and return a clone of the key-value pair previously corresponding to the
    /// key.
    ///
    /// `on_insert` may be invoked, even if [`None`] is returned.
    ///
    /// `on_modify` will be invoked at least once if [`Some`] is returned. It
    /// may also be invoked one or more times if [`None`] is returned.
    ///
    /// [`Some`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.Some
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    #[inline]
    pub fn insert_with_or_modify_entry<F: FnOnce() -> V, G: FnMut(&K, &V) -> V>(
        &self,
        key: K,
        on_insert: F,
        on_modify: G,
    ) -> Option<(K, V)>
    where
        K: Clone,
        V: Clone,
    {
        self.insert_with_or_modify_entry_and(key, on_insert, on_modify, |k, v| {
            (k.clone(), v.clone())
        })
    }

    /// If no value corresponds to the key, insert a new key-value pair into
    /// the map. Otherwise, modify the existing value and return the result of
    /// invoking a function with a reference to the value previously
    /// corresponding to the key.
    ///
    /// `on_modify` will be invoked at least once if [`Some`] is returned. It
    /// may also be invoked one or more times if [`None`] is returned.
    ///
    /// [`Some`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.Some
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    #[inline]
    pub fn insert_or_modify_and<F: FnMut(&K, &V) -> V, G: FnOnce(&V) -> T, T>(
        &self,
        key: K,
        value: V,
        on_modify: F,
        with_old_value: G,
    ) -> Option<T> {
        self.insert_with_or_modify_entry_and(
            key,
            move || value,
            on_modify,
            move |_, v| with_old_value(v),
        )
    }

    /// If no value corresponds to the key, insert a new key-value pair into
    /// the map. Otherwise, modify the existing value and return the result of
    /// invoking a function with a reference to the key-value pair previously
    /// corresponding to the supplied key.
    ///
    /// `on_modify` will be invoked at least once if [`Some`] is returned. It
    /// may also be invoked one or more times if [`None`] is returned.
    ///
    /// [`Some`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.Some
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    #[inline]
    pub fn insert_or_modify_entry_and<F: FnMut(&K, &V) -> V, G: FnOnce(&K, &V) -> T, T>(
        &self,
        key: K,
        value: V,
        on_modify: F,
        with_old_entry: G,
    ) -> Option<T> {
        self.insert_with_or_modify_entry_and(key, move || value, on_modify, with_old_entry)
    }

    /// If no value corresponds to the key, invoke a default function to insert
    /// a new key-value pair into the map. Otherwise, modify the existing value
    /// and return the result of invoking a function with a reference to the
    /// value previously corresponding to the key.
    ///
    /// `on_insert` may be invoked, even if [`None`] is returned.
    ///
    /// `on_modify` will be invoked at least once if [`Some`] is returned. It
    /// may also be invoked one or more times if [`None`] is returned.
    ///
    /// [`Some`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.Some
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    #[inline]
    pub fn insert_with_or_modify_and<
        F: FnOnce() -> V,
        G: FnMut(&K, &V) -> V,
        H: FnOnce(&V) -> T,
        T,
    >(
        &self,
        key: K,
        on_insert: F,
        on_modify: G,
        with_old_value: H,
    ) -> Option<T> {
        self.insert_with_or_modify_entry_and(key, on_insert, on_modify, move |_, v| {
            with_old_value(v)
        })
    }

    /// If no value corresponds to the key, invoke a default function to insert
    /// a new key-value pair into the map. Otherwise, modify the existing value
    /// and return the result of invoking a function with a reference to the
    /// key-value pair previously corresponding to the supplied key.
    ///
    /// `on_insert` may be invoked, even if [`None`] is returned.
    ///
    /// `on_modify` will be invoked at least once if [`Some`] is returned. It
    /// may also be invoked one or more times if [`None`] is returned.
    ///
    /// [`Some`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.Some
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    #[inline]
    pub fn insert_with_or_modify_entry_and<
        F: FnOnce() -> V,
        G: FnMut(&K, &V) -> V,
        H: FnOnce(&K, &V) -> T,
        T,
    >(
        &self,
        key: K,
        on_insert: F,
        on_modify: G,
        with_old_entry: H,
    ) -> Option<T> {
        let hash = bucket::hash(&self.build_hasher, &key);

        self.bucket_array_ref().insert_with_or_modify_entry_and(
            key,
            hash,
            on_insert,
            on_modify,
            with_old_entry,
        )
    }

    /// Modifies the value corresponding to a key, returning a clone of the
    /// value previously corresponding to that key.
    #[inline]
    pub fn modify<F: FnMut(&K, &V) -> V>(&self, key: K, on_modify: F) -> Option<V>
    where
        V: Clone,
    {
        self.modify_entry_and(key, on_modify, |_, v| v.clone())
    }

    /// Modifies the value corresponding to a key, returning a clone of the
    /// key-value pair previously corresponding to that key.
    #[inline]
    pub fn modify_entry<F: FnMut(&K, &V) -> V>(&self, key: K, on_modify: F) -> Option<(K, V)>
    where
        K: Clone,
        V: Clone,
    {
        self.modify_entry_and(key, on_modify, |k, v| (k.clone(), v.clone()))
    }

    /// Modifies the value corresponding to a key, returning the result of
    /// invoking a function with a reference to the value previously
    /// corresponding to the key.
    #[inline]
    pub fn modify_and<F: FnMut(&K, &V) -> V, G: FnOnce(&V) -> T, T>(
        &self,
        key: K,
        on_modify: F,
        with_old_value: G,
    ) -> Option<T> {
        self.modify_entry_and(key, on_modify, move |_, v| with_old_value(v))
    }

    /// Modifies the value corresponding to a key, returning the result of
    /// invoking a function with a reference to the key-value pair previously
    /// corresponding to the supplied key.
    #[inline]
    pub fn modify_entry_and<F: FnMut(&K, &V) -> V, G: FnOnce(&K, &V) -> T, T>(
        &self,
        key: K,
        on_modify: F,
        with_old_entry: G,
    ) -> Option<T> {
        let hash = bucket::hash(&self.build_hasher, &key);

        self.bucket_array_ref()
            .modify_entry_and(key, hash, on_modify, with_old_entry)
    }
}

impl<K, V, S> HashMap<K, V, S> {
    #[inline]
    fn bucket_array_ref(&'_ self) -> BucketArrayRef<'_, K, V, S> {
        BucketArrayRef {
            bucket_array: &self.bucket_array,
            build_hasher: &self.build_hasher,
            len: &self.len,
        }
    }
}

impl<K, V, S> Drop for HashMap<K, V, S> {
    fn drop(&mut self) {
        let guard = unsafe { &crossbeam_epoch::unprotected() };
        atomic::fence(Ordering::Acquire);

        let mut current_ptr = self.bucket_array.load(Ordering::Relaxed, guard);

        while let Some(current_ref) = unsafe { current_ptr.as_ref() } {
            let next_ptr = current_ref.next.load(Ordering::Relaxed, guard);

            for this_bucket_ptr in current_ref
                .buckets
                .iter()
                .map(|b| b.load(Ordering::Relaxed, guard))
                .filter(|p| !p.is_null())
                .filter(|p| next_ptr.is_null() || p.tag() & bucket::TOMBSTONE_TAG == 0)
            {
                // only delete tombstones from the newest bucket array
                // the only way this becomes a memory leak is if there was a panic during a rehash,
                // in which case i'm going to say that running destructors and freeing memory is
                // best-effort, and my best effort is to not do it
                unsafe { bucket::defer_acquire_destroy(guard, this_bucket_ptr) };
            }

            unsafe { bucket::defer_acquire_destroy(guard, current_ptr) };

            current_ptr = next_ptr;
        }
    }
}

#[cfg(feature = "serde")]
impl<K: Serialize, V: Serialize, H> Serialize for HashMap<K, V, H> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut contents = Vec::with_capacity(self.len());

        {
            let mut raw_iter = self.raw_iter();

            loop {
                match raw_iter.next() {
                    Some(Ok(entry)) => {
                        contents.push(entry);
                    }
                    Some(Err(_)) => {
                        contents.clear();
                        raw_iter = self.raw_iter();
                    }
                    None => {
                        break; // done!
                    }
                }
            }
        }

        let mut map = serializer.serialize_map(Some(contents.len()))?;

        for entry in contents.into_iter() {
            map.serialize_entry(entry.key(), entry.value())?;
        }

        map.end()
    }
}

#[cfg(feature = "serde")]
impl<'de, K: Deserialize<'de> + Eq + Hash, V: Deserialize<'de>, H: BuildHasher + Default>
    Deserialize<'de> for HashMap<K, V, H>
{
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct MapVisitor<K, V, H> {
            phantom: PhantomData<HashMap<K, V, H>>,
        }

        impl<
                'de,
                K: Deserialize<'de> + Eq + Hash,
                V: Deserialize<'de>,
                H: BuildHasher + Default,
            > Visitor<'de> for MapVisitor<K, V, H>
        {
            type Value = HashMap<K, V, H>;

            fn expecting(&self, formatter: &mut Formatter) -> fmt::Result {
                formatter.write_str("a map")
            }

            fn visit_map<M: MapAccess<'de>>(self, mut access: M) -> Result<Self::Value, M::Error> {
                let map = HashMap::with_capacity_and_hasher(
                    access.size_hint().unwrap_or(0),
                    H::default(),
                );

                while let Some((key, value)) = access.next_entry()? {
                    map.insert_entry_and(key, value, |_, _| ());
                }

                Ok(map)
            }
        }

        deserializer.deserialize_map(MapVisitor {
            phantom: PhantomData,
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::write_test_cases_for_me;

    use super::*;

    write_test_cases_for_me!(HashMap);

    #[test]
    fn raw_iter() {
        let map = HashMap::new();

        let mut raw_iter = map.raw_iter();
        assert!(raw_iter.next().is_none());
        assert_eq!(raw_iter.size_hint(), (0, Some(0)));

        map.insert(0, 0);
        map.insert(5, 5);
        map.insert(10, 10);
        map.insert(15, 15);

        let mut raw_iter = map.raw_iter();
        let mut elems = Vec::with_capacity(map.len());

        for i in 0..4 {
            assert!(raw_iter.size_hint().1.unwrap() >= 4 - i);
            elems.push(raw_iter.next().unwrap().unwrap());
        }

        assert!(raw_iter.next().is_none());
        assert_eq!(raw_iter.size_hint(), (0, Some(0)));

        elems.sort_by(|lhs, rhs| lhs.key().cmp(rhs.key()));
        assert_eq!(
            elems
                .into_iter()
                .map(|entry| (*entry.key(), *entry.value()))
                .collect::<Vec<_>>(),
            [(0, 0), (5, 5), (10, 10), (15, 15)]
        );

        // resize while holding an iterator
        raw_iter = map.raw_iter();

        for i in 4..512 {
            map.insert(i * 5, i * 5);
        }

        let should_not_be_an_elem = raw_iter.next();
        assert!(should_not_be_an_elem.is_some());
        assert!(should_not_be_an_elem.unwrap().is_err());

        let should_be_none = raw_iter.next();
        assert!(should_be_none.is_none());
    }

    #[test]
    fn serialize() {
        let map = HashMap::<i32, i32>::new();

        map.insert(0, 0);
        map.insert(5, 5);
        map.insert(10, 10);
        map.insert(15, 15);

        let json = serde_json::to_string(&map).unwrap();
        let deserialized_map: std::collections::HashMap<i32, i32> =
            serde_json::from_str(&json).unwrap();

        assert_eq!(map.len(), deserialized_map.len());

        for (key, value) in deserialized_map.iter() {
            assert_eq!(map.get(key).unwrap(), *value);
        }
    }

    #[test]
    fn deserialize() {
        let mut to_serialize = std::collections::HashMap::<i32, i32>::new();

        to_serialize.insert(0, 0);
        to_serialize.insert(5, 5);
        to_serialize.insert(10, 10);
        to_serialize.insert(15, 15);

        let json = serde_json::to_string(&to_serialize).unwrap();
        let map: HashMap<i32, i32> = serde_json::from_str(&json).unwrap();

        assert_eq!(to_serialize.len(), map.len());

        for (key, value) in to_serialize.iter() {
            assert_eq!(map.get(key).unwrap(), *value);
        }
    }
}
