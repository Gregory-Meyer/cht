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

//! A lockfree hash map implemented with segmented bucket pointer arrays, open
//! addressing, and linear probing.

use crate::map::{
    bucket::{self, BucketArray},
    bucket_array_ref::BucketArrayRef,
    DefaultHashBuilder,
};

use std::{
    borrow::Borrow,
    hash::{BuildHasher, Hash},
    ptr,
    sync::atomic::{self, AtomicUsize, Ordering},
};

use crossbeam_epoch::Atomic;

/// A lockfree hash map implemented with segmented bucket pointer arrays, open
/// addressing, and linear probing.
///
/// The default hashing algorithm is currently [`AHash`], though this is
/// subject to change at any point in the future. This hash function is very
/// fast for all types of keys, but this algorithm will typically *not* protect
/// against attacks such as HashDoS.
///
/// The hashing algorithm can be replaced on a per-`HashMap` basis using the
/// [`default`], [`with_hasher`], [`with_capacity_and_hasher`],
/// [`with_num_segments_and_hasher`], and
/// [`with_num_segments_capacity_and_hasher`] methods. Many alternative
/// algorithms are available on crates.io, such as the [`fnv`] crate.
///
/// The number of segments can be specified on a per-`HashMap` basis using the
/// [`with_num_segments`], [`with_num_segments_and_capacity`],
/// [`with_num_segments_and_hasher`], and
/// [`with_num_segments_capacity_and_hasher`] methods. By default, the
/// `num-cpus` feature is enabled and [`new`], [`with_capacity`],
/// [`with_hasher`], and [`with_capacity_and_hasher`] will create maps with
/// twice as many segments as the system has CPUs.
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
/// [`with_capacity`]: #method.with_capacity
/// [`with_capacity_and_hasher`]: #method.with_capacity_and_hasher
/// [`with_num_segments_and_hasher`]: #method.with_num_segments_and_hasher
/// [`with_num_segments_capacity_and_hasher`]: #method.with_num_segments_capacity_and_hasher
/// [`with_num_segments`]: #method.with_num_segments
/// [`with_num_segments_and_capacity`]: #method.with_num_segments_and_capacity
/// [`new`]: #method.new
/// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
/// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
/// [`Cell`]: https://doc.rust-lang.org/std/cell/struct.Ref.html
/// [`RefCell`]: https://doc.rust-lang.org/std/cell/struct.RefCell.html
pub struct HashMap<K, V, S = DefaultHashBuilder> {
    segments: Box<[Segment<K, V>]>,
    build_hasher: S,
    len: AtomicUsize,
    segment_shift: u32,
}

#[cfg(feature = "num-cpus")]
impl<K, V> HashMap<K, V, DefaultHashBuilder> {
    /// Creates an empty `HashMap`.
    ///
    /// The hash map is created with a capacity of 0 and no memory for segments
    /// will be allocated until the first insertion to each segment. However,
    /// memory will always be allocated to store segment pointers and lengths.
    ///
    /// The `HashMap` will be created with at least twice as many segments as
    /// the system has CPUs.
    pub fn new() -> Self {
        Self::with_num_segments_capacity_and_hasher(
            default_num_segments(),
            0,
            DefaultHashBuilder::default(),
        )
    }

    /// Creates an empty `HashMap` with space for at least `capacity` elements
    /// without reallocating.
    ///
    /// If `capacity == 0`, no memory for segments will be allocated until the
    /// first insertion to each segment. However, memory will always be
    /// allocated to store segment pointers and lengths.
    ///
    /// The `HashMap` will be created with at least twice as many segments as
    /// the system has CPUs.
    pub fn with_capacity(capacity: usize) -> Self {
        Self::with_num_segments_capacity_and_hasher(
            default_num_segments(),
            capacity,
            DefaultHashBuilder::default(),
        )
    }
}

#[cfg(feature = "num-cpus")]
impl<K, V, S: BuildHasher> HashMap<K, V, S> {
    /// Creates an empty `HashMap` which will use the given hash builder to hash
    /// keys.
    ///
    /// The hash map is initially created with a capacity of 0, so it will not
    /// allocate bucket pointer arrays until it is first inserted into. However,
    /// it will always allocate memory for segment pointers and lengths.
    ///
    /// The `HashMap` will be created with at least twice as many segments as
    /// the system has CPUs.
    pub fn with_hasher(build_hasher: S) -> Self {
        Self::with_num_segments_capacity_and_hasher(default_num_segments(), 0, build_hasher)
    }

    /// Creates an empty `HashMap` with the specified capacity, using
    /// `build_hasher` to hash the keys.
    ///
    /// The hash map will be able to hold at least `capacity` elements without
    /// reallocating any bucket pointer arrays. If `capacity` is 0, the hash map
    /// will not allocate any bucket pointer arrays. However, it will always
    /// allocate memory for segment pointers and lengths.
    ///
    /// The `HashMap` will be created with at least twice as many segments as
    /// the system has CPUs.
    pub fn with_capacity_and_hasher(capacity: usize, build_hasher: S) -> Self {
        Self::with_num_segments_capacity_and_hasher(default_num_segments(), capacity, build_hasher)
    }
}

impl<K, V> HashMap<K, V, DefaultHashBuilder> {
    /// Creates an empty `HashMap` with at least `num_segments` segments.
    ///
    /// The hash map is created with a capacity of 0 and no memory for segments
    /// will be allocated until the first insertion to each segment. However,
    /// memory will always be allocated to store segment pointers and lengths.
    ///
    /// # Panics
    ///
    /// Panics if `num_segments == 0`.
    pub fn with_num_segments(num_segments: usize) -> Self {
        Self::with_num_segments_capacity_and_hasher(num_segments, 0, DefaultHashBuilder::default())
    }

    /// Creates an empty `HashMap` with at least `num_segments` segments and
    /// space for at least `capacity` elements in each segment without
    /// reallocating.
    ///
    /// If `capacity == 0`, no memory for segments will be allocated until the
    /// first insertion to each segment. However, memory will always be
    /// allocated to store segment pointers and lengths.
    ///
    /// # Panics
    ///
    /// Panics if `num_segments == 0`.
    pub fn with_num_segments_and_capacity(num_segments: usize, capacity: usize) -> Self {
        Self::with_num_segments_capacity_and_hasher(
            num_segments,
            capacity,
            DefaultHashBuilder::default(),
        )
    }
}

impl<K, V, S> HashMap<K, V, S> {
    /// Creates an empty `HashMap` that will use `build_hasher` to hash keys
    /// with at least `num_segments` segments.
    ///
    /// The hash map is created with a capacity of 0 and no memory for segments
    /// will be allocated until the first insertion to each segment. However,
    /// memory will always be allocated to store segment pointers and lengths.
    ///
    /// # Panics
    ///
    /// Panics if `num_segments == 0`.
    pub fn with_num_segments_and_hasher(num_segments: usize, build_hasher: S) -> Self {
        Self::with_num_segments_capacity_and_hasher(num_segments, 0, build_hasher)
    }

    /// Creates an empty `HashMap` that will use `build_hasher` to hash keys,
    /// hold at least `capacity` elements without reallocating, and have at
    /// least `num_segments` segments.
    ///
    /// If `capacity == 0`, no memory for segments will be allocated until the
    /// first insertion to each segment. However, memory will always be
    /// allocated to store segment pointers and lengths.
    ///
    /// # Panics
    ///
    /// Panics if `num_segments == 0`.
    pub fn with_num_segments_capacity_and_hasher(
        num_segments: usize,
        capacity: usize,
        build_hasher: S,
    ) -> Self {
        assert!(num_segments > 0);

        let actual_num_segments = num_segments.next_power_of_two();
        let segment_shift = 64 - actual_num_segments.trailing_zeros();

        let mut segments = Vec::with_capacity(actual_num_segments);

        if capacity == 0 {
            unsafe {
                ptr::write_bytes(segments.as_mut_ptr(), 0, actual_num_segments);
                segments.set_len(actual_num_segments);
            }
        } else {
            let actual_capacity = (capacity * 2).next_power_of_two();

            for _ in 0..actual_num_segments {
                segments.push(Segment {
                    bucket_array: Atomic::new(BucketArray::with_length(0, actual_capacity)),
                    len: AtomicUsize::new(0),
                });
            }
        }

        let segments = segments.into_boxed_slice();

        Self {
            segments,
            build_hasher,
            len: AtomicUsize::new(0),
            segment_shift,
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

    /// Returns the number of elements the map can hold without reallocating a
    /// bucket pointer array.
    ///
    /// As the map is composed of multiple separately allocated segments, this
    /// method returns the minimum capacity of all segments.
    ///
    /// Note that all mutating operations, with the exception of removing
    /// elements, will result in an allocation for a new bucket.
    ///
    /// # Safety
    ///
    /// This method on its own is safe, but other threads can increase the
    /// capacity of each segment at any time by adding elements.
    pub fn capacity(&self) -> usize {
        let guard = &crossbeam_epoch::pin();

        self.segments
            .iter()
            .map(|s| s.bucket_array.load_consume(guard))
            .map(|p| unsafe { p.as_ref() })
            .map(|a| a.map(BucketArray::capacity).unwrap_or(0))
            .min()
            .unwrap()
    }

    /// Returns the number of elements the `index`-th segment of the map can
    /// hold without reallocating a bucket pointer array.
    ///
    /// Note that all mutating operations, with the exception of removing
    /// elements, will result in an allocation for a new bucket.
    ///
    /// # Safety
    ///
    /// This method on its own is safe, but other threads can increase the
    /// capacity of a segment at any time by adding elements.
    pub fn segment_capacity(&self, index: usize) -> usize {
        assert!(index < self.segments.len());

        let guard = &crossbeam_epoch::pin();

        unsafe {
            self.segments[index]
                .bucket_array
                .load_consume(guard)
                .as_ref()
        }
        .map(BucketArray::capacity)
        .unwrap_or(0)
    }

    /// Returns the number of segments in the map.
    pub fn num_segments(&self) -> usize {
        self.segments.len()
    }
}

impl<K, V, S: BuildHasher> HashMap<K, V, S> {
    /// Returns the index of the segment that `key` would belong to if inserted
    /// into the map.
    pub fn segment_index<Q: Hash>(&self, key: &Q) -> usize
    where
        K: Borrow<Q>,
    {
        let hash = bucket::hash(&self.build_hasher, key);

        self.segment_index_from_hash(hash)
    }
}

impl<K: Hash + Eq, V, S: BuildHasher> HashMap<K, V, S> {
    /// Returns a copy of the value associated with `key`.
    ///
    /// `Q` can be any borrowed form of `K`, but [`Hash`] and [`Eq`] on `Q`
    /// *must* match that of `K`. `V` must implement [`Clone`], as other threads
    /// may hold references to the associated value.
    ///
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    /// [`Clone`]: https://doc.rust-lang.org/std/clone/trait.Clone.html
    #[inline]
    pub fn get<Q: Hash + Eq + ?Sized>(&self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        V: Clone,
    {
        self.get_key_value_and(key, |_, v| v.clone())
    }

    /// Returns a copy of the key and value associated with `key`.
    ///
    /// `Q` can be any borrowed form of `K`, but [`Hash`] and [`Eq`] on `Q`
    /// *must* match that of `K`. `K` and `V` must implement [`Clone`], as other
    /// threads may hold references to the entry.
    ///
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    /// [`Clone`]: https://doc.rust-lang.org/std/clone/trait.Clone.html
    #[inline]
    pub fn get_key_value<Q: Hash + Eq + ?Sized>(&self, key: &Q) -> Option<(K, V)>
    where
        K: Borrow<Q> + Clone,
        V: Clone,
    {
        self.get_key_value_and(key, |k, v| (k.clone(), v.clone()))
    }

    /// Invokes `with_value` with a reference to the value associated with `key`.
    ///
    /// If there is no value associated with `key` in the map, `with_value` will
    /// not be invoked and [`None`] will be returned.
    ///
    /// `Q` can be any borrowed form of `K`, but [`Hash`] and [`Eq`] on `Q`
    /// *must* match that of `K`.
    ///
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
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

    /// Invokes `with_entry` with a reference to the key and value associated
    /// with `key`.
    ///
    /// If there is no value associated with `key` in the map, `with_entry` will
    /// not be invoked and [`None`] will be returned.
    ///
    /// `Q` can be any borrowed form of `K`, but [`Hash`] and [`Eq`] on `Q`
    /// *must* match that of `K`.
    ///
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
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

        self.bucket_array_ref(hash)
            .get_key_value_and(key, hash, with_entry)
    }

    /// Inserts a key-value pair, then returns a copy of the value previously
    /// associated with `key`.
    ///
    /// If the key was not previously present in this hash map, [`None`] is
    /// returned.
    ///
    /// `V` must implement [`Clone`], as other threads may hold references to
    /// the associated value.
    ///
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    /// [`Clone`]: https://doc.rust-lang.org/std/clone/trait.Clone.html
    #[inline]
    pub fn insert(&self, key: K, value: V) -> Option<V>
    where
        V: Clone,
    {
        self.insert_entry_and(key, value, |_, v| v.clone())
    }

    /// Inserts a key-value pair, then returns a copy of the previous entry.
    ///
    /// If the key was not previously present in this hash map, [`None`] is
    /// returned.
    ///
    /// `K` and `V` must implement [`Clone`], as other threads may hold
    /// references to the entry.
    ///
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    /// [`Clone`]: https://doc.rust-lang.org/std/clone/trait.Clone.html
    #[inline]
    pub fn insert_entry(&self, key: K, value: V) -> Option<(K, V)>
    where
        K: Clone,
        V: Clone,
    {
        self.insert_entry_and(key, value, |k, v| (k.clone(), v.clone()))
    }

    /// Inserts a key-value pair, then invokes `with_previous_value` with the
    /// value previously associated with `key`.
    ///
    /// If the key was not previously present in this hash map, [`None`] is
    /// returned and `with_previous_value` is not invoked.
    ///
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    #[inline]
    pub fn insert_and<F: FnOnce(&V) -> T, T>(
        &self,
        key: K,
        value: V,
        with_previous_value: F,
    ) -> Option<T> {
        self.insert_entry_and(key, value, move |_, v| with_previous_value(v))
    }

    /// Inserts a key-value pair, then invokes `with_previous_entry` with the
    /// previous entry.
    ///
    /// If the key was not previously present in this hash map, [`None`] is
    /// returned and `with_previous_entry` is not invoked.
    ///
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    #[inline]
    pub fn insert_entry_and<F: FnOnce(&K, &V) -> T, T>(
        &self,
        key: K,
        value: V,
        with_previous_entry: F,
    ) -> Option<T> {
        let hash = bucket::hash(&self.build_hasher, &key);

        let result =
            self.bucket_array_ref(hash)
                .insert_entry_and(key, hash, value, with_previous_entry);

        if result.is_none() {
            self.len.fetch_add(1, Ordering::Relaxed);
        }

        result
    }

    /// If there is a value associated with `key`, remove and return a copy of
    /// it.
    ///
    /// `Q` can be any borrowed form of `K`, but [`Hash`] and [`Eq`] on `Q`
    /// *must* match that of `K`. `V` must implement [`Clone`], as other
    /// threads may hold references to the associated value.
    ///
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    /// [`Clone`]: https://doc.rust-lang.org/std/clone/trait.Clone.html
    #[inline]
    pub fn remove<Q: Hash + Eq + ?Sized>(&self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        V: Clone,
    {
        self.remove_entry_if_and(key, |_, _| true, |_, v| v.clone())
    }

    /// If there is a value associated with `key`, remove it and return a copy
    /// of the previous entity.
    ///
    /// `Q` can be any borrowed form of `K`, but [`Hash`] and [`Eq`] on `Q`
    /// *must* match that of `K`. `K` and `V` must implement [`Clone`], as other
    /// threads may hold references to the entry.
    ///
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    /// [`Clone`]: https://doc.rust-lang.org/std/clone/trait.Clone.html
    #[inline]
    pub fn remove_entry<Q: Hash + Eq + ?Sized>(&self, key: &Q) -> Option<(K, V)>
    where
        K: Borrow<Q> + Clone,
        V: Clone,
    {
        self.remove_entry_if_and(key, |_, _| true, |k, v| (k.clone(), v.clone()))
    }

    /// If there is a value associated with `key`, remove it and return the
    /// result of invoking `with_previous_value` with that value.
    ///
    /// `Q` can be any borrowed form of `K`, but [`Hash`] and [`Eq`] on `Q`
    /// *must* match that of `K`.
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

    /// If there is a value associated with `key`, remove it and return the
    /// result of invoking `with_previous_entry` with that entry.
    ///
    /// `Q` can be any borrowed form of `K`, but [`Hash`] and [`Eq`] on `Q`
    /// *must* match that of `K`.
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

    /// If there is a value associated with `key` and `condition` returns true
    /// when invoked with the current entry, remove and return a copy of its
    /// value.
    ///
    /// `condition` may be invoked one or more times, even if no entry was
    /// removed.
    ///
    /// `Q` can be any borrowed form of `K`, but [`Hash`] and [`Eq`] on `Q`
    /// *must* match that of `K`. `K` and `V` must implement [`Clone`], as other
    /// threads may hold references to the entry.
    ///
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    /// [`Clone`]: https://doc.rust-lang.org/std/clone/trait.Clone.html
    #[inline]
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

    /// If there is a value associated with `key` and `condition` returns true
    /// when invoked with the current entry, remove and return a copy of it.
    ///
    /// `condition` may be invoked one or more times, even if no entry was
    /// removed.
    ///
    /// `Q` can be any borrowed form of `K`, but [`Hash`] and [`Eq`] on `Q`
    /// *must* match that of `K`. `K` and `V` must implement [`Clone`], as other
    /// threads may hold references to the entry.
    ///
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    /// [`Clone`]: https://doc.rust-lang.org/std/clone/trait.Clone.html
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

    /// If there is a value associated with `key` and `condition` returns true
    /// when invoked with the current entry, remove it and return the result of
    /// invoking `with_previous_value` with its value.
    ///
    /// `condition` may be invoked one or more times, even if no entry was
    /// removed. If `condition` failed or there was no value associated with
    /// `key`, `with_previous_entry` is not invoked and [`None`] is returned.
    ///
    /// `Q` can be any borrowed form of `K`, but [`Hash`] and [`Eq`] on `Q`
    /// *must* match that of `K`.
    ///
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
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

    /// If there is a value associated with `key` and `condition` returns true
    /// when invoked with the current entry, remove it and return the result of
    /// invoking `with_previous_entry` with it.
    ///
    /// `condition` may be invoked one or more times, even if no entry was
    /// removed. If `condition` failed or there was no value associated with
    /// `key`, `with_previous_entry` is not invoked and [`None`] is returned.
    ///
    /// `Q` can be any borrowed form of `K`, but [`Hash`] and [`Eq`] on `Q`
    /// *must* match that of `K`.
    ///
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
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

        self.bucket_array_ref(hash)
            .remove_entry_if_and(key, hash, condition, move |k, v| {
                self.len.fetch_sub(1, Ordering::Relaxed);

                with_previous_entry(k, v)
            })
    }

    /// Insert a value if none is associated with `key`. Otherwise, replace the
    /// value with the result of `on_modify` with the current entry as
    /// arguments. Finally, return a copy of the previously associated value.
    ///
    /// If there is no value associated with `key`, [`None`] will be returned.
    /// `on_modify` may be invoked multiple times, even if [`None`] is returned.
    ///
    /// `V` must implement [`Clone`], as other threads may hold references to
    /// the associated value.
    ///
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    /// [`Clone`]: https://doc.rust-lang.org/std/clone/trait.Clone.html
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

    /// Insert a value if none is associated with `key`. Otherwise, replace the
    /// value with the result of `on_modify` with the current entry as
    /// arguments. Finally, return a copy of the previous entry.
    ///
    /// If there is no value associated with `key`, [`None`] will be returned.
    /// `on_modify` may be invoked multiple times, even if [`None`] is returned.
    ///
    /// `K` and `V` must implement [`Clone`], as other threads may hold
    /// references to the entry.
    ///
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    /// [`Clone`]: https://doc.rust-lang.org/std/clone/trait.Clone.html
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

    /// Insert the result of `on_insert` if no value is associated with `key`.
    /// Otherwise, replace the value with the result of `on_modify` with the
    /// current entry as arguments. Finally, return a copy of the previously
    /// associated value.
    ///
    /// If there is no value associated with `key`, `on_insert` will be invoked
    /// and [`None`] will be returned. `on_modify` may be invoked multiple
    /// times, even if [`None`] is returned. Similarly, `on_insert` may be
    /// invoked if [`Some`] is returned.
    ///
    /// `V` must implement [`Clone`], as other threads may hold references to
    /// the associated value.
    ///
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    /// [`Some`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.Some
    /// [`Clone`]: https://doc.rust-lang.org/std/clone/trait.Clone.html
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

    /// Insert the result of `on_insert` if no value is associated with `key`.
    /// Otherwise, replace the value with the result of `on_modify` with the
    /// current entry as arguments. Finally, return a copy of the previous
    /// entry.
    ///
    /// If there is no value associated with `key`, `on_insert` will be invoked
    /// and [`None`] will be returned. `on_modify` may be invoked multiple
    /// times, even if [`None`] is returned. Similarly, `on_insert` may be
    /// invoked if [`Some`] is returned.
    ///
    /// `K` and `V` must implement [`Clone`], as other threads may hold
    /// references to the entry.
    ///
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    /// [`Some`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.Some
    /// [`Clone`]: https://doc.rust-lang.org/std/clone/trait.Clone.html
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

    /// Insert a value if none is associated with `key`. Otherwise, replace the
    /// value with the result of `on_modify` with the current entry as
    /// arguments. Finally, return the result of invoking `with_old_value` with
    /// the previously associated value.
    ///
    /// If there is no value associated with `key`, `with_old_value` will not be
    /// invoked and [`None`] will be returned. `on_modify` may be invoked
    /// multiple times, even if [`None`] is returned.
    ///
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

    /// Insert a value if none is associated with `key`. Otherwise, replace the
    /// value with the result of `on_modify` with the current entry as
    /// arguments. Finally, return the result of invoking `with_old_entry` with
    /// the previous entry.
    ///
    /// If there is no value associated with `key`, `with_old_value` will not be
    /// invoked and [`None`] will be returned. `on_modify` may be invoked
    /// multiple times, even if [`None`] is returned.
    ///
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

    /// Insert the result of `on_insert` if no value is associated with `key`.
    /// Otherwise, replace the value with the result of `on_modify` with the
    /// current entry as arguments. Finally, return the result of invoking
    /// `with_old_value` with the previously associated value.
    ///
    /// If there is no value associated with `key`, `on_insert` will be invoked,
    /// `with_old_value` will not be invoked, and [`None`] will be returned.
    /// `on_modify` may be invoked multiple times, even if [`None`] is returned.
    /// Similarly, `on_insert` may be invoked if [`Some`] is returned.
    ///
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    /// [`Some`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.Some
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

    /// Insert the result of `on_insert` if no value is associated with `key`.
    /// Otherwise, replace the value with the result of `on_modify` with the
    /// current entry as arguments. Finally, return the result of invoking
    /// `with_old_entry` with the previous entry.
    ///
    /// If there is no value associated with `key`, `on_insert` will be invoked,
    /// `with_old_value` will not be invoked, and [`None`] will be returned.
    /// `on_modify` may be invoked multiple times, even if [`None`] is returned.
    /// Similarly, `on_insert` may be invoked if [`Some`] is returned.
    ///
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    /// [`Some`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.Some
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

        let result = self.bucket_array_ref(hash).insert_with_or_modify_entry_and(
            key,
            hash,
            on_insert,
            on_modify,
            with_old_entry,
        );

        if result.is_none() {
            self.len.fetch_add(1, Ordering::Relaxed);
        }

        result
    }

    /// If there is a value associated with `key`, replace it with the result of
    /// invoking `on_modify` using the current key and value, then return a copy
    /// of the previously associated value.
    ///
    /// If there is no value associated with `key`, [`None`] will be returned.
    /// `on_modify` may be invoked multiple times, even if [`None`] is returned.
    ///
    /// `Q` can be any borrowed form of `K`, but [`Hash`] and [`Eq`] on `Q`
    /// *must* match that of `K`. `V` must implement [`Clone`], as other
    /// threads may hold references to the associated value.
    ///
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    /// [`Clone`]: https://doc.rust-lang.org/std/clone/trait.Clone.html
    #[inline]
    pub fn modify<F: FnMut(&K, &V) -> V>(&self, key: K, on_modify: F) -> Option<V>
    where
        V: Clone,
    {
        self.modify_entry_and(key, on_modify, |_, v| v.clone())
    }

    /// If there is a value associated with `key`, replace it with the result of
    /// invoking `on_modify` using the current key and value, then return a copy
    /// of the previously entry.
    ///
    /// If there is no value associated with `key`, [`None`] will be returned.
    /// `on_modify` may be invoked multiple times, even if [`None`] is returned.
    ///
    /// `Q` can be any borrowed form of `K`, but [`Hash`] and [`Eq`] on `Q`
    /// *must* match that of `K`. `K` and `V` must implement [`Clone`], as other
    /// threads may hold references to the entry.
    ///
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    /// [`Clone`]: https://doc.rust-lang.org/std/clone/trait.Clone.html
    #[inline]
    pub fn modify_entry<F: FnMut(&K, &V) -> V>(&self, key: K, on_modify: F) -> Option<(K, V)>
    where
        K: Clone,
        V: Clone,
    {
        self.modify_entry_and(key, on_modify, |k, v| (k.clone(), v.clone()))
    }

    /// If there is a value associated with `key`, replace it with the result of
    /// invoking `on_modify` using the current key and value, then return the
    /// result of invoking `with_old_value` with the previously associated
    /// value.
    ///
    /// If there is no value associated with `key`, `with_old_value` will not be
    /// invoked and [`None`] will be returned. `on_modify` may be invoked
    /// multiple times, even if [`None`] is returned.
    ///
    /// `Q` can be any borrowed form of `K`, but [`Hash`] and [`Eq`] on `Q`
    /// *must* match that of `K`.
    ///
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    #[inline]
    pub fn modify_and<F: FnMut(&K, &V) -> V, G: FnOnce(&V) -> T, T>(
        &self,
        key: K,
        on_modify: F,
        with_old_value: G,
    ) -> Option<T> {
        self.modify_entry_and(key, on_modify, move |_, v| with_old_value(v))
    }

    /// If there is a value associated with `key`, replace it with the result of
    /// invoking `on_modify` using the current key and value, then return the
    /// result of invoking `with_old_value` with the previous entry.
    ///
    /// If there is no value associated with `key`, `with_old_value` will not be
    /// invoked and [`None`] will be returned. `on_modify` may be invoked
    /// multiple times, even if [`None`] is returned.
    ///
    /// `Q` can be any borrowed form of `K`, but [`Hash`] and [`Eq`] on `Q`
    /// *must* match that of `K`.
    ///
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    #[inline]
    pub fn modify_entry_and<F: FnMut(&K, &V) -> V, G: FnOnce(&K, &V) -> T, T>(
        &self,
        key: K,
        on_modify: F,
        with_old_entry: G,
    ) -> Option<T> {
        let hash = bucket::hash(&self.build_hasher, &key);

        self.bucket_array_ref(hash)
            .modify_entry_and(key, hash, on_modify, with_old_entry)
    }
}

#[cfg(feature = "num-cpus")]
impl<K, V, S: Default> Default for HashMap<K, V, S> {
    fn default() -> Self {
        HashMap::with_num_segments_capacity_and_hasher(default_num_segments(), 0, S::default())
    }
}

impl<K, V, S> Drop for HashMap<K, V, S> {
    fn drop(&mut self) {
        let guard = unsafe { &crossbeam_epoch::unprotected() };
        atomic::fence(Ordering::Acquire);

        for Segment {
            bucket_array: this_bucket_array,
            ..
        } in self.segments.iter()
        {
            let mut current_ptr = this_bucket_array.load(Ordering::Relaxed, guard);

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
}

impl<K, V, S> HashMap<K, V, S> {
    #[inline]
    fn bucket_array_ref(&'_ self, hash: u64) -> BucketArrayRef<'_, K, V, S> {
        let index = self.segment_index_from_hash(hash);

        let Segment {
            ref bucket_array,
            ref len,
        } = self.segments[index];

        BucketArrayRef {
            bucket_array,
            build_hasher: &self.build_hasher,
            len,
        }
    }

    #[inline]
    fn segment_index_from_hash(&'_ self, hash: u64) -> usize {
        if self.segment_shift == 64 {
            0
        } else {
            (hash >> self.segment_shift) as usize
        }
    }
}

struct Segment<K, V> {
    bucket_array: Atomic<BucketArray<K, V>>,
    len: AtomicUsize,
}

#[cfg(feature = "num-cpus")]
fn default_num_segments() -> usize {
    num_cpus::get() * 2
}

#[cfg(test)]
mod tests {
    use crate::write_test_cases_for_me;

    use super::*;

    write_test_cases_for_me!(HashMap);

    #[test]
    fn single_segment() {
        let map = HashMap::with_num_segments(1);

        assert!(map.is_empty());
        assert_eq!(map.len(), 0);

        assert_eq!(map.insert("foo", 5), None);
        assert_eq!(map.get("foo"), Some(5));

        assert!(!map.is_empty());
        assert_eq!(map.len(), 1);

        assert_eq!(map.remove("foo"), Some(5));
        assert!(map.is_empty());
        assert_eq!(map.len(), 0);
    }
}
