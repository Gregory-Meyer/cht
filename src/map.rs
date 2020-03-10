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

//! A lockfree concurrent hash map implemented with open addressing and linear
//! probing.

pub(crate) mod bucket;
pub(crate) mod bucket_array_ref;

#[cfg(test)]
mod tests;

use bucket::BucketArray;
use bucket_array_ref::BucketArrayRef;

use std::{
    borrow::Borrow,
    hash::{BuildHasher, Hash},
    sync::atomic::{self, AtomicUsize, Ordering},
};

use ahash::RandomState;
use crossbeam_epoch::{self, Atomic};

/// Default hasher for `HashMap`.
///
/// This is currently [aHash], a hashing algorithm designed around acceleration
/// by the [AES-NI] instruction set on x86 processors. aHash is not
/// cryptographically secure, but is fast and resistant to DoS attacks. Compared
/// to [Fx Hash], the previous default hasher, aHash is slower at hashing
/// integers, faster at hashing strings, and provides DoS attack resistance.
///
/// [aHash]: https://docs.rs/ahash
/// [AES-NI]: https://en.wikipedia.org/wiki/AES_instruction_set
/// [Fx Hash]: https://docs.rs/fxhash
pub type DefaultHashBuilder = RandomState;

/// A lockfree concurrent hash map implemented with open addressing and linear
/// probing.
///
/// The default hashing algorithm is [aHash], a hashing algorithm that is
/// accelerated by the [AES-NI] instruction set on x86 proessors. aHash provides
/// some resistance to DoS attacks, but will not provide the same level of
/// resistance as something like [`RandomState`].
///
/// The hashing algorithm to be used can be chosen on a per-`HashMap` basis
/// using the [`with_hasher`] and [`with_capacity_and_hasher`] methods.
///
/// Key types must implement [`Hash`] and [`Eq`]. Any operations that return a
/// key or value require the return types to implement [`Clone`], as elements
/// may be in use by other threads and as such cannot be moved from.
///
/// `HashMap` is inspired by Jeff Phreshing's hash tables implemented in
/// [Junction], described in [this blog post]. In short, `HashMap` supports
/// fully concurrent lookups, insertions, removals, and updates.
///
/// [aHash]: https://docs.rs/ahash
/// [AES-NI]: https://en.wikipedia.org/wiki/AES_instruction_set
/// [`RandomState`]: https://doc.rust-lang.org/std/collections/hash_map/struct.RandomState.html
/// [`with_hasher`]: #method.with_hasher
/// [`with_capacity_and_hasher`]: #method.with_capacity_and_hasher
/// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
/// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
/// [`Clone`]: https://doc.rust-lang.org/std/clone/trait.Clone.html
/// [Junction]: https://github.com/preshing/junction
/// [this blog post]: https://preshing.com/20160222/a-resizable-concurrent-map/
#[derive(Default)]
pub struct HashMap<K, V, S = DefaultHashBuilder> {
    bucket_array: Atomic<bucket::BucketArray<K, V>>,
    build_hasher: S,
    len: AtomicUsize,
}

impl<K, V> HashMap<K, V, DefaultHashBuilder> {
    /// Creates an empty `HashMap`.
    ///
    /// The hash map is created with a capacity of 0 and will not allocate any
    /// space for elements until the first insertion.
    pub fn new() -> HashMap<K, V, DefaultHashBuilder> {
        HashMap::with_capacity_and_hasher(0, DefaultHashBuilder::default())
    }

    /// Creates an empty `HashMap` with space for at least `capacity` elements
    /// without reallocating.
    ///
    /// If `capacity == 0`, no allocations will occur.
    pub fn with_capacity(capacity: usize) -> HashMap<K, V, DefaultHashBuilder> {
        HashMap::with_capacity_and_hasher(capacity, DefaultHashBuilder::default())
    }
}

impl<K, V, S> HashMap<K, V, S> {
    /// Creates an empty `HashMap` that will use `build_hasher` to hash keys.
    ///
    /// The created map will have a capacity of 0 and as such will not have any
    /// space for elements allocated until the first insertion.
    pub fn with_hasher(build_hasher: S) -> HashMap<K, V, S> {
        HashMap::with_capacity_and_hasher(0, build_hasher)
    }

    /// Creates an empty `HashMap` that will hold at least `capacity` elements
    /// without reallocating and that uses `build_hasher` to hash keys.
    ///
    /// If `capacity == 0`, no allocations will occur.
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

    /// Returns the number of elements that are confirmed to have been inserted
    /// into this map.
    ///
    /// Because `HashMap` can be updated concurrently, this function reflects
    /// the number of insert operations that have returned to the user.
    /// In-progress insertions are not counted.
    pub fn len(&self) -> usize {
        self.len.load(Ordering::Relaxed)
    }

    /// Returns true if this `HashMap` contains no confirmed inserted elements.
    ///
    /// In-progress insertions into this `HashMap` are not considered.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the number of elements this `HashMap` can hold without
    /// reallocating a table.
    ///
    /// Note that all mutating operations, with the exception of removing
    /// elements, incur at least one allocation for the associated bucket.
    ///
    /// If there are insertion operations in flight, it is possible that a
    /// new, larger table has already been allocated.
    pub fn capacity(&self) -> usize {
        let guard = &crossbeam_epoch::pin();

        let bucket_array_ptr = self.bucket_array.load_consume(guard);

        unsafe { bucket_array_ptr.as_ref() }
            .map(BucketArray::capacity)
            .unwrap_or(0)
    }
}

impl<K: Hash + Eq, V, S: BuildHasher> HashMap<K, V, S> {
    /// Returns a copy of the value corresponding to `key`.
    ///
    /// `Q` can be any borrowed form of `K`, but [`Hash`] and [`Eq`] on `Q`
    /// *must* match that of `K`. `V` must implement [`Clone`], as the value may
    /// be deleted at any moment; the best we can do is to clone them while we
    /// know they exist.
    ///
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    /// [`Clone`]: https://doc.rust-lang.org/std/clone/trait.Clone.html
    /// [`get_and`]: #method.get_and
    #[inline]
    pub fn get<Q: Hash + Eq + ?Sized>(&self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        V: Clone,
    {
        self.get_key_value_and(key, |_, v| v.clone())
    }

    /// Returns a copy of the key and value corresponding to `key`.
    ///
    /// `Q` can be any borrowed form of `K`, but [`Hash`] and [`Eq`] on `Q`
    /// *must* match that of `K`. `K` and `V` must implement [`Clone`], as the
    /// bucket may be concurrently removed at any time; the best we can do is to
    /// clone them while we know they exist.
    ///
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    /// [`Clone`]: https://doc.rust-lang.org/std/clone/trait.Clone.html
    /// [`get_key_value_and`]: #method.get_key_value_and
    #[inline]
    pub fn get_key_value<Q: Hash + Eq + ?Sized>(&self, key: &Q) -> Option<(K, V)>
    where
        K: Borrow<Q> + Clone,
        V: Clone,
    {
        self.get_key_value_and(key, |k, v| (k.clone(), v.clone()))
    }

    /// Invokes `with_value` with a reference to the value corresponding to `key`.
    ///
    /// `with_value` will only be invoked if there is a value associated with
    /// `key` contained within this hash map.
    ///
    /// `Q` can be any borrowed form of `K`, but [`Hash`] and [`Eq`] on `Q`
    /// *must* match that of `K`.
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

    /// Invokes `with_entry` with a reference to the key and value corresponding
    /// to `key`.
    ///
    /// `with_entry` will only be invoked if there is a value associated with `key`
    /// contained within this hash map.
    ///
    /// `Q` can be any borrowed form of `K`, but [`Hash`] and [`Eq`] on `Q`
    /// *must* match that of `K`.
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

        self.bucket_array_ref()
            .insert_entry_and(key, hash, value, with_previous_entry)
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

        self.bucket_array_ref()
            .remove_entry_if_and(key, hash, condition, with_previous_entry)
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

        self.bucket_array_ref().insert_with_or_modify_entry_and(
            key,
            hash,
            on_insert,
            on_modify,
            with_old_entry,
        )
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
