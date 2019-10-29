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

//! A lockfree concurrent hash map implemented with open addressing and linear
//! probing.

use std::{
    borrow::Borrow,
    collections::HashSet,
    hash::{BuildHasher, Hash, Hasher},
    mem,
    sync::{
        atomic::{self, AtomicUsize, Ordering},
        Arc,
    },
};

use ahash::ABuildHasher;
use crossbeam_epoch::{self, Atomic, Guard, Owned, Pointer, Shared};

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
pub type DefaultHashBuilder = ABuildHasher;

/// A lockfree concurrent hash map implemented with open addressing and linear
/// probing.
///
/// The default hashing algorithm is [aHash], a hashing algorithm that is
/// accelerated by the [AES-NI] instruction set on x86 proessors. aHash provides
/// some resistance to DoS attacks, but will not provide the same level of
/// resistance as something like [`RandomState`] from the standard library.
///
/// The hashing algorithm to be used can be chosen on a per-`HashMap` basis
/// using the [`with_hasher`] and [`with_capacity_and_hasher`] methods.
///
/// Key types must implement [`Hash`] and [`Eq`]. Additionally, if you are going
/// to be removing elements from this `HashMap`, the key type must also
/// implement [`Clone`], as `HashMap` uses tombstones for deletion. Any
/// operations that return a value require the value type to implement
/// [`Clone`], as elements may be in use by other threads and as such cannot be
/// moved from.
///
/// `HashMap` is inspired by Jeff Phreshing's hash tables implemented in
/// [Junction], described in [this blog post]. In short, `HashMap` supports
/// fully concurrent lookups, insertions, and removals.
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
pub struct HashMap<K: Hash + Eq, V, S: BuildHasher = DefaultHashBuilder> {
    buckets: Atomic<BucketArray<K, V, S>>,
    len: AtomicUsize,
    hash_builder: Arc<S>,
}

impl<K: Hash + Eq, V> HashMap<K, V, DefaultHashBuilder> {
    /// Creates an empty `HashMap`.
    ///
    /// The hash map is created with a capacity of 0 and will not allocate any
    /// space for elements until the first insertion. However, the hash builder
    /// `S` will be allocated on the heap.
    pub fn new() -> HashMap<K, V, DefaultHashBuilder> {
        HashMap::with_capacity_and_hasher(0, DefaultHashBuilder::default())
    }

    /// Creates an empty `HashMap` with space for at least `capacity` elements
    /// without reallocating.
    ///
    /// If `capacity == 0`, the hash map will not allocate any space for
    /// elements, but it will allocate space for the hash builder.
    pub fn with_capacity(capacity: usize) -> HashMap<K, V, DefaultHashBuilder> {
        HashMap::with_capacity_and_hasher(capacity, DefaultHashBuilder::default())
    }
}

impl<K: Hash + Eq, V, S: BuildHasher> HashMap<K, V, S> {
    /// Creates an empty `HashMap` that will use `hash_builder` to hash keys.
    ///
    /// The created map will have a capacity of 0 and as such will not have any
    /// space for elements allocated until the first insertion. However, the
    /// hash builder `S` will be allocated on the heap.
    pub fn with_hasher(hash_builder: S) -> HashMap<K, V, S> {
        HashMap::with_capacity_and_hasher(0, hash_builder)
    }

    /// Creates an empty `HashMap` that will hold at least `capacity` elements
    /// without reallocating and that uses `hash_builder` to hash keys.
    ///
    /// If `capacity == 0`, the hash map will not allocate any space for
    /// elements. However, the hash map will always allocate its hash builder
    /// `S` on the heap.
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
    /// reallocating.
    ///
    /// If invoked while this hash map is growing, it is possible for
    /// [`len`](#method.len) to return a greater value than this function does.
    /// This is because new elements are being inserted into the next array of
    /// buckets, but the `HashMap`'s bucket pointer has not been swung up the
    /// list yet.
    pub fn capacity(&self) -> usize {
        let guard = &crossbeam_epoch::pin();
        let buckets_ptr = self.buckets.load_consume(guard);

        if buckets_ptr.is_null() {
            return 0;
        }

        let buckets_ref = unsafe { buckets_ptr.deref() };

        buckets_ref.buckets.len() / 2
    }

    /// Returns a copy of the value corresponding to `key`.
    ///
    /// `Q` can be any borrowed form of `K`, but [`Hash`] and [`Eq`] on `Q`
    /// *must* match that of `K`. In addition, `V` must implement [`Clone`], as
    /// the value may be concurrently removed at any moment, so the best we can
    /// do is return a copy of it.
    ///
    /// If your `V` does not implement [`Clone`], you will have to use
    /// [`get_and`] instead.
    ///
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    /// [`Clone`]: https://doc.rust-lang.org/std/clone/trait.Clone.html
    /// [`get_and`]: #method.get_and
    pub fn get<Q: ?Sized + Hash + Eq>(&self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        V: Clone,
    {
        self.get_and(key, V::clone)
    }

    /// Returns a copy of the key and value corresponding to `key`.
    ///
    /// `Q` can be any borrowed form of `K`, but [`Hash`] and [`Eq`] on `Q`
    /// *must* match that of `K`. In addition, `K` and `V` must implement
    /// [`Clone`], as the bucket may be concurrently removed at any moment, so
    /// the best we can do is return a copy of it.
    ///
    /// If your `K` or `V` do not implement [`Clone`], you will have to use
    /// [`get_key_value_and`] instead.
    ///
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    /// [`Clone`]: https://doc.rust-lang.org/std/clone/trait.Clone.html
    /// [`get_key_value_and`]: #method.get_key_value_and
    pub fn get_key_value<Q: ?Sized + Hash + Eq>(&self, key: &Q) -> Option<(K, V)>
    where
        K: Borrow<Q> + Clone,
        V: Clone,
    {
        self.get_key_value_and(key, |k, v| (k.clone(), v.clone()))
    }

    /// Invokes `func` with a reference to the value corresponding to `key`.
    ///
    /// `func` will only be invoked if there is a value associated with `key`
    /// contained within this hash map.
    ///
    /// `Q` can be any borrowed form of `K`, but [`Hash`] and [`Eq`] on `Q`
    /// *must* match that of `K`.
    ///
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    pub fn get_and<Q: ?Sized + Hash + Eq, F: FnOnce(&V) -> T, T>(
        &self,
        key: &Q,
        func: F,
    ) -> Option<T>
    where
        K: Borrow<Q>,
    {
        self.get_key_value_and(key, move |_, v| func(v))
    }

    /// Invokes `func` with a reference to the key and value corresponding to
    /// `key`.
    ///
    /// `func` will only be invoked if there is a value associated with `key`
    /// contained within this hash map.
    ///
    /// `Q` can be any borrowed form of `K`, but [`Hash`] and [`Eq`] on `Q`
    /// *must* match that of `K`.
    ///
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
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

    /// Inserts a key-value pair into the hash map, then returns a copy of the
    /// previous value associated with `key`.
    ///
    /// If the key was not previously present in this hash map, [`None`] is
    /// returned.
    ///
    /// `V` must implement [`Clone`] for this function, as it is possible that
    /// other threads may still hold references to the value previously
    /// associated with `key`. As such, the associated value cannot be moved
    /// from.
    ///
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    /// [`Clone`]: https://doc.rust-lang.org/std/clone/trait.Clone.html
    pub fn insert(&self, key: K, value: V) -> Option<V>
    where
        V: Clone,
    {
        self.insert_and(key, value, V::clone)
    }

    /// Inserts a key-value pair into the hash map, then returns a copy of the
    /// previous key-value pair.
    ///
    /// If the key was not previously present in this hash map, [`None`] is
    /// returned.
    ///
    /// `K` and `V` must implement [`Clone`] for this function, as it is
    /// possible that other threads may still hold references to the key-value
    /// pair previously associated with `key`.
    ///
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    /// [`Clone`]: https://doc.rust-lang.org/std/clone/trait.Clone.html
    pub fn insert_entry(&self, key: K, value: V) -> Option<(K, V)>
    where
        K: Clone,
        V: Clone,
    {
        self.insert_entry_and(key, value, |k, v| (k.clone(), v.clone()))
    }

    /// Inserts a key-value pair into the hash map, then invokes `func` with the
    /// previously-associated value.
    ///
    /// If the key was not previously present in this hash map, [`None`] is
    /// returned and `func` is not invoked.
    ///
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    pub fn insert_and<F: FnOnce(&V) -> T, T>(&self, key: K, value: V, func: F) -> Option<T> {
        self.insert_entry_and(key, value, move |_, v| func(v))
    }

    /// Inserts a key-value pair into the hash map, then invokes `func` with the
    /// new key and previously-associated value.
    ///
    /// If the key was not previously present in this hash map, [`None`] is
    /// returned and `func` is not invoked.
    ///
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    pub fn insert_entry_and<F: FnOnce(&K, &V) -> T, T>(
        &self,
        key: K,
        value: V,
        func: F,
    ) -> Option<T> {
        let guard = &crossbeam_epoch::pin();

        self.do_insert(key, value, guard).and_then(|bucket| {
            bucket
                .maybe_value
                .as_ref()
                .map(|previous_value| func(&bucket.key, previous_value))
        })
    }
}

impl<K: Hash + Eq + Clone, V, S: BuildHasher> HashMap<K, V, S> {
    /// Removes the value associated with `key` from the hash map, returning a
    /// copy of that value if there was one contained in this hash map.
    ///
    /// `Q` can be any borrowed form of `K`, but [`Hash`] and [`Eq`] on `Q`
    /// *must* match that of `K`. `K` and `V` must implement [`Clone`] for this
    /// function, as `K` must be cloned for the tombstone bucket and the
    /// previously-associated value cannot be moved from, as other threads
    /// may still hold references to it.
    ///
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    /// [`Clone`]: https://doc.rust-lang.org/std/clone/trait.Clone.html
    pub fn remove<Q: Hash + Eq + ?Sized>(&self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        V: Clone,
    {
        self.remove_and(key, V::clone)
    }

    /// Removes the value associated with `key` from the hash map, returning a
    /// copy of that key-value pair it was contained in this hash map.
    ///
    /// `Q` can be any borrowed form of `K`, but [`Hash`] and [`Eq`] on `Q`
    /// *must* match that of `K`. `K` and `V` must implement [`Clone`] for this
    /// function. `K` must be cloned twice: once for the tombstone bucket
    /// and once for the return value; the previously-associated value cannot be
    /// moved from, as other threads may still hold references to it.
    ///
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    /// [`Clone`]: https://doc.rust-lang.org/std/clone/trait.Clone.html
    pub fn remove_entry<Q: Hash + Eq + ?Sized>(&self, key: &Q) -> Option<(K, V)>
    where
        K: Borrow<Q>,
        V: Clone,
    {
        self.remove_entry_and(key, |k, v| (k.clone(), v.clone()))
    }

    /// Removes the value associated with `key` from the hash map, then returns
    /// the result of invoking `func` with the previously-associated value.
    ///
    /// `Q` can be any borrowed form of `K`, but [`Hash`] and [`Eq`] on `Q`
    /// *must* match that of `K`. `K` must implement [`Clone`] for this
    /// function, as `K` must be cloned to create a tombstone bucket.
    ///
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    /// [`Clone`]: https://doc.rust-lang.org/std/clone/trait.Clone.html
    pub fn remove_and<Q: Hash + Eq + ?Sized, F: FnOnce(&V) -> T, T>(
        &self,
        key: &Q,
        func: F,
    ) -> Option<T>
    where
        K: Borrow<Q>,
    {
        self.remove_entry_and(key, move |_, v| func(v))
    }

    /// Removes the value associated with `key` from the hash map, then returns
    /// the result of invoking `func` with the key and previously-associated
    /// value.
    ///
    /// `Q` can be any borrowed form of `K`, but [`Hash`] and [`Eq`] on `Q`
    /// *must* match that of `K`. `K` must implement [`Clone`] for this
    /// function, as `K` must be cloned to create a tombstone bucket.
    ///
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    /// [`Clone`]: https://doc.rust-lang.org/std/clone/trait.Clone.html
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

    /// Insert the a new value if none is associated with `key` or replace the
    /// value with the result of `on_modify`, then return a clone of the old
    /// value.
    ///
    /// If there is no value associated with `key`, [`None`] will be returned
    /// and `on_modify` will not be invoked. Otherwise, `on_modify` may be
    /// invoked multiple times depending on how much write contention there is
    /// on the bucket associated with `key`.
    ///
    /// It is possible for `on_modify` to be invoked even if [`None`] is
    /// returned if other threads are also writing to the bucket associated with
    /// `key`.
    ///
    /// `V` must implement [`Clone`] for this function, as it is possible that
    /// other threads may still hold references to the value previously
    /// associated with `key`. As such, the value previously associated with
    /// `key` cannot be moved from.
    ///
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    /// [`Clone`]: https://doc.rust-lang.org/std/clone/trait.Clone.html
    pub fn insert_or_modify<F: FnMut(&V) -> V>(&self, key: K, value: V, on_modify: F) -> Option<V>
    where
        V: Clone,
    {
        self.insert_with_or_modify_and(key, move || value, on_modify, V::clone)
    }

    /// Insert the result of `on_insert` if no value is associated with `key` or
    /// replace the value with the result of `on_modify`, then return a clone of
    /// the old value.
    ///
    /// If there is no value associated with `key`, `on_insert` will be invoked,
    /// `on_modify` will not be invoked, and [`None`] will be returned.
    /// Otherwise, `on_modify` may be invoked multiple times depending on how
    /// much write contention there is on the bucket associate with `key`.
    ///
    /// It is possible for both `on_insert` and `on_modify` to be invoked, even
    /// if [`None`] is returned, if other threads are also writing to the bucket
    /// associated with `key`.
    ///
    /// `V` must implement [`Clone`] for this function, as it is possible that
    /// other threads may still hold references to the value previously
    /// associated with `key`. As such, the value previously associated with
    /// `key` cannot be moved from.
    ///
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    /// [`Clone`]: https://doc.rust-lang.org/std/clone/trait.Clone.html
    pub fn insert_with_or_modify<F: FnOnce() -> V, G: FnMut(&V) -> V>(
        &self,
        key: K,
        on_insert: F,
        on_modify: G,
    ) -> Option<V>
    where
        V: Clone,
    {
        self.insert_with_or_modify_and(key, on_insert, on_modify, V::clone)
    }

    /// Insert the a new value if none is associated with `key` or replace the
    /// value with the result of `on_modify`, then return the result of
    /// `with_old_value` using the old value.
    ///
    /// If there is no value associated with `key`, [`None`] will be returned
    /// and `on_modify` and `with_old_value` will not be invoked. Otherwise,
    /// `on_modify` may be invoked multiple times depending on how much write
    /// contention there is on the bucket associated with `key`.
    ///
    /// It is possible for `on_modify` to be invoked even if [`None`] is
    /// returned if other threads are also writing to the bucket associated with
    /// `key`.
    ///
    /// `K` must implement [`Clone`] for this function to create a new bucket
    /// if one already exists.
    ///
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    /// [`Clone`]: https://doc.rust-lang.org/std/clone/trait.Clone.html
    pub fn insert_or_modify_and<F: FnMut(&V) -> V, G: FnOnce(&V) -> T, T>(
        &self,
        key: K,
        value: V,
        on_modify: F,
        with_old_value: G,
    ) -> Option<T> {
        self.insert_with_or_modify_and(key, move || value, on_modify, with_old_value)
    }

    /// Insert the result of `on_insert` if no value is associated with `key` or
    /// replace the value with the result of `on_modify`, then return the result
    /// of `with_old_value` using the old value.
    ///
    /// If there is no value associated with `key`, `on_insert` will be invoked,
    /// `on_modify` and `with_old_value`, will not be invoked, and [`None`] will
    /// be returned. Otherwise, `on_modify` may be invoked multiple times
    /// depending on how much write contention there is on the bucket associate
    /// with `key`.
    ///
    /// It is possible for both `on_insert` and `on_modify` to be invoked, even
    /// if [`None`] is returned, if other threads are also writing to the bucket
    /// associated with `key`.
    ///
    /// `K` must implement [`Clone`] for this function to create a new bucket
    /// if one already exists.
    ///
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    /// [`Clone`]: https://doc.rust-lang.org/std/clone/trait.Clone.html
    pub fn insert_with_or_modify_and<F: FnOnce() -> V, G: FnMut(&V) -> V, H: FnOnce(&V) -> T, T>(
        &self,
        key: K,
        on_insert: F,
        on_modify: G,
        with_old_value: H,
    ) -> Option<T> {
        unimplemented!()
    }

    /// Replace the value associated with `key` with the result of `on_modify`
    /// and return a clone of the previous value.
    ///
    /// If there is no value associated with `key`, `on_modify` will not be
    /// invoked and [`None`] will be returned. Otherwise, `on_modify` may be
    /// invoked multiple times depending on how much write contention there is
    /// on the bucket associate with `key`.
    ///
    /// It is possible for `on_modify` to be invoked even if [`None`] is
    /// returned if other threads are also writing to the bucket associated with
    /// `key`.
    ///
    /// `K` must implement [`Clone`] for this function to create a new bucket
    /// if one already exists. `V` must implement [`Clone`] for this function,
    /// as it is possible that other threads may still hold references to the
    /// value previously associated with `key`. As such, the value previously
    /// associated with `key` cannot be moved from. `Q` can be any borrowed form
    /// of `K`, but [`Hash`] and [`Eq`] on `Q` *must* match that of `K`.
    ///
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    /// [`Clone`]: https://doc.rust-lang.org/std/clone/trait.Clone.html
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    pub fn modify<Q: Hash + Eq, F: FnMut(&V) -> V>(&self, key: &Q, on_modify: F) -> Option<V>
    where
        K: Borrow<Q>,
        V: Clone,
    {
        self.modify_and(key, on_modify, V::clone)
    }

    /// Replace the value associated with `key` with the result of `on_modify`
    /// and return the result of invoking `with_old_value` on the old value.
    ///
    /// If there is no value associated with `key`, `on_modify` and
    /// `with_old_value` will not be invoked and [`None`] will be returned.
    /// Otherwise, `on_modify` may be invoked multiple times depending on how
    /// much write contention there is on the bucket associate with `key`.
    ///
    /// It is possible for `on_modify` to be invoked even if [`None`] is
    /// returned if other threads are also writing to the bucket associated with
    /// `key`.
    ///
    /// `K` must implement [`Clone`] for this function to create a new bucket
    /// if one already exists. `Q` can be any borrowed form of `K`, but
    /// [`Hash`] and [`Eq`] on `Q` *must* match that of `K`.
    ///
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    /// [`Clone`]: https://doc.rust-lang.org/std/clone/trait.Clone.html
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    pub fn modify_and<Q: Hash + Eq, F: FnMut(&V) -> V, G: FnOnce(&V) -> T, T>(
        &self,
        key: &Q,
        on_modify: F,
        with_old_value: G,
    ) -> Option<T> {
        unimplemented!()
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

        let buckets_ptr = self.buckets.load_consume(guard);

        if buckets_ptr.is_null() {
            return None;
        }

        let buckets = unsafe { buckets_ptr.deref() };
        let (found_bucket_ptr, redirected) = buckets.get(key, hash, guard);

        if redirected {
            self.try_swing_bucket_array_ptr(buckets_ptr, guard);
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

        let (previous_bucket_ptr, redirected) = buckets.insert(new_bucket, hash, guard);

        if let Some(previous_bucket) = unsafe { previous_bucket_ptr.as_ref() } {
            if previous_bucket.maybe_value.is_none() {
                self.len.fetch_add(1, Ordering::Relaxed);
            }
        } else {
            self.len.fetch_add(1, Ordering::Relaxed);
        }

        if !previous_bucket_ptr.is_null() {
            unsafe {
                guard.defer_unchecked(move || {
                    atomic::fence(Ordering::Acquire);
                    mem::drop(previous_bucket_ptr.into_owned());
                })
            };
        }

        if redirected {
            self.try_swing_bucket_array_ptr(buckets_ptr, guard);
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
        let buckets_ptr = self.buckets.load_consume(guard);

        if buckets_ptr.is_null() {
            return None;
        }

        let buckets_ref = unsafe { buckets_ptr.deref() };
        let hash = self.get_hash(key);

        let removed_ptr = buckets_ref.remove(key, hash, None, guard);

        if !removed_ptr.is_null() {
            unsafe {
                guard.defer_unchecked(move || {
                    atomic::fence(Ordering::Acquire);
                    mem::drop(removed_ptr.into_owned());
                })
            };

            self.len.fetch_sub(1, Ordering::Relaxed);

            Some(unsafe { removed_ptr.deref() })
        } else {
            None
        }
    }

    fn get_hash<Q: ?Sized + Hash + Eq>(&self, key: &Q) -> u64 {
        let mut hasher = self.hash_builder.build_hasher();
        key.hash(&mut hasher);

        hasher.finish()
    }

    fn get_or_create_buckets(&self, guard: &'g Guard) -> Shared<'g, BucketArray<K, V, S>> {
        const DEFAULT_CAPACITY: usize = 64;

        let mut buckets_ptr = self.buckets.load_consume(guard);
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
                    Shared::null(),
                    new_buckets,
                    (Ordering::AcqRel, Ordering::Acquire),
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

    fn try_swing_bucket_array_ptr(
        &self,
        current_ptr: Shared<'g, BucketArray<K, V, S>>,
        guard: &'g Guard,
    ) {
        assert!(!current_ptr.is_null());

        let current = unsafe { current_ptr.deref() };
        // this can be relaxed, since we don't check its contents and later
        // users will use the acquire load from below anyways
        let next_array_ptr = current.next_array.load(Ordering::Relaxed, guard);
        assert!(!next_array_ptr.is_null());

        // whatever the case, we need an acquire here so that the array_ptr has
        // its contents updated in this thread
        if self
            .buckets
            .compare_and_set(
                current_ptr,
                next_array_ptr,
                (Ordering::Acquire, Ordering::Acquire),
                guard,
            )
            .is_ok()
        {
            unsafe {
                guard.defer_unchecked(move || {
                    atomic::fence(Ordering::Acquire);
                    mem::drop(current_ptr.into_owned());
                })
            };
        }
    }
}

impl<K: Eq + Hash, V, S: BuildHasher> Drop for HashMap<K, V, S> {
    fn drop(&mut self) {
        // ensure all loads have the most recent data available
        atomic::fence(Ordering::Acquire);

        // all opeations can have relaxed memory ordering, since drop is called
        // with a mutable reference, forbidding any other thread from even
        // holding a reference to the map

        let guard = unsafe { crossbeam_epoch::unprotected() };

        let mut buckets_ptr = self.buckets.swap(Shared::null(), Ordering::Relaxed, guard);
        let mut freed_buckets = HashSet::with_hasher(DefaultHashBuilder::default());

        while !buckets_ptr.is_null() {
            let this_bucket_array = unsafe { buckets_ptr.deref() };
            let new_buckets_ptr =
                this_bucket_array
                    .next_array
                    .swap(Shared::null(), Ordering::Relaxed, guard);

            for this_bucket in this_bucket_array.buckets.iter() {
                let this_bucket_ptr = this_bucket
                    .swap(Shared::null(), Ordering::Relaxed, guard)
                    .with_tag(0);

                if this_bucket_ptr.is_null() {
                    continue;
                }

                if freed_buckets.insert(this_bucket_ptr.into_usize()) {
                    mem::drop(unsafe { this_bucket_ptr.into_owned() });
                }
            }

            mem::drop(unsafe { buckets_ptr.into_owned() });
            buckets_ptr = new_buckets_ptr;
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
    ) -> (Shared<'g, Bucket<K, V>>, bool)
    where
        K: Borrow<Q>,
    {
        let capacity = self.buckets.len();
        let offset = (hash & (self.buckets.len() - 1) as u64) as usize;

        for this_bucket_ptr in (0..capacity)
            .map(|x| (x + offset) & (capacity - 1))
            .map(|i| &self.buckets[i])
            .map(|this_bucket| this_bucket.load_consume(guard))
        {
            if let Some(this_bucket_ref) = unsafe { this_bucket_ptr.as_ref() } {
                if this_bucket_ref.key.borrow() != key {
                    continue;
                } else if this_bucket_ptr.tag() != REDIRECT_TAG {
                    return (this_bucket_ptr, false);
                }

                // consume load from this_bucket isn't strong enough to publish
                // writes to *self.next_array
                let next_array_ptr = self.next_array.load_consume(guard);
                assert!(!next_array_ptr.is_null());
                let next_array = unsafe { next_array_ptr.deref() };
                self.grow_into(next_array, guard);

                let mut result = next_array.get(key, hash, guard);
                result.1 = true;

                return result;
            } else {
                return (Shared::null(), false);
            }
        }

        (Shared::null(), false)
    }

    fn insert(
        &self,
        bucket_ptr: Shared<'g, Bucket<K, V>>,
        hash: u64,
        guard: &'g Guard,
    ) -> (Shared<'g, Bucket<K, V>>, bool) {
        assert!(!bucket_ptr.is_null());

        let bucket = unsafe { bucket_ptr.deref() };
        let capacity = self.buckets.len();
        let len = self.len.load(Ordering::Relaxed);

        let insert_into = |next_array_ptr: Shared<'_, BucketArray<K, V, S>>| {
            assert!(!next_array_ptr.is_null());
            let next_array = unsafe { next_array_ptr.deref() };

            let mut result = next_array.insert(bucket_ptr, hash, guard);
            result.1 = true;

            result
        };

        // grow if inserting would push us over a load factor of 0.5
        if (len + 1) > (capacity / 2) {
            return insert_into(self.grow(guard));
        }

        let grow_into_next_if_and_insert_into_next = |have_seen_redirect| {
            let next_array_ptr = if have_seen_redirect {
                let next_array_ptr = self.next_array.load_consume(guard);
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
            // to ensure the store to the key is visible in this thread
            let mut this_bucket_ptr = this_bucket.load_consume(guard);

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
                    (Ordering::AcqRel, Ordering::Acquire),
                    guard,
                ) {
                    Ok(_) => {
                        if should_increment_len {
                            // replaced a tombstone
                            self.len.fetch_add(1, Ordering::Relaxed);
                        }

                        return (this_bucket_ptr, false);
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
            let mut this_bucket_ptr = this_bucket.load_consume(guard);

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
                    (Ordering::AcqRel, Ordering::Acquire),
                    guard,
                ) {
                    Ok(_) => {
                        self.len.fetch_sub(1, Ordering::Relaxed);

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
        let maybe_next_array_ptr = self.next_array.load_consume(guard);

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
            (Ordering::AcqRel, Ordering::Acquire),
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
            let mut this_bucket_ptr = this_bucket.load_consume(guard);

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
                            (Ordering::AcqRel, Ordering::Acquire),
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
                        (Ordering::AcqRel, Ordering::Acquire),
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
                        (Ordering::AcqRel, Ordering::Acquire),
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
        unsafe { self.next_array.load_consume(guard).as_ref() }
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
