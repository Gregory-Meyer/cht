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
    hash::{BuildHasher, Hash, Hasher},
    mem::{self},
    sync::{
        atomic::{self, AtomicBool, AtomicUsize, Ordering},
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
                buckets: Atomic::new(BucketArray::with_capacity_hasher_and_epoch(
                    capacity,
                    hash_builder.clone(),
                    0,
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
    pub fn get<Q: Hash + Eq + ?Sized>(&self, key: &Q) -> Option<V>
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
    pub fn get_key_value<Q: Hash + Eq + ?Sized>(&self, key: &Q) -> Option<(K, V)>
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
    pub fn get_and<Q: Hash + Eq + ?Sized, F: FnOnce(&V) -> T, T>(
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
    pub fn get_key_value_and<Q: Hash + Eq + ?Sized, F: FnOnce(&K, &V) -> T, T>(
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
        self.insert_or_modify_and(key, value, on_modify, V::clone)
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
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
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
    /// [`None`]: https://doc.rust-lang.org/std/option/enum.Option.html#variant.None
    pub fn insert_with_or_modify_and<F: FnOnce() -> V, G: FnMut(&V) -> V, H: FnOnce(&V) -> T, T>(
        &self,
        key: K,
        on_insert: F,
        on_modify: G,
        with_old_value: H,
    ) -> Option<T> {
        unimplemented!()
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
    pub fn modify<Q: Hash + Eq + ?Sized, F: FnMut(&V) -> V>(
        &self,
        key: &Q,
        on_modify: F,
    ) -> Option<V>
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
    pub fn modify_and<Q: Hash + Eq + ?Sized, F: FnMut(&V) -> V, G: FnOnce(&V) -> T, T>(
        &self,
        key: &Q,
        on_modify: F,
        with_old_value: G,
    ) -> Option<T>
    where
        K: Borrow<Q>,
    {
        let guard = &crossbeam_epoch::pin();

        self.do_modify(key, on_modify, guard)
            .and_then(move |b| b.maybe_value.as_ref().map(with_old_value))
    }
}

impl<'g, K: Hash + Eq, V, S: 'g + BuildHasher> HashMap<K, V, S> {
    fn get_bucket<Q: Hash + Eq + ?Sized>(
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
        let (found_bucket_ptr, new_buckets_ptr) = buckets.get(key, hash, guard);

        if buckets_ptr != new_buckets_ptr {
            self.swing_bucket_array_ptr(buckets_ptr, new_buckets_ptr, guard);
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

        let (previous_bucket_ptr, new_buckets_ptr) = buckets.insert(new_bucket, hash, guard);

        if let Some(previous_bucket) = unsafe { previous_bucket_ptr.as_ref() } {
            if previous_bucket.maybe_value.is_none() {
                self.len.fetch_add(1, Ordering::Relaxed);
            }
        } else {
            self.len.fetch_add(1, Ordering::Relaxed);
        }

        if buckets_ptr != new_buckets_ptr {
            self.swing_bucket_array_ptr(buckets_ptr, new_buckets_ptr, guard);
        }

        if !previous_bucket_ptr.is_null() {
            unsafe {
                guard.defer_unchecked(move || {
                    atomic::fence(Ordering::Acquire);
                    mem::drop(previous_bucket_ptr.into_owned());
                })
            };
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

        let (removed_ptr, new_buckets_ptr) = buckets_ref.remove(key, hash, None, guard);

        if buckets_ptr != new_buckets_ptr {
            self.swing_bucket_array_ptr(buckets_ptr, new_buckets_ptr, guard);
        }

        if !removed_ptr.is_null() {
            unsafe {
                guard.defer_unchecked(move || {
                    atomic::fence(Ordering::Acquire);
                    mem::drop(removed_ptr.into_owned());
                })
            };

            self.len.fetch_sub(1, Ordering::Relaxed);
        }

        unsafe { removed_ptr.as_ref() }
    }

    fn do_modify<Q: Hash + Eq + ?Sized, F: FnMut(&V) -> V>(
        &self,
        key: &Q,
        modifier: F,
        guard: &'g Guard,
    ) -> Option<&'g Bucket<K, V>>
    where
        K: Borrow<Q> + Clone,
    {
        let buckets_ptr = self.buckets.load_consume(guard);

        if buckets_ptr.is_null() {
            return None;
        }

        let buckets = unsafe { buckets_ptr.deref() };
        let hash = self.get_hash(key);

        let (previous_bucket_ptr, new_buckets_ptr) =
            buckets.modify(key, hash, modifier, None, guard);

        if !previous_bucket_ptr.is_null() {
            unsafe {
                guard.defer_unchecked(move || {
                    atomic::fence(Ordering::Acquire);
                    mem::drop(previous_bucket_ptr.into_owned());
                })
            };
        }

        if buckets_ptr != new_buckets_ptr {
            self.swing_bucket_array_ptr(buckets_ptr, new_buckets_ptr, guard);
        }

        unsafe { previous_bucket_ptr.as_ref() }
    }

    fn get_hash<Q: Hash + Eq + ?Sized>(&self, key: &Q) -> u64 {
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
                    None => Owned::new(BucketArray::with_capacity_hasher_and_epoch(
                        DEFAULT_CAPACITY,
                        self.hash_builder.clone(),
                        0,
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

    fn swing_bucket_array_ptr(
        &self,
        mut current_ptr: Shared<'g, BucketArray<K, V, S>>,
        new_ptr: Shared<'g, BucketArray<K, V, S>>,
        guard: &'g Guard,
    ) {
        assert!(!current_ptr.is_null());
        assert!(!new_ptr.is_null());

        let minimum_epoch = unsafe { new_ptr.deref() }.epoch;
        let mut current = unsafe { current_ptr.deref() };

        while current.epoch < minimum_epoch {
            let next_ptr = current.next_array.load_consume(guard);
            assert!(!next_ptr.is_null());

            match self.buckets.compare_and_set(
                current_ptr,
                next_ptr,
                (Ordering::AcqRel, Ordering::Acquire),
                guard,
            ) {
                Ok(_) => {
                    unsafe {
                        guard.defer_unchecked(move || {
                            atomic::fence(Ordering::Acquire);
                            mem::drop(current_ptr.into_owned());
                        });
                    }

                    current_ptr = next_ptr;
                }
                Err(e) => current_ptr = e.current,
            }

            current = unsafe { current_ptr.deref() };
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

        while !buckets_ptr.is_null() {
            let this_bucket_array = unsafe { buckets_ptr.deref() };
            let new_buckets_ptr =
                this_bucket_array
                    .next_array
                    .swap(Shared::null(), Ordering::Relaxed, guard);

            for this_bucket in this_bucket_array.buckets.iter() {
                let this_bucket_ptr = this_bucket.swap(Shared::null(), Ordering::Relaxed, guard);

                if this_bucket_ptr.is_null() || this_bucket_ptr.tag().has_redirect() {
                    continue;
                }

                mem::drop(unsafe { this_bucket_ptr.into_owned() });
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
    epoch: u64,
    is_supplanted: AtomicBool,
}

impl<K: Hash + Eq, V, S: BuildHasher> BucketArray<K, V, S> {
    fn with_capacity_hasher_and_epoch(
        capacity: usize,
        hash_builder: Arc<S>,
        epoch: u64,
    ) -> BucketArray<K, V, S> {
        BucketArray {
            buckets: vec![Atomic::null(); (capacity * 2).next_power_of_two()],
            len: AtomicUsize::new(0),
            next_array: Atomic::null(),
            hash_builder,
            epoch,
            is_supplanted: AtomicBool::new(false),
        }
    }

    fn get_hash(&self, key: &K) -> u64 {
        let mut hasher = self.hash_builder.build_hasher();
        key.hash(&mut hasher);

        hasher.finish()
    }
}

// set on bucket pointers if this bucket has been moved into the next array
const REDIRECT_TAG: usize = 1;

// this might seem complex -- you're right, but i wanted to add another tag
// it ended up not being useful, but the code was already written...
trait Tag {
    fn has_redirect(self) -> bool;
    fn with_redirect(self) -> Self;
    fn without_redirect(self) -> Self;
}

impl Tag for usize {
    fn has_redirect(self) -> bool {
        (self & REDIRECT_TAG) != 0
    }

    fn with_redirect(self) -> Self {
        self | REDIRECT_TAG
    }

    fn without_redirect(self) -> Self {
        self & !REDIRECT_TAG
    }
}

impl<'g, K: Hash + Eq, V, S: BuildHasher> BucketArray<K, V, S> {
    fn get<Q: Hash + Eq + ?Sized>(
        &self,
        key: &Q,
        hash: u64,
        guard: &'g Guard,
    ) -> (Shared<'g, Bucket<K, V>>, Shared<'g, BucketArray<K, V, S>>)
    where
        K: Borrow<Q>,
    {
        let self_ptr = (self as *const BucketArray<K, V, S>).into();

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
                } else if !this_bucket_ptr.tag().has_redirect() {
                    return (this_bucket_ptr, self_ptr);
                }

                // consume load from this_bucket isn't strong enough to publish
                // writes to *self.next_array
                let next_array_ptr = self.next_array.load_consume(guard);
                assert!(!next_array_ptr.is_null());
                let next_array = unsafe { next_array_ptr.deref() };
                self.grow_into(next_array, guard);

                return next_array.get(key, hash, guard);
            } else {
                return (Shared::null(), self_ptr);
            }
        }

        (Shared::null(), self_ptr)
    }

    fn insert(
        &self,
        bucket_ptr: Shared<'g, Bucket<K, V>>,
        hash: u64,
        guard: &'g Guard,
    ) -> (Shared<'g, Bucket<K, V>>, Shared<'g, BucketArray<K, V, S>>) {
        assert!(!bucket_ptr.is_null());

        let bucket = unsafe { bucket_ptr.deref() };
        let capacity = self.buckets.len();
        let len = self.len.load(Ordering::Relaxed);

        let insert_into = |next_array_ptr: Shared<'_, BucketArray<K, V, S>>| {
            assert!(!next_array_ptr.is_null());
            let next_array = unsafe { next_array_ptr.deref() };

            next_array.insert(bucket_ptr, hash, guard)
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
                have_seen_redirect = have_seen_redirect || this_bucket_ptr.tag().has_redirect();

                let should_increment_len =
                    if let Some(this_bucket_ref) = unsafe { this_bucket_ptr.as_ref() } {
                        if this_bucket_ref.key != bucket.key {
                            break;
                        }

                        this_bucket_ref.is_tombstone()
                    } else {
                        true
                    };

                if this_bucket_ptr.tag().has_redirect() {
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

                        return (
                            this_bucket_ptr,
                            (self as *const BucketArray<K, V, S>).into(),
                        );
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
    ) -> (Shared<'g, Bucket<K, V>>, Shared<'g, BucketArray<K, V, S>>)
    where
        K: Clone + Borrow<Q>,
    {
        let self_ptr = (self as *const BucketArray<K, V, S>).into();

        let capacity = self.buckets.len();
        let offset = (hash & (capacity - 1) as u64) as usize;

        for this_bucket in (0..self.buckets.len())
            .map(|x| (x + offset) & (capacity - 1))
            .map(|i| &self.buckets[i])
        {
            let mut this_bucket_ptr = this_bucket.load_consume(guard);

            loop {
                if this_bucket_ptr.is_null() {
                    return (Shared::null(), self_ptr);
                }

                let this_bucket_ref = unsafe { this_bucket_ptr.deref() };

                if this_bucket_ref.key.borrow() != key {
                    // hash collision, keep probing
                    break;
                } else if this_bucket_ref.is_tombstone() {
                    return (Shared::null(), self_ptr);
                }

                let new_bucket = match maybe_new_bucket.take() {
                    Some(b) => b,
                    None => Owned::new(Bucket {
                        key: this_bucket_ref.key.clone(),
                        maybe_value: None,
                    }),
                };

                if this_bucket_ptr.tag().has_redirect() {
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

                        return (
                            this_bucket_ptr,
                            (self as *const BucketArray<K, V, S>).into(),
                        );
                    }
                    Err(e) => {
                        this_bucket_ptr = e.current;
                        maybe_new_bucket.replace(e.new);
                    }
                }
            }
        }

        (Shared::null(), (self as *const BucketArray<K, V, S>).into())
    }

    fn modify<Q: Hash + Eq + ?Sized, F: FnMut(&V) -> V>(
        &self,
        key: &Q,
        hash: u64,
        mut modifier: F,
        maybe_new_bucket_ptr: Option<Owned<Bucket<K, V>>>,
        guard: &'g Guard,
    ) -> (Shared<'g, Bucket<K, V>>, Shared<'g, BucketArray<K, V, S>>)
    where
        K: Clone + Borrow<Q>,
    {
        let self_ptr: Shared<'g, BucketArray<K, V, S>> = (self as *const Self).into();

        let capacity = self.buckets.len();
        let offset = (hash & (self.buckets.len() - 1) as u64) as usize;

        for this_bucket in (0..capacity)
            .map(|x| (x + offset) & (capacity - 1))
            .map(|i| &self.buckets[i])
        {
            let mut this_bucket_ptr = this_bucket.load_consume(guard);

            let mut this_bucket_ref = match unsafe { this_bucket_ptr.as_ref() } {
                Some(b) => b,
                None => return (Shared::null(), self_ptr),
            };

            // buckets will never have their key changed, so we only have to
            // make this check once
            if this_bucket_ref.key.borrow() != key {
                continue;
            }

            let mut new_bucket_ptr = maybe_new_bucket_ptr.unwrap_or_else(|| {
                Owned::new(Bucket {
                    key: this_bucket_ref.key.clone(),
                    maybe_value: None,
                })
            });

            loop {
                if this_bucket_ptr.tag().has_redirect() {
                    // consume load from this_bucket isn't strong enough to publish
                    // writes to *self.next_array
                    let next_array_ptr = self.next_array.load_consume(guard);
                    assert!(!next_array_ptr.is_null());
                    let next_array = unsafe { next_array_ptr.deref() };
                    self.grow_into(next_array, guard);

                    return next_array.modify(key, hash, modifier, Some(new_bucket_ptr), guard);
                }

                let old_value = match this_bucket_ref.maybe_value.as_ref() {
                    Some(v) => v,
                    None => return (Shared::null(), self_ptr),
                };

                new_bucket_ptr.maybe_value = Some(modifier(old_value));

                // strong CAS here because i guessed it is more expensive to
                // invoke modifier again than it is to strong CAS
                match this_bucket.compare_and_set(
                    this_bucket_ptr,
                    new_bucket_ptr,
                    (Ordering::AcqRel, Ordering::Acquire),
                    guard,
                ) {
                    Ok(_) => return (this_bucket_ptr, self_ptr),
                    Err(e) => {
                        new_bucket_ptr = e.new;
                        this_bucket_ptr = e.current;
                    }
                }

                // we'll never replace a non-null pointer with a null pointer
                // so this should never fail
                this_bucket_ref = unsafe { this_bucket_ptr.as_ref().unwrap() };
            }
        }

        (Shared::null(), self_ptr)
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
            Owned::new(BucketArray::with_capacity_hasher_and_epoch(
                self.buckets.len() * 2,
                self.hash_builder.clone(),
                self.epoch + 1,
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
        'outer: for this_bucket in self.buckets.iter() {
            if self.is_supplanted.load(Ordering::Relaxed) {
                return;
            }

            let mut this_bucket_ptr = this_bucket.load_consume(guard);

            if this_bucket_ptr.tag().has_redirect() {
                continue;
            }

            let mut this_bucket_ref = match unsafe { this_bucket_ptr.as_ref() } {
                Some(b) => b,
                None => {
                    loop {
                        if self.is_supplanted.load(Ordering::Relaxed) {
                            return;
                        }

                        match this_bucket.compare_and_set_weak(
                            Shared::null(),
                            Shared::null().with_tag(this_bucket_ptr.tag().with_redirect()),
                            (Ordering::AcqRel, Ordering::Acquire),
                            guard,
                        ) {
                            Ok(_) => continue 'outer,
                            Err(e) => {
                                this_bucket_ptr = e.current;

                                if this_bucket_ptr.tag().has_redirect() {
                                    continue 'outer;
                                }

                                if !this_bucket_ptr.is_null() {
                                    break;
                                }
                            }
                        }
                    }

                    unsafe { this_bucket_ptr.deref() }
                }
            };

            loop {
                if self.is_supplanted.load(Ordering::Relaxed) {
                    return;
                }

                if this_bucket_ptr.tag().has_redirect() {
                    break;
                }

                if this_bucket_ref.is_tombstone() {
                    match this_bucket.compare_and_set_weak(
                        this_bucket_ptr,
                        this_bucket_ptr.with_tag(this_bucket_ptr.tag().with_redirect()),
                        (Ordering::AcqRel, Ordering::Acquire),
                        guard,
                    ) {
                        Ok(_) => break,
                        Err(e) => {
                            this_bucket_ptr = e.current;
                            assert!(!this_bucket_ptr.is_null());
                            this_bucket_ref = unsafe { this_bucket_ptr.deref() };

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
                    this_bucket_ptr.with_tag(this_bucket_ptr.tag().with_redirect()),
                    (Ordering::AcqRel, Ordering::Acquire),
                    guard,
                ) {
                    Ok(_) => break,
                    Err(e) => {
                        this_bucket_ptr = e.current;
                        assert!(!this_bucket_ptr.is_null());
                        this_bucket_ref = unsafe { this_bucket_ptr.deref() };
                    }
                }
            }
        }

        self.is_supplanted.store(true, Ordering::Relaxed);
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

enum FunctionOrValue<T, F: FnOnce() -> T> {
    Function(F),
    Value(T),
}

impl<T, F: FnOnce() -> T> FunctionOrValue<T, F> {
    fn into_value(self) -> T {
        match self {
            FunctionOrValue::Function(f) => f(),
            FunctionOrValue::Value(v) => v,
        }
    }
}

impl<K: Hash + Eq, V> Bucket<K, V> {
    fn is_tombstone(&self) -> bool {
        self.maybe_value.is_none()
    }
}
