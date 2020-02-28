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
use crossbeam_epoch::{self, Atomic, Guard, Owned, Shared};

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
                    capacity + 1,
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
        let guard = &crossbeam_epoch::pin();

        let hash = self.get_hash(&key);

        let buckets_ptr = self.get_or_create_buckets(guard);
        assert!(!buckets_ptr.is_null());

        let buckets = unsafe { buckets_ptr.deref() };

        let BucketAndParent {
            bucket: previous_bucket_ptr,
            parent: new_buckets_ptr,
        } = buckets.insert_or_modify(
            KeyOrBucket::Key(key),
            hash,
            FunctionOrValue::Function(on_insert),
            on_modify,
            guard,
        );

        if new_buckets_ptr != buckets_ptr {
            self.swing_bucket_array_ptr(buckets_ptr, new_buckets_ptr, guard);
        }

        if !previous_bucket_ptr.is_null() {
            unsafe {
                guard.defer_unchecked(move || {
                    atomic::fence(Ordering::Acquire);
                    mem::drop(previous_bucket_ptr.into_owned());
                })
            };
        } else {
            self.len.fetch_add(1, Ordering::Relaxed);
        }

        unsafe { previous_bucket_ptr.as_ref() }
            .and_then(move |b| b.maybe_value.as_ref().map(with_old_value))
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

        if let Some(found_bucket) = unsafe { found_bucket_ptr.as_ref() } {
            assert!(found_bucket.key.borrow() == key);

            Some(found_bucket)
        } else {
            None
        }
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

        // increment length if we replaced a null or tombstone bucket
        if unsafe { previous_bucket_ptr.as_ref() }
            .map(|b| b.maybe_value.is_none())
            .unwrap_or(true)
        {
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
                    (Ordering::Release, Ordering::Relaxed),
                    guard,
                ) {
                    Ok(new_buckets) => return new_buckets,
                    Err(e) => {
                        maybe_new_buckets = Some(e.new);
                        buckets_ptr = self.buckets.load_consume(guard);
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
                (Ordering::Release, Ordering::Relaxed),
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
                Err(_) => current_ptr = self.buckets.load_consume(guard),
            }

            current = unsafe { current_ptr.deref() };
        }
    }
}

impl<K: Eq + Hash, V, S: BuildHasher> Drop for HashMap<K, V, S> {
    fn drop(&mut self) {
        let guard = unsafe { crossbeam_epoch::unprotected() };

        let mut buckets_ptr = self.buckets.load_consume(guard);

        while !buckets_ptr.is_null() {
            let this_bucket_array = unsafe { buckets_ptr.deref() };
            let new_buckets_ptr = this_bucket_array.next_array.load_consume(guard);

            for this_bucket in this_bucket_array.buckets.iter() {
                let this_bucket_ptr = this_bucket.load_consume(guard);

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

        // grow if inserting would push us over a load factor of 0.5
        if (len + 1) > (capacity / 2) {
            let next_array = self.grow(guard);

            return next_array.insert(bucket_ptr, hash, guard);
        }

        let grow_into_and_insert_into_next = || {
            let next_array_ptr = self.next_array.load_consume(guard);
            assert!(!next_array_ptr.is_null());
            let next_array = unsafe { next_array_ptr.deref() };
            // self.grow_into(next_array, guard);

            next_array.insert(bucket_ptr, hash, guard)
        };

        let offset = (hash & (capacity - 1) as u64) as usize;
        let mut have_seen_redirect = false;

        for this_bucket in (0..capacity)
            .map(|x| (x + offset) & (capacity - 1))
            .map(|i| &self.buckets[i])
        {
            loop {
                let this_bucket_ptr = this_bucket.load_consume(guard);

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
                    return grow_into_and_insert_into_next();
                }

                if this_bucket
                    .compare_and_set_weak(
                        this_bucket_ptr,
                        bucket_ptr,
                        (Ordering::Release, Ordering::Relaxed),
                        guard,
                    )
                    .is_ok()
                {
                    if should_increment_len {
                        // replaced a tombstone
                        self.len.fetch_add(1, Ordering::Relaxed);
                    }

                    return (
                        this_bucket_ptr,
                        (self as *const BucketArray<K, V, S>).into(),
                    );
                }
            }
        }

        if have_seen_redirect {
            grow_into_and_insert_into_next()
        } else {
            let next_array = self.grow(guard);

            next_array.insert(bucket_ptr, hash, guard)
        }
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
        let self_shared = (self as *const BucketArray<K, V, S>).into();

        let capacity = self.buckets.len();
        let offset = (hash & (capacity - 1) as u64) as usize;

        for this_bucket in (0..self.buckets.len())
            .map(|x| (x + offset) & (capacity - 1))
            .map(|i| &self.buckets[i])
        {
            let mut this_bucket_ptr = this_bucket.load_consume(guard);

            if let Some(this_bucket_ref) = unsafe { this_bucket_ptr.as_ref() } {
                if this_bucket_ref.key.borrow() != key {
                    // hash collision
                    continue;
                }
            }

            loop {
                if this_bucket_ptr.tag().has_redirect() {
                    let next_array = unsafe { self.get_next_unchecked(guard) };

                    return next_array.remove(key, hash, maybe_new_bucket, guard);
                }

                let this_bucket_ref =
                    if let Some(this_bucket_ref) = unsafe { this_bucket_ptr.as_ref() } {
                        if this_bucket_ref.is_tombstone() {
                            return (Shared::null(), self_shared);
                        }

                        this_bucket_ref
                    } else {
                        return (Shared::null(), self_shared);
                    };

                let new_bucket = match maybe_new_bucket.take() {
                    Some(b) => b,
                    None => Owned::new(Bucket {
                        key: this_bucket_ref.key.clone(),
                        maybe_value: None,
                    }),
                };

                match this_bucket.compare_and_set_weak(
                    this_bucket_ptr,
                    new_bucket,
                    (Ordering::Release, Ordering::Relaxed),
                    guard,
                ) {
                    Ok(_) => {
                        self.len.fetch_sub(1, Ordering::Relaxed);

                        return (this_bucket_ptr, self_shared);
                    }
                    Err(e) => {
                        maybe_new_bucket = Some(e.new);
                        let current_bucket_ptr = this_bucket.load_consume(guard);

                        // check is only necessary once -- keys never change
                        // after being inserted/removed
                        if this_bucket_ptr.is_null()
                            && unsafe { current_bucket_ptr.as_ref() }
                                .map(|b| b.key.borrow() != key)
                                .unwrap_or(false)
                        {
                            break;
                        }

                        this_bucket_ptr = current_bucket_ptr;
                    }
                }
            }
        }

        (Shared::null(), self_shared)
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
        let self_shared: Shared<'g, BucketArray<K, V, S>> = (self as *const Self).into();

        let capacity = self.buckets.len();
        let offset = (hash & (self.buckets.len() - 1) as u64) as usize;

        for this_bucket in (0..capacity)
            .map(|x| (x + offset) & (capacity - 1))
            .map(|i| &self.buckets[i])
        {
            let mut this_bucket_ptr = this_bucket.load_consume(guard);

            let mut this_bucket_ref = match unsafe { this_bucket_ptr.as_ref() } {
                Some(b) => {
                    // buckets will never have their key changed, so we only have to
                    // make this check once
                    if b.key.borrow() != key {
                        continue;
                    }

                    b
                }
                None => return (Shared::null(), self_shared),
            };

            let mut new_bucket_ptr = maybe_new_bucket_ptr.unwrap_or_else(|| {
                Owned::new(Bucket {
                    key: this_bucket_ref.key.clone(),
                    maybe_value: None,
                })
            });

            loop {
                if this_bucket_ptr.tag().has_redirect() {
                    let next_array_ptr = self.next_array.load_consume(guard);
                    assert!(!next_array_ptr.is_null());
                    let next_array = unsafe { next_array_ptr.deref() };
                    self.grow_into(next_array, guard);

                    return next_array.modify(key, hash, modifier, Some(new_bucket_ptr), guard);
                }

                let old_value = match this_bucket_ref.maybe_value.as_ref() {
                    Some(v) => v,
                    None => return (Shared::null(), self_shared),
                };

                new_bucket_ptr.maybe_value = Some(modifier(old_value));

                // i assume that a strong CAS is less expensive than invoking
                // modifier a second time
                match this_bucket.compare_and_set(
                    this_bucket_ptr,
                    new_bucket_ptr,
                    (Ordering::Release, Ordering::Relaxed),
                    guard,
                ) {
                    Ok(_) => return (this_bucket_ptr, self_shared),
                    Err(e) => {
                        new_bucket_ptr = e.new;

                        this_bucket_ptr = this_bucket.load_consume(guard);
                        assert!(!this_bucket_ptr.is_null());

                        this_bucket_ref = unsafe { this_bucket_ptr.deref() };
                    }
                }
            }
        }

        (Shared::null(), self_shared)
    }

    fn insert_or_modify<G: FnOnce() -> V, F: FnMut(&V) -> V>(
        &self,
        mut key_or_bucket: KeyOrBucket<K, V>,
        hash: u64,
        mut inserter: FunctionOrValue<G, V>,
        mut modifier: F,
        guard: &'g Guard,
    ) -> BucketAndParent<'g, K, V, S> {
        let self_shared = (self as *const BucketArray<K, V, S>).into();

        let capacity = self.buckets.len();
        let len = self.len.load(Ordering::Relaxed);

        let insert_into_next = |key_or_bucket, inserter, modifier| {
            let next_array_ptr = self.next_array.load_consume(guard);
            assert!(!next_array_ptr.is_null());
            let next_array = unsafe { next_array_ptr.deref() };
            self.grow_into(next_array, guard);

            next_array.insert_or_modify(key_or_bucket, hash, inserter, modifier, guard)
        };

        // grow if inserting would push us over a load factor of 0.5
        if (len + 1) > (capacity / 2) {
            let next_array = self.grow(guard);

            return next_array.insert_or_modify(key_or_bucket, hash, inserter, modifier, guard);
        }

        let offset = (hash & (capacity - 1) as u64) as usize;
        let mut have_seen_redirect = false;

        for this_bucket in (0..capacity)
            .map(|x| (x + offset) & (capacity - 1))
            .map(|i| &self.buckets[i])
        {
            let mut this_bucket_ptr = this_bucket.load_consume(guard);

            have_seen_redirect = have_seen_redirect || this_bucket_ptr.tag().has_redirect();

            // if the bucket pointer is non-null and its key does not match, move to the next bucket
            if !this_bucket_ptr.tag().has_redirect()
                && unsafe { this_bucket_ptr.as_ref() }
                    .map(|this_bucket_ref| &this_bucket_ref.key != key_or_bucket.as_key())
                    .unwrap_or(false)
            {
                continue;
            }

            loop {
                if this_bucket_ptr.tag().has_redirect() {
                    return insert_into_next(key_or_bucket, inserter, modifier);
                }

                let new_value = unsafe { this_bucket_ptr.as_ref() }
                    .and_then(|this_bucket_ref| this_bucket_ref.maybe_value.as_ref())
                    .map(&mut modifier)
                    .unwrap_or_else(|| inserter.into_value());
                let new_bucket_ptr = key_or_bucket.into_bucket_with_value(new_value);

                // i assume it is more expensive to invoke modifier than it is
                // to strong CAS
                match this_bucket.compare_and_set(
                    this_bucket_ptr,
                    new_bucket_ptr,
                    (Ordering::Release, Ordering::Relaxed),
                    guard,
                ) {
                    Ok(_) => {
                        if this_bucket_ptr.is_null() {
                            self.len.fetch_add(1, Ordering::Relaxed);
                        }

                        return BucketAndParent {
                            bucket: this_bucket_ptr,
                            parent: self_shared,
                        };
                    }
                    Err(mut e) => {
                        inserter = FunctionOrValue::Value(e.new.maybe_value.take().unwrap());
                        key_or_bucket = KeyOrBucket::Bucket(e.new);

                        have_seen_redirect = have_seen_redirect || e.current.tag().has_redirect();

                        // if another thread inserted into this bucket, check to see if its key
                        // matches the one we are trying to insert/modify
                        if this_bucket_ptr.is_null()
                            && !e.current.tag().has_redirect()
                            && unsafe { e.current.as_ref() }
                                .map(|this_bucket_ref| {
                                    &this_bucket_ref.key != key_or_bucket.as_key()
                                })
                                .unwrap_or(false)
                        {
                            continue;
                        }

                        this_bucket_ptr = this_bucket.load_consume(guard);
                    }
                }
            }
        }

        let next_array = if have_seen_redirect {
            let next_array_ptr = self.next_array.load_consume(guard);
            assert!(!next_array_ptr.is_null());

            let next_array = unsafe { next_array_ptr.deref() };
            self.grow_into(next_array, guard);

            next_array
        } else {
            self.grow(guard)
        };

        next_array.insert_or_modify(key_or_bucket, hash, inserter, modifier, guard)
    }

    fn grow(&self, guard: &'g Guard) -> &'g BucketArray<K, V, S> {
        let maybe_next_array_ptr = self.next_array.load_consume(guard);

        if let Some(next_array) = unsafe { maybe_next_array_ptr.as_ref() } {
            self.grow_into(next_array, guard);

            return next_array;
        }

        let allocated_array_ptr = Owned::new(BucketArray::with_capacity_hasher_and_epoch(
            self.buckets.len() * 2,
            self.hash_builder.clone(),
            self.epoch + 1,
        ));

        let next_array_ptr = match self.next_array.compare_and_set(
            Shared::null(),
            allocated_array_ptr,
            (Ordering::Release, Ordering::Relaxed),
            guard,
        ) {
            Ok(next_array_ptr) => next_array_ptr,
            Err(_) => self.next_array.load_consume(guard),
        };

        assert!(!next_array_ptr.is_null());
        let next_array = unsafe { next_array_ptr.deref() };

        self.grow_into(next_array, guard);

        next_array
    }

    fn grow_into(&self, next_array: &'g BucketArray<K, V, S>, guard: &'g Guard) {
        for this_bucket in self.buckets.iter() {
            let mut this_bucket_ptr = this_bucket.load_consume(guard);

            // if we insert a bucket that is then tombstone-d, we need to
            // insert into the new bucket arrays
            let mut maybe_hash = None;

            loop {
                if this_bucket_ptr.tag().has_redirect() {
                    break;
                }

                // if we already inserted this bucket, or if this bucket is
                // non-null and not a tombstone
                if maybe_hash.is_some()
                    || !unsafe { this_bucket_ptr.as_ref() }
                        .map(Bucket::is_tombstone)
                        .unwrap_or(true)
                {
                    assert!(!this_bucket_ptr.is_null());

                    let hash = maybe_hash.unwrap_or_else(|| {
                        let key = unsafe { &this_bucket_ptr.deref().key };

                        self.get_hash(key)
                    });

                    next_array.insert(this_bucket_ptr, hash, guard);
                    maybe_hash = Some(hash);
                }

                // strong CAS to avoid spurious duplicate re-insertions
                match this_bucket.compare_and_set(
                    this_bucket_ptr,
                    this_bucket_ptr.with_tag(this_bucket_ptr.tag().with_redirect()),
                    (Ordering::Release, Ordering::Relaxed),
                    guard,
                ) {
                    Ok(_) => break,
                    Err(_) => this_bucket_ptr = this_bucket.load_consume(guard),
                }
            }
        }
    }

    unsafe fn get_next_unchecked(&self, guard: &'g Guard) -> &'g BucketArray<K, V, S> {
        let next_array_ptr = self.next_array.load_consume(guard);
        assert!(!next_array_ptr.is_null());

        let next_array = next_array_ptr.deref();
        self.grow_into(next_array, guard);

        next_array
    }
}

struct BucketAndParent<'a, K: Hash + Eq, V, S: BuildHasher> {
    bucket: Shared<'a, Bucket<K, V>>,
    parent: Shared<'a, BucketArray<K, V, S>>,
}

#[repr(align(2))]
struct Bucket<K: Hash + Eq, V> {
    key: K,
    maybe_value: Option<V>,
}

enum FunctionOrValue<F: FnOnce() -> T, T> {
    Function(F),
    Value(T),
}

impl<F: FnOnce() -> T, T> FunctionOrValue<F, T> {
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

enum KeyOrBucket<K: Hash + Eq, V> {
    Key(K),
    Bucket(Owned<Bucket<K, V>>),
}

impl<K: Hash + Eq, V> KeyOrBucket<K, V> {
    fn into_bucket_with_value(self, value: V) -> Owned<Bucket<K, V>> {
        match self {
            KeyOrBucket::Key(key) => Owned::new(Bucket {
                key,
                maybe_value: Some(value),
            }),
            KeyOrBucket::Bucket(mut bucket_ptr) => {
                bucket_ptr.maybe_value = Some(value);

                bucket_ptr
            }
        }
    }

    fn as_key(&self) -> &K {
        match self {
            KeyOrBucket::Key(key) => &key,
            KeyOrBucket::Bucket(bucket) => &bucket.key,
        }
    }
}
