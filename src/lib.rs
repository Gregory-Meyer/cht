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

//! Lockfree resizeable concurrent hash table.
//!
//! The hash table in this crate was inspired by
//! [a blog post by Jeff Phreshing], which describes the implementation of a
//! hash table in [Junction].
//!
//! [a blog post by Jeff Phreshing]: https://preshing.com/20160222/a-resizable-concurrent-map/
//! [Junction]: https://github.com/preshing/junction

pub mod map;

pub use map::HashMap;

#[cfg(test)]
mod tests {
    use super::*;

    use std::{
        sync::{Arc, Barrier},
        thread::{self, JoinHandle},
    };

    #[test]
    fn hash_map_insertion() {
        const MAX_VALUE: i32 = 512;

        let map = HashMap::with_capacity(MAX_VALUE as usize);

        for i in 0..MAX_VALUE {
            assert_eq!(map.insert(i, i), None);

            for j in 0..i {
                assert_eq!(map.get(&j), Some(j));
                assert_eq!(map.insert(j, j), Some(j));
            }
        }
    }

    #[test]
    fn hash_map_growth() {
        const MAX_VALUE: i32 = 512;

        let map = HashMap::with_capacity(1);

        for i in 0..MAX_VALUE {
            assert_eq!(map.insert(i, i), None);

            for j in 0..i {
                assert_eq!(map.get(&j), Some(j));
                assert_eq!(map.insert(j, j), Some(j));
            }
        }
    }

    #[test]
    fn hash_map_concurrent_insertion() {
        const MAX_VALUE: i32 = 512;
        const NUM_THREADS: usize = 64;
        const MAX_INSERTED_VALUE: i32 = (NUM_THREADS as i32) * MAX_VALUE;

        let map = Arc::new(HashMap::with_capacity(MAX_INSERTED_VALUE as usize));
        let barrier = Arc::new(Barrier::new(NUM_THREADS));

        let threads: Vec<_> = (0..NUM_THREADS)
            .map(|i| {
                let map = map.clone();
                let barrier = barrier.clone();

                thread::spawn(move || {
                    barrier.wait();

                    for j in (0..MAX_VALUE).map(|j| j + (i as i32 * MAX_VALUE)) {
                        assert_eq!(map.insert(j, j), None);
                    }
                })
            })
            .collect();

        for result in threads.into_iter().map(|t| t.join()) {
            assert!(result.is_ok());
        }

        assert_eq!(map.len(), MAX_INSERTED_VALUE as usize);

        for i in 0..MAX_INSERTED_VALUE {
            assert_eq!(map.get(&i), Some(i));
        }
    }

    #[test]
    fn hash_map_concurrent_growth() {
        const MAX_VALUE: i32 = 512;
        const NUM_THREADS: usize = 64;
        const MAX_INSERTED_VALUE: i32 = (NUM_THREADS as i32) * MAX_VALUE;

        let map = Arc::new(HashMap::with_capacity(1));
        let barrier = Arc::new(Barrier::new(NUM_THREADS));

        let threads: Vec<_> = (0..NUM_THREADS)
            .map(|i| {
                let map = map.clone();
                let barrier = barrier.clone();

                thread::spawn(move || {
                    barrier.wait();

                    for j in (0..MAX_VALUE).map(|j| j + (i as i32 * MAX_VALUE)) {
                        assert_eq!(map.insert(j, j), None);
                    }
                })
            })
            .collect();

        for result in threads.into_iter().map(|t| t.join()) {
            assert!(result.is_ok());
        }

        assert_eq!(map.len(), MAX_INSERTED_VALUE as usize);

        for i in 0..MAX_INSERTED_VALUE {
            assert_eq!(map.get(&i), Some(i));
        }
    }

    #[test]
    fn hash_map_removal() {
        const MAX_VALUE: i32 = 512;

        let map = HashMap::with_capacity(1);

        for i in 0..MAX_VALUE {
            assert_eq!(map.insert(i, i), None);
        }

        for i in 0..MAX_VALUE {
            assert_eq!(map.remove(&i), Some(i));
        }

        for i in 0..MAX_VALUE {
            assert_eq!(map.get(&i), None);
        }
    }

    #[test]
    fn hash_map_concurrent_removal() {
        const MAX_VALUE: i32 = 512;
        const NUM_THREADS: usize = 64;
        const MAX_INSERTED_VALUE: i32 = (NUM_THREADS as i32) * MAX_VALUE;

        let map = Arc::new(HashMap::with_capacity(1));

        for i in 0..MAX_INSERTED_VALUE {
            assert_eq!(map.insert(i, i), None);
        }

        let barrier = Arc::new(Barrier::new(NUM_THREADS));

        let threads: Vec<_> = (0..NUM_THREADS)
            .map(|i| {
                let map = map.clone();
                let barrier = barrier.clone();

                thread::spawn(move || {
                    barrier.wait();

                    for j in (0..MAX_VALUE).map(|j| j + (i as i32 * MAX_VALUE)) {
                        assert_eq!(map.remove(&j), Some(j));
                    }
                })
            })
            .collect();

        for result in threads.into_iter().map(|t| t.join()) {
            assert!(result.is_ok());
        }

        assert_eq!(map.len(), 0);

        for i in 0..MAX_INSERTED_VALUE {
            assert_eq!(map.get(&i), None);
        }
    }

    #[test]
    fn hash_map_concurrent_insertion_and_removal() {
        const MAX_VALUE: i32 = 512;
        const NUM_THREADS: usize = 64;
        const MAX_INSERTED_VALUE: i32 = (NUM_THREADS as i32) * MAX_VALUE * 2;
        const INSERTED_MIDPOINT: i32 = MAX_INSERTED_VALUE / 2;

        let map = Arc::new(HashMap::with_capacity(MAX_INSERTED_VALUE as usize));

        for i in INSERTED_MIDPOINT..MAX_INSERTED_VALUE {
            assert_eq!(map.insert(i, i), None);
        }

        let barrier = Arc::new(Barrier::new(NUM_THREADS * 2));

        let insert_threads: Vec<_> = (0..NUM_THREADS)
            .map(|i| {
                let map = map.clone();
                let barrier = barrier.clone();

                thread::spawn(move || {
                    barrier.wait();

                    for j in (0..MAX_VALUE).map(|j| j + (i as i32 * MAX_VALUE)) {
                        assert_eq!(map.insert(j, j), None);
                    }
                })
            })
            .collect();

        let remove_threads: Vec<_> = (0..NUM_THREADS)
            .map(|i| {
                let map = map.clone();
                let barrier = barrier.clone();

                thread::spawn(move || {
                    barrier.wait();

                    for j in (0..MAX_VALUE).map(|j| INSERTED_MIDPOINT + j + (i as i32 * MAX_VALUE))
                    {
                        assert_eq!(map.remove(&j), Some(j));
                    }
                })
            })
            .collect();

        for result in insert_threads
            .into_iter()
            .chain(remove_threads.into_iter())
            .map(|t| t.join())
        {
            assert!(result.is_ok());
        }

        assert_eq!(map.len(), INSERTED_MIDPOINT as usize);

        for i in 0..INSERTED_MIDPOINT {
            assert_eq!(map.get(&i), Some(i));
        }

        for i in INSERTED_MIDPOINT..MAX_INSERTED_VALUE {
            assert_eq!(map.get(&i), None);
        }
    }

    #[test]
    fn hash_map_concurrent_growth_and_removal() {
        const MAX_VALUE: i32 = 512;
        const NUM_THREADS: usize = 64;
        const MAX_INSERTED_VALUE: i32 = (NUM_THREADS as i32) * MAX_VALUE * 2;
        const INSERTED_MIDPOINT: i32 = MAX_INSERTED_VALUE / 2;

        let map = Arc::new(HashMap::with_capacity(1));

        for i in INSERTED_MIDPOINT..MAX_INSERTED_VALUE {
            assert_eq!(map.insert(i, i), None);
        }

        let barrier = Arc::new(Barrier::new(NUM_THREADS * 2));

        let insert_threads: Vec<_> = (0..NUM_THREADS)
            .map(|i| {
                let map = map.clone();
                let barrier = barrier.clone();

                thread::spawn(move || {
                    barrier.wait();

                    for j in (0..MAX_VALUE).map(|j| j + (i as i32 * MAX_VALUE)) {
                        assert_eq!(map.insert(j, j), None);
                    }
                })
            })
            .collect();

        let remove_threads: Vec<_> = (0..NUM_THREADS)
            .map(|i| {
                let map = map.clone();
                let barrier = barrier.clone();

                thread::spawn(move || {
                    barrier.wait();

                    for j in (0..MAX_VALUE).map(|j| INSERTED_MIDPOINT + j + (i as i32 * MAX_VALUE))
                    {
                        assert_eq!(map.remove(&j), Some(j));
                    }
                })
            })
            .collect();

        for result in insert_threads
            .into_iter()
            .chain(remove_threads.into_iter())
            .map(|t| t.join())
        {
            assert!(result.is_ok());
        }

        assert_eq!(map.len(), INSERTED_MIDPOINT as usize);

        for i in 0..INSERTED_MIDPOINT {
            assert_eq!(map.get(&i), Some(i));
        }

        for i in INSERTED_MIDPOINT..MAX_INSERTED_VALUE {
            assert_eq!(map.get(&i), None);
        }
    }

    #[test]
    fn hash_map_modify() {
        let map = HashMap::new();

        assert_eq!(map.modify("foo", |x| x * 2), None);

        map.insert("foo", 1);
        assert_eq!(map.modify("foo", |x| x * 2), Some(1));

        map.remove("foo");
        assert_eq!(map.modify("foo", |x| x * 2), None);
    }

    #[test]
    fn hash_map_concurrent_modification() {
        const MAX_VALUE: i64 = 512;
        const NUM_THREADS: usize = 64;
        const MAX_INSERTED_VALUE: i64 = (NUM_THREADS as i64) * MAX_VALUE;

        let map = Arc::new(HashMap::new());

        for i in 0..MAX_INSERTED_VALUE {
            map.insert(i, i);
        }

        let threads: Vec<_> = (0..NUM_THREADS)
            .map(|i| {
                let map = map.clone();

                thread::spawn(move || {
                    for j in (i as i64 * MAX_VALUE)..((i as i64 + 1) * MAX_VALUE) {
                        assert_eq!(map.modify(&j, |x| x * 2), Some(j));
                    }
                })
            })
            .collect();

        for result in threads.into_iter().map(JoinHandle::join) {
            assert!(result.is_ok());
        }

        for i in 0..MAX_INSERTED_VALUE {
            assert_eq!(map.get(&i), Some(i * 2));
        }
    }

    #[test]
    fn hash_map_insert_or_modify() {
        let map = HashMap::new();

        assert_eq!(map.insert_or_modify("foo", 1, |x| x + 1), None);
        assert_eq!(map.get("foo"), Some(1));

        assert_eq!(map.insert_or_modify("foo", 1, |x| x + 1), Some(1));
        assert_eq!(map.get("foo"), Some(2));
    }

    #[test]
    fn hash_map_concurrent_insert_or_modify() {
        const NUM_THREADS: usize = 64;
        const MAX_VALUE: i32 = 512;

        let map = Arc::new(HashMap::new());

        let threads: Vec<_> = (0..NUM_THREADS)
            .map(|_| {
                let map = map.clone();

                thread::spawn(move || {
                    for j in 0..MAX_VALUE {
                        map.insert_or_modify(j, 1, |x| x + 1);
                    }
                })
            })
            .collect();

        for result in threads.into_iter().map(JoinHandle::join) {
            assert!(result.is_ok());
        }

        assert_eq!(map.len(), MAX_VALUE as usize);

        for i in 0..MAX_VALUE {
            assert_eq!(map.get(&i), Some(NUM_THREADS as i32));
        }
    }

    #[test]
    fn hash_map_concurrent_insert_overlapped() {
        const NUM_THREADS: usize = 64;
        const MAX_VALUE: i32 = 512;

        let map = Arc::new(HashMap::new());

        let threads: Vec<_> = (0..NUM_THREADS)
            .map(|_| {
                let map = map.clone();

                thread::spawn(move || {
                    for j in 0..MAX_VALUE {
                        map.insert(j, j);
                    }
                })
            })
            .collect();

        for result in threads.into_iter().map(JoinHandle::join) {
            assert!(result.is_ok());
        }

        assert_eq!(map.len(), MAX_VALUE as usize);

        for i in 0..MAX_VALUE {
            assert_eq!(map.get(&i), Some(i));
        }
    }
}
