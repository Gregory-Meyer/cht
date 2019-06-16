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

pub mod map;
pub mod set;

pub use map::HashMap;
pub use set::HashSet;

#[cfg(test)]
mod tests {
    use super::*;

    use std::{
        sync::{Arc, Barrier},
        thread,
    };

    #[test]
    fn hash_map_basics() {
        let map = HashMap::with_capacity(8);

        assert_eq!(map.insert("foo".to_string(), 5), None);
        assert_eq!(map.insert("bar".to_string(), 10), None);
        assert_eq!(map.insert("baz".to_string(), 15), None);
        assert_eq!(map.insert("qux".to_string(), 20), None);

        assert_eq!(map.get("foo"), Some(5));
        assert_eq!(map.get("bar"), Some(10));
        assert_eq!(map.get("baz"), Some(15));
        assert_eq!(map.get("qux"), Some(20));

        assert_eq!(map.insert("qux".to_string(), 5), Some(20));
        assert_eq!(map.insert("baz".to_string(), 10), Some(15));
        assert_eq!(map.insert("bar".to_string(), 15), Some(10));
        assert_eq!(map.insert("foo".to_string(), 20), Some(5));
    }

    #[test]
    fn hash_map_growth() {
        const MAX_VALUE: i32 = 512;

        let map = HashMap::new();

        for i in 0..MAX_VALUE {
            assert_eq!(map.insert(i, i), None);
        }

        for i in 0..MAX_VALUE {
            assert_eq!(map.get(&i), Some(i));
            assert_eq!(map.insert(i, i), Some(i));
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

        let map = Arc::new(HashMap::new());
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

        let map = HashMap::new();

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

        let map = Arc::new(HashMap::with_capacity(MAX_INSERTED_VALUE as usize));

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
}
