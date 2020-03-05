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

mod util;

use util::{DropNotifier, NoisyDropper};

use super::*;

use std::{
    iter,
    sync::{Arc, Barrier},
    thread::{self, JoinHandle},
};

#[test]
fn insertion() {
    const MAX_VALUE: i32 = 512;

    let map = HashMap::with_capacity(MAX_VALUE as usize);

    for i in 0..MAX_VALUE {
        assert_eq!(map.insert(i, i), None);

        assert!(!map.is_empty());
        assert_eq!(map.len(), (i + 1) as usize);

        for j in 0..=i {
            assert_eq!(map.get(&j), Some(j));
            assert_eq!(map.insert(j, j), Some(j));
        }

        for k in i + 1..MAX_VALUE {
            assert_eq!(map.get(&k), None);
        }
    }
}

#[test]
fn growth() {
    const MAX_VALUE: i32 = 512;

    let map = HashMap::new();

    for i in 0..MAX_VALUE {
        assert_eq!(map.insert(i, i), None);

        assert!(!map.is_empty());
        assert_eq!(map.len(), (i + 1) as usize);

        for j in 0..=i {
            assert_eq!(map.get(&j), Some(j));
            assert_eq!(map.insert(j, j), Some(j));
        }

        for k in i + 1..MAX_VALUE {
            assert_eq!(map.get(&k), None);
        }
    }
}

#[test]
fn concurrent_insertion() {
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

    for result in threads.into_iter().map(JoinHandle::join) {
        assert!(result.is_ok());
    }

    assert!(!map.is_empty());
    assert_eq!(map.len(), MAX_INSERTED_VALUE as usize);

    for i in 0..MAX_INSERTED_VALUE {
        assert_eq!(map.get(&i), Some(i));
    }
}

#[test]
fn concurrent_growth() {
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

    assert!(!map.is_empty());
    assert_eq!(map.len(), MAX_INSERTED_VALUE as usize);

    for i in 0..MAX_INSERTED_VALUE {
        assert_eq!(map.get(&i), Some(i));
    }
}

#[test]
fn removal() {
    const MAX_VALUE: i32 = 512;

    let map = HashMap::with_capacity(MAX_VALUE as usize);

    for i in 0..MAX_VALUE {
        assert_eq!(map.insert(i, i), None);
    }

    for i in 0..MAX_VALUE {
        assert_eq!(map.remove(&i), Some(i));
    }

    assert!(map.is_empty());
    assert_eq!(map.len(), 0);

    for i in 0..MAX_VALUE {
        assert_eq!(map.get(&i), None);
    }
}

#[test]
fn concurrent_removal() {
    const MAX_VALUE: i32 = 512;
    const NUM_THREADS: usize = 64;
    const MAX_INSERTED_VALUE: i32 = (NUM_THREADS as i32) * MAX_VALUE;

    let map = HashMap::with_capacity(MAX_INSERTED_VALUE as usize);

    for i in 0..MAX_INSERTED_VALUE {
        assert_eq!(map.insert(i, i), None);
    }

    let map = Arc::new(map);
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
fn concurrent_insertion_and_removal() {
    const MAX_VALUE: i32 = 512;
    const NUM_THREADS: usize = 64;
    const MAX_INSERTED_VALUE: i32 = (NUM_THREADS as i32) * MAX_VALUE * 2;
    const INSERTED_MIDPOINT: i32 = MAX_INSERTED_VALUE / 2;

    let map = HashMap::with_capacity(MAX_INSERTED_VALUE as usize);

    for i in INSERTED_MIDPOINT..MAX_INSERTED_VALUE {
        assert_eq!(map.insert(i, i), None);
    }

    let map = Arc::new(map);
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

                for j in (0..MAX_VALUE).map(|j| INSERTED_MIDPOINT + j + (i as i32 * MAX_VALUE)) {
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

    assert!(!map.is_empty());
    assert_eq!(map.len(), INSERTED_MIDPOINT as usize);

    for i in 0..INSERTED_MIDPOINT {
        assert_eq!(map.get(&i), Some(i));
    }

    for i in INSERTED_MIDPOINT..MAX_INSERTED_VALUE {
        assert_eq!(map.get(&i), None);
    }
}

#[test]
fn concurrent_growth_and_removal() {
    const MAX_VALUE: i32 = 512;
    const NUM_THREADS: usize = 64;
    const MAX_INSERTED_VALUE: i32 = (NUM_THREADS as i32) * MAX_VALUE * 2;
    const INSERTED_MIDPOINT: i32 = MAX_INSERTED_VALUE / 2;

    let map = HashMap::with_capacity(INSERTED_MIDPOINT as usize);

    for i in INSERTED_MIDPOINT..MAX_INSERTED_VALUE {
        assert_eq!(map.insert(i, i), None);
    }

    let map = Arc::new(map);
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

                for j in (0..MAX_VALUE).map(|j| INSERTED_MIDPOINT + j + (i as i32 * MAX_VALUE)) {
                    assert_eq!(map.remove(&j), Some(j));
                }
            })
        })
        .collect();

    for result in insert_threads
        .into_iter()
        .chain(remove_threads.into_iter())
        .map(JoinHandle::join)
    {
        assert!(result.is_ok());
    }

    assert!(!map.is_empty());
    assert_eq!(map.len(), INSERTED_MIDPOINT as usize);

    for i in 0..INSERTED_MIDPOINT {
        assert_eq!(map.get(&i), Some(i));
    }

    for i in INSERTED_MIDPOINT..MAX_INSERTED_VALUE {
        assert_eq!(map.get(&i), None);
    }
}

#[test]
fn modify() {
    let map = HashMap::new();

    assert!(map.is_empty());
    assert_eq!(map.len(), 0);

    assert_eq!(map.modify("foo", |_, x| x * 2), None);

    assert!(map.is_empty());
    assert_eq!(map.len(), 0);

    map.insert("foo", 1);
    assert_eq!(map.modify("foo", |_, x| x * 2), Some(1));

    assert!(!map.is_empty());
    assert_eq!(map.len(), 1);

    map.remove("foo");
    assert_eq!(map.modify("foo", |_, x| x * 2), None);

    assert!(map.is_empty());
    assert_eq!(map.len(), 0);
}

#[test]
fn concurrent_modification() {
    const MAX_VALUE: i32 = 512;
    const NUM_THREADS: usize = 64;
    const MAX_INSERTED_VALUE: i32 = (NUM_THREADS as i32) * MAX_VALUE;

    let map = HashMap::with_capacity(MAX_INSERTED_VALUE as usize);

    for i in 0..MAX_INSERTED_VALUE {
        map.insert(i, i);
    }

    let map = Arc::new(map);
    let barrier = Arc::new(Barrier::new(NUM_THREADS));

    let threads: Vec<_> = (0..NUM_THREADS)
        .map(|i| {
            let map = map.clone();
            let barrier = barrier.clone();

            thread::spawn(move || {
                barrier.wait();

                for j in (i as i32 * MAX_VALUE)..((i as i32 + 1) * MAX_VALUE) {
                    assert_eq!(map.modify(j, |_, x| x * 2), Some(j));
                }
            })
        })
        .collect();

    for result in threads.into_iter().map(JoinHandle::join) {
        assert!(result.is_ok());
    }

    assert!(!map.is_empty());
    assert_eq!(map.len(), MAX_INSERTED_VALUE as usize);

    for i in 0..MAX_INSERTED_VALUE {
        assert_eq!(map.get(&i), Some(i * 2));
    }
}

#[test]
fn concurrent_overlapped_modification() {
    const MAX_VALUE: i32 = 512;
    const NUM_THREADS: usize = 64;

    let map = HashMap::with_capacity(MAX_VALUE as usize);

    for i in 0..MAX_VALUE {
        assert_eq!(map.insert(i, 0), None);
    }

    let map = Arc::new(map);
    let barrier = Arc::new(Barrier::new(NUM_THREADS));

    let threads: Vec<_> = (0..NUM_THREADS)
        .map(|_| {
            let map = map.clone();
            let barrier = barrier.clone();

            thread::spawn(move || {
                barrier.wait();

                for i in 0..MAX_VALUE {
                    assert!(map.modify(i, |_, x| x + 1).is_some());
                }
            })
        })
        .collect();

    for result in threads.into_iter().map(JoinHandle::join) {
        assert!(result.is_ok());
    }

    assert!(!map.is_empty());
    assert_eq!(map.len(), MAX_VALUE as usize);

    for i in 0..MAX_VALUE {
        assert_eq!(map.get(&i), Some(NUM_THREADS as i32));
    }
}

#[test]
fn insert_or_modify() {
    let map = HashMap::new();

    assert_eq!(map.insert_or_modify("foo", 1, |_, x| x + 1), None);
    assert_eq!(map.get("foo"), Some(1));

    assert_eq!(map.insert_or_modify("foo", 1, |_, x| x + 1), Some(1));
    assert_eq!(map.get("foo"), Some(2));
}

#[test]
fn concurrent_insert_or_modify() {
    const NUM_THREADS: usize = 64;
    const MAX_VALUE: i32 = 512;

    let map = Arc::new(HashMap::new());
    let barrier = Arc::new(Barrier::new(NUM_THREADS));

    let threads: Vec<_> = (0..NUM_THREADS)
        .map(|_| {
            let map = map.clone();
            let barrier = barrier.clone();

            thread::spawn(move || {
                barrier.wait();

                for j in 0..MAX_VALUE {
                    map.insert_or_modify(j, 1, |_, x| x + 1);
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
fn concurrent_overlapped_insertion() {
    const NUM_THREADS: usize = 64;
    const MAX_VALUE: i32 = 512;

    let map = Arc::new(HashMap::with_capacity(MAX_VALUE as usize));
    let barrier = Arc::new(Barrier::new(NUM_THREADS));

    let threads: Vec<_> = (0..NUM_THREADS)
        .map(|_| {
            let map = map.clone();
            let barrier = barrier.clone();

            thread::spawn(move || {
                barrier.wait();

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

#[test]
fn concurrent_overlapped_growth() {
    const NUM_THREADS: usize = 64;
    const MAX_VALUE: i32 = 512;

    let map = Arc::new(HashMap::with_capacity(1));
    let barrier = Arc::new(Barrier::new(NUM_THREADS));

    let threads: Vec<_> = (0..NUM_THREADS)
        .map(|_| {
            let map = map.clone();
            let barrier = barrier.clone();

            thread::spawn(move || {
                barrier.wait();

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

#[test]
fn concurrent_overlapped_removal() {
    const NUM_THREADS: usize = 64;
    const MAX_VALUE: i32 = 512;

    let map = HashMap::with_capacity(MAX_VALUE as usize);

    for i in 0..MAX_VALUE {
        map.insert(i, i);
    }

    let map = Arc::new(map);
    let barrier = Arc::new(Barrier::new(NUM_THREADS));

    let threads: Vec<_> = (0..NUM_THREADS)
        .map(|_| {
            let map = map.clone();
            let barrier = barrier.clone();

            thread::spawn(move || {
                barrier.wait();

                for j in 0..MAX_VALUE {
                    let prev_value = map.remove(&j);

                    if let Some(v) = prev_value {
                        assert_eq!(v, j);
                    }
                }
            })
        })
        .collect();

    for result in threads.into_iter().map(JoinHandle::join) {
        assert!(result.is_ok());
    }

    assert!(map.is_empty());
    assert_eq!(map.len(), 0);

    for i in 0..MAX_VALUE {
        assert_eq!(map.get(&i), None);
    }
}

#[test]
fn drop_value() {
    let key_parent = Arc::new(DropNotifier::new());
    let value_parent = Arc::new(DropNotifier::new());

    {
        let map = HashMap::new();

        assert_eq!(
            map.insert_and(
                NoisyDropper::new(key_parent.clone(), 0),
                NoisyDropper::new(value_parent.clone(), 0),
                |_| ()
            ),
            None
        );
        assert!(!map.is_empty());
        assert_eq!(map.len(), 1);
        map.get_and(&0, |v| assert_eq!(v, &0));

        map.remove_and(&0, |v| assert_eq!(v, &0));
        assert!(map.is_empty());
        assert_eq!(map.len(), 0);
        assert_eq!(map.get_and(&0, |_| ()), None);

        util::run_deferred();

        assert!(!key_parent.was_dropped());
        assert!(value_parent.was_dropped());
    }

    util::run_deferred();

    assert!(key_parent.was_dropped());
    assert!(value_parent.was_dropped());
}

#[test]
fn drop_many_values() {
    const NUM_VALUES: usize = 1 << 16;

    let key_parents: Vec<_> = iter::repeat_with(|| Arc::new(DropNotifier::new()))
        .take(NUM_VALUES)
        .collect();
    let value_parents: Vec<_> = iter::repeat_with(|| Arc::new(DropNotifier::new()))
        .take(NUM_VALUES)
        .collect();

    {
        let map = HashMap::new();
        assert!(map.is_empty());
        assert_eq!(map.len(), 0);

        for (i, (this_key_parent, this_value_parent)) in
            key_parents.iter().zip(value_parents.iter()).enumerate()
        {
            assert_eq!(
                map.insert_and(
                    NoisyDropper::new(this_key_parent.clone(), i),
                    NoisyDropper::new(this_value_parent.clone(), i),
                    |_| ()
                ),
                None
            );

            assert!(!map.is_empty());
            assert_eq!(map.len(), i + 1);
        }

        for i in 0..NUM_VALUES {
            assert_eq!(
                map.get_key_value_and(&i, |k, v| {
                    assert_eq!(*k, i);
                    assert_eq!(*v, i);
                }),
                Some(())
            );
        }

        for i in 0..NUM_VALUES {
            assert_eq!(
                map.remove_entry_and(&i, |k, v| {
                    assert_eq!(*k, i);
                    assert_eq!(*v, i);
                }),
                Some(())
            );
        }

        assert!(map.is_empty());
        assert_eq!(map.len(), 0);

        util::run_deferred();

        for this_key_parent in key_parents.iter() {
            assert!(!this_key_parent.was_dropped());
        }

        for this_value_parent in value_parents.iter() {
            assert!(this_value_parent.was_dropped());
        }

        for i in 0..NUM_VALUES {
            assert_eq!(map.get_and(&i, |_| ()), None);
        }
    }

    util::run_deferred();

    for this_key_parent in key_parents.into_iter() {
        assert!(this_key_parent.was_dropped());
    }

    for this_value_parent in value_parents.into_iter() {
        assert!(this_value_parent.was_dropped());
    }
}

#[test]
fn drop_many_values_concurrent() {
    const NUM_THREADS: usize = 64;
    const NUM_VALUES_PER_THREAD: usize = 512;
    const NUM_VALUES: usize = NUM_THREADS * NUM_VALUES_PER_THREAD;

    let key_parents: Arc<Vec<_>> = Arc::new(
        iter::repeat_with(|| Arc::new(DropNotifier::new()))
            .take(NUM_VALUES)
            .collect(),
    );
    let value_parents: Arc<Vec<_>> = Arc::new(
        iter::repeat_with(|| Arc::new(DropNotifier::new()))
            .take(NUM_VALUES)
            .collect(),
    );

    {
        let map = Arc::new(HashMap::new());
        assert!(map.is_empty());
        assert_eq!(map.len(), 0);

        let barrier = Arc::new(Barrier::new(NUM_THREADS));

        let handles: Vec<_> = (0..NUM_THREADS)
            .map(|i| {
                let map = Arc::clone(&map);
                let barrier = Arc::clone(&barrier);
                let key_parents = Arc::clone(&key_parents);
                let value_parents = Arc::clone(&value_parents);

                thread::spawn(move || {
                    barrier.wait();

                    let these_key_parents =
                        &key_parents[i * NUM_VALUES_PER_THREAD..(i + 1) * NUM_VALUES_PER_THREAD];
                    let these_value_parents =
                        &value_parents[i * NUM_VALUES_PER_THREAD..(i + 1) * NUM_VALUES_PER_THREAD];

                    for (j, (this_key_parent, this_value_parent)) in these_key_parents
                        .iter()
                        .zip(these_value_parents.iter())
                        .enumerate()
                    {
                        let key_value = i * NUM_VALUES_PER_THREAD + j;

                        assert_eq!(
                            map.insert_and(
                                NoisyDropper::new(this_key_parent.clone(), key_value),
                                NoisyDropper::new(this_value_parent.clone(), key_value),
                                |_| ()
                            ),
                            None
                        );
                    }
                })
            })
            .collect();

        for result in handles.into_iter().map(JoinHandle::join) {
            assert!(result.is_ok());
        }

        assert!(!map.is_empty());
        assert_eq!(map.len(), NUM_VALUES);

        util::run_deferred();

        for this_key_parent in key_parents.iter() {
            assert!(!this_key_parent.was_dropped());
        }

        for this_value_parent in value_parents.iter() {
            assert!(!this_value_parent.was_dropped());
        }

        for i in 0..NUM_VALUES {
            assert_eq!(
                map.get_key_value_and(&i, |k, v| {
                    assert_eq!(*k, i);
                    assert_eq!(*v, i);
                }),
                Some(())
            );
        }

        let handles: Vec<_> = (0..NUM_THREADS)
            .map(|i| {
                let map = Arc::clone(&map);
                let barrier = Arc::clone(&barrier);

                thread::spawn(move || {
                    barrier.wait();

                    for j in 0..NUM_VALUES_PER_THREAD {
                        let key_value = i * NUM_VALUES_PER_THREAD + j;

                        assert_eq!(
                            map.remove_entry_and(&key_value, |k, v| {
                                assert_eq!(*k, key_value);
                                assert_eq!(*v, key_value);
                            }),
                            Some(())
                        );
                    }
                })
            })
            .collect();

        for result in handles.into_iter().map(JoinHandle::join) {
            assert!(result.is_ok());
        }

        assert!(map.is_empty());
        assert_eq!(map.len(), 0);

        util::run_deferred();

        for this_key_parent in key_parents.iter() {
            assert!(!this_key_parent.was_dropped());
        }

        for this_value_parent in value_parents.iter() {
            assert!(this_value_parent.was_dropped());
        }

        for i in 0..NUM_VALUES {
            assert_eq!(map.get_and(&i, |_| ()), None);
        }
    }

    util::run_deferred();

    for this_key_parent in key_parents.iter() {
        assert!(this_key_parent.was_dropped());
    }

    for this_value_parent in value_parents.iter() {
        assert!(this_value_parent.was_dropped());
    }
}
