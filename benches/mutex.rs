use std::{
    hash::{BuildHasher, Hash},
    mem,
    sync::{
        atomic::{AtomicBool, Ordering},
        Arc,
    },
    thread,
};

use ahash::ABuildHasher;
use criterion::{criterion_group, criterion_main, Criterion};
use hashbrown::{hash_map::Entry, HashMap};
use parking_lot::RwLock;

struct ConcurrentHashMap<K: Hash + Eq, V, S: BuildHasher> {
    map: RwLock<HashMap<K, Arc<RwLock<V>>, S>>,
}

impl<K: Hash + Eq, V> ConcurrentHashMap<K, V, ABuildHasher> {
    fn new() -> ConcurrentHashMap<K, V, ABuildHasher> {
        ConcurrentHashMap {
            map: RwLock::new(HashMap::with_hasher(ABuildHasher::default())),
        }
    }
}

impl<K: Hash + Eq, V, S: BuildHasher> ConcurrentHashMap<K, V, S> {
    fn insert(&self, key: K, mut value: V) -> Option<V> {
        {
            let guard = self.map.read();

            if let Some(bucket) = guard.get(&key) {
                let mut bucket_value = bucket.write();
                mem::swap(&mut *bucket_value, &mut value);

                return Some(value);
            }
        }

        let mut guard = self.map.write();

        match guard.entry(key) {
            Entry::Occupied(e) => {
                let mut bucket_value = e.get().write();
                mem::swap(&mut *bucket_value, &mut value);

                Some(value)
            }
            Entry::Vacant(e) => {
                e.insert(Arc::new(RwLock::new(value)));

                None
            }
        }
    }
}

fn bench_single_thread_insertion(c: &mut Criterion) {
    c.bench_function_over_inputs(
        "hashbrown/parking_lot: single threaded insertion",
        |b, &&numel| {
            let map = ConcurrentHashMap::new();

            for i in 0..numel {
                map.insert(i, i);
            }

            b.iter(|| map.insert(criterion::black_box(numel + 1), numel + 1))
        },
        [8, 64, 512, 4096, 32768].iter(),
    );
}

fn bench_multi_thread_insertion(c: &mut Criterion) {
    let num_threads = num_cpus::get();

    let map = Arc::new(ConcurrentHashMap::new());
    let keep_going = Arc::new(AtomicBool::new(true));

    let threads: Vec<_> = (0..num_threads - 1)
        .map(|i| {
            let map = map.clone();
            let keep_going = keep_going.clone();

            thread::spawn(move || {
                while keep_going.load(Ordering::SeqCst) {
                    map.insert(criterion::black_box(i), i);
                }
            })
        })
        .collect();

    c.bench_function("hashbrown/parking_lot: multithreaded insertion", move |b| {
        b.iter(|| {
            map.insert(criterion::black_box(num_threads + 1), num_threads + 1);
        })
    });

    keep_going.store(false, Ordering::SeqCst);

    let _: Vec<_> = threads.into_iter().map(|t| t.join()).collect();
}

fn bench_multi_thread_contended_insertion(c: &mut Criterion) {
    let num_threads = num_cpus::get();

    let map = Arc::new(ConcurrentHashMap::new());
    let keep_going = Arc::new(AtomicBool::new(true));

    let threads: Vec<_> = (0..num_threads - 1)
        .map(|_| {
            let map = map.clone();
            let keep_going = keep_going.clone();

            thread::spawn(move || {
                while keep_going.load(Ordering::SeqCst) {
                    map.insert(criterion::black_box(0), 0);
                }
            })
        })
        .collect();

    c.bench_function(
        "hashbrown/parking_lot: contended multithreaded insertion",
        move |b| {
            b.iter(|| {
                map.insert(criterion::black_box(0), 0);
            })
        },
    );

    keep_going.store(false, Ordering::SeqCst);

    let _: Vec<_> = threads.into_iter().map(|t| t.join()).collect();
}

criterion_group!(
    benches,
    bench_single_thread_insertion,
    bench_multi_thread_insertion,
    bench_multi_thread_contended_insertion,
);
criterion_main!(benches);
