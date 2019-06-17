use std::{
    borrow::Borrow,
    hash::{BuildHasher, Hash},
    mem,
    sync::{
        atomic::{AtomicBool, Ordering},
        Arc,
    },
    thread,
};

use criterion::{criterion_group, criterion_main, Criterion};
use fxhash::FxBuildHasher;
use hashbrown::{hash_map::Entry, HashMap};
use parking_lot::RwLock;

struct ConcurrentHashMap<K: Hash + Eq, V, S: BuildHasher> {
    map: RwLock<HashMap<K, Arc<RwLock<V>>, S>>,
}

impl<K: Hash + Eq, V> ConcurrentHashMap<K, V, FxBuildHasher> {
    fn new() -> ConcurrentHashMap<K, V, FxBuildHasher> {
        ConcurrentHashMap {
            map: RwLock::new(HashMap::with_hasher(FxBuildHasher::default())),
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

    fn get<Q: Hash + Eq + ?Sized>(&self, key: &Q) -> Option<Arc<RwLock<V>>>
    where
        K: Borrow<Q>,
    {
        let guard = self.map.read();
        guard.get(key).cloned()
    }
}

fn bench_single_thread_insertion(c: &mut Criterion) {
    let map = ConcurrentHashMap::new();

    c.bench_function(
        "hashbrown/parking_lot: single threaded insertion",
        move |b| b.iter(|| map.insert(criterion::black_box(5), 5)),
    );
}

fn bench_multi_thread_insertion(c: &mut Criterion) {
    const NUM_THREADS: usize = 64;

    let map = Arc::new(ConcurrentHashMap::new());
    let keep_going = Arc::new(AtomicBool::new(true));

    let threads: Vec<_> = (0..NUM_THREADS - 1)
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
            map.insert(criterion::black_box(NUM_THREADS + 1), NUM_THREADS + 1);
        })
    });

    keep_going.store(false, Ordering::SeqCst);

    let _: Vec<_> = threads.into_iter().map(|t| t.join()).collect();
}

fn bench_multi_thread_contended_insertion(c: &mut Criterion) {
    const NUM_THREADS: usize = 64;

    let map = Arc::new(ConcurrentHashMap::new());
    let keep_going = Arc::new(AtomicBool::new(true));

    let threads: Vec<_> = (0..NUM_THREADS - 1)
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
