use ccl::dhashmap::DHashMap;

use std::{
    sync::{
        atomic::{AtomicBool, Ordering},
        Arc,
    },
    thread,
};

use criterion::{criterion_group, criterion_main, Criterion};

fn bench_single_thread_insertion(c: &mut Criterion) {
    c.bench_function_over_inputs(
        "ccl: single threaded insertion",
        |b, &&numel| {
            let map = DHashMap::default();

            for i in 0..numel {
                map.insert(i, i);
            }

            b.iter(|| map.insert(criterion::black_box(numel + 1), numel + 1))
        },
        [8, 64, 512, 4096, 32768].into_iter(),
    );
}

fn bench_multi_thread_insertion(c: &mut Criterion) {
    const NUM_THREADS: usize = 64;

    let map = Arc::new(DHashMap::default());
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

    c.bench_function("ccl: multithreaded insertion", move |b| {
        b.iter(|| map.insert(criterion::black_box(NUM_THREADS + 1), NUM_THREADS + 1))
    });

    keep_going.store(false, Ordering::SeqCst);

    let _: Vec<_> = threads.into_iter().map(|t| t.join()).collect();
}

fn bench_multi_thread_contended_insertion(c: &mut Criterion) {
    const NUM_THREADS: usize = 64;

    let map = Arc::new(DHashMap::default());
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

    c.bench_function("ccl: contended multithreaded insertion", move |b| {
        b.iter(|| map.insert(criterion::black_box(0), 0))
    });

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
