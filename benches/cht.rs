use cht::HashMap;

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
        "cht: single threaded insertion",
        |b, &&numel| {
            let map = HashMap::new();

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

    let map = Arc::new(HashMap::new());
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

    c.bench_function("cht: multithreaded insertion", move |b| {
        b.iter(|| map.insert(criterion::black_box(num_threads + 1), num_threads + 1))
    });

    keep_going.store(false, Ordering::SeqCst);

    let _: Vec<_> = threads.into_iter().map(|t| t.join()).collect();
}

fn bench_multi_thread_contended_insertion(c: &mut Criterion) {
    let num_threads = num_cpus::get();

    let map = Arc::new(HashMap::new());
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

    c.bench_function("cht: contended multithreaded insertion", move |b| {
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
