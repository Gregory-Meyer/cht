use cht::HashMap;

use std::{
    sync::{
        atomic::{AtomicBool, Ordering},
        Arc,
    },
    thread,
    time::Duration,
};

fn main() {
    const NUM_THREADS: usize = 64;

    let keep_running = Arc::new(AtomicBool::new(true));
    let map = Arc::new(HashMap::new());
    let threads: Vec<_> = (0..NUM_THREADS)
        .map(|_| {
            let keep_running = keep_running.clone();
            let map = map.clone();

            thread::spawn(move || {
                while keep_running.load(Ordering::Relaxed) {
                    map.insert(0, 0);
                }
            })
        })
        .collect();

    thread::sleep(Duration::from_secs(5));
    keep_running.store(false, Ordering::Relaxed);

    let results = threads.into_iter().map(|t| t.join());

    for result in results.into_iter() {
        assert!(result.is_ok());
    }
}
