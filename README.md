# cht

[![crates.io](https://img.shields.io/crates/v/cht.svg)](https://crates.io/crates/cht)
[![docs.rs](https://docs.rs/cht/badge.svg)](https://docs.rs/cht)
[![Travis CI](https://travis-ci.com/Gregory-Meyer/cht.svg?branch=master)](https://travis-ci.com/Gregory-Meyer/cht)

cht provides a lockfree hash table that supports fully concurrent lookups,
insertions, modifications, and deletions. The table may also be concurrently
resized to allow more elements to be inserted. cht also provides a segmented
hash table using the same lockfree algorithm for increased concurrent write
performance.

## Usage

In your `Cargo.toml`:

```toml
cht = "^0.4.1"
```

Then in your code:

```rust
use cht::HashMap;

use std::{sync::Arc, thread};

let map = Arc::new(HashMap::new());

let threads: Vec<_> = (0..16)
    .map(|i| {
        let map = map.clone();

        thread::spawn(move || {
            const NUM_INSERTIONS: usize = 64;

            for j in (i * NUM_INSERTIONS)..((i + 1) * NUM_INSERTIONS) {
                map.insert_and(j, j, |prev| assert_eq!(prev, None));
            }
        })
    })
    .collect();

let _: Vec<_> = threads.into_iter().map(|t| t.join()).collect();
```

## License

cht is licensed under the MIT license.
