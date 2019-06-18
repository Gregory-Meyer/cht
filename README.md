# cht

cht provides a lockfree hash table that supports concurrent lookups, insertions,
and deletions.

## Usage

In your `Cargo.toml`:

```toml
cht = "0.1"
```

Then in your code:

```rs
use cht::HashMap;

use std::{sync::Arc, thread};

let map = Arc::new(HashMap::new());

let threads: Vec<_> = (0..16)
    .map(|i| {
        let map = map.clone();

        thread::spawn(move || {
            for j in 0..64 {
                map.insert_and(j, j, |prev| assert_eq!(prev, None));
            }
        })
    })
    .collect();

let _: Vec<_> = threads.into_iter().map(|t| t.join()).collect();
```

## License

cht is licensed under the MIT license.
