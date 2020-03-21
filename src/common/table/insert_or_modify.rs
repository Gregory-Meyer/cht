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

use super::{BucketResult, MutateResult, MutateVisitResult, MutateVisitor, Table};

use crate::common::Bucket;

use std::sync::atomic::Ordering;

use crossbeam_epoch::{Guard, Owned, Shared};

impl<'g, K: 'g + Eq, V: 'g> Table<K, V> {
    pub(crate) fn insert_or_modify<F: FnOnce() -> V, G: FnMut(&K, &V) -> V>(
        &self,
        guard: &'g Guard,
        hash: u64,
        state: State<K, V, F>,
        modifier: G,
    ) -> BucketResult<'g, K, V, (State<K, V, F>, G)> {
        match self.mutate(
            guard,
            hash,
            Visitor {
                state,
                modifier,
                table: self,
            },
        ) {
            MutateResult::Returned(r) => r.map_err(Visitor::into_state_modifier),
            MutateResult::LoopEnded(visitor) | MutateResult::FoundSentinelTag(visitor) => {
                Err(visitor.into_state_modifier())
            }
        }
    }
}

pub(crate) enum State<K, V, F: FnOnce() -> V> {
    New(K, F),
    AttemptedInsertion(Owned<Bucket<K, V>>),
    AttemptedModification(Owned<Bucket<K, V>>, ValueOrFunction<V, F>),
}

struct Visitor<'a, K, V, F: FnOnce() -> V, G: FnMut(&K, &V) -> V> {
    state: State<K, V, F>,
    modifier: G,
    table: &'a Table<K, V>,
}

impl<'a, K, V, F: FnOnce() -> V, G: FnMut(&K, &V) -> V> Visitor<'a, K, V, F, G> {
    fn into_state_modifier(self) -> (State<K, V, F>, G) {
        let Visitor {
            state, modifier, ..
        } = self;

        (state, modifier)
    }
}

impl<'g, 'a, K, V, F: FnOnce() -> V, G: FnMut(&K, &V) -> V> MutateVisitor<'g, K, V>
    for Visitor<'a, K, V, F, G>
{
    type Memento = (Option<ValueOrFunction<V, F>>, G, &'a Table<K, V>);
    type Pointer = Owned<Bucket<K, V>>;
    type Key = K;

    fn key(&self) -> &K {
        match &self.state {
            State::New(key, _) => &key,
            State::AttemptedInsertion(bucket) | State::AttemptedModification(bucket, _) => {
                &bucket.key
            }
        }
    }

    fn on_filled(
        self,
        _: Shared<'_, Bucket<K, V>>,
        key: &K,
        value: &V,
    ) -> MutateVisitResult<'g, K, V, Self> {
        let Visitor {
            state,
            mut modifier,
            table,
        } = self;

        let new_value = modifier(key, value);

        let (bucket, value_or_function) = match state {
            State::New(k, f) => (Bucket::new(k, new_value), ValueOrFunction::Function(f)),
            State::AttemptedInsertion(b) => {
                let (bucket_ptr, insert_value) = Bucket::with_value(b, new_value);

                (bucket_ptr, ValueOrFunction::Value(insert_value))
            }
            State::AttemptedModification(bucket_ptr, v_or_f) => {
                (Bucket::with_value(bucket_ptr, new_value).0, v_or_f)
            }
        };

        let memento = (Some(value_or_function), modifier, table);

        Ok(Some((bucket, memento)))
    }

    fn on_tombstone(self, _: Shared<'_, Bucket<K, V>>, _: &K) -> MutateVisitResult<'g, K, V, Self> {
        self.on_null()
    }

    fn on_null(self) -> MutateVisitResult<'g, K, V, Self> {
        if self.table.num_nonnull_buckets.load(Ordering::Relaxed) >= self.table.capacity() {
            return Err(self);
        }

        let Visitor {
            state,
            modifier,
            table,
        } = self;

        let bucket = match state {
            State::New(k, f) => Bucket::new(k, f()),
            State::AttemptedInsertion(b) => b,
            State::AttemptedModification(b, v_or_f) => Bucket::with_value(b, v_or_f.into_value()).0,
        };

        let memento = (None, modifier, table);

        Ok(Some((bucket, memento)))
    }

    fn from_pointer(bucket: Owned<Bucket<K, V>>, memento: Self::Memento) -> Self {
        let (maybe_value_or_function, modifier, table) = memento;

        let state = if let Some(value_or_function) = maybe_value_or_function {
            State::AttemptedModification(bucket, value_or_function)
        } else {
            State::AttemptedInsertion(bucket)
        };

        Self {
            state,
            modifier,
            table,
        }
    }
}

pub(crate) enum ValueOrFunction<V, F: FnOnce() -> V> {
    Value(V),
    Function(F),
}

impl<V, F: FnOnce() -> V> ValueOrFunction<V, F> {
    fn into_value(self) -> V {
        match self {
            ValueOrFunction::Value(v) => v,
            ValueOrFunction::Function(f) => f(),
        }
    }
}
