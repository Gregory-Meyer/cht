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
    New {
        key: K,
        insert_function: F,
    },
    AttemptedInsertion {
        bucket: Owned<Bucket<K, V>>,
    },
    AttemptedModification {
        bucket: Owned<Bucket<K, V>>,
        insert_value_or_function: ValueOrFunction<V, F>,
    },
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
            State::New { key, .. } => &key,
            State::AttemptedInsertion { bucket } | State::AttemptedModification { bucket, .. } => {
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
            State::New {
                key,
                insert_function,
            } => (
                Bucket::new(key, new_value),
                ValueOrFunction::Function(insert_function),
            ),
            State::AttemptedInsertion { bucket } => {
                let (bucket, insert_value) = Bucket::with_value(bucket, new_value);

                (bucket, ValueOrFunction::Value(insert_value))
            }
            State::AttemptedModification {
                bucket,
                insert_value_or_function,
            } => (
                Bucket::with_value(bucket, new_value).0,
                insert_value_or_function,
            ),
        };

        let memento = (Some(value_or_function), modifier, table);

        Ok(Some((bucket, memento)))
    }

    fn on_tombstone(self, _: Shared<'_, Bucket<K, V>>, _: &K) -> MutateVisitResult<'g, K, V, Self> {
        self.on_null()
    }

    fn on_null(self) -> MutateVisitResult<'g, K, V, Self> {
        if !self.table.can_insert() {
            return Err(self);
        }

        let Visitor {
            state,
            modifier,
            table,
        } = self;

        let bucket = match state {
            State::New {
                key,
                insert_function,
            } => Bucket::new(key, insert_function()),
            State::AttemptedInsertion { bucket } => bucket,
            State::AttemptedModification {
                bucket,
                insert_value_or_function,
            } => Bucket::with_value(bucket, insert_value_or_function.into_value()).0,
        };

        let memento = (None, modifier, table);

        Ok(Some((bucket, memento)))
    }

    fn from_pointer(bucket: Owned<Bucket<K, V>>, memento: Self::Memento) -> Self {
        let (maybe_insert_value_or_function, modifier, table) = memento;

        let state = if let Some(insert_value_or_function) = maybe_insert_value_or_function {
            State::AttemptedModification {
                bucket,
                insert_value_or_function,
            }
        } else {
            State::AttemptedInsertion { bucket }
        };

        Self {
            state,
            modifier,
            table,
        }
    }
}
