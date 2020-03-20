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

use super::*;

use crate::common::{Bucket, BucketRef};

use std::sync::atomic::Ordering;

impl<'g, K: 'g + Eq, V: 'g> Table<K, V> {
    pub(crate) fn insert_or_modify<F: FnOnce() -> V, G: FnMut(&K, &V) -> V>(
        &self,
        guard: &'g Guard,
        hash: u64,
        state: InsertOrModifyState<K, V, F>,
        mut modifier: G,
    ) -> BucketResult<'g, K, V, (InsertOrModifyState<K, V, F>, G)> {
        let mut maybe_state = Some(state);

        match self.probe_loop(
            hash,
            |_, j, these_control_bytes, control, expected, this_bucket| {
                let state = maybe_state.take().unwrap();
                let this_bucket_ptr = this_bucket.load_consume(guard);

                let (new_bucket, maybe_insert_value) =
                    match unsafe { Bucket::as_ref(this_bucket_ptr) } {
                        BucketRef::Filled(this_key, this_value) if this_key == state.key() => {
                            let new_value = modifier(this_key, this_value);

                            let (new_bucket, insert_value) = state.into_modify_bucket(new_value);

                            (new_bucket, Some(insert_value))
                        }
                        BucketRef::Tombstone(this_key) if this_key == state.key() => {
                            (state.into_insert_bucket(), None)
                        }
                        BucketRef::Filled(_, _) | BucketRef::Tombstone(_) => {
                            maybe_state = Some(state);

                            return ProbeLoopAction::Continue;
                        }
                        BucketRef::Null => {
                            assert_eq!(expected, 0);

                            if self.num_nonnull_buckets.load(Ordering::Relaxed) >= self.capacity() {
                                return ProbeLoopAction::Return(Err(state));
                            }

                            (state.into_insert_bucket(), None)
                        }
                        BucketRef::Sentinel => {
                            return ProbeLoopAction::Return(Err(state));
                        }
                    };

                if let Err(CompareAndSetError { new, .. }) = this_bucket.compare_and_set_weak(
                    this_bucket_ptr,
                    new_bucket,
                    (Ordering::Release, Ordering::Relaxed),
                    guard,
                ) {
                    maybe_state = Some(InsertOrModifyState::from_bucket_value(
                        new,
                        maybe_insert_value,
                    ));

                    ProbeLoopAction::Reload
                } else {
                    these_control_bytes.set(expected, j, control);

                    if this_bucket_ptr.is_null() {
                        self.num_nonnull_buckets.fetch_add(1, Ordering::Relaxed);
                    }

                    ProbeLoopAction::Return(Ok(this_bucket_ptr))
                }
            },
        ) {
            ProbeLoopResult::Returned(Ok(previous_bucket_ptr)) => Ok(previous_bucket_ptr),
            ProbeLoopResult::Returned(Err(state)) => Err((state, modifier)),
            ProbeLoopResult::LoopEnded => Ok(Shared::null()),
            ProbeLoopResult::FoundSentinelTag => Err((maybe_state.unwrap(), modifier)),
        }
    }
}

pub(crate) enum InsertOrModifyState<K, V, F: FnOnce() -> V> {
    New(K, F),
    AttemptedInsertion(Owned<Bucket<K, V>>),
    AttemptedModification(Owned<Bucket<K, V>>, ValueOrFunction<V, F>),
}

impl<K, V, F: FnOnce() -> V> InsertOrModifyState<K, V, F> {
    fn from_bucket_value(
        bucket: Owned<Bucket<K, V>>,
        value_or_function: Option<ValueOrFunction<V, F>>,
    ) -> Self {
        if let Some(value_or_function) = value_or_function {
            Self::AttemptedModification(bucket, value_or_function)
        } else {
            Self::AttemptedInsertion(bucket)
        }
    }

    fn key(&self) -> &K {
        match self {
            InsertOrModifyState::New(k, _) => &k,
            InsertOrModifyState::AttemptedInsertion(b)
            | InsertOrModifyState::AttemptedModification(b, _) => &b.key,
        }
    }

    fn into_insert_bucket(self) -> Owned<Bucket<K, V>> {
        match self {
            InsertOrModifyState::New(k, f) => Bucket::new(k, f()),
            InsertOrModifyState::AttemptedInsertion(b) => b,
            InsertOrModifyState::AttemptedModification(b, v_or_f) => {
                Bucket::with_value(b, v_or_f.into_value()).0
            }
        }
    }

    fn into_modify_bucket(self, value: V) -> (Owned<Bucket<K, V>>, ValueOrFunction<V, F>) {
        match self {
            InsertOrModifyState::New(k, f) => (Bucket::new(k, value), ValueOrFunction::Function(f)),
            InsertOrModifyState::AttemptedInsertion(b) => {
                let (bucket_ptr, insert_value) = Bucket::with_value(b, value);

                (bucket_ptr, ValueOrFunction::Value(insert_value))
            }
            InsertOrModifyState::AttemptedModification(bucket_ptr, v_or_f) => {
                (Bucket::with_value(bucket_ptr, value).0, v_or_f)
            }
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
