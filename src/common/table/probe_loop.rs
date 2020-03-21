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

use super::{ControlByteGroup, Searcher, Table};

use crate::common::Bucket;

use crossbeam_epoch::Atomic;

pub(super) enum Action<T> {
    Continue,
    Reload,
    Return(T),
}

pub(super) enum Result<T> {
    LoopEnded,
    FoundSentinelTag,
    Returned(T),
}

pub(super) struct State<'a, K, V> {
    pub(super) hash_control_byte: u8,
    pub(super) group_index: usize,
    pub(super) this_control_byte_group: &'a ControlByteGroup,
    pub(super) group_offset: usize,
    pub(super) current_control_byte: u8,
    pub(super) this_bucket: &'a Atomic<Bucket<K, V>>,
}

impl<K, V> Clone for State<'_, K, V> {
    fn clone(&self) -> Self {
        Self {
            hash_control_byte: self.hash_control_byte,
            group_index: self.group_index,
            this_control_byte_group: self.this_control_byte_group,
            group_offset: self.group_offset,
            current_control_byte: self.current_control_byte,
            this_bucket: self.this_bucket,
        }
    }
}

impl<K, V> Copy for State<'_, K, V> {}

impl<K, V> State<'_, K, V> {
    pub(super) fn set_control_byte(self) {
        self.this_control_byte_group.set(
            self.current_control_byte,
            self.group_offset,
            self.hash_control_byte,
        );
    }
}

impl<'g, K: 'g, V: 'g> Table<K, V> {
    pub(super) fn probe_loop<F: FnMut(State<'_, K, V>) -> Action<T>, T>(
        &self,
        hash: u64,
        mut f: F,
    ) -> Result<T> {
        let (hash_control_byte, without_control) = split_hash(hash);
        let initial_group_index = without_control & self.modulo_mask;

        let searcher = Searcher::new(hash_control_byte);

        for group_index in (0..self.control_bytes.len())
            .map(|i| i.wrapping_add(initial_group_index) & self.modulo_mask)
        {
            let this_group = &self.groups[group_index];
            let this_control_byte_group = &self.control_bytes[group_index];

            let (mut zero_move_mask, mut query_move_mask) =
                if let Some((z, q)) = searcher.search(this_control_byte_group.load()) {
                    (z, q)
                } else {
                    return Result::FoundSentinelTag;
                };

            match (zero_move_mask, query_move_mask) {
                (0, 0) => continue, // no zeros and no matches; keep probing
                _ => {
                    while query_move_mask != 0 || zero_move_mask != 0 {
                        let query_tz = query_move_mask.trailing_zeros();
                        let zeros_tz = zero_move_mask.trailing_zeros();

                        assert_ne!(zeros_tz, query_tz);

                        let (group_offset, current_control_byte) = if zeros_tz < query_tz {
                            zero_move_mask &= !(1 << zeros_tz);

                            (zeros_tz as usize, 0)
                        } else {
                            query_move_mask &= !(1 << query_tz);

                            (query_tz as usize, hash_control_byte)
                        };

                        let this_bucket = &this_group.buckets[group_offset];

                        let state = State {
                            hash_control_byte,
                            group_index,
                            this_control_byte_group,
                            group_offset,
                            current_control_byte,
                            this_bucket,
                        };

                        loop {
                            match f(state) {
                                Action::Continue => break,
                                Action::Reload => (),
                                Action::Return(t) => return Result::Returned(t),
                            }
                        }
                    }
                }
            }
        }

        Result::LoopEnded
    }
}

fn split_hash(hash: u64) -> (u8, usize) {
    (
        (hash & 0b0111_1111) as u8 | 0b1000_0000,
        (hash >> 7) as usize,
    )
}
