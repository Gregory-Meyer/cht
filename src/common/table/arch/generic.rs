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

use std::{
    mem,
    sync::atomic::{AtomicU64, AtomicU8, Ordering},
};

pub(crate) const BUCKETS_PER_GROUP: usize = 8;

pub(crate) struct ControlByteGroup {
    bytes: AtomicU64,
}

impl ControlByteGroup {
    pub(crate) fn load(&self) -> u64 {
        self.bytes.load(Ordering::Relaxed)
    }

    pub(crate) fn set(&self, mut current: u8, index: u32, value: u8) {
        let addr = unsafe { &*(&self.bytes as *const _ as *const AtomicU8).offset(index as isize) };

        loop {
            if current == super::SENTINEL_CONTROL_BYTE || current == value {
                return;
            }

            current = if let Err(e) =
                addr.compare_exchange_weak(current, value, Ordering::Relaxed, Ordering::Relaxed)
            {
                e
            } else {
                return;
            };
        }
    }

    pub(crate) fn set_sentinel(&self, index: usize) {
        let addr = unsafe { &*(&self.bytes as *const _ as *const AtomicU8).add(index) };

        if addr.load(Ordering::Relaxed) == super::SENTINEL_CONTROL_BYTE {
            return;
        }

        addr.store(super::SENTINEL_CONTROL_BYTE, Ordering::Relaxed);
    }
}

pub(crate) struct Searcher {
    query: u8,
}

impl Searcher {
    pub(crate) fn new(query: u8) -> Self {
        Self { query }
    }

    pub(crate) fn search(&self, bytes: u64) -> Option<(u32, u32)> {
        if has_byte(bytes, super::SENTINEL_CONTROL_BYTE) {
            return None;
        }

        let has_zero = has_zero_byte(bytes);
        let has_query = has_byte(bytes, self.query);

        let as_bytes: [u8; 8] = unsafe { mem::transmute(bytes) };
        let mut zero_move_mask = 0;
        let mut query_move_mask = 0;

        if has_zero && has_query {
            for (i, b) in as_bytes.iter().cloned().enumerate() {
                if b == 0 {
                    zero_move_mask |= 1 << i;
                } else if b == self.query {
                    query_move_mask |= 1 << i;
                }
            }
        } else if has_zero {
            for (i, b) in as_bytes.iter().cloned().enumerate() {
                if b == 0 {
                    zero_move_mask |= 1 << i;
                }
            }
        } else if has_query {
            for (i, b) in as_bytes.iter().cloned().enumerate() {
                if b == self.query {
                    query_move_mask |= 1 << i;
                }
            }
        }

        Some((zero_move_mask, query_move_mask))
    }
}

fn has_zero_byte(v: u64) -> bool {
    ((v.overflowing_sub(0x0101_0101_0101_0101).0) & !v & 0x8080_8080_8080_8080) != 0
}

fn has_byte(v: u64, n: u8) -> bool {
    has_zero_byte(v ^ (u64::MAX / u8::MAX as u64 * n as u64))
}
