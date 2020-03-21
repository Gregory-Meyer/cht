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
    cell::UnsafeCell,
    sync::atomic::{AtomicU8, Ordering},
};

#[cfg(target_arch = "x86")]
use std::arch::x86 as stdarch;

#[cfg(target_arch = "x86_64")]
use std::arch::x86_64 as stdarch;

use stdarch::__m128i;

pub(crate) const BUCKETS_PER_GROUP: usize = 16;

pub(crate) struct ControlByteGroup {
    bytes: UnsafeCell<__m128i>,
}

impl ControlByteGroup {
    pub(crate) fn load(&self) -> __m128i {
        unsafe { stdarch::_mm_load_si128(self.bytes.get()) }
    }

    pub(crate) fn set(&self, mut current: u8, offset: usize, value: u8) {
        let addr = unsafe { &*((self.bytes.get() as *const u8).add(offset) as *const AtomicU8) };

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

    pub(crate) fn set_sentinel(&self, offset: usize) {
        let addr = unsafe { &*((self.bytes.get() as *const u8).add(offset) as *const AtomicU8) };

        if addr.load(Ordering::Relaxed) == super::SENTINEL_CONTROL_BYTE {
            return;
        }

        addr.store(super::SENTINEL_CONTROL_BYTE, Ordering::Relaxed);
    }
}

unsafe impl Send for ControlByteGroup {}
unsafe impl Sync for ControlByteGroup {}

pub(crate) struct Searcher {
    sentinel: __m128i,
    zero: __m128i,
    query: __m128i,
}

impl Searcher {
    pub(crate) fn new(query: u8) -> Self {
        Self {
            sentinel: unsafe { stdarch::_mm_set1_epi8(super::SENTINEL_CONTROL_BYTE as i8) },
            zero: unsafe { stdarch::_mm_setzero_si128() },
            query: unsafe { stdarch::_mm_set1_epi8(query as i8) },
        }
    }

    pub(crate) fn search(&self, bytes: __m128i) -> Option<(u32, u32)> {
        let sentinel_move_mask =
            unsafe { stdarch::_mm_movemask_epi8(stdarch::_mm_cmpeq_epi8(bytes, self.sentinel)) }
                as u32;

        if sentinel_move_mask != 0 {
            return None;
        }

        let zero_move_mask =
            unsafe { stdarch::_mm_movemask_epi8(stdarch::_mm_cmpeq_epi8(bytes, self.zero)) } as u32;
        let query_move_mask =
            unsafe { stdarch::_mm_movemask_epi8(stdarch::_mm_cmpeq_epi8(bytes, self.query)) }
                as u32;

        Some((zero_move_mask, query_move_mask))
    }
}
