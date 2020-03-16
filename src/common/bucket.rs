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
    mem::{self, ManuallyDrop},
    ops::{Deref, DerefMut},
    ptr,
    sync::atomic::{self, Ordering},
};

use crossbeam_epoch::{Guard, Owned, Shared};

#[repr(align(8))]
#[derive(Debug)]
pub(crate) struct Bucket<K, V> {
    pub(crate) key: K,
    maybe_value: ManuallyDrop<V>,
}

#[derive(Debug)]
pub(crate) enum BucketRef<'g, K, V> {
    Filled(&'g K, &'g V),
    Tombstone(&'g K),
    Null,
    Sentinel,
}

impl<K, V> Bucket<K, V> {
    pub(crate) fn new(key: K, value: V) -> Owned<Bucket<K, V>> {
        Owned::new(Bucket {
            key,
            maybe_value: ManuallyDrop::new(value),
        })
    }

    pub(crate) fn is_sentinel(self_ptr: Shared<'_, Self>) -> bool {
        if self_ptr.tag() & SENTINEL_TAG != 0 {
            assert!(self_ptr.is_null());

            true
        } else {
            false
        }
    }

    pub(crate) fn is_tombstone(self_ptr: Shared<'_, Self>) -> bool {
        if self_ptr.tag() & TOMBSTONE_TAG != 0 {
            assert!(!self_ptr.is_null());

            true
        } else {
            false
        }
    }

    pub(crate) fn is_borrowed(self_ptr: Shared<'_, Self>) -> bool {
        if self_ptr.tag() & BORROWED_TAG != 0 {
            assert!(!self_ptr.is_null());

            true
        } else {
            false
        }
    }

    pub(crate) unsafe fn as_ref(self_ptr: Shared<'_, Self>) -> BucketRef<'_, K, V> {
        if self_ptr.tag() & SENTINEL_TAG == 0 {
            self_ptr
                .as_ref()
                .map(|self_ref| {
                    assert_ne!(self_ptr.tag() & SENTINEL_TAG, SENTINEL_TAG);

                    if self_ptr.tag() & TOMBSTONE_TAG == 0 {
                        BucketRef::Filled(&self_ref.key, self_ref.maybe_value.deref())
                    } else {
                        BucketRef::Tombstone(&self_ref.key)
                    }
                })
                .unwrap_or_else(|| {
                    assert_ne!(self_ptr.tag() & TOMBSTONE_TAG, TOMBSTONE_TAG);
                    assert_ne!(self_ptr.tag() & BORROWED_TAG, BORROWED_TAG);

                    BucketRef::Null
                })
        } else {
            assert!(self_ptr.is_null());
            assert_eq!(self_ptr.tag(), SENTINEL_TAG);

            BucketRef::Sentinel
        }
    }

    pub(crate) fn sentinel<'g>() -> Shared<'g, Self> {
        Shared::null().with_tag(SENTINEL_TAG)
    }

    pub(crate) fn to_tombstone(self_ptr: Shared<'_, Self>) -> Shared<'_, Self> {
        assert!(!self_ptr.is_null());
        assert_ne!(self_ptr.tag() & SENTINEL_TAG, SENTINEL_TAG);
        assert_ne!(self_ptr.tag() & TOMBSTONE_TAG, TOMBSTONE_TAG);

        self_ptr.with_tag(TOMBSTONE_TAG)
    }

    pub(crate) fn to_borrowed(self_ptr: Shared<'_, Self>) -> Shared<'_, Self> {
        assert!(!self_ptr.is_null());
        assert_ne!(self_ptr.tag() & SENTINEL_TAG, SENTINEL_TAG);

        self_ptr.with_tag(self_ptr.tag() | BORROWED_TAG)
    }

    pub(crate) fn with_value(mut self_ptr: Owned<Self>, value: V) -> (Owned<Self>, V) {
        let previous_value = mem::replace(self_ptr.maybe_value.deref_mut(), value);

        (self_ptr, previous_value)
    }

    pub(crate) unsafe fn defer_destroy<'g>(guard: &'g Guard, mut self_ptr: Shared<'g, Self>) {
        assert!(!self_ptr.is_null());

        if self_ptr.tag() & TOMBSTONE_TAG == 0 {
            guard.defer_unchecked(move || {
                atomic::fence(Ordering::Acquire);

                ManuallyDrop::drop(&mut self_ptr.deref_mut().maybe_value);
                mem::drop(self_ptr.into_owned());
            });
        } else {
            guard.defer_unchecked(move || {
                atomic::fence(Ordering::Acquire);

                mem::drop(self_ptr.into_owned());
            });
        }
    }

    pub(crate) unsafe fn defer_destroy_value<'g>(guard: &'g Guard, mut self_ptr: Shared<'g, Self>) {
        assert!(!self_ptr.is_null());
        assert_ne!(self_ptr.tag() & TOMBSTONE_TAG, TOMBSTONE_TAG);

        let value = ptr::read(self_ptr.deref_mut().maybe_value.deref());

        // to be entirely honest, i don't know what order deferred functions are
        // called in crossbeam-epoch. in the case that the deferred functions are
        // called out of order, this prevents that from being an issue.
        guard.defer_unchecked(move || mem::drop(value));
    }

    pub(crate) unsafe fn drop(mut self_ptr: Shared<'_, Self>) {
        assert!(!self_ptr.is_null());
        assert_ne!(self_ptr.tag() & SENTINEL_TAG, SENTINEL_TAG);

        if self_ptr.tag() & TOMBSTONE_TAG == 0 {
            ManuallyDrop::drop(&mut self_ptr.deref_mut().maybe_value);
        }

        mem::drop(self_ptr.into_owned());
    }
}

const SENTINEL_TAG: usize = 0b001; // set on old table buckets when copied into a new table
const TOMBSTONE_TAG: usize = 0b010; // set when the value has been destroyed
const BORROWED_TAG: usize = 0b100; // set on new table buckets when copied from an old table
