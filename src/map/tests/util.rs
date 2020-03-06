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
    borrow::{Borrow, BorrowMut},
    hash::{Hash, Hasher},
    ops::{Deref, DerefMut},
    sync::{
        atomic::{AtomicBool, Ordering},
        Arc,
    },
};

use crossbeam_epoch::Owned;

#[derive(Debug)]
pub(crate) struct NoisyDropper<T: ?Sized> {
    parent: Arc<DropNotifier>,
    pub elem: T,
}

impl<T> NoisyDropper<T> {
    pub(crate) fn new(parent: Arc<DropNotifier>, elem: T) -> Self {
        Self { parent, elem }
    }
}

impl<T: ?Sized> Drop for NoisyDropper<T> {
    fn drop(&mut self) {
        assert_eq!(self.parent.dropped.swap(true, Ordering::Relaxed), false);
    }
}

impl<T: ?Sized + PartialEq> PartialEq for NoisyDropper<T> {
    fn eq(&self, other: &Self) -> bool {
        self.elem == other.elem
    }
}

impl<T: ?Sized + PartialEq> PartialEq<T> for NoisyDropper<T> {
    fn eq(&self, other: &T) -> bool {
        &self.elem == other
    }
}

impl<T: ?Sized + Eq> Eq for NoisyDropper<T> {}

impl<T: ?Sized + Hash> Hash for NoisyDropper<T> {
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        self.elem.hash(hasher);
    }
}

impl<T: ?Sized> AsRef<T> for NoisyDropper<T> {
    fn as_ref(&self) -> &T {
        &self.elem
    }
}

impl<T: ?Sized> AsMut<T> for NoisyDropper<T> {
    fn as_mut(&mut self) -> &mut T {
        &mut self.elem
    }
}

impl<T: ?Sized> Borrow<T> for NoisyDropper<T> {
    fn borrow(&self) -> &T {
        &self.elem
    }
}

impl<T: ?Sized> BorrowMut<T> for NoisyDropper<T> {
    fn borrow_mut(&mut self) -> &mut T {
        &mut self.elem
    }
}

impl<T: ?Sized> Deref for NoisyDropper<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.elem
    }
}

impl<T: ?Sized> DerefMut for NoisyDropper<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.elem
    }
}

#[derive(Debug)]
pub(crate) struct DropNotifier {
    dropped: AtomicBool,
}

impl DropNotifier {
    pub(crate) fn new() -> Self {
        Self {
            dropped: AtomicBool::new(false),
        }
    }

    pub(crate) fn was_dropped(&self) -> bool {
        self.dropped.load(Ordering::Relaxed)
    }
}

pub(crate) fn run_deferred() {
    for _ in 0..65536 {
        let guard = crossbeam_epoch::pin();

        unsafe { guard.defer_destroy(Owned::new(0).into_shared(&guard)) };

        guard.flush();
    }
}
