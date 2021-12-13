// Copyright (C) 2020 Gregory Meyer
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Affero General Public License for more details.
//
// You should have received a copy of the GNU Affero General Public License
// along with this program.  If not, see <https://www.gnu.org/licenses/>.

#[macro_use]
pub(crate) mod tests;

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
