// Copyright © 2024 Andrea Corbellini and contributors
// SPDX-License-Identifier: BSD-3-Clause

//! Wrappers for lazy-initialization of the Teaspoon allocator.
//!
//! See [`LazyTeaspoon`] for information and examples.

use crate::sizing::Sizing;
use crate::sizing::Sizing128KiB;
use crate::sizing::Sizing16MiB;
use crate::sizing::Sizing4KiB;
use crate::Teaspoon;
use core::alloc::GlobalAlloc;
use core::alloc::Layout;
use core::ops::Deref;
use spin::Lazy;

#[cfg(feature = "allocator-api")]
use core::alloc::AllocError;
#[cfg(feature = "allocator-api")]
use core::alloc::Allocator;
#[cfg(feature = "allocator-api")]
use core::ptr::NonNull;

/// Lazy-initialized version of [`Teaspoon128KiB`](crate::Teaspoon128KiB).
///
/// This can be used in `static` items. See the documentation for [`LazyTeaspoon`] for more
/// information and examples.
#[cfg(feature = "lazy")]
pub type LazyTeaspoon128KiB<F = fn() -> Teaspoon<'static, Sizing128KiB>> =
    LazyTeaspoon<Sizing128KiB, F>;

/// Lazy-initialized version of [`Teaspoon16MiB`](crate::Teaspoon16MiB).
///
/// This can be used in `static` items. See the documentation for [`LazyTeaspoon`] for more
/// information and examples.
#[cfg(feature = "lazy")]
pub type LazyTeaspoon16MiB<F = fn() -> Teaspoon<'static, Sizing16MiB>> =
    LazyTeaspoon<Sizing16MiB, F>;

/// Lazy-initialized version of [`Teaspoon4KiB`](crate::Teaspoon4KiB).
///
/// This can be used in `static` items. See the documentation for [`LazyTeaspoon`] for more
/// information and examples.
#[cfg(feature = "lazy")]
pub type LazyTeaspoon4KiB<F = fn() -> Teaspoon<'static, Sizing4KiB>> = LazyTeaspoon<Sizing4KiB, F>;

/// Lazy-initialized version of [`Teaspoon`].
///
/// This allows constructing a [`Teaspoon`] allocator *lazily*, which means: the allocator is not
/// constructed when `LazyTeaspoon` is constructed, but when `LazyTeaspoon` is first accessed.
///
/// `LazyTeaspoon` implements [`GlobalAlloc`] and [`Allocator`], so it can be used in all places
/// where `Teaspoon` would be accepted.
///
/// The main purpose of `LazyTeaspoon` is to be used in `static` items. This is particularly useful
/// when you want to use the Teaspoon allocator as a [global
/// allocator](https://doc.rust-lang.org/stable/std/alloc/index.html#the-global_allocator-attribute).
///
/// # Examples
///
/// ```
/// # #![allow(static_mut_refs)]
/// use teaspoon::lazy::LazyTeaspoon4KiB;
/// use teaspoon::Teaspoon4KiB;
///
/// #[global_allocator]
/// static SPOON: LazyTeaspoon4KiB = LazyTeaspoon4KiB::new(|| {
///     static mut MEMORY: [u8; 1024] = [0u8; 1024];
///     // SAFETY: This closure is called only once, therefore `MEMORY` is entirely owned by
///     // this `Teaspoon4KiB`, and no other reference can be created.
///     Teaspoon4KiB::from(unsafe { &mut MEMORY })
/// });
///
/// // Use the `GlobalAlloc` trait on `LazyTeaspoon`. If this is the first time `SPOON` is used,
/// // the underlaying `Teaspoon` will be initialized now.
/// use std::alloc::GlobalAlloc;
/// use std::alloc::Layout;
/// let _ = unsafe { SPOON.alloc(Layout::new::<u32>()) };
/// ```
#[derive(Debug)]
pub struct LazyTeaspoon<S: Sizing, F = fn() -> Teaspoon<'static, S>>(Lazy<Teaspoon<'static, S>, F>);

impl<S: Sizing, F> LazyTeaspoon<S, F> {
    /// Constructs a new [`LazyTeaspoon`] from the given initialization function.
    ///
    /// The initialization function will be called when the `LazyTeaspoon` is first used. "Used"
    /// here means either dereferencing, or using one of the implemented traits.
    #[inline]
    #[must_use]
    pub const fn new(f: F) -> Self {
        Self(Lazy::new(f))
    }
}

impl<S: Sizing, F: FnOnce() -> Teaspoon<'static, S>> LazyTeaspoon<S, F> {
    /// Returns a reference to the underlaying `Teaspoon`.
    ///
    /// Calling this method is equivalent to dereferencing (`lazy.get()` is equivalent to
    /// `&*lazy`).
    ///
    /// This method can be used to ensure that the Teaspoon allocator is initialized.
    #[inline]
    pub fn get(&self) -> &Teaspoon<'static, S> {
        self
    }
}

impl<S: Sizing, F: FnOnce() -> Teaspoon<'static, S>> Deref for LazyTeaspoon<S, F> {
    type Target = Teaspoon<'static, S>;

    #[inline]
    fn deref(&self) -> &Teaspoon<'static, S> {
        &self.0
    }
}

#[cfg(feature = "allocator-api")]
unsafe impl<S: Sizing, F: FnOnce() -> Teaspoon<'static, S>> Allocator for LazyTeaspoon<S, F> {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        self.get().allocate(layout)
    }

    fn allocate_zeroed(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        self.get().allocate_zeroed(layout)
    }

    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        self.get().deallocate(ptr, layout)
    }

    unsafe fn grow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError> {
        self.get().grow(ptr, old_layout, new_layout)
    }

    unsafe fn grow_zeroed(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError> {
        self.get().grow_zeroed(ptr, old_layout, new_layout)
    }

    unsafe fn shrink(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError> {
        self.get().shrink(ptr, old_layout, new_layout)
    }
}

unsafe impl<S: Sizing, F: FnOnce() -> Teaspoon<'static, S>> GlobalAlloc for LazyTeaspoon<S, F> {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        self.get().alloc(layout)
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        self.get().alloc_zeroed(layout)
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        self.get().dealloc(ptr, layout)
    }

    unsafe fn realloc(&self, ptr: *mut u8, old_layout: Layout, new_size: usize) -> *mut u8 {
        self.get().realloc(ptr, old_layout, new_size)
    }
}
