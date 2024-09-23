// Copyright © 2024 Andrea Corbellini and contributors
// SPDX-License-Identifier: BSD-3-Clause

//! Teaspoon: an allocator for when all you have is a teaspoon of memory.
//!
//! Teaspoon is a lightweight memory allocator designed for minimal overhead. It's meant to be used
//! in situations where you have very limited memory available, or when you want to allocate
//! objects on the stack.
//!
//! Teaspoon is optimized for low memory overhead first, and performance second.
//!
//! This is a no-`std` and no-`alloc` crate, as such it does not interact with the operating system
//! to reserve memory pages; the allocatable memory needs to be provided by you as an input to
//! Teaspoon.
//!
//! # Features
//!
//! * Small memory overhead: starting at 4 bytes per allocated object
//! * Compatible with `no_std` environments
//! * Support for the nightly [`Allocator`](`core::alloc::Allocator`) API
//!
//! # Quick start & examples
//!
//! ## Initialization
//!
//! There are 3 variants of the allocator to choose from:
//!
//! * [`Teaspoon4KiB`]
//! * [`Teaspoon128KiB`]
//! * [`Teaspoon16MiB`]
//!
//! The size in the name (4KiB, 128KiB, 16MiB) refers to the **maximum size for an individual
//! allocated object**, and the total memory that can be allocated may be greater than that. For
//! example, with `Teaspoon4KiB`, you *cannot* allocate a 5000-byte object (because that exceeds
//! the 4 KiB = 4096 byte limit), but you *can* allocate two 3000-byte objects.
//!
//! Choosing the right variant is a matter of how much memory you have available, how much memory
//! you're willing to sacrifice for overhead, and performance. Smaller variants have smaller
//! overheads. Note that the smaller variants may not necessarily be the faster. All the
//! differences between the 3 allocator variants are described in [Allocator
//! limits](#allocator-limits).
//!
//! Because Teaspoon does not interact with the operating system, you'll need to initialize the
//! allocator with some contiguous memory area that you already have. If you know the address, you
//! can use one of [`Teaspoon::from_ptr`], [`Teaspoon::from_ptr_size`],
//! [`Teaspoon::from_addr_size`], like this:
//!
//! ```no_run
//! use teaspoon::Teaspoon4KiB;
//! # #[allow(unused_variables)]
//! let spoon = unsafe { Teaspoon4KiB::<'static>::from_addr_size(0xdeadbeef, 1024) };
//! ```
//!
//! You can also construct the allocator from a byte slice. This can be useful for example to
//! construct the allocator from an array on the stack:
//!
//! ```
//! use teaspoon::Teaspoon4KiB;
//! let mut memory = [0u8; 1024];
//! # #[allow(unused_variables)]
//! let spoon = Teaspoon4KiB::from(&mut memory);
//! ```
//!
//! You could also initialize the Teaspoon allocator from memory obtained from the operating system
//! like this:
//!
//! ```
//! use std::alloc::GlobalAlloc;
//! use std::alloc::Layout;
//! use std::alloc::System;
//! use teaspoon::Teaspoon4KiB;
//!
//! let size = 1024;
//! let ptr =
//!     unsafe { System.alloc(Layout::from_size_align(size, 4).expect("layout creation failed")) };
//! # #[allow(unused_variables)]
//! let spoon = unsafe { Teaspoon4KiB::from_ptr_size(ptr, size) };
//! # // dealloc to make miri checks pass
//! # unsafe { System.dealloc(ptr, Layout::from_size_align(size, 4).unwrap()) }
//! ```
//!
//! Regardless of how you initialize the Teaspoon allocator, you have two choices for using it:
//! using it as a [global allocator](core::alloc::GlobalAlloc) for your entire Rust program, or
//! using it through the new [Allocator API](core::alloc::Allocator) (currently available on the
//! nighly compiler only).
//!
//! ## Using as a global allocator
//!
//! Teaspoon can be used as a [custom global allocator via the `#[global_allocator]`
//! attribute](https://doc.rust-lang.org/stable/std/alloc/index.html#the-global_allocator-attribute).
//! Because `#[global_allocator]` requires a `static` item, it's not possible to use [`Teaspoon`]
//! objects directly, and instead lazy initialization is required. To aid with this, this crate
//! provides a [`LazyTeaspoon`](lazy::LazyTeaspoon) type that can be used as follows:
//!
//! `Cargo.toml`:
//!
//! ```toml
//! teaspoon = { version = "0.1", features = ["lazy"] }
//! ```
//!
//! `main.rs`:
//!
//! ```
//! # #[allow(static_mut_refs)]
//! # #[cfg(feature = "lazy")]
//! # {
//! use teaspoon::lazy::LazyTeaspoon4KiB;
//! use teaspoon::Teaspoon4KiB;
//!
//! #[global_allocator]
//! static SPOON: LazyTeaspoon4KiB = LazyTeaspoon4KiB::new(|| {
//!     static mut MEMORY: [u8; 1024] = [0u8; 1024];
//!     // SAFETY: This closure is called only once, therefore `MEMORY` is entirely owned by
//!     // this `Teaspoon4KiB`, and no other reference can be created.
//!     Teaspoon4KiB::from(unsafe { &mut MEMORY })
//! });
//! # }
//! ```
//!
//! [`LazyTeaspoon`](lazy::LazyTeaspoon) is initialized on first use by calling the initialization
//! function passed to [`new`](lazy::LazyTeaspoon::new).
//!
//! [`LazyTeaspoon`](lazy::LazyTeaspoon) is a simple wrapper around [`spin::Lazy`] (which is a
//! `no_std` equivalent to [`std::sync::LazyLock`]) that implements the [`GlobalAlloc`] and
//! [`Allocator`] traits. There's nothing too special about it--you can write your own custom
//! wrapper if you need to.
//!
//! [`std::sync::LazyLock`]: https://doc.rust-lang.org/stable/std/sync/struct.LazyLock.html
//!
//! ## Using via the Allocator API
//!
//! Teaspoon can be used as a custom allocator to be passed to the "`new_in`" methods of various
//! container types (such as [`Box::new_in`], [`Vec::new_in`], ...). Because the Allocator API is
//! currently experimental, it is only available in the Rust nightly compiler, and with
//! `#![feature(allocator_api)]`. It can be used as follows:
//!
//! [`Box::new_in`]: https://doc.rust-lang.org/stable/std/boxed/struct.Box.html#method.new_in
//! [`Vec::new_in`]: https://doc.rust-lang.org/stable/std/vec/struct.Vec.html#method.new_in
//!
//! `Cargo.toml`:
//!
//! ```toml
//! teaspoon = { version = "0.1", features = ["allocator-api"] }
//! ```
//!
//! `main.rs`:
//!
//! ```
//! #![feature(allocator_api)]
//!
//! # #[cfg(feature = "allocator-api")]
//! # {
//! use teaspoon::Teaspoon4KiB;
//!
//! let mut memory = [0u8; 1024];
//! let spoon = Teaspoon4KiB::from(&mut memory);
//!
//! let mut vec = Vec::<i32, _>::new_in(&spoon);
//! vec.push(1);
//! vec.push(2);
//! vec.push(3);
//! # }
//! ```
//!
//! # Allocator limits
//!
//! * **Arena Overhead:** amount of memory that is reserved for Teaspoon internal structures. This
//!   amount of memory is always used by Teaspoon, even when no objects are allocated.
//!
//! * **Object Overhead:** amount of extra memory that is allocated for every allocated object
//!   (with the exception of [zero-sized types], which have no overhead).
//!
//! * **Minimum Object Size:** minimum size that is always allocated for every object (with the
//!   exception of [zero-sized types]). If an allocation requests a size less than the minimum
//!   size, it is rounded up to the minimum size.
//!
//! * **Maximum Object Size:** maximum size that can be allocated to a single object. Allocations
//!   larger than the maximum size always fail. This does not mean that all allocations up to this
//!   maximum size will succeed: factors like available memory and memory fragmentation may result
//!   in an actual lower limit at runtime.
//!
//! * **Maximum Total Memory<sup>[note 1]</sup>:** maximum total memory that can be addressed by a
//!   Teaspoon object.
//!
//! |                    | Arena Overhead | Object Overhead | Minimum Object Size | Maximum Object Size     | Maximum Total Memory<sup>[note 1]</sup> |
//! |--------------------|----------------|-----------------|---------------------|-------------------------|-----------------------------------------|
//! | [`Teaspoon4KiB`]   | 4 bytes        | 4 bytes         | 4 bytes             | 4096 bytes (4 KiB)      | 8192 bytes (8 KiB)                      |
//! | [`Teaspoon128KiB`] | 4 bytes        | 6 bytes         | 2 bytes             | 131072 bytes (128 KiB)  | 131072 bytes (128 KiB)                  |
//! | [`Teaspoon16MiB`]  | 8 bytes        | 8 bytes         | 8 bytes             | 16777216 bytes (16 MiB) | 16777216 bytes (16 MiB)                 |
//!
//! **[note 1]:** this restriction may be lifted in a future version of this crate.
//!
//! [zero-sized types]: https://doc.rust-lang.org/nomicon/exotic-sizes.html#zero-sized-types-zsts
//!
//! # Internal details
//!
//! Teaspoon is a compact memory allocator using a doubly-linked list to track allocated objects,
//! and a [spin lock](https://en.wikipedia.org/wiki/Spinlock) to ensure thread safety.
//!
//! The "Object Overhead" listed in [Allocator limits](#allocator-limits) is used to store the
//! previous/next pointers of the linked list, and the size of the object. The "Arena Overhead" is
//! used to store the head/tail pointers of the linked list.
//!
//! # Cargo feature flags
//!
//! * `allocator-api`: enables the implementation of the [`core::alloc::Allocator`] trait (requires
//!   a nightly compiler).
//! * `lazy`: enables the [`LazyTeaspoon`](lazy::LazyTeaspoon) type along with its sized variants.

#![no_std]
#![cfg_attr(feature = "allocator-api", feature(allocator_api))]
#![warn(clippy::dbg_macro)]
#![warn(clippy::print_stderr)]
#![warn(clippy::print_stdout)]
#![warn(missing_debug_implementations)]
#![warn(missing_docs)]
#![warn(unreachable_pub)]
#![warn(unused_crate_dependencies)]
#![warn(unused_macro_rules)]
#![warn(unused_qualifications)]
#![doc(test(attr(deny(warnings))))]

mod arena;
mod iter;
mod ptr;
mod segment;
mod sizing;
mod usage;

#[cfg(test)]
mod tests;

#[cfg(feature = "lazy")]
pub mod lazy;

use crate::arena::Arena;
use crate::iter::ArenaChunks;
use crate::iter::Chunk;
use crate::ptr::SegmentDataPtr;
use crate::segment::Segment;
use core::alloc::GlobalAlloc;
use core::alloc::Layout;
use core::cmp;
use core::ptr::NonNull;
use spin::Mutex;

#[cfg(feature = "allocator-api")]
use core::alloc::AllocError;
#[cfg(feature = "allocator-api")]
use core::alloc::Allocator;

pub use crate::sizing::Sizing;
pub use crate::sizing::Sizing128KiB;
pub use crate::sizing::Sizing16MiB;
pub use crate::sizing::Sizing4KiB;
pub use crate::usage::Usage;

/// Allocator that supports allocating objects up to 128 KiB.
///
/// See the [module-level documentation](crate#allocator-limits) for more information about the
/// Teaspoon allocator variants and their sizing limits.
pub type Teaspoon128KiB<'a> = Teaspoon<'a, Sizing128KiB>;

/// Allocator that supports allocating objects up to 16 MiB.
///
/// See the [module-level documentation](crate#allocator-limits) for more information about the
/// Teaspoon allocator variants and their sizing limits.
pub type Teaspoon16MiB<'a> = Teaspoon<'a, Sizing16MiB>;

/// Allocator that supports allocating objects up to 4 KiB.
///
/// See the [module-level documentation](crate#allocator-limits) for more information about the
/// Teaspoon allocator variants and their sizing limits.
pub type Teaspoon4KiB<'a> = Teaspoon<'a, Sizing4KiB>;

/// The Teaspoon allocator.
///
/// The allocator comes in 3 variants that set different memory overheads and limits. The `S`
/// parameter specifies the variant, which may be:
///
/// * [`Sizing4KiB`]: allows allocating objects up to 4 KiB
/// * [`Sizing128KiB`]: allows allocating objects up to 128 KiB
/// * [`Sizing16MiB`]: allows allocating objects up to 16 MiB
///
/// See the [module-level documentation](crate#allocator-limits) for more information about
/// overheads and sizing limits.
///
/// `Teaspoon` can be constructed from either a pointer (unsafe) or a slice, and may be accessed
/// using either the [`GlobalAlloc`] or [`Allocator`] traits. See the [module-level
/// documentation](file:///home/andrea/src/teaspoon/target/doc/teaspoon/index.html#quick-start--examples)
/// for details and examples.
#[derive(Debug)]
pub struct Teaspoon<'a, S: Sizing> {
    inner: Mutex<TeaspoonInner<'a, S>>,
}

impl<'a, S: Sizing> Teaspoon<'a, S> {
    /// Constructs a Teaspoon memory allocator from a slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use teaspoon::Teaspoon4KiB;
    ///
    /// let mut memory = [0u8; 1024];
    /// # #[allow(unused_variables)]
    /// let spoon = Teaspoon4KiB::from_slice(&mut memory);
    /// ```
    #[inline]
    #[must_use]
    pub fn from_slice(slice: &'a mut [u8]) -> Self {
        Self {
            inner: Mutex::new(TeaspoonInner::from_slice(slice)),
        }
    }

    /// Constructs a Teaspoon memory allocator from a slice pointer.
    ///
    /// The pointer must be valid for both reads and writes, and must be alive for the lifetime of
    /// `'a`. Note that because there's no connection between the pointer and the lifetime `'a`,
    /// you must ensure that the pointer lives long enough; you cannot rely on the compiler to
    /// check that for you.
    ///
    /// # Panics
    ///
    /// If `ptr` is a null pointer.
    ///
    /// # Safety
    ///
    /// - `ptr` must be
    ///   ["dereferenceable"](https://doc.rust-lang.org/stable/std/ptr/index.html#safety).
    /// - `ptr` must be alive for the lifetime of `'a`.
    /// - `ptr` must not be an [*alias*](https://doc.rust-lang.org/nomicon/aliasing.html) for
    ///   another reference or pointer (in other words, `ptr` is a *unique* pointer).
    ///
    /// An exception to those rules is if the length of `ptr` is 0. In that case, `ptr` may be a
    /// dangling non-null pointer.
    ///
    /// # Examples
    ///
    /// ```
    /// use teaspoon::Teaspoon4KiB;
    ///
    /// let mut memory = [0u8; 1024];
    /// let ptr = std::ptr::slice_from_raw_parts_mut(memory.as_mut_ptr(), memory.len());
    /// # #[allow(unused_variables)]
    /// let spoon = unsafe { Teaspoon4KiB::from_ptr(ptr) };
    /// ```
    #[inline]
    #[must_use]
    pub unsafe fn from_ptr(ptr: *mut [u8]) -> Self {
        Self::from_ptr_size(ptr.cast(), ptr.len())
    }

    /// Constructs a Teaspoon memory allocator from a pointer and a size.
    ///
    /// The pointer must be valid for both reads and writes, and must be alive for the lifetime of
    /// `'a`. Note that because there's no connection between the pointer and the lifetime `'a`,
    /// you must ensure that the pointer lives long enough; you cannot rely on the compiler to
    /// check that for you.
    ///
    /// # Panics
    ///
    /// If `ptr` is a null pointer.
    ///
    /// # Safety
    ///
    /// - `ptr` must be
    ///   ["dereferenceable"](https://doc.rust-lang.org/stable/std/ptr/index.html#safety).
    /// - `ptr` must be alive for the lifetime of `'a`.
    /// - `ptr` must not be an [*alias*](https://doc.rust-lang.org/nomicon/aliasing.html) for
    ///   another reference or pointer (in other words, `ptr` is a *unique* pointer).
    ///
    /// An exception to those rules is if the `size` is 0. In that case, `ptr` may be a dangling
    /// non-null pointer.
    ///
    /// # Examples
    ///
    /// ```
    /// use teaspoon::Teaspoon4KiB;
    ///
    /// let mut memory = [0u8; 1024];
    /// # #[allow(unused_variables)]
    /// let spoon = unsafe { Teaspoon4KiB::from_ptr_size(memory.as_mut_ptr(), memory.len()) };
    /// ```
    #[inline]
    #[must_use]
    pub unsafe fn from_ptr_size(ptr: *mut u8, size: usize) -> Self {
        Self {
            inner: Mutex::new(TeaspoonInner::from_ptr_size(ptr, size)),
        }
    }

    /// Constructs a Teaspoon memory allocator from an address and a size.
    ///
    /// The memory pointed by address must be valid for both reads and writes, and must be alive
    /// for the lifetime of `'a`. Note that because there's no connection between the address and
    /// the lifetime `'a`, you must ensure that the memory pointed by address lives long enough;
    /// you cannot rely on the compiler to check that for you.
    ///
    /// # Panics
    ///
    /// If `addr` is 0.
    ///
    /// # Safety
    ///
    /// - the memory pointed by `addr` must be
    ///   ["dereferenceable"](https://doc.rust-lang.org/stable/std/ptr/index.html#safety).
    /// - the memory pointed by `addr` must be alive for the lifetime of `'a`.
    /// - the memory pointed by `addr` must not be an
    ///   [*alias*](https://doc.rust-lang.org/nomicon/aliasing.html) for another reference or
    ///   address (in other words, `addr` is a *unique* address).
    ///
    /// An exception to those rules is if the `size` is 0. In that case, `addr` may be a dangling
    /// non-null address.
    ///
    /// # Examples
    ///
    /// ```
    /// use teaspoon::Teaspoon4KiB;
    ///
    /// let mut memory = [0u8; 1024];
    /// # #[allow(unused_variables)]
    /// let spoon = unsafe { Teaspoon4KiB::from_addr_size(memory.as_mut_ptr() as usize, memory.len()) };
    /// ```
    #[inline]
    #[must_use]
    pub unsafe fn from_addr_size(addr: usize, size: usize) -> Self {
        Self::from_ptr_size(addr as *mut u8, size)
    }

    /// Returns memory usage information for this Teaspoon allocator.
    ///
    /// The returned value contains some basic information about the memory currently used by the
    /// allocator, such as: the total memory available, the total memory used, the total memory
    /// usable, and the number of objects allocated.
    ///
    /// See the [`Usage`] documentation for the exact meaning of each field returned.
    ///
    /// Note that the usage computation is not cached or optimized in any way, and requires
    /// visiting all the objects currently allocated. As such, `usage()` is not a constant-time
    /// operation (`O(1)`), but it's a linear-time operation (`O(n)`, where `n` is the number of
    /// objects currently allocated). This is because the Teaspoon allocator is optimized to
    /// minimize overhead, and a faster `usage()` would require more overhead.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(allocator_api)]
    ///
    /// # #[cfg(feature = "allocator-api")]
    /// # {
    /// use std::alloc::Allocator;
    /// use std::alloc::Layout;
    /// use teaspoon::Teaspoon4KiB;
    /// use teaspoon::Usage;
    ///
    /// let mut memory = [0u8; 1024];
    /// let spoon = Teaspoon4KiB::from(&mut memory);
    ///
    /// assert_eq!(
    ///     spoon.usage(),
    ///     Usage {
    ///         total: 1024,
    ///         used: 0,
    ///         free: 1020,
    ///         objects: 0
    ///     }
    /// );
    ///
    /// let _ = spoon.allocate(Layout::new::<u128>());
    ///
    /// assert_eq!(
    ///     spoon.usage(),
    ///     Usage {
    ///         total: 1024,
    ///         used: 16,
    ///         free: 1000,
    ///         objects: 1
    ///     }
    /// );
    /// # }
    /// ```
    #[inline]
    #[must_use]
    pub fn usage(&self) -> Usage {
        self.inner.lock().usage()
    }
}

impl<'a, S: Sizing> From<&'a mut [u8]> for Teaspoon<'a, S> {
    #[inline]
    fn from(slice: &'a mut [u8]) -> Self {
        Self::from_slice(slice)
    }
}

impl<'a, S: Sizing, const N: usize> From<&'a mut [u8; N]> for Teaspoon<'a, S> {
    #[inline]
    fn from(array: &'a mut [u8; N]) -> Self {
        Self::from(array.as_mut_slice())
    }
}

#[cfg(feature = "allocator-api")]
unsafe impl<'a, S: Sizing> Allocator for Teaspoon<'a, S> {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        self.inner.lock().allocate(layout).ok_or(AllocError)
    }

    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        let data_ptr = SegmentDataPtr::new(ptr);
        self.inner.lock().deallocate(data_ptr, layout)
    }

    unsafe fn grow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError> {
        let data_ptr = SegmentDataPtr::new(ptr);
        self.inner
            .lock()
            .grow(data_ptr, old_layout, new_layout)
            .ok_or(AllocError)
    }

    unsafe fn shrink(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError> {
        let data_ptr = SegmentDataPtr::new(ptr);
        self.inner
            .lock()
            .shrink(data_ptr, old_layout, new_layout)
            .ok_or(AllocError)
    }
}

unsafe impl<'a, S: Sizing> GlobalAlloc for Teaspoon<'a, S> {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        self.inner
            .lock()
            .allocate(layout)
            .map(|ptr| ptr.cast().as_ptr())
            .unwrap_or_else(core::ptr::null_mut)
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        let data_ptr = SegmentDataPtr::new(NonNull::new_unchecked(ptr));
        self.inner.lock().deallocate(data_ptr, layout)
    }

    unsafe fn realloc(&self, ptr: *mut u8, old_layout: Layout, new_size: usize) -> *mut u8 {
        let data_ptr = SegmentDataPtr::new(NonNull::new_unchecked(ptr));
        let new_layout = Layout::from_size_align_unchecked(new_size, old_layout.align());
        self.inner
            .lock()
            .resize(data_ptr, old_layout, new_layout)
            .map(|ptr| ptr.cast().as_ptr())
            .unwrap_or_else(core::ptr::null_mut)
    }
}

#[repr(transparent)]
#[derive(Debug)]
struct TeaspoonInner<'a, S: Sizing> {
    arena: Arena<'a, S>,
}

impl<'a, S: Sizing> TeaspoonInner<'a, S> {
    #[inline]
    #[must_use]
    fn from_slice(slice: &'a mut [u8]) -> Self {
        Self {
            arena: Arena::from(slice),
        }
    }

    #[inline]
    #[must_use]
    unsafe fn from_ptr_size(ptr: *mut u8, size: usize) -> Self {
        let ptr = NonNull::new(ptr).expect("expected non-null pointer");
        let slice = NonNull::slice_from_raw_parts(ptr, size);
        let arena = Arena::new(slice);
        Self { arena }
    }

    fn allocate(&mut self, layout: Layout) -> Option<NonNull<[u8]>> {
        if layout.size() == 0 {
            // SAFETY: `Layout` guarantees that `align` is non-zero
            // TODO switch to `layout.dangling()` once it's stabilized
            let dangling = unsafe { NonNull::new_unchecked(layout.align() as *mut u8) };
            return Some(NonNull::slice_from_raw_parts(dangling, 0));
        }

        let data = match self.arena.head() {
            None => self.allocate_first(layout),
            Some(_) => self
                .allocate_tail(layout)
                .or_else(|| self.allocate_anywhere(layout)),
        };

        if let Some(data) = data {
            debug_assert!(
                data.len() >= layout.size(),
                "allocation returned fewer bytes than requested"
            );
            debug_assert!(
                // TODO switch to `data.is_aligned_to(layout.align())` once it's stabiled
                data.cast::<u8>().align_offset(layout.align()) == 0,
                "allocation returned data with wrong alignment"
            );
        }

        data
    }

    fn allocate_first(&mut self, layout: Layout) -> Option<NonNull<[u8]>> {
        debug_assert!(
            layout.size() > 0,
            "`layout.size()` must be greater than zero"
        );
        debug_assert!(
            self.arena.head().is_none(),
            "arena is expected to be empty, but has a head pointer"
        );
        debug_assert!(
            self.arena.tail().is_none(),
            "arena is expected to be empty, but has a tail pointer"
        );

        let segment = unsafe { Segment::new_in(self.arena, self.arena.usable(), layout)? };
        segment.write();

        self.arena.set_head(Some(segment.ptr()));
        self.arena.set_tail(Some(segment.ptr()));

        Some(segment.data(layout))
    }

    fn allocate_tail(&mut self, layout: Layout) -> Option<NonNull<[u8]>> {
        debug_assert!(
            layout.size() > 0,
            "`layout.size()` must be greater than zero"
        );
        debug_assert!(
            self.arena.head().is_some(),
            "arena is expected to be non-empty, but does not have a head pointer"
        );
        debug_assert!(
            self.arena.tail().is_some(),
            "arena is expected to be non-empty, but does not have a tail pointer"
        );

        let mut tail_segment =
            unsafe { Segment::read(self.arena, self.arena.tail().unwrap_unchecked()) };
        let mut new_segment =
            unsafe { Segment::new_in(self.arena, tail_segment.trailing(), layout)? };
        Segment::connect(&mut tail_segment, &mut new_segment);

        self.arena.set_tail(Some(new_segment.ptr()));

        Some(new_segment.data(layout))
    }

    fn allocate_anywhere(&mut self, layout: Layout) -> Option<NonNull<[u8]>> {
        debug_assert!(
            layout.size() > 0,
            "`layout.size()` must be greater than zero"
        );

        let mut iter = ArenaChunks::new(self.arena);
        let mut prev_segment: Option<Segment<'a, S>> = None;

        while let Some(chunk) = iter.next() {
            match chunk {
                Chunk::Used(segment) => {
                    prev_segment = Some(segment);
                }
                Chunk::Unused(unused) => {
                    if let Some(mut new_segment) =
                        unsafe { Segment::new_in(self.arena, unused, layout) }
                    {
                        let next_segment = match iter.next() {
                            Some(Chunk::Used(segment)) => Some(segment),
                            _ => None,
                        };

                        match prev_segment {
                            None => self.arena.set_head(Some(new_segment.ptr())),
                            Some(mut prev_segment) => {
                                Segment::connect(&mut prev_segment, &mut new_segment)
                            }
                        }
                        match next_segment {
                            None => self.arena.set_tail(Some(new_segment.ptr())),
                            Some(mut next_segment) => {
                                Segment::connect(&mut new_segment, &mut next_segment)
                            }
                        }

                        return Some(new_segment.data(layout));
                    }
                }
            }
        }

        None
    }

    fn deallocate(&mut self, data_ptr: SegmentDataPtr<S>, layout: Layout) {
        if layout.size() == 0 {
            // `data_ptr` is a dangling pointer previously returned by `allocate()`; it doesn't
            // have a corresponding segment
            return;
        }

        let segment = unsafe { Segment::read(self.arena, data_ptr.to_header_ptr()) };
        self.remove_segment(segment)
    }

    fn remove_segment(&mut self, segment: Segment<'a, S>) {
        debug_assert!(
            self.arena.head().is_some(),
            "arena is expected to be non-empty, but does not have a head pointer"
        );
        debug_assert!(
            self.arena.tail().is_some(),
            "arena is expected to be non-empty, but does not have a tail pointer"
        );

        if segment.prev_ptr().is_none() {
            self.arena.set_head(segment.next_ptr());
        }
        if segment.next_ptr().is_none() {
            self.arena.set_tail(segment.prev_ptr());
        }

        segment.disconnect();
    }

    #[cfg(feature = "allocator-api")]
    fn grow(
        &mut self,
        data_ptr: SegmentDataPtr<S>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Option<NonNull<[u8]>> {
        debug_assert!(
            new_layout.size() >= old_layout.size(),
            "`new_layout` must be bigger than or equal to `old_layout`"
        );
        self.resize(data_ptr, old_layout, new_layout)
    }

    #[cfg(feature = "allocator-api")]
    fn shrink(
        &mut self,
        data_ptr: SegmentDataPtr<S>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Option<NonNull<[u8]>> {
        debug_assert!(
            new_layout.size() <= old_layout.size(),
            "`new_layout` must be smaller than or equal to `old_layout`"
        );
        self.resize(data_ptr, old_layout, new_layout)
    }

    fn resize(
        &mut self,
        data_ptr: SegmentDataPtr<S>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Option<NonNull<[u8]>> {
        if old_layout.size() == 0 || new_layout.size() == 0 {
            // If `old_layout` is zero-sized, then `data_ptr` is a dangling pointer, and it doesn't
            // have a corresponding segment. If `new_layout` is zero-sized, then we need to return
            // a dangling pointer.
            self.deallocate(data_ptr, old_layout);
            return self.allocate(new_layout);
        }

        debug_assert!(
            self.arena.head().is_some(),
            "arena is expected to be non-empty, but does not have a head pointer"
        );
        debug_assert!(
            self.arena.tail().is_some(),
            "arena is expected to be non-empty, but does not have a tail pointer"
        );

        let copy_size = cmp::min(old_layout.size(), new_layout.size());
        let old_segment = unsafe { Segment::read(self.arena, data_ptr.to_header_ptr()) };
        let old_data = old_segment.data(old_layout);

        match unsafe { Segment::new_in(self.arena, old_segment.available(), new_layout) } {
            None => {
                let new_data = self.allocate(new_layout)?;
                unsafe {
                    core::ptr::copy_nonoverlapping(
                        old_data.cast::<u8>().as_ptr(),
                        new_data.cast::<u8>().as_ptr(),
                        copy_size,
                    )
                };
                self.remove_segment(old_segment);
                Some(new_data)
            }
            Some(mut new_segment) => {
                let new_data = new_segment.data(new_layout);
                unsafe {
                    core::ptr::copy(
                        old_data.cast::<u8>().as_ptr(),
                        new_data.cast::<u8>().as_ptr(),
                        copy_size,
                    )
                };

                match old_segment.prev() {
                    None => self.arena.set_head(Some(new_segment.ptr())),
                    Some(mut prev) => Segment::connect(&mut prev, &mut new_segment),
                }
                match old_segment.next() {
                    None => self.arena.set_tail(Some(new_segment.ptr())),
                    Some(mut next) => Segment::connect(&mut new_segment, &mut next),
                }

                new_segment.write();

                Some(new_data)
            }
        }
    }

    #[inline]
    #[must_use]
    fn usage(&self) -> Usage {
        Usage::get(self.arena)
    }
}
