// Copyright © 2024 Andrea Corbellini and contributors
// SPDX-License-Identifier: BSD-3-Clause

use crate::ptr::SegmentHeaderPtr;
use crate::sizing::Sizing;
use core::alloc::Layout;
use core::marker::PhantomData;
use core::num::NonZero;
use core::ptr::NonNull;

#[inline]
#[must_use]
fn slice_to_nonnull<T>(slice: &mut [T]) -> NonNull<[T]> {
    // SAFETY: `slice` is a mutable reference, so the pointer that comes from it is guaranteed to
    // be non-null and valid.
    let start = unsafe { NonNull::new_unchecked(slice.as_mut_ptr()) };
    let size = slice.len();
    NonNull::slice_from_raw_parts(start, size)
}

#[repr(transparent)]
#[derive(Copy, Clone, Debug)]
pub(crate) struct Arena<'a, S: Sizing> {
    slice: NonNull<[u8]>,
    phantom: PhantomData<(&'a mut [u8], S)>,
}

// SAFETY: The `'a` lifetime and the `&'a mut [u8]` reference in `phantom` are there to ensure that
// the `NonNull` pointer is unique and not aliased. Of course, `Arena` cannot enforce that, but
// callers of `Arena::new` are expected to enforce it.
unsafe impl<'a, S: Sizing> Send for Arena<'a, S> where &'a mut [u8]: Send {}

impl<'a, S: Sizing> Arena<'a, S> {
    /// Initializes a new arena at the given memory area.
    ///
    /// This method writes a new arena header to the start of `slice`.
    ///
    /// `slice` can be an arbitrary valid pointer (subject to the "safety" rules below). In
    /// particular, it does not have any alignment or sizing restrictions: this method takes care
    /// of adjusting the align and size of `slice` automatically as needed. If `slice` is not large
    /// enough to contain an `Arena`, this method does not write any memory and returns an `Arena`
    /// with no usable memory.
    ///
    /// # Safety
    ///
    /// - `slice` must be ["dereferenceable"](std::ptr#safety).
    /// - `slice` must be valid for reads and writes.
    /// - `slice` must be alive for the lifetime of `'a`.
    /// - `slice` must not be an [*alias*](https://doc.rust-lang.org/nomicon/aliasing.html) for
    ///   another reference or pointer (in other words, `slice` is a *unique* pointer).
    /// - `slice` must point to a contiguous memory location that is part of the same [allocated
    ///   object](https://doc.rust-lang.org/std/ptr/index.html#allocated-object).
    #[inline]
    #[must_use]
    pub(crate) unsafe fn new(slice: NonNull<[u8]>) -> Self {
        let start = slice.cast::<u8>();

        let header_layout = Layout::new::<S::ArenaHeaderRepr>();
        let header_start = start.align_offset(header_layout.align());
        let header_end = header_start.saturating_add(header_layout.size());

        let aligned_slice = if header_end <= slice.len() {
            // SAFETY: We just verified that `slice` is large enough to contain the aligned
            // `ArenaHeaderRepr`. `start.byte_add(header_start)` therefore cannot overflow and will
            // point to a memory area valid for writes.
            let header_ptr = unsafe { start.byte_add(header_start).cast::<S::ArenaHeaderRepr>() };
            debug_assert!(header_ptr.is_aligned(), "failed to align slice");
            NonNull::slice_from_raw_parts(header_ptr.cast::<u8>(), slice.len() - header_start)
        } else {
            let header_ptr = NonNull::<S::ArenaHeaderRepr>::dangling();
            NonNull::slice_from_raw_parts(header_ptr.cast::<u8>(), 0)
        };

        let mut arena = Self {
            slice: aligned_slice,
            phantom: PhantomData,
        };

        arena.write_header(&ArenaHeader::default());

        arena
    }

    #[inline]
    #[must_use]
    pub(crate) const fn size(&self) -> usize {
        self.slice.len()
    }

    #[inline]
    #[must_use]
    pub(crate) const fn start(&self) -> NonNull<u8> {
        self.slice.cast()
    }

    #[inline]
    #[must_use]
    pub(crate) const fn end(&self) -> NonNull<u8> {
        // SAFETY: The construction in `Arena::new()` guarantees that the expression below cannot
        // overflow.
        unsafe { self.start().byte_add(self.size()) }
    }

    #[inline]
    #[must_use]
    pub(crate) fn usable(&self) -> NonNull<[u8]> {
        if self.size() == 0 {
            let ptr = NonNull::<S::SegmentHeaderRepr>::dangling().cast::<u8>();
            return NonNull::slice_from_raw_parts(ptr, 0);
        }

        let header_layout = Layout::new::<S::ArenaHeaderRepr>();
        let segment_layout = Layout::new::<S::SegmentHeaderRepr>();

        // SAFETY: The construction in `Arena::new()` guarantees that the expression below cannot
        // overflow.
        let header_end = unsafe { self.start().byte_add(header_layout.size()) };
        let segment_offset = header_end.align_offset(segment_layout.align());

        let usable_size = self
            .size()
            .saturating_sub(header_layout.size())
            .saturating_sub(segment_offset);

        let usable_ptr = if usable_size > 0 {
            // SAFETY: The construction in `Arena::new()` guarantees that the memory pointed by
            // `self.start()` is valid for at least `self.size()` bytes. A non-zero `usable_size`
            // ensures that `self.size()` is larger than `header_layout.size() + segment_offset`.
            // The expression below is equivalent to `self.start.byte_add(header_layout.size() +
            // segment_offset)`, therefore it cannot overflow.
            unsafe { header_end.byte_add(segment_offset) }
        } else {
            NonNull::<S::SegmentHeaderRepr>::dangling().cast::<u8>()
        };

        NonNull::slice_from_raw_parts(usable_ptr, usable_size)
    }

    fn read_header(&self) -> ArenaHeader {
        if self.size() == 0 {
            return ArenaHeader::default();
        }
        // SAFETY: The construction in `Arena::new()` guarantees that the expression below cannot
        // overflow.
        let header_ref = unsafe { self.start().cast::<S::ArenaHeaderRepr>().as_ref() };
        S::read_arena_header(header_ref)
    }

    fn write_header(&mut self, header: &ArenaHeader) {
        if self.size() == 0 {
            return;
        }
        // SAFETY: The construction in `Arena::new()` guarantees that the expression below cannot
        // overflow.
        let header_mut = unsafe { self.start().cast::<S::ArenaHeaderRepr>().as_mut() };
        S::write_arena_header(header_mut, header)
    }

    pub(crate) fn head(&self) -> Option<SegmentHeaderPtr<S>> {
        let header = self.read_header();
        header
            .head_offset
            // SAFETY: By construction, `head_offset` points to a valid segment.
            .map(|offset| unsafe { self.segment_offset_to_ptr(offset) })
    }

    /// # Safety
    ///
    /// `ptr` (if `Some`) must be pointing to a valid segment that belongs to this arena.
    pub(crate) unsafe fn set_head(&mut self, ptr: Option<SegmentHeaderPtr<S>>) {
        let mut header = self.read_header();
        // SAFETY: Upheld by the caller.
        header.head_offset = ptr.map(|ptr| unsafe { self.segment_ptr_to_offset(ptr) });
        self.write_header(&header);
    }

    pub(crate) fn tail(&self) -> Option<SegmentHeaderPtr<S>> {
        let header = self.read_header();
        header
            .tail_offset
            // SAFETY: By construction, `tail_offset` points to a valid segment.
            .map(|offset| unsafe { self.segment_offset_to_ptr(offset) })
    }

    /// # Safety
    ///
    /// `ptr` (if `Some`) must be pointing to a valid segment that belongs to this arena.
    pub(crate) unsafe fn set_tail(&mut self, ptr: Option<SegmentHeaderPtr<S>>) {
        let mut header = self.read_header();
        // SAFETY: Upheld by the caller.
        header.tail_offset = ptr.map(|ptr| unsafe { self.segment_ptr_to_offset(ptr) });
        self.write_header(&header);
    }

    /// # Safety
    ///
    /// `offset`, when added to `self.start()`, must be pointing to a memory area that:
    /// - belongs to this arena;
    /// - contains a segment header.
    ///
    /// Adding `offset` to `self.start()` must not cause an overflow.
    pub(crate) unsafe fn segment_offset_to_ptr(
        &self,
        offset: NonZero<usize>,
    ) -> SegmentHeaderPtr<S> {
        let start = self.start();
        let offset = offset.get();
        let size = size_of::<S::SegmentHeaderRepr>();
        let limit = offset.saturating_add(size);
        debug_assert!(
            offset >= size_of::<S::ArenaHeaderRepr>(),
            "`offset` must point to a location past the arena header"
        );
        debug_assert!(
            limit <= self.size(),
            "`offset` exceeds the size of the arena"
        );
        // SAFETY: upheld by the caller
        let ptr = unsafe { start.byte_add(offset) };
        debug_assert!(
            self.contains_bytes(ptr, size),
            "arena does not contain a segment at the given `offset`"
        );
        // SAFETY: upheld by the caller
        unsafe { SegmentHeaderPtr::new(ptr) }
    }

    /// # Safety
    ///
    /// `ptr` must be pointing to a valid segment that belongs to this arena.
    pub(crate) unsafe fn segment_ptr_to_offset(&self, ptr: SegmentHeaderPtr<S>) -> NonZero<usize> {
        debug_assert!(
            self.contains_segment(ptr),
            "`ptr` does not belong to the arena"
        );

        // SAFETY: The caller ensures that `ptr` points to a segment that belongs to this arena.
        // This implies that `ptr` must be `> self.start()` (therefore `offset` is non-zero and
        // positive), and `ptr` belongs to the same allocation as `self.start()`.
        unsafe {
            let offset = ptr.as_nonnull().byte_offset_from_unsigned(self.start());
            NonZero::new_unchecked(offset)
        }
    }

    #[inline]
    #[must_use]
    pub(crate) fn contains_segment(&self, ptr: SegmentHeaderPtr<S>) -> bool {
        let ptr = ptr.as_nonnull();
        let size = size_of::<S::SegmentHeaderRepr>();
        self.contains_bytes(ptr, size)
    }

    #[inline]
    #[must_use]
    pub(crate) fn contains_bytes(&self, range_start: NonNull<u8>, range_size: usize) -> bool {
        let usable = self.usable().as_ptr();
        let usable_start = usable.cast::<u8>();
        let usable_end = usable_start.wrapping_byte_add(usable.len());

        let range_start = range_start.as_ptr();
        let range_end = range_start.wrapping_byte_add(range_size);

        !range_start.is_null()
            && range_start <= range_end
            && range_start >= usable_start
            && range_end <= usable_end
    }
}

impl<'a, S: Sizing> From<&'a mut [u8]> for Arena<'a, S> {
    fn from(slice: &'a mut [u8]) -> Self {
        let slice = slice_to_nonnull(slice);
        // SAFETY: `slice` comes from a mutable reference, therefore it's a valid pointer, alive
        // for the lifetime of `'a`, respecting Rust's aliasing rules.
        unsafe { Self::new(slice) }
    }
}

impl<'a, S: Sizing> PartialEq for Arena<'a, S> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        core::ptr::eq(self.slice.as_ptr(), other.slice.as_ptr())
    }
}

impl<'a, S: Sizing> Eq for Arena<'a, S> {}

#[derive(Default, Copy, Clone, PartialEq, Eq, Debug)]
pub(crate) struct ArenaHeader {
    pub(crate) head_offset: Option<NonZero<usize>>,
    pub(crate) tail_offset: Option<NonZero<usize>>,
}
