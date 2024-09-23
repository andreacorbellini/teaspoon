// Copyright © 2024 Andrea Corbellini and contributors
// SPDX-License-Identifier: BSD-3-Clause

use crate::arena::Arena;
use crate::ptr::SegmentHeaderPtr;
use crate::sizing::Sizing;
use core::alloc::Layout;
use core::num::NonZero;
use core::ptr::NonNull;

#[derive(Copy, Clone, Debug)]
pub(crate) struct Segment<'a, S: Sizing> {
    arena: Arena<'a, S>,
    ptr: SegmentHeaderPtr<S>,
    size: usize,
    prev_ptr: Option<SegmentHeaderPtr<S>>,
    next_ptr: Option<SegmentHeaderPtr<S>>,
}

impl<'a, S: Sizing> Segment<'a, S> {
    /// Find an optimal placement for a segment containing data with the given [`Layout`].
    ///
    /// This method returns a pointer contained in `slice` such that:
    ///
    /// 1. it allows to place a segment header directly followed by the data (with no padding in
    ///    between);
    /// 2. the header is correctly aligned (as specified by the layout of `S::SegmentHeaderRepr`);
    /// 3. the data is correctly aligned (as specified by `data_layout`).
    ///
    /// If the segment cannot fit in `slice`, this method returns `None`.
    ///
    /// # Safety
    ///
    /// `slice` must point to a contiguous memory location that is part of the same [allocated
    /// object](https://doc.rust-lang.org/std/ptr/index.html#allocated-object).
    #[must_use]
    unsafe fn placement(slice: NonNull<[u8]>, data_layout: Layout) -> Option<NonNull<[u8]>> {
        let header_layout = Layout::new::<S::SegmentHeaderRepr>();
        let mut required_size = header_layout.size().checked_add(data_layout.size())?;
        if slice.len() < required_size {
            return None;
        }

        let start = slice.cast::<u8>();

        // Find the minimum value for `header_pad` necessary to ensure that the header is properly
        // aligned.
        let header_pad = start.align_offset(header_layout.align());
        required_size = required_size.checked_add(header_pad)?;
        if slice.len() < required_size {
            return None;
        }

        let header_start = start.byte_add(header_pad);
        let header_end = header_start.byte_add(header_layout.size());

        // Find an initial (not optimized) value for `data_pad` necessary to ensure that the data
        // is properly aligned.
        let data_pad = header_end.align_offset(data_layout.align());
        required_size = required_size.checked_add(data_pad)?;
        if slice.len() < required_size {
            return None;
        }

        // Move the header to the "right", closer to the data, still keeping the header aligned.
        debug_assert_eq!(
            data_pad % header_layout.align(),
            0,
            "expected data padding to be a multiple of the header alignment"
        );
        let header_start = header_start.byte_add(data_pad);

        // Ensure that the final data size is a multiple of `S::min_align()`
        let data_size = data_layout
            .size()
            .checked_next_multiple_of(S::min_align())?;
        required_size = required_size.checked_add(data_size - data_layout.size())?;
        if slice.len() < required_size {
            return None;
        }

        Some(NonNull::slice_from_raw_parts(header_start, data_size))
    }

    /// Create a new segment large enough to hold data with the given [`Layout`].
    ///
    /// This method returns `None` if the `slice` is not large enough to contain the segment.
    ///
    /// You need to call [`write()`](Self::write) in order to actually write the segment to memory.
    ///
    /// # Safety
    ///
    /// * `slice` must be part of `arena`.
    /// * `slice` must point to unallocated memory.
    #[must_use]
    pub(crate) unsafe fn new_in(
        arena: Arena<'a, S>,
        slice: NonNull<[u8]>,
        data_layout: Layout,
    ) -> Option<Self> {
        debug_assert!(arena.contains_bytes(slice.cast(), slice.len()));

        let placement = Self::placement(slice, data_layout)?;
        let ptr = SegmentHeaderPtr::new(placement.cast::<u8>());
        let size = placement.len();

        if arena.segment_ptr_to_offset(ptr).get() > S::max_offset() || size > S::max_size() {
            return None;
        }

        Some(Self {
            arena,
            ptr,
            size,
            prev_ptr: None,
            next_ptr: None,
        })
    }

    /// Return a pointer to the segment header.
    #[inline]
    pub(crate) const fn ptr(&self) -> SegmentHeaderPtr<S> {
        self.ptr
    }

    /// Returns a pointer to the segment data.
    ///
    /// The pointer is correctly aligned for the given [`Layout`].
    ///
    /// The layout does not necessarily need to be the same layout that was passed to [`new_in()`].
    ///
    /// # Panics
    ///
    /// If the layout does not fit into the usable space of the segment.
    pub(crate) fn data(&self, data_layout: Layout) -> NonNull<[u8]> {
        let usable = self.usable();
        let usable_start = usable.cast::<u8>();

        let data_pad = usable_start.align_offset(data_layout.align());
        assert!(
            data_layout.size().saturating_add(data_pad) <= usable.len(),
            "segment too small to contain `data_layout`"
        );

        // SAFETY: Both `usable_start` and `data_start` are in bounds of `usable` (this is checked
        // by the `assert` above), and `usable` points to a contiguous memory location part of the
        // same allocated object.
        let data_start = unsafe { usable_start.byte_add(data_pad) };
        let data_size = usable.len() - data_pad;
        NonNull::slice_from_raw_parts(data_start, data_size)
    }

    /// Returns a pointer to the memory space of the segment that can contain data.
    ///
    /// This method is similar to [`data()`]. The main difference is that [`data()`] returns a
    /// pointer with size and alignment specified by a given [`Layout`], while this method returns
    /// *all* available data. As such, [`data()`] may return a subset of [`usable()`].
    pub(crate) fn usable(&self) -> NonNull<[u8]> {
        let header_layout = Layout::new::<S::SegmentHeaderRepr>();
        // SAFETY: It is assumed that `self.ptr` points to a contiguous memory location large
        // enough to contain the segment header and its data. This is enforced by `new_in()` and is
        // required by `read()`.
        let header_end = unsafe { self.ptr.byte_add(header_layout.size()) };
        NonNull::slice_from_raw_parts(header_end, self.size)
    }

    /// Returns a pointer to the memory space that comes right after the segment.
    ///
    /// The returned memory is essentially the unused memory space between this segment and the
    /// next one (if any), or between this segment and the end of the arena.
    pub(crate) fn trailing(&self) -> NonNull<[u8]> {
        let header_layout = Layout::new::<S::SegmentHeaderRepr>();
        let header_end = unsafe { self.ptr.byte_add(header_layout.size()) };
        let data_end = unsafe { header_end.byte_add(self.size) };

        let limit = match self.next_ptr {
            Some(next_ptr) => next_ptr.as_nonnull(),
            None => self.arena.end(),
        };

        // TODO: Use `limit.sub_ptr(data_end)` once that's stabilized
        let unused_size = unsafe { limit.offset_from(data_end) };
        debug_assert!(unused_size >= 0, "negative offset");

        NonNull::slice_from_raw_parts(data_end, unused_size as usize)
    }

    /// Returns a pointer to the contiguous memory space that the segment may grow into.
    ///
    /// The returned memory space includes: the segment header, the segment data, and any unused
    /// memory that follows the segment.
    ///
    /// This can be thought as the concatenation of the segment header memory, the memory from
    /// [`usable()`], the memory from [`trailing()`].
    pub(crate) fn available(&self) -> NonNull<[u8]> {
        let header_start = self.ptr.as_nonnull();

        let limit = match self.next_ptr {
            Some(next_ptr) => next_ptr.as_nonnull(),
            None => self.arena.end(),
        };

        // TODO: Use `limit.sub_ptr(data_end)` once that's stabilized
        let available_size = unsafe { limit.offset_from(header_start) };
        debug_assert!(available_size >= 0, "negative offset");

        NonNull::slice_from_raw_parts(header_start, available_size as usize)
    }

    pub(crate) fn prev(&self) -> Option<Self> {
        self.prev_ptr
            .map(|prev_ptr| unsafe { Self::read(self.arena, prev_ptr) })
    }

    pub(crate) const fn prev_ptr(&self) -> Option<SegmentHeaderPtr<S>> {
        self.prev_ptr
    }

    pub(crate) fn next(&self) -> Option<Self> {
        self.next_ptr
            .map(|next_ptr| unsafe { Self::read(self.arena, next_ptr) })
    }

    pub(crate) const fn next_ptr(&self) -> Option<SegmentHeaderPtr<S>> {
        self.next_ptr
    }

    #[inline]
    #[must_use]
    pub(crate) unsafe fn read(arena: Arena<'a, S>, ptr: SegmentHeaderPtr<S>) -> Self {
        let header_ptr = ptr.cast::<S::SegmentHeaderRepr>();
        debug_assert!(header_ptr.is_aligned(), "pointer is not aligned");
        debug_assert!(
            arena.contains_segment(ptr),
            "pointer does not belong to the arena"
        );

        let repr_ref = unsafe { header_ptr.as_ref() };
        let header = S::read_segment_header(repr_ref);

        let prev_ptr = header
            .prev_offset
            .map(|offset| arena.segment_offset_to_ptr(offset));
        let next_ptr = header
            .next_offset
            .map(|offset| arena.segment_offset_to_ptr(offset));
        let size = header.size;

        Self {
            arena,
            ptr,
            size,
            prev_ptr,
            next_ptr,
        }
    }

    #[inline]
    pub(crate) fn write(&self) {
        let mut header_ptr = self.ptr.cast::<S::SegmentHeaderRepr>();
        debug_assert!(header_ptr.is_aligned(), "pointer is not aligned");
        debug_assert!(
            self.arena.contains_segment(self.ptr),
            "pointer does not belong to the arena"
        );

        let header = SegmentHeader {
            prev_offset: self
                .prev_ptr
                .map(|ptr| self.arena.segment_ptr_to_offset(ptr)),
            next_offset: self
                .next_ptr
                .map(|ptr| self.arena.segment_ptr_to_offset(ptr)),
            size: self.size,
        };

        let repr_mut = unsafe { header_ptr.as_mut() };
        S::write_segment_header(repr_mut, &header);
    }

    pub(crate) fn connect(left: &mut Self, right: &mut Self) {
        debug_assert_eq!(
            left.arena, right.arena,
            "segments do not belong to the same arena"
        );
        left.next_ptr = Some(right.ptr);
        right.prev_ptr = Some(left.ptr);
        left.write();
        right.write();
    }

    pub(crate) fn disconnect(self) {
        if let Some(mut prev) = self.prev() {
            prev.next_ptr = self.next_ptr;
            prev.write();
        }
        if let Some(mut next) = self.next() {
            next.prev_ptr = self.prev_ptr;
            next.write();
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub(crate) struct SegmentHeader {
    pub(crate) prev_offset: Option<NonZero<usize>>,
    pub(crate) next_offset: Option<NonZero<usize>>,
    pub(crate) size: usize,
}
