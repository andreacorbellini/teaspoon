// Copyright © 2024 Andrea Corbellini and contributors
// SPDX-License-Identifier: BSD-3-Clause

use crate::Arena;
use crate::sizing::Sizing;
use core::alloc::Layout;
use core::fmt;
use core::marker::PhantomData;
use core::ops::Deref;
use core::ptr::NonNull;

#[repr(transparent)]
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct SegmentHeaderPtr<S: Sizing> {
    header_ptr: NonNull<u8>,
    phantom: PhantomData<S>,
}

impl<S: Sizing> SegmentHeaderPtr<S> {
    /// # Safety
    ///
    /// * `header_ptr` must point to a contiguous memory location that is part of the same
    ///   [allocated object](https://doc.rust-lang.org/std/ptr/index.html#allocated-object).
    /// * `header_ptr` must be valid for writes.
    /// * `header_ptr` must point to a valid segment, which means that the memory it points to must
    ///   be properly aligned and large enough to contain a segment header and its corresponding
    ///   data.
    #[inline]
    pub(crate) unsafe fn new(header_ptr: NonNull<u8>) -> Self {
        debug_assert!(
            header_ptr.cast::<S::SegmentHeaderRepr>().is_aligned(),
            "pointer is not aligned"
        );
        Self {
            header_ptr,
            phantom: PhantomData,
        }
    }

    #[inline]
    pub(crate) const fn as_nonnull(self) -> NonNull<u8> {
        self.header_ptr
    }
}

impl<S: Sizing> Deref for SegmentHeaderPtr<S> {
    type Target = NonNull<u8>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.header_ptr
    }
}

impl<S: Sizing> fmt::Pointer for SegmentHeaderPtr<S> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.header_ptr.fmt(f)
    }
}

impl<S: Sizing> fmt::Debug for SegmentHeaderPtr<S> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "SegmentHeaderPtr({:p})", self)
    }
}

#[repr(transparent)]
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct SegmentDataPtr<S: Sizing> {
    data_ptr: NonNull<u8>,
    phantom: PhantomData<S>,
}

impl<S: Sizing> SegmentDataPtr<S> {
    /// # Safety
    ///
    /// * `data_ptr` must point to a contiguous memory location that is part of the same [allocated
    ///   object](https://doc.rust-lang.org/std/ptr/index.html#allocated-object).
    /// * `data_ptr` must be valid for writes.
    /// * `data_ptr` must point to the start of the data section of a segment, which means that the
    ///   memory it points to must be properly aligned, preceeded by a segment header, and large
    ///   enough to contain the data.
    #[inline]
    pub(crate) unsafe fn new(data_ptr: NonNull<u8>) -> Self {
        Self {
            data_ptr,
            phantom: PhantomData,
        }
    }

    /// # Safety
    ///
    /// `self` must belong to `arena`.
    pub(crate) unsafe fn to_header_ptr(self, arena: Arena<'_, S>) -> SegmentHeaderPtr<S> {
        let header_layout = Layout::new::<S::SegmentHeaderRepr>();
        let pad = ((self.data_ptr.as_ptr() as usize) - header_layout.size())
            & (header_layout.align() - 1);

        // We could retrieve the header pointer by simply taking `self.data_ptr` and subtracting
        // `header_layout.size() + pad`, however doing so confuses Miri and makes its stacked borrow
        // checks fail.
        //
        // Involving `arena` in the math is not technically necessary, but it makes Miri understand
        // that we're getting a pointer that was derived from a valid read-only reference.

        // SAFETY: The caller of `SegmentDataPtr::new()` ensures that this pointer is preceeded by
        // a header. The caller of this method (`to_header_ptr()`) ensures that this pointer belongs
        // to `arena`.
        unsafe {
            let data_offset = self.data_ptr.byte_offset_from(arena.start());
            debug_assert!(data_offset > 0, "pointer does not belong to the arena");
            let header_offset = (data_offset as usize) - (header_layout.size() + pad);
            let header_ptr = arena.start().byte_add(header_offset);
            SegmentHeaderPtr::<S>::new(header_ptr)
        }
    }
}

impl<S: Sizing> fmt::Pointer for SegmentDataPtr<S> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.data_ptr.fmt(f)
    }
}

impl<S: Sizing> fmt::Debug for SegmentDataPtr<S> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "SegmentDataPtr({:p})", self)
    }
}
