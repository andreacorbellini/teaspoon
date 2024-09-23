// Copyright © 2024 Andrea Corbellini and contributors
// SPDX-License-Identifier: BSD-3-Clause

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
    #[inline]
    pub(crate) fn new(data_ptr: NonNull<u8>) -> Self {
        Self {
            data_ptr,
            phantom: PhantomData,
        }
    }

    pub(crate) unsafe fn to_header_ptr(self) -> SegmentHeaderPtr<S> {
        let header_layout = Layout::new::<S::SegmentHeaderRepr>();
        let pad = ((self.data_ptr.as_ptr() as usize) - header_layout.size())
            & (header_layout.align() - 1);
        unsafe {
            let header_ptr = self.data_ptr.byte_sub(header_layout.size()).byte_sub(pad);
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
