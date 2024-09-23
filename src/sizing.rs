// Copyright © 2024 Andrea Corbellini and contributors
// SPDX-License-Identifier: BSD-3-Clause

#![allow(private_interfaces)]

use crate::arena::ArenaHeader;
use crate::segment::SegmentHeader;
use core::fmt;
use core::num::NonZero;

macro_rules! const_assert {
    ( $( $tt:tt )* ) => {
        const _: () = assert!($($tt)*);
    }
}

/// Trait to define overhead and sizing limits on [`Teaspoon`](crate::Teaspoon) variants.
///
/// This trait is implemented by 3 marker types:
///
/// * [`Sizing4KiB`]: supports allocating objects up to 4 KiB.
/// * [`Sizing128KiB`]: supports allocating objects up to 128 KiB.
/// * [`Sizing16MiB`]: supports allocating objects up to 16 MiB.
///
/// This is a sealed trait and you cannot implement your own.
///
/// See the [module-level documentation](crate#allocator-limits) for more information about the
/// Teaspoon allocator variants and their sizing limits.
pub trait Sizing: Copy + Clone + PartialEq + Eq + fmt::Debug + private::Sealed {}

pub(crate) mod private {
    use crate::arena::ArenaHeader;
    use crate::segment::SegmentHeader;
    use core::fmt;

    #[doc(hidden)]
    pub trait Sealed: SizingInternals {}

    #[doc(hidden)]
    pub trait SizingInternals {
        type ArenaHeaderRepr: Copy + Clone + fmt::Debug;
        type SegmentHeaderRepr: Copy + Clone + fmt::Debug;

        fn min_align() -> usize;
        fn max_size() -> usize;
        fn max_offset() -> usize;

        fn read_arena_header(src: &Self::ArenaHeaderRepr) -> ArenaHeader;
        fn write_arena_header(dst: &mut Self::ArenaHeaderRepr, value: &ArenaHeader);

        fn read_segment_header(src: &Self::SegmentHeaderRepr) -> SegmentHeader;
        fn write_segment_header(dst: &mut Self::SegmentHeaderRepr, value: &SegmentHeader);
    }
}

/// Marker trait for [`Teaspoon`](crate::Teaspoon) that supports allocating objects up to 4 KiB.
///
/// See the [module-level documentation](crate#allocator-limits) for more information about the
/// Teaspoon allocator variants and their sizing limits.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct Sizing4KiB;

impl Sizing for Sizing4KiB {}

impl private::Sealed for Sizing4KiB {}

const_assert!(align_of::<u32>() % Sizing4KiB::MIN_ALIGN == 0);

impl Sizing4KiB {
    const MIN_ALIGN: usize = 4;
    const MIN_ALIGN_BITS: u32 = Self::MIN_ALIGN.trailing_zeros();
    const MIN_ALIGN_MASK: usize = Self::MIN_ALIGN - 1;

    const OFFSET_BITS: u32 = 11;
    const OFFSET_MASK: u32 = (1 << Self::OFFSET_BITS) - 1;
    const OFFSET_MAX: usize = (Self::OFFSET_MASK as usize) * Self::MIN_ALIGN;

    const SIZE_BITS: u32 = 10;
    const SIZE_MASK: u32 = (1 << Self::SIZE_BITS) - 1;
    const SIZE_MIN: usize = Self::MIN_ALIGN;
    const SIZE_MAX: usize = Self::SIZE_MIN + (Self::SIZE_MASK as usize) * Self::MIN_ALIGN;

    #[inline]
    const fn read_compact_value(mut value: u32) -> (u32, u32, u32) {
        let a = (value & Self::OFFSET_MASK) << Self::MIN_ALIGN_BITS;
        value >>= Self::OFFSET_BITS;
        let b = (value & Self::OFFSET_MASK) << Self::MIN_ALIGN_BITS;
        value >>= Self::OFFSET_BITS;
        let c = (value & Self::SIZE_MASK) << Self::MIN_ALIGN_BITS;
        (a, b, c)
    }

    #[inline]
    const fn write_compact_value(a: u32, b: u32, c: u32) -> u32 {
        let mut value = c >> Self::MIN_ALIGN_BITS;
        value <<= Self::OFFSET_BITS;
        value |= b >> Self::MIN_ALIGN_BITS;
        value <<= Self::OFFSET_BITS;
        value |= a >> Self::MIN_ALIGN_BITS;
        value
    }
}

impl private::SizingInternals for Sizing4KiB {
    type ArenaHeaderRepr = u32;
    type SegmentHeaderRepr = u32;

    fn min_align() -> usize {
        Self::MIN_ALIGN
    }

    fn max_size() -> usize {
        Self::SIZE_MAX
    }

    fn max_offset() -> usize {
        Self::OFFSET_MAX
    }

    fn read_arena_header(src: &Self::ArenaHeaderRepr) -> ArenaHeader {
        let (head_offset, tail_offset, _) = Self::read_compact_value(*src);
        ArenaHeader {
            head_offset: NonZero::new(head_offset as usize),
            tail_offset: NonZero::new(tail_offset as usize),
        }
    }

    fn write_arena_header(dst: &mut Self::ArenaHeaderRepr, value: &ArenaHeader) {
        let head_offset = value.head_offset.map(NonZero::get).unwrap_or_default();
        let tail_offset = value.tail_offset.map(NonZero::get).unwrap_or_default();

        debug_assert_eq!(
            head_offset & Self::MIN_ALIGN_MASK,
            0,
            "`head_offset` must be a multiple of unit"
        );
        debug_assert_eq!(
            tail_offset & Self::MIN_ALIGN_MASK,
            0,
            "`tail_offset` must be a multiple of unit"
        );

        debug_assert!(
            head_offset <= Self::OFFSET_MAX,
            "`head_offset` out of bounds"
        );
        debug_assert!(
            tail_offset <= Self::OFFSET_MAX,
            "`tail_offset` out of bounds"
        );

        *dst = Self::write_compact_value(head_offset as u32, tail_offset as u32, 0);
    }

    fn read_segment_header(src: &Self::SegmentHeaderRepr) -> SegmentHeader {
        let (prev_offset, next_offset, size) = Self::read_compact_value(*src);
        SegmentHeader {
            prev_offset: NonZero::new(prev_offset as usize),
            next_offset: NonZero::new(next_offset as usize),
            size: Self::SIZE_MIN + (size as usize),
        }
    }

    fn write_segment_header(dst: &mut Self::SegmentHeaderRepr, value: &SegmentHeader) {
        let prev_offset = value.prev_offset.map(NonZero::get).unwrap_or_default();
        let next_offset = value.next_offset.map(NonZero::get).unwrap_or_default();
        let size = value.size;

        debug_assert_eq!(
            prev_offset & Self::MIN_ALIGN_MASK,
            0,
            "`prev_offset` must be a multiple of unit"
        );
        debug_assert_eq!(
            next_offset & Self::MIN_ALIGN_MASK,
            0,
            "`next_offset` must be a multiple of unit"
        );
        debug_assert_eq!(
            size & Self::MIN_ALIGN_MASK,
            0,
            "`size` must be a multiple of unit"
        );

        debug_assert!(
            prev_offset <= Self::OFFSET_MAX,
            "`prev_offset` out of bounds"
        );
        debug_assert!(
            next_offset <= Self::OFFSET_MAX,
            "`next_offset` out of bounds"
        );
        debug_assert!(
            (Self::SIZE_MIN..=Self::SIZE_MAX).contains(&size),
            "`size` out of bounds"
        );

        let size = size - Self::SIZE_MIN;
        *dst = Self::write_compact_value(prev_offset as u32, next_offset as u32, size as u32);
    }
}

/// Marker trait for [`Teaspoon`](crate::Teaspoon) that supports allocating objects up to 16 MiB.
///
/// See the [module-level documentation](crate#allocator-limits) for more information about the
/// Teaspoon allocator variants and their sizing limits.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct Sizing16MiB;

impl Sizing for Sizing16MiB {}

impl private::Sealed for Sizing16MiB {}

const_assert!(align_of::<u64>() % Sizing16MiB::MIN_ALIGN == 0);

impl Sizing16MiB {
    const MIN_ALIGN: usize = 8;
    const MIN_ALIGN_BITS: u32 = Self::MIN_ALIGN.trailing_zeros();
    const MIN_ALIGN_MASK: usize = Self::MIN_ALIGN - 1;

    const OFFSET_BITS: u64 = 21;
    const OFFSET_MASK: u64 = (1 << Self::OFFSET_BITS) - 1;
    const OFFSET_MAX: usize = (Self::OFFSET_MASK as usize) * Self::MIN_ALIGN;

    const SIZE_BITS: u64 = 21;
    const SIZE_MASK: u64 = (1 << Self::SIZE_BITS) - 1;
    const SIZE_MIN: usize = Self::MIN_ALIGN;
    const SIZE_MAX: usize = Self::SIZE_MIN + (Self::SIZE_MASK as usize) * Self::MIN_ALIGN;

    #[inline]
    const fn read_compact_value(mut value: u64) -> (u64, u64, u64) {
        let a = (value & Self::OFFSET_MASK) << Self::MIN_ALIGN_BITS;
        value >>= Self::OFFSET_BITS;
        let b = (value & Self::OFFSET_MASK) << Self::MIN_ALIGN_BITS;
        value >>= Self::OFFSET_BITS;
        let c = (value & Self::SIZE_MASK) << Self::MIN_ALIGN_BITS;
        (a, b, c)
    }

    #[inline]
    const fn write_compact_value(a: u64, b: u64, c: u64) -> u64 {
        let mut value = c >> Self::MIN_ALIGN_BITS;
        value <<= Self::SIZE_BITS;
        value |= b >> Self::MIN_ALIGN_BITS;
        value <<= Self::OFFSET_BITS;
        value |= a >> Self::MIN_ALIGN_BITS;
        value
    }
}

impl private::SizingInternals for Sizing16MiB {
    type ArenaHeaderRepr = u64;
    type SegmentHeaderRepr = u64;

    fn min_align() -> usize {
        Self::MIN_ALIGN
    }

    fn max_size() -> usize {
        Self::SIZE_MAX
    }

    fn max_offset() -> usize {
        Self::OFFSET_MAX
    }

    fn read_arena_header(src: &Self::ArenaHeaderRepr) -> ArenaHeader {
        let (head_offset, tail_offset, _) = Self::read_compact_value(*src);
        ArenaHeader {
            head_offset: NonZero::new(head_offset as usize),
            tail_offset: NonZero::new(tail_offset as usize),
        }
    }

    fn write_arena_header(dst: &mut Self::ArenaHeaderRepr, value: &ArenaHeader) {
        let head_offset = value.head_offset.map(NonZero::get).unwrap_or_default();
        let tail_offset = value.tail_offset.map(NonZero::get).unwrap_or_default();

        debug_assert_eq!(
            head_offset & Self::MIN_ALIGN_MASK,
            0,
            "`head_offset` must be a multiple of unit"
        );
        debug_assert_eq!(
            tail_offset & Self::MIN_ALIGN_MASK,
            0,
            "`tail_offset` must be a multiple of unit"
        );

        debug_assert!(
            head_offset <= Self::OFFSET_MAX,
            "`head_offset` out of bounds"
        );
        debug_assert!(
            tail_offset <= Self::OFFSET_MAX,
            "`tail_offset` out of bounds"
        );

        *dst = Self::write_compact_value(head_offset as u64, tail_offset as u64, 0);
    }

    fn read_segment_header(src: &Self::SegmentHeaderRepr) -> SegmentHeader {
        let (prev_offset, next_offset, size) = Self::read_compact_value(*src);
        SegmentHeader {
            prev_offset: NonZero::new(prev_offset as usize),
            next_offset: NonZero::new(next_offset as usize),
            size: Self::SIZE_MIN + (size as usize),
        }
    }

    fn write_segment_header(dst: &mut Self::SegmentHeaderRepr, value: &SegmentHeader) {
        let prev_offset = value.prev_offset.map(NonZero::get).unwrap_or_default();
        let next_offset = value.next_offset.map(NonZero::get).unwrap_or_default();
        let size = value.size;

        debug_assert_eq!(
            prev_offset & Self::MIN_ALIGN_MASK,
            0,
            "`prev_offset` must be a multiple of unit"
        );
        debug_assert_eq!(
            next_offset & Self::MIN_ALIGN_MASK,
            0,
            "`next_offset` must be a multiple of unit"
        );
        debug_assert_eq!(
            size & Self::MIN_ALIGN_MASK,
            0,
            "`size` must be a multiple of unit"
        );

        debug_assert!(
            prev_offset <= Self::OFFSET_MAX,
            "`prev_offset` out of bounds"
        );
        debug_assert!(
            next_offset <= Self::OFFSET_MAX,
            "`next_offset` out of bounds"
        );
        debug_assert!(
            (Self::SIZE_MIN..=Self::SIZE_MAX).contains(&size),
            "`size` out of bounds"
        );

        let size = size - Self::SIZE_MIN;
        *dst = Self::write_compact_value(prev_offset as u64, next_offset as u64, size as u64);
    }
}

/// Marker trait for [`Teaspoon`](crate::Teaspoon) that supports allocating objects up to 128 KiB.
///
/// See the [module-level documentation](crate#allocator-limits) for more information about the
/// Teaspoon allocator variants and their sizing limits.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct Sizing128KiB;

impl Sizing for Sizing128KiB {}

impl private::Sealed for Sizing128KiB {}

const_assert!(align_of::<[u16; 2]>() % Sizing128KiB::MIN_ALIGN == 0);
const_assert!(align_of::<[u16; 3]>() % Sizing128KiB::MIN_ALIGN == 0);

impl Sizing128KiB {
    const MIN_ALIGN: usize = 2;
    const MIN_ALIGN_BITS: u32 = Self::MIN_ALIGN.trailing_zeros();
    const MIN_ALIGN_MASK: usize = Self::MIN_ALIGN - 1;

    const OFFSET_MAX: usize = (u16::MAX as usize) * Self::MIN_ALIGN;

    const SIZE_MIN: usize = Self::MIN_ALIGN;
    const SIZE_MAX: usize = Self::SIZE_MIN + (u16::MAX as usize) * Self::MIN_ALIGN;
}

impl private::SizingInternals for Sizing128KiB {
    type ArenaHeaderRepr = [u16; 2];
    type SegmentHeaderRepr = [u16; 3];

    fn min_align() -> usize {
        Self::MIN_ALIGN
    }

    fn max_size() -> usize {
        Self::SIZE_MAX
    }

    fn max_offset() -> usize {
        Self::OFFSET_MAX
    }

    fn read_arena_header(src: &Self::ArenaHeaderRepr) -> ArenaHeader {
        let head_offset = NonZero::new((src[0] as usize) << Self::MIN_ALIGN_BITS);
        let tail_offset = NonZero::new((src[1] as usize) << Self::MIN_ALIGN_BITS);
        ArenaHeader {
            head_offset,
            tail_offset,
        }
    }

    fn write_arena_header(dst: &mut Self::ArenaHeaderRepr, value: &ArenaHeader) {
        let head_offset = value.head_offset.map(NonZero::get).unwrap_or_default();
        let tail_offset = value.tail_offset.map(NonZero::get).unwrap_or_default();

        debug_assert_eq!(
            head_offset & Self::MIN_ALIGN_MASK,
            0,
            "`head_offset` must be a multiple of unit"
        );
        debug_assert_eq!(
            tail_offset & Self::MIN_ALIGN_MASK,
            0,
            "`tail_offset` must be a multiple of unit"
        );

        debug_assert!(
            head_offset <= Self::OFFSET_MAX,
            "`head_offset` out of bounds"
        );
        debug_assert!(
            tail_offset <= Self::OFFSET_MAX,
            "`tail_offset` out of bounds"
        );

        let head_offset = (head_offset >> Self::MIN_ALIGN_BITS) as u16;
        let tail_offset = (tail_offset >> Self::MIN_ALIGN_BITS) as u16;
        *dst = [head_offset, tail_offset];
    }

    fn read_segment_header(src: &Self::SegmentHeaderRepr) -> SegmentHeader {
        let prev_offset = NonZero::new((src[0] as usize) << Self::MIN_ALIGN_BITS);
        let next_offset = NonZero::new((src[1] as usize) << Self::MIN_ALIGN_BITS);
        let size = Self::SIZE_MIN + ((src[2] as usize) << Self::MIN_ALIGN_BITS);
        SegmentHeader {
            prev_offset,
            next_offset,
            size,
        }
    }

    fn write_segment_header(dst: &mut Self::SegmentHeaderRepr, value: &SegmentHeader) {
        let prev_offset = value.prev_offset.map(NonZero::get).unwrap_or_default();
        let next_offset = value.next_offset.map(NonZero::get).unwrap_or_default();
        let size = value.size;

        debug_assert_eq!(
            prev_offset & Self::MIN_ALIGN_MASK,
            0,
            "`prev_offset` must be a multiple of unit"
        );
        debug_assert_eq!(
            next_offset & Self::MIN_ALIGN_MASK,
            0,
            "`next_offset` must be a multiple of unit"
        );
        debug_assert_eq!(
            size & Self::MIN_ALIGN_MASK,
            0,
            "`size` must be a multiple of unit"
        );

        debug_assert!(
            prev_offset <= Self::OFFSET_MAX,
            "`prev_offset` out of bounds"
        );
        debug_assert!(
            next_offset <= Self::OFFSET_MAX,
            "`next_offset` out of bounds"
        );
        debug_assert!(
            (Self::SIZE_MIN..=Self::SIZE_MAX).contains(&size),
            "`size` out of bounds"
        );

        let prev_offset = (prev_offset >> Self::MIN_ALIGN_BITS) as u16;
        let next_offset = (next_offset >> Self::MIN_ALIGN_BITS) as u16;
        let size = ((size - Self::SIZE_MIN) >> Self::MIN_ALIGN_BITS) as u16;
        *dst = [prev_offset, next_offset, size];
    }
}
