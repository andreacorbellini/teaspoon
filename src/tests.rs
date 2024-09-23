// Copyright © 2024 Andrea Corbellini and contributors
// SPDX-License-Identifier: BSD-3-Clause

#![cfg(feature = "allocator-api")]

extern crate alloc;

use crate::Sizing;
use crate::Teaspoon;
use crate::Usage;
use alloc::boxed::Box;
use alloc::vec;
use alloc::vec::Vec;
use core::alloc::AllocError;
use core::alloc::Allocator;
use core::alloc::Layout;
use core::ptr::NonNull;
use rand::rngs::SmallRng;
use rand::seq::SliceRandom;
use rand::Rng;
use rand::SeedableRng;

macro_rules! assert_aligned {
    ( $ptr:expr , $layout:expr $( , $( $tt:tt )* )? ) => {
        assert_eq!($ptr.cast::<u8>().align_offset($layout.align()), 0 $(, $($tt)*)?);
    }
}

#[repr(align(8))]
#[derive(Debug)]
struct AlignedArray<const N: usize>([u8; N]);

fn boxes<S: Sizing>() {
    let mut arena = [0u8; 512];
    let spoon = Teaspoon::<S>::from(&mut arena);

    let boxes = [
        Box::new_in(0u32, &spoon),
        Box::new_in(1u32, &spoon),
        Box::new_in(2u32, &spoon),
        Box::new_in(3u32, &spoon),
        Box::new_in(4u32, &spoon),
        Box::new_in(5u32, &spoon),
        Box::new_in(6u32, &spoon),
        Box::new_in(7u32, &spoon),
        Box::new_in(8u32, &spoon),
    ];

    for (index, b) in boxes.into_iter().enumerate() {
        assert_eq!(*b, index as u32);
    }
}

fn vec<S: Sizing>() {
    let mut arena = [0u8; 512];
    let spoon = Teaspoon::<S>::from(&mut arena);
    let mut vec = Vec::<u32, _>::new_in(spoon);
    for i in 1..=32 {
        vec.push(i);
    }
    assert_eq!(vec, (1..=32).collect::<Vec<u32>>());
}

fn zst<S: Sizing>() {
    let mut arena = [0u8; 512];
    let spoon = Teaspoon::<S>::from(&mut arena);

    let layout = Layout::new::<()>();
    let ptr = spoon.allocate(layout).expect("allocation of zst failed");

    assert_aligned!(ptr, layout);
}

#[cfg(not(miri))]
fn random<S: Sizing>() {
    fn random_layout<R: Rng>(mut rng: R) -> Layout {
        let size = rng.gen_range(0..=512);
        let align = [1usize, 2, 4, 8, 16, 32, 64]
            .choose(&mut rng)
            .copied()
            .unwrap();
        Layout::from_size_align(size, align).expect("layout error")
    }

    fn alloc_random<A: Allocator, R: Rng>(
        allocator: A,
        rng: R,
        objects: &mut Vec<(NonNull<[u8]>, Layout)>,
    ) {
        let layout = random_layout(rng);
        if let Ok(ptr) = allocator.allocate(layout) {
            assert_aligned!(ptr, layout);
            objects.push((ptr, layout));
        }
    }

    fn dealloc_random<A: Allocator, R: Rng>(
        allocator: A,
        mut rng: R,
        objects: &mut Vec<(NonNull<[u8]>, Layout)>,
    ) {
        if objects.is_empty() {
            return;
        }
        let index = rng.gen_range(0..objects.len());
        let (ptr, layout) = objects.remove(index);
        unsafe { allocator.deallocate(ptr.cast(), layout) }
    }

    fn resize_random<A: Allocator, R: Rng>(
        allocator: A,
        mut rng: R,
        objects: &mut Vec<(NonNull<[u8]>, Layout)>,
    ) {
        if objects.is_empty() {
            return;
        }
        let object = objects.choose_mut(&mut rng).unwrap();
        let (old_ptr, old_layout) = *object;
        let new_layout = random_layout(&mut rng);
        let new_ptr = if new_layout.size() < old_layout.size() {
            unsafe { allocator.shrink(old_ptr.cast(), old_layout, new_layout) }
        } else {
            unsafe { allocator.grow(old_ptr.cast(), old_layout, new_layout) }
        };
        if let Ok(new_ptr) = new_ptr {
            assert_aligned!(new_ptr, new_layout);
            *object = (new_ptr, new_layout);
        }
    }

    let mut arena = vec![0u8; 2 * 1024 * 1024];
    let spoon = Teaspoon::<S>::from(&mut arena[..]);

    let mut rng = SmallRng::seed_from_u64(12345);

    let mut objects = Vec::<(NonNull<[u8]>, Layout)>::new();

    for _ in 0..2000 {
        match rng.gen_range(0..8) {
            0 => dealloc_random(&spoon, &mut rng, &mut objects),
            1 => resize_random(&spoon, &mut rng, &mut objects),
            _ => alloc_random(&spoon, &mut rng, &mut objects),
        }
    }

    while !objects.is_empty() {
        dealloc_random(&spoon, &mut rng, &mut objects);
    }
}

fn max_alloc<S: Sizing>(expected_max: usize) {
    fn try_alloc<S: Sizing>(
        arena_size: usize,
        alloc_size: usize,
    ) -> Result<NonNull<[u8]>, AllocError> {
        let mut arena = vec![0u8; arena_size];
        let spoon = Teaspoon::<S>::from(&mut arena[..]);
        let layout = Layout::from_size_align(alloc_size, 1).unwrap();
        spoon.allocate(layout)
    }

    let arena_size = 2 * expected_max;
    assert!(try_alloc::<S>(arena_size, expected_max).is_ok());
    assert!(try_alloc::<S>(arena_size, expected_max + 1).is_err());
}

fn fill_with_smallest<S: Sizing>(arena_overhead: usize, segment_overhead: usize, min_size: usize) {
    const SIZE: usize = 1024;
    let mut arena = AlignedArray([0u8; SIZE]);
    let spoon = Teaspoon::<S>::from(&mut arena.0);

    let layout = Layout::new::<u8>();
    let max_allocations = (SIZE - arena_overhead) / (segment_overhead + min_size);

    for _ in 0..max_allocations {
        assert!(spoon.allocate(layout).is_ok());
    }

    assert!(spoon.allocate(layout).is_err());
}

fn shrink_in_place<S: Sizing>() {
    let mut arena = [0u8; 128];
    let spoon = Teaspoon::<S>::from(&mut arena);

    let layout1 = Layout::new::<[u32; 10]>();
    let mut ptr1 = spoon.allocate_zeroed(layout1).expect("allocation failed");
    unsafe {
        ptr1.as_mut()
            .copy_from_slice(b"abcdefghijklmnopqrstuvwxyz0123456789!#@:")
    };

    let layout2 = Layout::new::<[u32; 4]>();
    let ptr2 = unsafe { spoon.shrink(ptr1.cast(), layout1, layout2) }.expect("reallocation failed");

    assert!(core::ptr::addr_eq(ptr1.as_ptr(), ptr2.as_ptr()));
    assert_eq!(ptr1.len(), layout1.size());
    assert_eq!(ptr2.len(), layout2.size());
    assert_eq!(unsafe { ptr2.as_ref() }, b"abcdefghijklmnop");
}

fn grow_in_place<S: Sizing>() {
    let mut arena = [0u8; 128];
    let spoon = Teaspoon::<S>::from(&mut arena);

    let layout1 = Layout::new::<[u32; 4]>();
    let mut ptr1 = spoon.allocate_zeroed(layout1).expect("allocation failed");
    unsafe { ptr1.as_mut().copy_from_slice(b"abcdefghijklmnop") };

    let layout2 = Layout::new::<[u32; 10]>();
    let ptr2 = unsafe { spoon.grow(ptr1.cast(), layout1, layout2) }.expect("reallocation failed");

    assert!(core::ptr::addr_eq(ptr1.as_ptr(), ptr2.as_ptr()));
    assert_eq!(ptr1.len(), layout1.size());
    assert_eq!(ptr2.len(), layout2.size());
    assert_eq!(
        unsafe { ptr2.as_ref() },
        b"abcdefghijklmnop\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0"
    );
}

fn grow_reallocated<S: Sizing>() {
    let mut arena = [0u8; 128];
    let spoon = Teaspoon::<S>::from(&mut arena);

    let layout1 = Layout::new::<[u32; 4]>();
    let mut ptr1 = spoon.allocate_zeroed(layout1).expect("allocation failed");
    unsafe { ptr1.as_mut().copy_from_slice(b"abcdefghijklmnop") };

    spoon
        .allocate(Layout::new::<u8>())
        .expect("allocation failed");

    let layout2 = Layout::new::<[u32; 10]>();
    let ptr2 = unsafe { spoon.grow(ptr1.cast(), layout1, layout2) }.expect("reallocation failed");

    assert!(!core::ptr::addr_eq(ptr1.as_ptr(), ptr2.as_ptr()));
    assert_eq!(ptr1.len(), layout1.size());
    assert_eq!(ptr2.len(), layout2.size());
    assert_eq!(
        unsafe { ptr2.as_ref() },
        b"abcdefghijklmnop\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0"
    );
}

fn min_arena_size<S: Sizing>(arena_overhead: usize, segment_overhead: usize, min_align: usize) {
    let layout = Layout::new::<u8>();
    let mut arena = AlignedArray([0u8; 1024]);
    let expected_min_size = arena_overhead + segment_overhead + min_align;

    for n in 0..expected_min_size {
        let spoon = Teaspoon::<S>::from(&mut arena.0[..n]);
        assert!(
            spoon.allocate(layout).is_err(),
            "allocation with an arena of {n} bytes should have failed"
        );
    }

    let spoon = Teaspoon::<S>::from(&mut arena.0[..expected_min_size]);
    assert!(
        spoon.allocate(layout).is_ok(),
        "allocation with an arena of {} bytes should have succeeded",
        expected_min_size
    );
}

fn usage<S: Sizing>(arena_overhead: usize, segment_overhead: usize, min_align: usize) {
    fn alloc<A: Allocator>(allocator: A, size: usize) -> NonNull<[u8]> {
        let layout = Layout::from_size_align(size, 1).expect("layout error");
        allocator.allocate(layout).expect("allocation failed")
    }

    fn dealloc<A: Allocator>(allocator: A, ptr: NonNull<[u8]>, size: usize) {
        let layout = Layout::from_size_align(size, 1).expect("layout error");
        unsafe { allocator.deallocate(ptr.cast(), layout) }
    }

    const SIZE: usize = 1024;
    let mut arena = AlignedArray([0u8; SIZE]);
    let spoon = Teaspoon::<S>::from(&mut arena.0);

    assert_eq!(
        spoon.usage(),
        Usage {
            total: SIZE,
            used: 0,
            free: SIZE - arena_overhead,
            objects: 0
        }
    );

    let ptr1 = alloc(&spoon, 0);
    assert_eq!(
        spoon.usage(),
        Usage {
            total: SIZE,
            used: 0,
            free: SIZE - arena_overhead,
            objects: 0,
        }
    );

    let ptr2 = alloc(&spoon, 16);
    assert_eq!(
        spoon.usage(),
        Usage {
            total: SIZE,
            used: 16,
            free: SIZE - arena_overhead - segment_overhead - 16,
            objects: 1,
        }
    );

    let ptr3 = alloc(&spoon, 1);
    assert_eq!(
        spoon.usage(),
        Usage {
            total: SIZE,
            used: 16 + min_align,
            free: SIZE - arena_overhead - 2 * segment_overhead - 16 - min_align,
            objects: 2,
        }
    );

    dealloc(&spoon, ptr3, 1);
    assert_eq!(
        spoon.usage(),
        Usage {
            total: SIZE,
            used: 16,
            free: SIZE - arena_overhead - segment_overhead - 16,
            objects: 1,
        }
    );

    let last_size = spoon.usage().free - segment_overhead;
    let ptr4 = alloc(&spoon, last_size);
    assert_eq!(
        spoon.usage(),
        Usage {
            total: SIZE,
            used: 16 + last_size,
            free: 0,
            objects: 2,
        }
    );

    dealloc(&spoon, ptr2, 16);
    assert_eq!(
        spoon.usage(),
        Usage {
            total: SIZE,
            used: last_size,
            free: SIZE - arena_overhead - segment_overhead - last_size,
            objects: 1,
        }
    );

    dealloc(&spoon, ptr4, last_size);
    assert_eq!(
        spoon.usage(),
        Usage {
            total: SIZE,
            used: 0,
            free: SIZE - arena_overhead,
            objects: 0,
        }
    );

    dealloc(&spoon, ptr1, 0);
    assert_eq!(
        spoon.usage(),
        Usage {
            total: SIZE,
            used: 0,
            free: SIZE - arena_overhead,
            objects: 0,
        }
    );
}

macro_rules! common_tests {
    (
        S = $sizing:ty ,
        arena overhead : $arena_overhead:expr ,
        segment overhead : $segment_overhead:expr ,
        min align : $min_align:expr ,
        max alloc : $max_alloc:expr $(,)?
    ) => {
        #[test]
        fn boxes() {
            $crate::tests::boxes::<$sizing>()
        }

        #[test]
        fn vec() {
            $crate::tests::vec::<$sizing>()
        }

        #[test]
        fn zst() {
            $crate::tests::zst::<$sizing>()
        }

        #[test]
        #[cfg(not(miri))]
        fn random() {
            $crate::tests::random::<$sizing>()
        }

        #[test]
        fn max_alloc() {
            $crate::tests::max_alloc::<$sizing>($max_alloc)
        }

        #[test]
        fn fill_with_smallest() {
            $crate::tests::fill_with_smallest::<$sizing>(
                $arena_overhead,
                $segment_overhead,
                $min_align,
            )
        }

        #[test]
        fn shrink_in_place() {
            $crate::tests::shrink_in_place::<$sizing>()
        }

        #[test]
        fn grow_in_place() {
            $crate::tests::grow_in_place::<$sizing>()
        }

        #[test]
        fn grow_reallocated() {
            $crate::tests::grow_reallocated::<$sizing>()
        }

        #[test]
        fn min_arena_size() {
            $crate::tests::min_arena_size::<$sizing>($arena_overhead, $segment_overhead, $min_align)
        }

        #[test]
        fn usage() {
            $crate::tests::usage::<$sizing>($arena_overhead, $segment_overhead, $min_align)
        }
    };
}

use common_tests;

#[allow(non_snake_case)]
mod Sizing4KiB {
    super::common_tests!(
        S = crate::Sizing4KiB,
        arena overhead: 4,
        segment overhead: 4,
        min align: 4,
        max alloc: 4 * 1024,
    );
}

#[allow(non_snake_case)]
mod Sizing128KiB {
    super::common_tests!(
        S = crate::Sizing128KiB,
        arena overhead: 4,
        segment overhead: 6,
        min align: 2,
        max alloc: 128 * 1024,
    );
}

#[allow(non_snake_case)]
mod Sizing16MiB {
    super::common_tests!(
        S = crate::Sizing16MiB,
        arena overhead: 8,
        segment overhead: 8,
        min align: 8,
        max alloc: 16 * 1024 * 1024,
    );
}
