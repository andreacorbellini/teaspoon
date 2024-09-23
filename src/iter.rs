// Copyright © 2024 Andrea Corbellini and contributors
// SPDX-License-Identifier: BSD-3-Clause

use crate::arena::Arena;
use crate::ptr::SegmentHeaderPtr;
use crate::segment::Segment;
use crate::sizing::Sizing;
use core::ptr::NonNull;

#[derive(Copy, Clone, Debug)]
pub(crate) enum Chunk<'a, S: Sizing> {
    Used(Segment<'a, S>),
    Unused(NonNull<[u8]>),
}

#[derive(Copy, Clone, Debug)]
enum State<'a, S: Sizing> {
    Initial,
    BeforeSegment(SegmentHeaderPtr<S>),
    AtSegment(Segment<'a, S>),
    Final,
}

#[derive(Clone, Debug)]
pub(crate) struct ArenaChunks<'a, S: Sizing> {
    arena: Arena<'a, S>,
    state: State<'a, S>,
}

impl<'a, S: Sizing> ArenaChunks<'a, S> {
    pub(crate) const fn new(arena: Arena<'a, S>) -> Self {
        Self {
            arena,
            state: State::Initial,
        }
    }
}

impl<'a, S: Sizing> Iterator for ArenaChunks<'a, S> {
    type Item = Chunk<'a, S>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let (item, new_state) = match self.state {
                State::Initial => {
                    match self.arena.head() {
                        // No allocated objects; return the whole usable space in the arena
                        None => (Some(Chunk::Unused(self.arena.usable())), State::Final),
                        // At least one allocated object; return the usable space before that (if
                        // any)
                        Some(head) => {
                            let usable = self.arena.usable().cast::<u8>();
                            // TODO: Use `head.sub_ptr(usable)` once that's stabilized
                            let unused_size = unsafe { head.byte_offset_from(usable) };
                            debug_assert!(unused_size >= 0, "negative offset");
                            let unused =
                                NonNull::slice_from_raw_parts(usable, unused_size as usize);
                            (Some(Chunk::Unused(unused)), State::BeforeSegment(head))
                        }
                    }
                }
                State::BeforeSegment(segment_ptr) => {
                    let segment = unsafe { Segment::read(self.arena, segment_ptr) };
                    (Some(Chunk::Used(segment)), State::AtSegment(segment))
                }
                State::AtSegment(segment) => {
                    let new_state = match segment.next_ptr() {
                        None => State::Final,
                        Some(ptr) => State::BeforeSegment(ptr),
                    };
                    (Some(Chunk::Unused(segment.trailing())), new_state)
                }
                State::Final => (None, State::Final),
            };

            self.state = new_state;

            if let Some(Chunk::Unused(unused)) = item {
                if unused.is_empty() {
                    continue;
                }
            }

            break item;
        }
    }
}
