// Copyright © 2024 Andrea Corbellini and contributors
// SPDX-License-Identifier: BSD-3-Clause

use crate::arena::Arena;
use crate::iter::ArenaChunks;
use crate::iter::Chunk;
use crate::sizing::Sizing;

/// Memory usage information.
///
/// This structure is returned by [`Teaspoon::usage`](crate::Teaspoon::usage). See that method
/// documentation for information and examples.
#[derive(Default, Clone, PartialEq, Eq, Debug)]
pub struct Usage {
    /// Total memory available to the allocator.
    ///
    /// This includes memory that may be used by the allocator for both allocated objects and
    /// internal structures. `total` usually matches the size passed to the
    /// [`Teaspoon`](crate::Teaspoon) constructor, but sometimes may be slightly lower due to align
    /// requirements.
    ///
    /// Note that `total` does not equal `used + free`. That's because `used` does not keep into
    /// account the overhead from the internal structures used by the allocator. The expression
    /// `total - used - free` may be used to calculate this overhead.
    pub total: usize,
    /// Total memory used by allocated objects.
    ///
    /// This is the sum of the usable data of each allocated object. It does not take into account
    /// the overhead from the internal structures used by the allocator.
    pub used: usize,
    /// Memory unused by the allocator.
    ///
    /// This is the total memory available, minus all the allocated memory, minus all the memory
    /// used by internal structures. Note that trying to allocate an object of size equal to (or
    /// close to) `free` may not succeed, due to overheads and memory fragmentation.
    pub free: usize,
    /// Number of objects currently allocated.
    ///
    /// Allocating an object increments this number; deallocating an object decrements it;
    /// growing/shrinking an object does not alter this number.
    pub objects: usize,
}

impl Usage {
    pub(crate) fn get<S: Sizing>(arena: Arena<'_, S>) -> Self {
        let mut usage = Self {
            total: arena.size(),
            used: 0,
            free: 0,
            objects: 0,
        };

        for chunk in ArenaChunks::new(arena) {
            match chunk {
                Chunk::Used(segment) => {
                    usage.used += segment.usable().len();
                    usage.objects += 1;
                }
                Chunk::Unused(slice) => usage.free += slice.len(),
            }
        }

        usage
    }
}
