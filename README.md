# Teaspoon: an allocator for when all you have is a teaspoon of memory.

[![Crate](https://img.shields.io/crates/v/teaspoon)](https://crates.io/crates/teaspoon) [![Documentation](https://img.shields.io/docsrs/teaspoon)](https://docs.rs/teaspoon/) [![License](https://img.shields.io/crates/l/teaspoon)](https://choosealicense.com/licenses/bsd-3-clause/)

Teaspoon is a lightweight memory allocator designed for minimal overhead. It's
meant to be used in situations where you have very limited memory available, or
when you want to allocate objects on the stack.

Teaspoon is optimized for low memory overhead first, and performance second.

Check out the [documentation](https://docs.rs/teaspoon/) for usage and examples.

## Features

* Small memory overhead: starting at 4 bytes per allocated object
* Compatible with `no_std` environments
* Support for the nightly `Allocator` API
