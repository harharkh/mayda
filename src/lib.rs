// Copyright 2016 Jeremy Mason
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

//! This crate provides three types to compress integer arrays. The design
//! generally favors decompression speed and the ability to index the
//! compressed array over the compression ratio, on the principle that the 
//! runtime penalty for using compressed arrays should be as small as possible.
//!
//! # Usage
//! 
//! Add this to your `Cargo.toml`:
//!
//! ```toml
//! [dependencies]
//! mayda = "0.1"
//! ```
//!
//! and this to your crate root:
//!
//! ```rust
//! extern crate mayda;
//! ```
//! 
//! # Example: encoding and decoding
//!
//! The `Uniform` struct is recommended for general purpose integer compression.
//! Use the `Encode` trait to encode and decode the array.
//!
//! ```rust
//! use std::mem;
//! use mayda::{Uniform, Encode};
//! 
//! // Integers in some interval of length 255, require one byte per integer
//! let input: Vec<u32> = (0..128).map(|x| (x * 73) % 181 + 307).collect();
//! 
//! let mut uniform = Uniform::new();
//! uniform.encode(&input).unwrap();
//! 
//! let i_bytes = std::mem::size_of_val(input.as_slice());
//! let u_bytes = std::mem::size_of_val(uniform.storage());
//! 
//! // 128 bytes for encoded entries, 12 bytes of overhead
//! assert_eq!(i_bytes, 512);
//! assert_eq!(u_bytes, 140);
//! 
//! let output: Vec<u32> = uniform.decode();
//! assert_eq!(input, output);
//! ```
//!
//! # Example: indexing
//! 
//! Use the `Access` trait to index the compressed array. This is similar to
//! `Index`, but returns a vector instead of a slice.
//!
//! ```rust
//! use mayda::{Uniform, Encode, Access};
//! 
//! // All primitive integer types supported
//! let input: Vec<i16> = (-64..64).collect();
//! 
//! let mut uniform = Uniform::new();
//! uniform.encode(&input).unwrap();
//! 
//! let val: i16 = uniform.access(64);
//! assert_eq!(val, 0);
//! 
//! // Vector is returned to give ownership to the caller
//! let range: Vec<i16> = uniform.access(..10);
//! assert_eq!(range, (-64..-54).collect::<Vec<_>>());
//! ```
//!
//! # Algorithm
//!
//! The compression algorithm relies on the observation that for many integer
//! arrays, the probability distribution of a block of 128 entries is not
//! uniform over all values that can be represented by the integer type. For
//! example, an array of indices into a second array with 256 entries has
//! entries that are bounded below by 0 and above by 255. This requires only
//! eight bits per entry, rather than the 32 or 64 generally set aside for a
//! usize index. The basic idea of the compression algorithm is to represent
//! all of the entries in a block with a single minimum necessary bit width.
//! This allows SIMD operations and manual loop unrolling to avoid branches to
//! be used to accelerate encoding and decoding.
//!
//! This approach does not perform well for probability distributions with
//! outliers though, or for situations where the median value is nonzero. This
//! crate provides three types that handle this situation by applying different
//! initial transformations to the input integer array.
//!
//! The `Uniform` type targets encoding and decoding speed. The only
//! transformation is to subtract the minimum value from the entries, with the
//! result that the compression depends only on the difference between the
//! largest and smallest entries.
//!
//! The `Monotone` type is specifically intended for arrays with monotone
//! increasing entries. A blocks of entries is transformed into an offset and
//! an array of differences of successive entries, and the array of differences
//! is encoded by the approach above. The compression depends only on the 
//! largest entry in the difference array.
//!
//! The `Unimodal` type performs the most extensive transformations and offers
//! the most robust compression. The median value is subtracted from the
//! entries, the entries are mapped to the unsigned integers by the zig-zag
//! encoding, and the most significant bits of any outliers are removed and
//! stored separately. The result is that the compression effectively depends
//! only on the standard deviation of the probability distribution of the block
//! entries.
//!
//! # Indexing
//!
//! Indexing an object of the `Uniform`, `Monotone` or `Unimodal` types is not
//! a simple pointer offset. Part of the header encodes the relative offsets to
//! every block in a compressed form, with the result that random access via
//! the `Access` trait is an `O(log(idx))` operation, where `idx` is the value
//! of the index (not the length of the array). The overhead of this part of
//! the header is around a tenth of a bit per encoded integer.
//!
//! If you need to access several nearby entries, consider accessing the range
//! and indexing the returned vector for performance.
//!
//! # Safety
//!
//! As a general rule, you **should not** decode or access objects of the
//! `Uniform`, `Monotone` or `Unimodal` types from untrusted sources.
//!
//! `mayda` performs wildly unsafe pointer operations during encoding and
//! decoding. Changing the header information with `mut_storage` can cause data
//! to be written to or read from arbitrary addresses in memory.
//!
//! That said, the situation is the same for any of the data structures in the
//! standard library (consider the `set_len` method of a `Vec`).

#![feature(inclusive_range)]
#![feature(inclusive_range_syntax)]
#![feature(iter_arith)]
#![feature(specialization)]

extern crate mayda_codec;

pub mod error;
pub mod monotone;
pub mod uniform;
pub mod unimodal;
pub mod utility;

pub use self::error::Error;
pub use self::monotone::Monotone;
pub use self::uniform::Uniform;
pub use self::unimodal::Unimodal;
pub use self::utility::{Access, Encode};
