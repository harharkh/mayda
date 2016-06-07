// Copyright 2016 Jeremy Mason
//
// Licensed under the MIT license <LICENSE or
// http://opensource.org/licenses/MIT>. This file may not be copied, modified,
// or distributed except according to those terms.

#![feature(inclusive_range, inclusive_range_syntax)]
#![feature(iter_arith, specialization)]

extern crate mayda_codec;

pub mod bit_packed;
pub mod error;
pub mod patched;
pub mod utility;

pub use self::bit_packed::BitPacked;
pub use self::error::Error;
pub use self::patched::Patched;
pub use self::utility::{Access, Encodable};
