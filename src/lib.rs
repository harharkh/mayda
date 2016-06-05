// Copyright 2016 Jeremy Mason
//
// Licensed under the MIT license <LICENSE or
// http://opensource.org/licenses/MIT>. This file may not be copied, modified,
// or distributed except according to those terms.

#![feature(inclusive_range, inclusive_range_syntax)]
#![feature(iter_arith, specialization)]

extern crate mayda_codec;

//pub mod binary;
pub mod error;
pub mod patched;
pub mod utility;

pub use self::error::Error;
pub use self::utility::{Access, Encodable};
pub use self::patched::Patched;
