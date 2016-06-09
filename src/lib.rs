// Copyright 2016 Jeremy Mason
//
// Licensed under the MIT license <LICENSE or
// http://opensource.org/licenses/MIT>. This file may not be copied, modified,
// or distributed except according to those terms.

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
pub use self::utility::{Access, Encodable};
