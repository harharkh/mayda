// Copyright 2016 Jeremy Mason
//
// Licensed under the MIT license <LICENSE or
// http://opensource.org/licenses/MIT>. This file may not be copied, modified,
// or distributed except according to those terms.

#![feature(specialization)]
#![feature(iter_arith)]

extern crate pfor_codec;

pub mod binary;
pub mod error;
pub mod utility;

#[doc(no_inline)]
pub use self::error::Error;
