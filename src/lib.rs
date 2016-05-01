#![feature(specialization)]

extern crate pfor_codec;

pub mod binary;
pub mod error;
pub mod utility;

#[doc(no_inline)]
pub use self::error::Error;
