// Copyright 2016 Jeremy Mason
//
// Licensed under the MIT license <LICENSE or
// http://opensource.org/licenses/MIT>. This file may not be copied, modified,
// or distributed except according to those terms.

//! The only purpose of this crate is to relegate the functions generated by
//! the encode! and decode! syntax extensions of pfor_macros to a separate
//! compilation unit. More extensive documentation is given in the pfor_macros
//! crate.

#![feature(plugin)]
#![plugin(pfor_macros)]

#![allow(unused_mut)]

encode!(u8, 8, 8);
decode!(u8, 8, 8);
encode!(u16, 16, 8);
decode!(u16, 16, 8);
encode!(u32, 32, 8);
decode!(u32, 32, 8);
encode!(u64, 64, 8);
decode!(u64, 64, 8);