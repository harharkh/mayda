// Copyright 2016 Jeremy Mason
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

//! Defines the `mayda::Error` type. Currently only used for the return types of
//! functions defined in the `Encodable` trait, but intended to allow for more
//! complex error handling in the future.

use std::error;
use std::fmt;

/// The `mayda::Error` type.
#[derive(Debug)]
pub struct Error {
  message: String
}

impl Error {
  /// Creates an empty Error object.
  pub fn new(s: &str) -> Error {
    Error {
      message: s.to_string()
    }
  }
}

impl error::Error for Error {
  fn description(&self) -> &str { &self.message }
}

impl fmt::Display for Error {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{}", self.message)
  }
}
