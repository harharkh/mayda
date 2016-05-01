// Copyright 2016 Jeremy Mason
//
// Licensed under the MIT license <LICENSE or
// http://opensource.org/licenses/MIT>. This file may not be copied, modified,
// or distributed except according to those terms.

//! Defines the pfor::Error type. Currently only used for the return type of
//! utility::decode, but intended to allow for more complex error handling in
//! the future.

use std::error;
use std::fmt;

/// The pfor::Error type.
#[derive(Debug)]
pub struct Error {
  message: String
}

impl Error {
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
