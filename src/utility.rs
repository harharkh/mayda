// Licensed under the MIT license <LICENSE or
// http://opensource.org/licenses/MIT>. This file may not be copied, modified,
// or distributed except according to those terms.

//! Contains constants, enums, traits and functions used by all of the encoding
//! types provided by the pfor crate.

use std::mem;

// Flags that indicate minimum width required to decode. Hidden from the docs
// because the constants are implementation dependent.
#[doc(hidden)]
pub const U8_FLAG: u32 = 0x00000000;
#[doc(hidden)]
pub const U16_FLAG: u32 = 0x00000001;
#[doc(hidden)]
pub const U32_FLAG: u32 = 0x00000002;
#[doc(hidden)]
pub const U64_FLAG: u32 = 0x00000003;

/// Indicates that the bitwise representation of the type is known to pfor.
/// Intended to be implemented only for the primitive unsigned integer types.
/// Mainly used as a bound on the Encodable trait.
pub trait Bits {
  /// Name of the type as a static string.
  fn name() -> &'static str;
  /// Number of bits in the standard representation.
  fn width() -> usize;
  /// Number of bits required to represent the number in binary.
  fn bits(&self) -> u32;
}

macro_rules! bits_impl {
  ($(($t: ty: $name: expr, $size: expr))*) => ($(
    impl Bits for $t {
      #[inline]
      fn name() -> &'static str { $name }
      #[inline]
      fn width() -> usize { $size }
      #[inline]
      fn bits(&self) -> u32 { $size as u32 - self.leading_zeros() }
    }
  )*)
}

bits_impl!{
  (u8: "u8", 8)
  (u16: "u16", 16)
  (u32: "u32", 32)
  (u64: "u64", 64)
  (usize: "usize", mem::size_of::<usize>() * 8)
}

/// Indicates that the type can be encoded and decoded by pfor.
///
/// # Panics
///
/// The default implementations of encode and decode panic to indicate that
/// there is no available specialization for the type. This should not happen
/// unless the user implements Bits for some other type, or there is a library
/// bug.
pub trait Encodable<U: Bits> {
  fn encode(&mut self, &[U]);
  fn decode(&self) -> Result<Vec<U>, super::Error>;
}

/// Returns number of words required to store the given number of bits. A word
/// is 32 bits long.
///
/// # Panics
///
/// Integer overflow occurs when the value of bits is above usize::MAX - 31.
/// This should not happen within pfor since the function is only used to find
/// the number of words required for a block of up to 128 primitive unsigned
/// integers.
///
/// # Examples
///
/// ```
/// use std::mem;
/// use pfor::utility::words_for_bits;
/// let words = words_for_bits(13 * (mem::size_of::<u8>() * 8));
/// assert_eq!(4, words);
/// ```
#[inline]
pub fn words_for_bits(bits: usize) -> usize {
  (bits + 31) / 32
}
