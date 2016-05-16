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
  fn bits(&self) -> usize;
}

macro_rules! bits_impl {
  ($(($t: ty: $name: expr, $size: expr))*) => ($(
    impl Bits for $t {
      #[inline]
      fn name() -> &'static str { $name }
      #[inline]
      fn width() -> usize { $size }
      #[inline]
      fn bits(&self) -> usize { $size - self.leading_zeros() as usize }
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
/// The default implementations of encode and decode returns an error to
/// indicate that there is no available specialization for the type. This
/// should not happen unless the user implements Bits for some other type, or
/// there is a library bug.
pub trait Encodable<B: Bits> {
  fn encode(&mut self, &[B]) -> Result<(), super::Error>;
  fn decode(&self) -> Result<Vec<B>, super::Error>;
}

/// Effectively a trait for indexing an encoded vector type.
///
/// The interface is less convenient interface than for Index. Index::index()
/// returns a reference, but an encoded vector type must give ownership to the
/// caller.
pub trait Access<Idx> {
  type Output;
  fn access(&self, index: Idx) -> Self::Output;
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
  (bits + 31) >> 5
}

/// A modified version of the Floyd-Rivest algorithm with fewer comparisions
/// and fewer swaps, specialized for the case of slices with length < 500. The
/// modifications may not be known in the literature. This is intended to be
/// used to find the median of a block.
///
/// # Examples
///
/// ```
/// use pfor::utility::select_m;
///
/// let mut array: [u32; 7] = [1, 4, 2, 8, 5, 7, 1];
///
/// let min: u32 = select_m(&mut array, 0);
/// let max: u32 = select_m(&mut array, 6);
/// let med: u32 = select_m(&mut array, 3);
///
/// assert_eq!(1, min);
/// assert_eq!(8, max);
/// assert_eq!(4, med);
/// ```
pub fn select_m<T: Copy + Ord>(array: &mut [T], k: usize) -> T {
  unsafe {
    let k: *mut T = array.as_mut_ptr().offset(k as isize);
    let mut l: *mut T = array.as_mut_ptr();
    let mut r: *mut T = array.as_mut_ptr().offset(array.len() as isize - 1);

    while (l as usize) < (r as usize) {
      // Median of three
      if *k < *l { mem::swap(&mut *l, &mut *k); }
      if *k < *r { mem::swap(&mut *k, &mut *r); }
      if *r < *l { mem::swap(&mut *r, &mut *l); }

      // Median value is on the right
      let t: T = *r;

      let mut i: *mut T = l.offset(1);
      let mut j: *mut T = r.offset(-1);
      while *i < t { i = i.offset(1); }
      while *j > t { j = j.offset(-1); }

      while (i as usize) < (j as usize) {
        mem::swap(&mut *i, &mut *j);
        i = i.offset(1);
        j = j.offset(-1);
        while *i < t { i = i.offset(1); }
        while *j > t { j = j.offset(-1); }
      }

      // Move pivot to sorted positon
      j = j.offset(1);
      mem::swap(&mut *j, &mut *r);

      if (j as usize) <= (k as usize) {
        l = j.offset(1);
      }
      if (k as usize) <= (j as usize) {
        r = j.offset(-1);
      }
    }
    *k
  }
}
