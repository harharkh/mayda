// Copyright 2016 Jeremy Mason
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

//! Contains constants, enums, traits and functions used by all of the encoding
//! types provided by the `mayda` crate.

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

/// Indicates that the bitwise representation of the type is known to `mayda`.
/// Intended to be implemented only for the primitive integer types. Mainly
/// used as a bound on the `Encode` trait.
pub trait Bits {
  /// Number of bits in the standard representation.
  fn width() -> u32;

  /// Number of bits required to represent the number in binary. Notice that
  /// `0.bits() == 0u32` intentionally.
  fn bits(&self) -> u32;
}

macro_rules! bits_impl {
  ($(($t: ty: $size: expr))*) => ($(
    impl Bits for $t {
      #[inline]
      fn width() -> u32 { $size }

      #[inline]
      fn bits(&self) -> u32 { $size - self.leading_zeros() }
    }
  )*)
}

bits_impl!{
  (u8: 8)
  (u16: 16)
  (u32: 32)
  (u64: 64)
  (usize: mem::size_of::<usize>() as u32 * 8)
  (i8: 8)
  (i16: 16)
  (i32: 32)
  (i64: 64)
  (isize: mem::size_of::<isize>() as u32 * 8)
}

/// Indicates that the type can be encoded and decoded by `mayda`.
///
/// The default implementations of `encode` and `decode` return an error or
/// panic to indicate that there is no available specialization for the type.
/// This should not happen unless the user implements `Bits` for some other
/// type or there is a library bug.
pub trait Encode<B: Bits> {
  /// Encodes the slice into the `Encode` object.
  ///
  /// # Errors
  ///
  /// By convention, returns an error if the input slice contains more than the
  /// supported number of entries (currently 2<sup>37</sup> - 2<sup>7</sup>).
  fn encode(&mut self, &[B]) -> Result<(), super::Error>;

  /// Decodes the contents of the `Encode` object. Returns a vector because
  /// ownership of the returned value must be given to the caller.
  fn decode(&self) -> Vec<B>;

  /// Decodes the contents of the `Encode` object into the slice. Slightly more
  /// efficient than `decode` if the slice is already allocated. Returns the
  /// number of decoded entries.
  ///
  /// # Panics
  ///
  /// By convention, panics if the slice is of insufficient length.
  fn decode_into(&self, &mut [B]) -> usize;
}

/// A trait for indexing an encoded vector. Similar to but less convenient than
/// `Index`. `Index::index()` returns a reference, but an encoded vector type
/// must give ownership of the returned value to the caller.
///
/// # Panics
///
/// By convention, all implementations panic when the index is out of bounds.
///
/// The default implementations of `access` panic to indicate that there is no
/// available specialization for the type. This should not happen unless the
/// user implements `Bits` for some other type or there is a library bug.
pub trait Access<Idx> {
  /// The type returned by the access operation.
  type Output;

  /// The method for the access `foo.access(bar)` operation.
  fn access(&self, index: Idx) -> Self::Output;
}

/// Returns number of words required to store the given number of bits. A word
/// is 32 bits long.
///
/// # Panics
///
/// Integer overflow occurs when the value of bits is above `u32::MAX - 31`.
/// This should not happen in `mayda` since this function is only used to find
/// the number of words required for an encoded block of up to 128 integers.
///
/// # Examples
///
/// ```
/// use std::mem;
/// use mayda::utility::words_for_bits;
/// 
/// let words = words_for_bits(13 * (mem::size_of::<u8>() * 8) as u32);
/// assert_eq!(4, words);
/// ```
#[inline]
pub fn words_for_bits(bits: u32) -> usize {
  ((bits + 31) >> 5) as usize
}

/// A modified version of the Floyd-Rivest algorithm with fewer comparisions
/// and fewer swaps, specialized for the case of slices with length < 500. The
/// modifications may not be known in the literature. Intended to be used to
/// find the median of a block.
///
/// # Examples
///
/// ```
/// use mayda::utility::select_m;
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
