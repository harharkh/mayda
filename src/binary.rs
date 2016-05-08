// Copyright 2016 Jeremy Mason
//
// Licensed under the MIT license <LICENSE or
// http://opensource.org/licenses/MIT>. This file may not be copied, modified,
// or distributed except according to those terms.

//! Binary encoding of unsigned integer arrays. Designed for efficient
//! decoding, random access, and moderate compression.
//!
//! # Examples
//!
//! ```
//! use pfor::utility::Encodable;
//! use pfor::binary::Binary;
//!
//! let mut bin = Binary::new();
//!
//! let input: Vec<u32> = vec![1, 4, 2, 8, 5, 7];
//! bin.encode(&input).unwrap();
//! let output = bin.decode().unwrap();
//!
//! assert_eq!(input, output);
//! ```

use std::marker::PhantomData;
use std::ops;

use pfor_codec;
use utility::{self, Bits, Encodable, Access};

const WIDTH_MASK: u32 = 0x0000003f;
const ENTRIES_MASK: u32 = 0x00001fc0;

/// The type of a binary encoded integer array.
pub struct Binary<B> {
  storage: Box<[u32]>,
  phantom: PhantomData<B>
}

impl<B: Bits> Binary<B> {
  /// Creates an empty Binary.
  ///
  /// # Examples
  /// ```
  /// use pfor::binary::Binary;
  /// use pfor::utility::Encodable;
  ///
  /// let mut bin = Binary::new();
  ///
  /// let input: Vec<u32> = vec![1, 4, 2, 8, 5, 7];
  /// bin.encode(&input);
  ///
  /// // Storage contains three u32 (two for headers, one for values)
  /// assert_eq!(bin.storage().len(), 3);
  /// ```
  pub fn new() -> Self {
    Binary {
      storage: Box::new([0; 0]),
      phantom: PhantomData
    }
  }

  /// Exposes the word storage of the Binary.
  ///
  /// # Examples
  /// ```
  /// use pfor::binary::Binary;
  /// use pfor::utility::Encodable;
  ///
  /// let mut bin = Binary::new();
  ///
  /// let input: Vec<u32> = vec![1, 4, 2, 8, 5, 7];
  /// bin.encode(&input);
  ///
  /// // Storage contains three u32 (two for headers, one for values)
  /// assert_eq!(bin.storage().len(), 3);
  /// ```
  pub fn storage(&self) -> &[u32] {
    &self.storage
  }

  /// Exposes the word storage of the Binary. Probably unsafe.
  pub unsafe fn mut_storage(&mut self) -> &mut Box<[u32]> {
    &mut self.storage
  }

  /// Returns the width of the encoded integer type.
  ///
  /// # Examples
  /// ```
  /// use pfor::binary::Binary;
  /// use pfor::utility::Encodable;
  ///
  /// let mut bin = Binary::new();
  ///
  /// let input: Vec<u32> = vec![1, 4, 2, 8, 5, 7];
  /// bin.encode(&input);
  ///
  /// assert_eq!(bin.required_width(), 32);
  /// ```
  pub fn required_width(&self) -> usize {
    B::width()
  }
}

/// Default is only for unimplemented types, should not be reachable.
impl<B: Bits> Encodable<B> for Binary<B> {
  default fn encode(&mut self, _: &[B]) -> Result<(), super::Error> {
    Err(super::Error::new("Encodable not implemented for this type"))
  }
  default fn decode(&self) -> Result<Vec<B>, super::Error> {
    Err(super::Error::new("Encodable not implemented for this type"))
  }
}

macro_rules! encodable_impl {
  ($(($ty: ident: $step: expr, $enc: ident, $dec: ident,
      $enc_simd: ident, $dec_simd: ident))*) => ($(
    impl Encodable<$ty> for Binary<$ty> {
      fn encode(&mut self, input: &[$ty]) -> Result<(), super::Error> {
        // Nothing to do
        if input.is_empty() { return Ok(()) }
        
        // Internal representation of ty
        let flag = match $ty::width() {
          8 => utility::U8_FLAG,
          16 => utility::U16_FLAG,
          32 => utility::U32_FLAG,
          64 => utility::U64_FLAG,
          _ => unreachable!()
        };

        // Allow arrays of 2^37 - 2^7 entries (127 GB)
        let blocks = (input.len() + 127) / 128;
        if (blocks - 1).bits() > 30 {
          return Err(super::Error::new("exceeded internal capacity"))
        }

        // Pointers avoid memory initialization, bounds checking, etc.
        let mut block_max: $ty;
        let mut i_ptr = input.as_ptr();
        let mut i_left = input.len() - (blocks - 1) * 128;
        unsafe {
          // Widths of all blocks should be known to construct header
          let mut widths = Vec::with_capacity(blocks);
          let mut lwr_bnd = 0;
          for _ in 0..(blocks - 1) {
            block_max = 1;
            for a in lwr_bnd..(lwr_bnd + 128) {
              block_max |= *(i_ptr.offset(a));
            }
            widths.push(block_max.bits());
            lwr_bnd += 128;
          }
          block_max = 1;
          for a in lwr_bnd..(input.len() as isize) {
            block_max |= *(i_ptr.offset(a));
          }
          widths.push(block_max.bits());

          // Length of storage
          let s_len: usize = 1 + blocks
            + 4 * widths[0..(blocks - 1)].iter().sum::<usize>()
            + utility::words_for_bits(i_left * widths[blocks - 1]);
          let mut storage = Vec::with_capacity(s_len);
          let mut s_ptr = storage.as_mut_ptr();

          // Binary header
          *s_ptr = (blocks as u32 - 1) << 2 | flag;
          s_ptr = s_ptr.offset(1);

          // Block size is known for all but the final block
          for wd in widths[0..(blocks - 1)].iter() {
            // Block header
            *s_ptr = 0x00001fc0 | (wd - 1) as u32;
            s_ptr = s_ptr.offset(1);

            // Encode the block
            pfor_codec::$enc_simd[wd - 1](i_ptr, s_ptr);
            i_ptr = i_ptr.offset(128);
            s_ptr = s_ptr.offset((4 * wd) as isize);
          }

          // Width of the final block
          let wd = widths[blocks - 1];

          // Block header
          *s_ptr = ((i_left - 1) as u32) << 6 | (wd - 1) as u32;
          s_ptr = s_ptr.offset(1);

          // Encode any runs of 128 integers
          if i_left == 128 {
            pfor_codec::$enc_simd[wd - 1](i_ptr, s_ptr);
          } else {
            // Encode any runs of 32 integers
            while i_left >= 32 {
              pfor_codec::$enc[wd - 1][32 / $step - 1](i_ptr, s_ptr);
              i_ptr = i_ptr.offset(32);
              s_ptr = s_ptr.offset(wd as isize);
              i_left -= 32;
            }

            // If there are still entries...
            if i_left > 0 {
              let mut i_bits: usize;
              let mut s_bits: usize = 32;
              // Encode any runs of step integers
              if i_left >= $step {
                let part = i_left - i_left % $step;
                pfor_codec::$enc[wd - 1][part / $step - 1](i_ptr, s_ptr);
                i_ptr = i_ptr.offset(part as isize);
                s_ptr = s_ptr.offset(((part * wd) / 32) as isize);
                i_left -= part;
                s_bits -= (part * wd) % 32;
                // Finished word, *s_ptr is uninitialized
                if s_bits == 32 { *s_ptr = 0; }
              } else {
                *s_ptr = 0;
              }
              // Encode any remaining integers one by one
              for a in 0..i_left {
                i_bits = wd;

                // Encode in the available space
                let lsft = 32 - s_bits;
                *s_ptr |= (*i_ptr as u32) << lsft;

                // While the available space is not enough...
                while s_bits < i_bits {
                  i_bits -= s_bits;
                  s_ptr = s_ptr.offset(1);
                  *s_ptr = (*i_ptr >> (wd - i_bits)) as u32;
                  s_bits = 32;
                }
                s_bits -= i_bits;

                if a < i_left - 1 {
                  i_ptr = i_ptr.offset(1);
                  if s_bits == 0 {
                    s_ptr = s_ptr.offset(1);
                    *s_ptr = 0;
                    s_bits = 32;
                  }
                }
              }
            }
          }

          // Set the length of storage AFTER everything is initialized
          storage.set_len(s_len);
          self.storage = storage.into_boxed_slice();
        }
        Ok(())
      }

      fn decode(&self) -> Result<Vec<$ty>, super::Error> {
        // Nothing to do
        if self.storage.is_empty() { return Ok(Vec::new()) }

        let blocks = ((self.storage[0] >> 2) + 1) as usize;
        let mut output = Vec::with_capacity(blocks * 128);

        // Avoids memory initialization, bounds checking, etc.
        unsafe {
          let mut s_ptr = self.storage.as_ptr().offset(1);
          let mut o_ptr = output.as_mut_ptr();

          // Block size is known for all but the final block
          for _ in 0..(blocks - 1) {
            // Find the width of the block
            let width = ((*s_ptr & WIDTH_MASK) + 1) as usize;
            s_ptr = s_ptr.offset(1);

            // Decode the block
            pfor_codec::$dec_simd[width - 1](s_ptr, o_ptr);
            s_ptr = s_ptr.offset(4 * width as isize);
            o_ptr = o_ptr.offset(128);
          }

          // Final block, number of entries is unknown in advance
          let width = ((*s_ptr & WIDTH_MASK) + 1) as usize;
          let mut o_left = (((*s_ptr & ENTRIES_MASK) >> 6) + 1) as usize;
          s_ptr = s_ptr.offset(1);
          let o_len = (blocks - 1) * 128 + o_left;

          // Decode any runs of 128 integers
          if o_left == 128 {
            pfor_codec::$dec_simd[width - 1](s_ptr, o_ptr);
          } else {
            // Decode any runs of 32 integers
            while o_left >= 32 {
              pfor_codec::$dec[width - 1][32 / $step - 1](s_ptr, o_ptr);
              s_ptr = s_ptr.offset(width as isize);
              o_ptr = o_ptr.offset(32);
              o_left -= 32;
            }
            // If there are still entries...
            if o_left > 0 {
              let mask: $ty = !0 >> ($ty::width() - width);
              let mut s_bits: usize = 32;
              let mut o_bits: usize;
              // Encode any runs of step integers
              if o_left >= $step {
                let part = o_left - o_left % $step;
                pfor_codec::$dec[width - 1][part / $step - 1](s_ptr, o_ptr);
                s_ptr = s_ptr.offset(((part * width) / 32) as isize);
                o_ptr = o_ptr.offset(part as isize);
                o_left -= part;
                s_bits -= (part * width) % 32;
              }
              // Decode any remaining integers one by one
              for a in 0..o_left {
                o_bits = width;

                // Decode anything in the available space
                let rsft = 32 - s_bits;
                *o_ptr = ((*s_ptr >> rsft) as $ty) & mask;

                // While the available space is not enough
                while o_bits > s_bits {
                  o_bits -= s_bits;
                  s_ptr = s_ptr.offset(1);
                  *o_ptr |= ((*s_ptr as $ty) << (width - o_bits)) & mask;
                  s_bits = 32;
                }
                s_bits -= o_bits;

                // Prepare for the following iteration
                if a < o_left - 1 {
                  o_ptr = o_ptr.offset(1);
                  if s_bits == 0 {
                    s_ptr = s_ptr.offset(1);
                    s_bits = 32;
                  }
                }
              }
            }
          }

          // Set the length of output AFTER everything is initialized
          output.set_len(o_len);
        }
        Ok(output)
      }
    }
  )*)
}

encodable_impl!{
  (u8: 16, ENCODE_U8, DECODE_U8, ENCODE_SIMD_U8, DECODE_SIMD_U8)
  (u16: 16, ENCODE_U16, DECODE_U16, ENCODE_SIMD_U16, DECODE_SIMD_U16)
  (u32: 16, ENCODE_U32, DECODE_U32, ENCODE_SIMD_U32, DECODE_SIMD_U32)
  (u64: 16, ENCODE_U64, DECODE_U64, ENCODE_SIMD_U64, DECODE_SIMD_U64)
}

/*
impl Access<usize> for Binary<u8> {
  type Output = u8;
  fn access(&self, index: usize) -> u8 {
    0u8
  }
}

impl Access<ops::Range<usize>> for Binary<u8> {
  type Output = Vec<u8>;
  fn access(&self, index: ops::Range<usize>) -> Vec<u8> {
    vec![0u8]
  }
}

impl Access<ops::RangeTo<usize>> for Binary<u8> {
  type Output = Vec<u8>;
  fn access(&self, index: ops::RangeTo<usize>) -> Vec<u8> {
    self.access(0..index.end)
  }
}

impl Access<ops::RangeFrom<usize>> for Binary<u8> {
  type Output = Vec<u8>;
  fn access(&self, index: ops::RangeFrom<usize>) -> Vec<u8> {
    vec![0u8]
  }
}

impl Access<ops::RangeFull> for Binary<u8> {
  type Output = Vec<u8>;
  fn access(&self, index: ops::RangeFull) -> Vec<u8> {
    self.decode().unwrap()
  }
}
*/
