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
//! bin.encode(&input);
//! let output = bin.decode().unwrap();
//!
//! assert_eq!(input, output);
//! ```

use pfor_codec;
use utility::{self, Bits, Encodable};

const ENTRY_MASK: u32 = 0x03f80000;
const BLOCKS_MASK: u32 = 0x3fffffff;

/// The type of a binary encoded integer array.
pub struct Binary {
  storage: Box<[u32]>
}

impl Binary {
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
  /// let output: Vec<u8> = bin.decode().unwrap();
  ///
  /// for pair in input.into_iter().zip(output.into_iter()) {
  ///   assert_eq!(pair.0, pair.1 as u32);
  /// }
  /// ```
  pub fn new() -> Self {
    Binary {
      storage: Box::new([0; 0])
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

  /// Returns the width of the minimum width unsigned integer required to
  /// decode.
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
  /// // The maximum encoded value is less than 256
  /// assert_eq!(bin.required_width(), 8);
  /// ```
  pub fn required_width(&self) -> usize {
    match self.storage[0] & utility::U64_FLAG {
      utility::U8_FLAG => 8,
      utility::U16_FLAG => 16,
      utility::U32_FLAG => 32,
      utility::U64_FLAG => 64,
      _ => panic!("Binary storage corrupted")
    }
  }
}

/// Default is only for unimplemented types, should not be reachable.
impl<U: Bits> Encodable<U> for Binary {
  default fn encode(&mut self, _: &[U]) {
    panic!("Encodable not implemented for this type")
  }
  default fn decode(&self) -> Result<Vec<U>, super::Error> {
    panic!("Encodable not implemented for this type")
  }
}

macro_rules! encodable_impl {
  // $t should be a type, but is an ident to satisfy compiler
  ($(($t: ident, $step: expr, $encode: ident, $decode: ident)),*) => ($(
    impl Encodable<$t> for Binary {
      fn encode(&mut self, input: &[$t]) {
        // Nothing to do
        if input.is_empty() { return }
        
        // Allow arrays of 2^7 * (2^30 - 1) entries (127 GB)
        let blocks = (input.len() + 127) / 128;
        assert!((blocks - 1).bits() < 31);

        // One word for header, five words per block
        let mut storage = Vec::with_capacity(
          if blocks == 1 { 3 } else { 1 + 5 * blocks }
        );

        // Pointers avoid memory initialization, bounds checking, slice
        // construction, etc. Use offset instead of changing s_ptr, storage can
        // be reallocated
        let mut block_max: $t;
        let mut overall_max: $t = 1;
        let mut i_ptr = input.as_ptr();
        let mut s_ptr;
        let mut s_len: isize = 1;
        unsafe {
          // Block size is known for all but the final block
          for _ in 0..(blocks - 1) {
            // Find the width of the block
            block_max = 1;
            for a in 0..128 {
              block_max |= *(i_ptr.offset(a));
            }
            overall_max |= block_max;
            let width = block_max.bits() as usize;

            // Can reallocate, s_ptr should be renewed
            storage.reserve(s_len as usize + 1 + 4 * width);
            s_ptr = storage.as_mut_ptr().offset(s_len);
            s_len += 1 + 4 * width as isize;

            // Block header
            *s_ptr = 
              ((width - 1) as u32 ) << 26 |
              0x03f80000;
            s_ptr = s_ptr.offset(1);

            // Encode the block
            for _ in 0..4 {
              pfor_codec::$encode[width - 1][32 / $step - 1](i_ptr, s_ptr);
              i_ptr = i_ptr.offset(32);
              s_ptr = s_ptr.offset(width as isize);
            }
          }

          // Final block, number of entries is unknown in advance
          let mut entries = input.len() - (blocks - 1) * 128;

          // Find the width of the block
          block_max = 1;
          for a in 0..(entries as isize) {
            block_max |= *(i_ptr.offset(a));
          }
          overall_max |= block_max;
          let width = block_max.bits() as usize;

          // Can reallocate, s_ptr should be renewed
          let words = utility::words_for_bits(entries * width);
          let s_end = s_len as usize + 1 + words;
          storage.reserve(s_end);
          s_ptr = storage.as_mut_ptr().offset(s_len);

          // Block header
          *s_ptr = 
            ((width - 1) as u32) << 26 |
            ((entries - 1) as u32) << 19;
          s_ptr = s_ptr.offset(1);

          // Encode any runs of 32 integers
          while entries > 31 {
            pfor_codec::$encode[width - 1][32 / $step - 1](i_ptr, s_ptr);
            i_ptr = i_ptr.offset(32);
            s_ptr = s_ptr.offset(width as isize);
            entries -= 32;
          }

          // If there are still entries...
          if entries > 0 {
            let mut i_bits: usize;
            let mut s_bits: usize = 32;
            *s_ptr = 0;
            // Encode any runs of step integers
            if entries > $step {
              let part = entries - entries % $step;

              pfor_codec::$encode[width - 1][part / $step - 1](i_ptr, s_ptr);
              i_ptr = i_ptr.offset(part as isize);
              s_ptr = s_ptr.offset(((part * width) / 32) as isize);
              entries -= part;

              s_bits -= (part * width) % 32;
              // Finished a word and moved s_ptr to uninitialized word
              if s_bits == 32 { *s_ptr = 0; }
            }
            // Encode any remaining integers one by one
            for _ in 0..entries {
              i_bits = width;
              // While the integer requires more bits than the current word...
              while i_bits > s_bits {
                let rsft = i_bits - s_bits;
                *s_ptr |= (*i_ptr >> rsft) as u32;

                i_bits -= s_bits;
                s_bits = 32;
                s_ptr = s_ptr.offset(1);
                *s_ptr = 0;
              }

              // Encode any remaining bits
              let lsft = s_bits - i_bits;
              *s_ptr |= (*i_ptr as u32) << lsft;

              s_bits -= i_bits;
              if s_bits == 0 {
                s_bits = 32;
                s_ptr = s_ptr.offset(1);
                *s_ptr = 0;
              }
              i_ptr = i_ptr.offset(1);
            }
          }

          // Binary header
          let flag = match overall_max.bits() {
            1...8   => utility::U8_FLAG,
            9...16  => utility::U16_FLAG,
            17...32 => utility::U32_FLAG,
            33...64 => utility::U64_FLAG,
            _ => unreachable!()
          };
          *storage.as_mut_ptr() =
            flag |
            (blocks - 1) as u32;

          // Set the length of storage AFTER everything is initialized
          storage.set_len(s_end);
        }
        self.storage = storage.into_boxed_slice();
      }

      fn decode(&self) -> Result<Vec<$t>, super::Error> {
        // Nothing to do
        if self.storage.is_empty() { return Ok(Vec::new()) }

        // Check minimum number of bits required to decode
        if $t::width() < self.required_width() {
          return Err(super::Error::new(
            &format!(
              "decoding as {}, but width of {} or more is required",
              $t::name(),
              self.required_width()
            )
          ))
        }

        // Prepare output
        let blocks = ((self.storage[0] & BLOCKS_MASK) + 1) as usize;
        let mut output: Vec<$t> = Vec::with_capacity(blocks * 128);
        
        // Avoids memory initialization, bounds checking, slice construction
        // etc.
        let mut s_ptr = self.storage.as_ptr();
        let mut o_ptr = output.as_mut_ptr();
        unsafe {
          s_ptr = s_ptr.offset(1);

          // Block size is known for all but the final block
          for _ in 0..(blocks - 1) {
            // Find the width of the block
            let width = ((*s_ptr >> 26) + 1) as usize;
            s_ptr = s_ptr.offset(1);

            // Decode the block
            for _ in 0..4 {
              pfor_codec::$decode[width - 1][32 / $step - 1](s_ptr, o_ptr);
              s_ptr = s_ptr.offset(width as isize);
              o_ptr = o_ptr.offset(32);
            }
          }

          // Final block, number of entries is unknown in advance
          let width = ((*s_ptr >> 26) + 1) as usize;
          let mut entries = (((*s_ptr & ENTRY_MASK) >> 19) + 1) as usize;
          let o_end = (blocks - 1) * 128 + entries;
          s_ptr = s_ptr.offset(1);

          // Decode any runs of 32 integers
          while entries > 31 {
            pfor_codec::$decode[width - 1][32 / $step - 1](s_ptr, o_ptr);
            s_ptr = s_ptr.offset(width as isize);
            o_ptr = o_ptr.offset(32);
            entries -= 32;
          }

          // If there are still entries...
          if entries > 0 {
            let mut s_bits: usize = 32;
            let mut o_bits: usize;
            if entries > $step {
              let part = entries - entries % $step;

              pfor_codec::$decode[width - 1][part / $step - 1](s_ptr, o_ptr);
              s_ptr = s_ptr.offset(((part * width) / 32) as isize);
              o_ptr = o_ptr.offset(part as isize);
              entries -= part;

              s_bits -= (part * width) % 32;
            }
            // Decode any remaining integers one by one
            for _ in 0..entries {
              *o_ptr = 0;
              o_bits = width;
              // While the integer requires more bits than the current word...
              while o_bits > s_bits {
                let mask = !0u32 >> (32 - s_bits);
                let lsft = o_bits - s_bits;
                *o_ptr |= ((*s_ptr & mask) as $t) << lsft;

                o_bits -= s_bits;
                s_bits = 32;
                s_ptr = s_ptr.offset(1);
              }

              // Decode any bits that remain
              let mask = !0u32 >> (32 - s_bits);
              let rsft = s_bits - o_bits;
              *o_ptr |= ((*s_ptr & mask) >> rsft) as $t;

              s_bits -= o_bits;
              if s_bits == 0 {
                s_bits = 32;
                s_ptr = s_ptr.offset(1);
              }
              o_ptr = o_ptr.offset(1);
            }
          }

          // Set the length of output AFTER everything is initialized
          output.set_len(o_end);
        }
        Ok(output)
      }
    }
  )*)
}

encodable_impl!{
  (u8, 8, ENCODE_U8_ARRAY,  DECODE_U8_ARRAY),
  (u16, 8, ENCODE_U16_ARRAY, DECODE_U16_ARRAY),
  (u32, 8, ENCODE_U32_ARRAY, DECODE_U32_ARRAY),
  (u64, 8, ENCODE_U64_ARRAY, DECODE_U64_ARRAY)
}
