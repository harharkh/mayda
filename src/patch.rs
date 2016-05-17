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
//! use pfor::utility::{Access, Encodable};
//! use pfor::binary::Binary;
//!
//! let input: Vec<u32> = vec![1, 4, 2, 8, 5, 7];
//! let mut bin = Binary::new();
//! bin.encode(&input).unwrap();
//!
//! let output = bin.decode().unwrap();
//! assert_eq!(input, output);
//!
//! let value = bin.access(4);
//! assert_eq!(value, 5);
//!
//! let range = bin.access(1..4);
//! assert_eq!(range, vec![4, 2, 8]); 
//! ```

use std::marker::PhantomData;
use std::ops;
use std::slice;

use pfor_codec;
use utility::{self, Bits, Encodable, Access};

const E_WIDTH_MASK: u32 = 0x0000003f;
const E_ENTRY_MASK: u32 = 0x00001fc0;
const X_WIDTH_MASK: u32 = 0x0007e000;
const X_ENTRY_MASK: u32 = 0x03f80000;
const X_FLAG: u32 = 0x04000000;
const M_WIDTH: u32 = 0x08000000;
const M_FLAG: u32 = 0x10000000;

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
  /// use std::mem;
  /// use pfor::binary::Binary;
  /// use pfor::utility::Encodable;
  ///
  /// let mut bin = Binary::new();
  ///
  /// let input: Vec<u32> = vec![1, 4, 2, 8, 5, 7];
  /// bin.encode(&input);
  ///
  /// let bytes = mem::size_of_val(&bin);
  /// assert_eq!(bytes, 16);
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
  /// let storage = bin.storage();
  /// assert_eq!(storage.len(), 3);
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
        let flag: u32 = match $ty::width() {
          8 => utility::U8_FLAG,
          16 => utility::U16_FLAG,
          32 => utility::U32_FLAG,
          64 => utility::U64_FLAG,
          _ => unreachable!()
        };

        // Allow arrays of 2^37 entries (128 GB of u8)
        let n_blks: usize = (input.len() - 1) >> 7;
        let n_lvls: usize = n_blks.bits();
        if n_lvls > 30 {
          return Err(super::Error::new("exceeded internal capacity"))
        }

        // Avoid memory initialization, bounds checking, etc.
        let mut i_ptr: *const $ty = input.as_ptr();

        let mut medians: Vec<$ty> = Vec::with_capacity(n_blks + 1);
        let mut scratch: Vec<$ty> = vec![0; 128];
        let mut bit_bins: Vec<usize> = vec![0, $ty::width() + 1];
        unsafe {
          for _ in 0..n_blks {
            scratch.copy_from_slice(slice::from_raw_parts(i_ptr, 128));
            let median: $ty = utility::select_m(&mut scratch, 64);
            medians.push(median);
            for a in scratch.iter() {
              (a - median).bits();
            }

            i_ptr = i_ptr.offset(128);
          }
        }
        i_ptr = input.as_ptr();


        //let mut e_width: Vec<u32> = Vec::with_capacity(n_blks + 1);
        //let mut x_width: Vec<u32> = Vec::with_capacity(n_blks + 1);
        //let mut words: Vec<u32> = Vec::with_capacity(n_blks + 1);

        /*

        let mut e_bits: [u32; 65];
        let mut blk_words: [u32; 65];

        e_bits = [0; 65];
        for a in 0..128 {
          e_bits[(*i_ptr.offset(a)).bits()] += 1;
        }
        blk_words = [0; 65];
        let mut e_num: u32 = e_bits[0];
        for a in 1...(wd_1 + 1) {
          e_num += e_bits[a];
          let x_num = 128 - e_num;
          let i_bit = (128 / x_num).bits();
          blk_words[a] = a * e_num + 

        }*/




        let mut blk_max: $ty;
        let mut i_left: usize = input.len() - (n_blks << 7);
        let mut widths_1: Vec<u64> = Vec::with_capacity(n_blks);

        let w_ptr: *mut u64 = widths_1.as_mut_ptr();
        unsafe {
          // Find widths of all blocks
          for a in 0..(n_blks as isize) {
            blk_max = 1;
            for b in 0..128 {
              blk_max |= *(i_ptr.offset(b));
            }
            // Widths offset by one to encode index header
            *w_ptr.offset(a) = blk_max.bits() as u64 - 1;
            i_ptr = i_ptr.offset(128);
          }
          widths_1.set_len(n_blks);

          // Width of final block
          blk_max = 1;
          for a in 0..(i_left as isize) {
            blk_max |= *(i_ptr.offset(a));
          }
        }
        let tail_wd: usize = blk_max.bits();
        i_ptr = input.as_ptr();

        // Construct index header
        let mut lvls: Vec<Vec<u64>> = Vec::with_capacity(n_lvls);
        unsafe {
          for a in 0..(n_lvls as isize) {
            let length: usize = ((n_blks - (1 << a)) >> (a + 1)) + 1;
            let mut lvl: Vec<u64> = Vec::with_capacity(length);
            for b in (0..(length as isize)).map(|x| x << (a + 1)) {
              let mut acc: u64 = 0;
              for c in 0..(1 << a) {
                acc += *w_ptr.offset(b + c);
              }
              lvl.push(acc);
            }
            lvls.push(lvl);
          }
        }
        
        // Lengths of index header and blocks
        let base_wd: usize = ($ty::width() - 1).bits();
        let w_words: usize = lvls.iter()
          .enumerate()
          .map(|(a, x)| utility::words_for_bits((base_wd + a) * x.len()))
          .sum::<usize>();
        let b_words: usize = 1 + 5 * n_blks
          + 4 * widths_1.iter().sum::<u64>() as usize
          + utility::words_for_bits(i_left * tail_wd);
        let s_len: usize = 1 + w_words + b_words;

        // Construct self.storage
        let mut storage: Vec<u32> = Vec::with_capacity(s_len);
        let mut s_ptr: *mut u32 = storage.as_mut_ptr();

        unsafe {
          // Binary header
          *s_ptr = (n_blks as u32) << 2 | flag;
          s_ptr = s_ptr.offset(1);

          // Index header
          let mut w_left: usize;
          for a in 0..n_lvls {
            let wd: usize = (base_wd + a) as usize;
            w_left = lvls[a].len();
            let mut l_ptr = lvls[a].as_ptr();

            // Encode any runs of 128 integers 
            for _ in 0..(w_left >> 7) {
              pfor_codec::ENCODE_SIMD_U64[wd - 1](l_ptr, s_ptr);
              l_ptr = l_ptr.offset(128);
              s_ptr = s_ptr.offset((4 * wd) as isize);
            }
            w_left &= 127;

            // Encode any runs of 32 integers
            for _ in 0..(w_left >> 5) {
              pfor_codec::ENCODE_U64[wd - 1][32 / $step - 1](l_ptr, s_ptr);
              l_ptr = l_ptr.offset(32);
              s_ptr = s_ptr.offset(wd as isize);
            }
            w_left &= 31;

            // Encode any runs of $step integers
            let mut s_bits: usize = 32;
            if w_left >= $step {
              let part = w_left - w_left % $step;
              pfor_codec::ENCODE_U64[wd - 1][part / $step - 1](l_ptr, s_ptr);
              l_ptr = l_ptr.offset(part as isize);
              s_ptr = s_ptr.offset(((part * wd) / 32) as isize);
              w_left -= part;
              s_bits -= (part * wd) & 31;
            }

            // If there are still entries...
            if w_left > 0 {
              let mut w_bits: usize;
              // If s_bits points to unitialized word...
              if s_bits == 32 {
                *s_ptr = 0;
              }

              // Encode any remaining integers one by one
              for b in 0..w_left {
                w_bits = wd;

                // Encode in the available space
                let lsft = 32 - s_bits;
                *s_ptr |= (*l_ptr as u32) << lsft;

                // While the available space is not enough...
                while s_bits < w_bits {
                  w_bits -= s_bits;
                  s_ptr = s_ptr.offset(1);
                  *s_ptr = (*l_ptr >> (wd - w_bits)) as u32;
                  s_bits = 32;
                }
                s_bits -= w_bits;

                if b < w_left - 1 {
                  l_ptr = l_ptr.offset(1);
                  if s_bits == 0 {
                    s_ptr = s_ptr.offset(1);
                    *s_ptr = 0;
                    s_bits = 32;
                  }
                }
              }
            }

            // If a word is partially consumed...
            if s_bits < 32 {
              s_ptr = s_ptr.offset(1);
            }
          }

          // Block length is known for all but the final block
          for wd_1 in widths_1.iter() {
            // Block header
            *s_ptr = 0x00001fc0 | *wd_1 as u32;
            s_ptr = s_ptr.offset(1);

            // Encode the block
            pfor_codec::$enc_simd[*wd_1 as usize](i_ptr, s_ptr);
            i_ptr = i_ptr.offset(128);
            s_ptr = s_ptr.offset((4 * (wd_1 + 1)) as isize);
          }

          // Block header
          *s_ptr = ((i_left - 1) as u32) << 6 | (tail_wd - 1) as u32;
          s_ptr = s_ptr.offset(1);

          // Encode any runs of 128 integers
          if i_left == 128 {
            pfor_codec::$enc_simd[tail_wd - 1](i_ptr, s_ptr);
          } else {
            // Encode any runs of 32 integers
            for _ in 0..(i_left >> 5) {
              pfor_codec::$enc[tail_wd - 1][32 / $step - 1](i_ptr, s_ptr);
              i_ptr = i_ptr.offset(32);
              s_ptr = s_ptr.offset(tail_wd as isize);
            }
            i_left &= 31;

            // Encode any runs of step integers
            let mut s_bits: usize = 32;
            if i_left >= $step {
              let part = i_left - i_left % $step;
              pfor_codec::$enc[tail_wd - 1][part / $step - 1](i_ptr, s_ptr);
              i_ptr = i_ptr.offset(part as isize);
              s_ptr = s_ptr.offset(((part * tail_wd) / 32) as isize);
              i_left -= part;
              s_bits -= (part * tail_wd) & 31;
            }

            // If there are still entries...
            if i_left > 0 {
              let mut i_bits: usize;
              // If s_bits points to unitialized word...
              if s_bits == 32 {
                *s_ptr = 0;
              }

              // Encode any remaining integers one by one
              for a in 0..i_left {
                i_bits = tail_wd;

                // Encode in the available space
                let lsft = 32 - s_bits;
                *s_ptr |= (*i_ptr as u32) << lsft;

                // While the available space is not enough...
                while s_bits < i_bits {
                  i_bits -= s_bits;
                  s_ptr = s_ptr.offset(1);
                  *s_ptr = (*i_ptr >> (tail_wd - i_bits)) as u32;
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
        }
        self.storage = storage.into_boxed_slice();
        Ok(())
      }

      fn decode(&self) -> Result<Vec<$ty>, super::Error> {
        // Nothing to do
        if self.storage.is_empty() { return Ok(Vec::new()) }

        // Read binary header
        let n_blks: usize = (self.storage[0] >> 2) as usize;
        let mut output: Vec<$ty> = Vec::with_capacity((n_blks + 1) << 7);

        // Length of index header
        let n_lvls: usize = n_blks.bits();
        let base_wd: usize  = ($ty::width() - 1).bits();
        let mut w_words: usize = 0;
        for a in 0..n_lvls {
          let len: usize = ((n_blks - (1 << a)) >> (a + 1)) + 1;
          w_words += utility::words_for_bits((base_wd + a) * len);
        }

        // Avoid memory initialization, bounds checking, etc.
        let mut s_ptr: *const u32 = self.storage.as_ptr();
        let mut o_ptr: *mut $ty = output.as_mut_ptr();
        unsafe {
          s_ptr = s_ptr.offset(1 + w_words as isize);

          // Block size is known for all but the final block
          for _ in 0..n_blks {
            // Find the width of the block
            let wd: usize = ((*s_ptr & E_WIDTH_MASK) + 1) as usize;
            s_ptr = s_ptr.offset(1);

            // Decode the block
            pfor_codec::$dec_simd[wd - 1](s_ptr, o_ptr);
            s_ptr = s_ptr.offset(4 * wd as isize);
            o_ptr = o_ptr.offset(128);
          }

          // Final block
          let tail_wd: usize = ((*s_ptr & E_WIDTH_MASK) + 1) as usize;
          let mut o_left: usize = (((*s_ptr & E_ENTRY_MASK) >> 6) + 1) as usize;
          let o_len: usize = (n_blks << 7) + o_left;
          s_ptr = s_ptr.offset(1);

          // Decode any runs of 128 integers
          if o_left == 128 {
            pfor_codec::$dec_simd[tail_wd - 1](s_ptr, o_ptr);
          } else {
            // Decode any runs of 32 integers
            for _ in 0..(o_left >> 5) {
              pfor_codec::$dec[tail_wd - 1][32 / $step - 1](s_ptr, o_ptr);
              s_ptr = s_ptr.offset(tail_wd as isize);
              o_ptr = o_ptr.offset(32);
            }
            o_left &= 31;

            // Decode any runs of step integers
            let mut s_bits: usize = 32;
            if o_left >= $step {
              let part = o_left - o_left % $step;
              pfor_codec::$dec[tail_wd - 1][part / $step - 1](s_ptr, o_ptr);
              s_ptr = s_ptr.offset(((part * tail_wd) / 32) as isize);
              o_ptr = o_ptr.offset(part as isize);
              o_left -= part;
              s_bits -= (part * tail_wd) & 31;
            }

            // If there are still entries...
            if o_left > 0 {
              let mut o_bits: usize;
              let mask: $ty = !0 >> ($ty::width() - tail_wd);

              // Decode any remaining integers one by one
              for _ in 0..(o_left - 1) {
                o_bits = tail_wd;

                // Decode anything in the available space
                let rsft = 32 - s_bits;
                *o_ptr = (*s_ptr >> rsft) as $ty;

                // While the available space is not enough...
                while o_bits > s_bits {
                  o_bits -= s_bits;
                  s_ptr = s_ptr.offset(1);
                  *o_ptr |= (*s_ptr as $ty) << (tail_wd - o_bits);
                  s_bits = 32;
                }
                s_bits -= o_bits;

                *o_ptr &= mask;
                o_ptr = o_ptr.offset(1);
                if s_bits == 0 {
                  s_ptr = s_ptr.offset(1);
                  s_bits = 32;
                }
              }
              // Final iteration moved out of for loop to avoid branching
              o_bits = tail_wd;

              // Decode anything in the available space
              let rsft = 32 - s_bits;
              *o_ptr = (*s_ptr >> rsft) as $ty;

              // While the available space is not enough...
              while o_bits > s_bits {
                o_bits -= s_bits;
                s_ptr = s_ptr.offset(1);
                *o_ptr |= (*s_ptr as $ty) << (tail_wd - o_bits);
                s_bits = 32;
              }

              *o_ptr &= mask;
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

macro_rules! access_impl {
  ($(($ty: ident: $step: expr, $dec: ident, $dec_simd: ident))*) => ($(
    impl Access<usize> for Binary<$ty> {
      type Output = $ty;
      fn access(&self, index: usize) -> $ty {
        if self.storage.is_empty() {
          panic!(format!("index is {} but length is 0", index))
        }

        let n_blks: usize = (self.storage[0] >> 2) as usize;
        let blk: usize = index >> 7;
        if blk > n_blks {
          let length_bnd: usize = (n_blks + 1) << 7;
          panic!(format!("index is {} but length < {}", index, length_bnd))
        }

        // Find the block containing the index
        let base_wd: usize = ($ty::width() - 1).bits();
        let mut lvl: usize = 0;
        let mut lvl_head: usize = 1;
        let mut wrd_to_blk: usize = 0;
        let mut s_ptr: *const u32;

        if blk > 0 {
          let mut w_idx: usize = blk;

          // Initial iteration moved out of loop to avoid branching
          let shift: usize = (w_idx.trailing_zeros() + 1) as usize;
          for _ in 1..shift {
            let wd: usize = base_wd + lvl;
            let len: usize = ((n_blks - (1 << lvl)) >> (lvl + 1)) + 1;
            lvl_head += utility::words_for_bits(wd * len);
            lvl += 1;
          }
          w_idx >>= shift;

          let wd: usize = base_wd + lvl;
          let len: usize = ((n_blks - (1 << lvl)) >> (lvl + 1)) + 1;
          let mut output: u64;
          unsafe {
            s_ptr = self.storage.as_ptr().offset(lvl_head as isize);
            if (w_idx & !127) + 128 <= len {
              // Width encoded using SIMD
              let l_bits: usize = (w_idx / 2) * wd;
              let w_bits: usize = 64 - (l_bits & 63);

              let mut w_ptr: *const u64 = s_ptr as *const u64;
              w_ptr = w_ptr.offset(((w_idx & 1) + (l_bits / 64) * 2) as isize);

              output = *w_ptr >> (64 - w_bits);
              if wd > w_bits {
                w_ptr = w_ptr.offset(2);
                output |= *w_ptr << w_bits;
              }
            } else {
              // Width encoded using u32
              let l_bits: usize = w_idx * wd;
              let mut s_bits: usize = 32 - (l_bits & 31);
              let mut o_bits: usize = wd;

              s_ptr = s_ptr.offset((l_bits / 32) as isize);

              output = (*s_ptr >> (32 - s_bits)) as u64;
              while o_bits > s_bits {
                o_bits -= s_bits;
                s_ptr = s_ptr.offset(1);
                output |= (*s_ptr as u64) << (wd - o_bits);
                s_bits = 32;
              }
            }
          }
          wrd_to_blk += (output & (!0 >> (64 - wd))) as usize;

          // Decode widths for all other levels
          for _ in 0..w_idx.count_ones() {
            let shift: usize = (w_idx.trailing_zeros() + 1) as usize;
            for _ in 0..shift {
              let wd: usize = base_wd + lvl;
              let len: usize = ((n_blks - (1 << lvl)) >> (lvl + 1)) + 1;
              lvl_head += utility::words_for_bits(wd * len);
              lvl += 1;
            }
            w_idx >>= shift;

            let wd: usize = base_wd + lvl;
            let len: usize = ((n_blks - (1 << lvl)) >> (lvl + 1)) + 1;
            unsafe {
              s_ptr = self.storage.as_ptr().offset(lvl_head as isize);
              if (w_idx & !127) + 128 <= len {
                // Width encoded using SIMD
                let l_bits: usize = (w_idx / 2) * wd;
                let w_bits: usize = 64 - (l_bits & 63);

                let mut w_ptr: *const u64 = s_ptr as *const u64;
                w_ptr = w_ptr.offset(((w_idx & 1) + (l_bits / 64) * 2) as isize);

                output = *w_ptr >> (64 - w_bits);
                if wd > w_bits {
                  w_ptr = w_ptr.offset(2);
                  output |= *w_ptr << w_bits;
                }
              } else {
                // Width encoded using u32
                let bits: usize = w_idx * wd;
                let mut s_bits: usize = 32 - (bits & 31);
                let mut o_bits: usize = wd;

                s_ptr = s_ptr.offset((bits / 32) as isize);

                output = (*s_ptr >> (32 - s_bits)) as u64;
                while o_bits > s_bits {
                  o_bits -= s_bits;
                  s_ptr = s_ptr.offset(1);
                  output |= (*s_ptr as u64) << (wd - o_bits);
                  s_bits = 32;
                }
              }
            }
            wrd_to_blk += (output & (!0 >> (64 - wd))) as usize;
          }
          wrd_to_blk = 4 * wrd_to_blk + 5 * blk;
        }

        // Include the header words
        wrd_to_blk += lvl_head;
        for a in lvl..n_blks.bits() {
          let wd: usize = base_wd + a;
          let len: usize = ((n_blks - (1 << a)) >> (a + 1)) + 1;
          wrd_to_blk += utility::words_for_bits(wd * len);
        }

        // Block found, decode the value
        unsafe {
          s_ptr = self.storage.as_ptr().offset(wrd_to_blk as isize);
          let wd: usize = ((*s_ptr & E_WIDTH_MASK) + 1) as usize;
          let o_left: usize = (((*s_ptr & E_ENTRY_MASK) >> 6) + 1) as usize;
          s_ptr = s_ptr.offset(1);

          let idx: usize = index & 127;
          if idx >= o_left {
            let len: usize = index - idx + o_left;
            panic!(format!("index is {} but length is {}", index, len))
          }

          let ty_wd: usize = $ty::width();
          let mut output: $ty;

          if o_left == 128 {
            // Value encoded using SIMD
            let lanes: usize = 128 / ty_wd;
            let l_bits: usize = (idx / lanes) * wd;
            let mut w_bits: usize = ty_wd - l_bits % ty_wd;
            let mut o_bits: usize = wd;

            let mut w_ptr: *const $ty = s_ptr as *const $ty;
            w_ptr = w_ptr.offset((idx % lanes + (l_bits / ty_wd) * lanes) as isize);

            output = *w_ptr >> (ty_wd - w_bits);
            while o_bits > w_bits {
              o_bits -= w_bits;
              w_ptr = w_ptr.offset(lanes as isize);
              output |= *w_ptr << (wd - o_bits);
              w_bits = ty_wd;
            }
          } else {
            // Value encoded using u32
            let l_bits: usize = idx * wd;
            let mut s_bits: usize = 32 - (l_bits & 31);
            let mut o_bits: usize = wd;

            s_ptr = s_ptr.offset((l_bits / 32) as isize);

            output = (*s_ptr >> (32 - s_bits)) as $ty;
            while o_bits > s_bits {
              o_bits -= s_bits;
              s_ptr = s_ptr.offset(1);
              output |= (*s_ptr as $ty) << (wd - o_bits);
              s_bits = 32;
            }
          }
          output & (!0 >> (ty_wd - wd))
        }
      }
    }

    impl Access<ops::Range<usize>> for Binary<$ty> {
      type Output = Vec<$ty>;
      fn access(&self, range: ops::Range<usize>) -> Vec<$ty> {
        if range.end < range.start {
          panic!(
            format!(
              "range start is {} but range end is {}", range.start, range.end
            )
          )
        }
        if self.storage.is_empty() {
          if range.start > 0 {
            panic!(format!("range start is {} but length is 0", range.start))
          }
          if range.end > 0 {
            panic!(format!("range end is {} but length is 0", range.end))
          }
        }

        let n_blks: usize = (self.storage[0] >> 2) as usize;
        let s_blk: usize = range.start >> 7;
        if s_blk > n_blks {
          let length_bnd: usize = (n_blks + 1) << 7;
          panic!(
            format!(
              "range start is {} but length < {}", range.start, length_bnd
            )
          )
        }
        let e_blk: usize = range.end >> 7;
        if e_blk > n_blks {
          let length_bnd: usize = (n_blks + 1) << 7;
          panic!(
            format!(
              "range end is {} but length < {}", range.end, length_bnd
            )
          )
        }

        // Find the block containing the range start
        let base_wd: usize = ($ty::width() - 1).bits();
        let mut lvl: usize = 0;
        let mut lvl_head: usize = 1;
        let mut wrd_to_blk: usize = 0;
        let mut s_ptr: *const u32;

        if s_blk > 0 {
          let mut w_idx: usize = s_blk;

          // Initial iteration moved out of loop to avoid branching
          let shift: usize = (w_idx.trailing_zeros() + 1) as usize;
          for _ in 1..shift {
            let wd: usize = base_wd + lvl;
            let len: usize = ((n_blks - (1 << lvl)) >> (lvl + 1)) + 1;
            lvl_head += utility::words_for_bits(wd * len);
            lvl += 1;
          }
          w_idx >>= shift;

          let wd: usize = base_wd + lvl;
          let len: usize = ((n_blks - (1 << lvl)) >> (lvl + 1)) + 1;
          let mut output: u64;
          unsafe {
            s_ptr = self.storage.as_ptr().offset(lvl_head as isize);
            if (w_idx & !127) + 128 <= len {
              // Width encoded using SIMD
              let l_bits: usize = (w_idx / 2) * wd;
              let w_bits: usize = 64 - (l_bits & 63);

              let mut w_ptr: *const u64 = s_ptr as *const u64;
              w_ptr = w_ptr.offset(((w_idx & 1) + (l_bits / 64) * 2) as isize);

              output = *w_ptr >> (64 - w_bits);
              if wd > w_bits {
                w_ptr = w_ptr.offset(2);
                output |= *w_ptr << w_bits;
              }
            } else {
              // Width encoded using u32
              let l_bits: usize = w_idx * wd;
              let mut s_bits: usize = 32 - (l_bits & 31);
              let mut o_bits: usize = wd;

              s_ptr = s_ptr.offset((l_bits / 32) as isize);

              output = (*s_ptr >> (32 - s_bits)) as u64;
              while o_bits > s_bits {
                o_bits -= s_bits;
                s_ptr = s_ptr.offset(1);
                output |= (*s_ptr as u64) << (wd - o_bits);
                s_bits = 32;
              }
            }
          }
          wrd_to_blk += (output & (!0 >> (64 - wd))) as usize;

          // Decode widths for all other levels
          for _ in 0..w_idx.count_ones() {
            let shift: usize = (w_idx.trailing_zeros() + 1) as usize;
            for _ in 0..shift {
              let wd: usize = base_wd + lvl;
              let len: usize = ((n_blks - (1 << lvl)) >> (lvl + 1)) + 1;
              lvl_head += utility::words_for_bits(wd * len);
              lvl += 1;
            }
            w_idx >>= shift;

            let wd: usize = base_wd + lvl;
            let len: usize = ((n_blks - (1 << lvl)) >> (lvl + 1)) + 1;
            unsafe {
              s_ptr = self.storage.as_ptr().offset(lvl_head as isize);
              if (w_idx & !127) + 128 <= len {
                // Width encoded using SIMD
                let l_bits: usize = (w_idx / 2) * wd;
                let w_bits: usize = 64 - (l_bits & 63);

                let mut w_ptr: *const u64 = s_ptr as *const u64;
                w_ptr = w_ptr.offset(((w_idx & 1) + (l_bits / 64) * 2) as isize);

                output = *w_ptr >> (64 - w_bits);
                if wd > w_bits {
                  w_ptr = w_ptr.offset(2);
                  output |= *w_ptr << w_bits;
                }
              } else {
                // Width encoded using u32
                let bits: usize = w_idx * wd;
                let mut s_bits: usize = 32 - (bits & 31);
                let mut o_bits: usize = wd;

                s_ptr = s_ptr.offset((bits / 32) as isize);

                output = (*s_ptr >> (32 - s_bits)) as u64;
                while o_bits > s_bits {
                  o_bits -= s_bits;
                  s_ptr = s_ptr.offset(1);
                  output |= (*s_ptr as u64) << (wd - o_bits);
                  s_bits = 32;
                }
              }
            }
            wrd_to_blk += (output & (!0 >> (64 - wd))) as usize;
          }
          wrd_to_blk = 4 * wrd_to_blk + 5 * s_blk;
        }

        // Include the header words
        wrd_to_blk += lvl_head;
        for a in lvl..n_blks.bits() {
          let wd: usize = base_wd + a;
          let len: usize = ((n_blks - (1 << a)) >> (a + 1)) + 1;
          wrd_to_blk += utility::words_for_bits(wd * len);
        }

        // Prepare return variable
        let mut output: Vec<$ty> = Vec::with_capacity((e_blk - s_blk + 1) << 7);
        let mut o_ptr: *mut $ty = output.as_mut_ptr();

        // Start block known, decode the range
        unsafe {
          s_ptr = self.storage.as_ptr().offset(wrd_to_blk as isize);

          // Block size is known for all but the final block
          for _ in 0..(e_blk - s_blk) {
            // Find the width of the block
            let wd: usize = ((*s_ptr & E_WIDTH_MASK) + 1) as usize;
            s_ptr = s_ptr.offset(1);

            // Decode the block
            pfor_codec::$dec_simd[wd - 1](s_ptr, o_ptr);
            s_ptr = s_ptr.offset(4 * wd as isize);
            o_ptr = o_ptr.offset(128);
          }

          // Final block
          let tail_wd: usize = ((*s_ptr & E_WIDTH_MASK) + 1) as usize;
          let mut o_left: usize = (((*s_ptr & E_ENTRY_MASK) >> 6) + 1) as usize;
          s_ptr = s_ptr.offset(1);

          // Checks a lower bound on the length
          let length_bnd: usize = (e_blk << 7) + o_left;
          if range.start > length_bnd {
            panic!(
              format!(
                "range start is {} but length is {}", range.start, length_bnd
              )
            )
          }
          if range.end > length_bnd {
            panic!(
              format!(
                "range end is {} but length is {}", range.end, length_bnd
              )
            )
          }
          if range.start == range.end {
            return Vec::new();
          }

          // Decode any runs of 128 integers
          if o_left == 128 {
            pfor_codec::$dec_simd[tail_wd - 1](s_ptr, o_ptr);
          } else {
            // Decode any runs of 32 integers
            for _ in 0..(o_left >> 5) {
              pfor_codec::$dec[tail_wd - 1][32 / $step - 1](s_ptr, o_ptr);
              s_ptr = s_ptr.offset(tail_wd as isize);
              o_ptr = o_ptr.offset(32);
            }
            o_left &= 31;

            // Decode any runs of step integers
            let mut s_bits: usize = 32;
            if o_left >= $step {
              let part = o_left - o_left % $step;
              pfor_codec::$dec[tail_wd - 1][part / $step - 1](s_ptr, o_ptr);
              s_ptr = s_ptr.offset(((part * tail_wd) / 32) as isize);
              o_ptr = o_ptr.offset(part as isize);
              o_left -= part;
              s_bits -= (part * tail_wd) & 31;
            }

            // If there are still entries...
            if o_left > 0 {
              let mut o_bits: usize;
              let mask: $ty = !0 >> ($ty::width() - tail_wd);

              // Decode any remaining integers one by one
              for _ in 0..(o_left - 1) {
                o_bits = tail_wd;

                // Decode anything in the available space
                let rsft = 32 - s_bits;
                *o_ptr = (*s_ptr >> rsft) as $ty;

                // While the available space is not enough...
                while o_bits > s_bits {
                  o_bits -= s_bits;
                  s_ptr = s_ptr.offset(1);
                  *o_ptr |= (*s_ptr as $ty) << (tail_wd - o_bits);
                  s_bits = 32;
                }
                s_bits -= o_bits;

                *o_ptr &= mask;
                o_ptr = o_ptr.offset(1);
                if s_bits == 0 {
                  s_ptr = s_ptr.offset(1);
                  s_bits = 32;
                }
              }
              // Final iteration moved out of for loop to avoid branching
              o_bits = tail_wd;

              // Decode anything in the available space
              let rsft = 32 - s_bits;
              *o_ptr = (*s_ptr >> rsft) as $ty;

              // While the available space is not enough...
              while o_bits > s_bits {
                o_bits -= s_bits;
                s_ptr = s_ptr.offset(1);
                *o_ptr |= (*s_ptr as $ty) << (tail_wd - o_bits);
                s_bits = 32;
              }

              *o_ptr &= mask;
            }
          }

          // Shift the entries into the desired range
          let src_sft: usize = range.start - (s_blk << 7);
          let mut o_src: *const $ty = output.as_ptr().offset(src_sft as isize);
          let mut o_snk: *mut $ty = output.as_mut_ptr();

          *o_snk = *o_src;
          for _ in range.start..(range.end - 1) {
            o_src = o_src.offset(1);
            o_snk = o_snk.offset(1);
            *o_snk = *o_src;
          }
          output.set_len(range.end - range.start);
        }
        output
      }
    }

    impl Access<ops::RangeTo<usize>> for Binary<$ty> {
      type Output = Vec<$ty>;
      fn access(&self, range: ops::RangeTo<usize>) -> Vec<$ty> {
        self.access(0..range.end)
      }
    }

    impl Access<ops::RangeFrom<usize>> for Binary<$ty> {
      type Output = Vec<$ty>;
      fn access(&self, range: ops::RangeFrom<usize>) -> Vec<$ty> {
        if self.storage.is_empty() {
          if range.start > 0 {
            panic!(format!("range start is {} but length is 0", range.start))
          }
        }

        let n_blks: usize = (self.storage[0] >> 2) as usize;
        let s_blk: usize = range.start >> 7;
        if s_blk > n_blks {
          let length_bnd: usize = (n_blks + 1) << 7;
          panic!(
            format!(
              "range start is {} but length < {}", range.start, length_bnd
            )
          )
        }

        // Find the block containing the range start
        let base_wd: usize = ($ty::width() - 1).bits();
        let mut lvl: usize = 0;
        let mut lvl_head: usize = 1;
        let mut wrd_to_blk: usize = 0;
        let mut s_ptr: *const u32;

        if s_blk > 0 {
          let mut w_idx: usize = s_blk;

          // Initial iteration moved out of loop to avoid branching
          let shift: usize = (w_idx.trailing_zeros() + 1) as usize;
          for _ in 1..shift {
            let wd: usize = base_wd + lvl;
            let len: usize = ((n_blks - (1 << lvl)) >> (lvl + 1)) + 1;
            lvl_head += utility::words_for_bits(wd * len);
            lvl += 1;
          }
          w_idx >>= shift;

          let wd: usize = base_wd + lvl;
          let len: usize = ((n_blks - (1 << lvl)) >> (lvl + 1)) + 1;
          let mut output: u64;
          unsafe {
            s_ptr = self.storage.as_ptr().offset(lvl_head as isize);
            if (w_idx & !127) + 128 <= len {
              // Width encoded using SIMD
              let l_bits: usize = (w_idx / 2) * wd;
              let w_bits: usize = 64 - (l_bits & 63);

              let mut w_ptr: *const u64 = s_ptr as *const u64;
              w_ptr = w_ptr.offset(((w_idx & 1) + (l_bits / 64) * 2) as isize);

              output = *w_ptr >> (64 - w_bits);
              if wd > w_bits {
                w_ptr = w_ptr.offset(2);
                output |= *w_ptr << w_bits;
              }
            } else {
              // Width encoded using u32
              let l_bits: usize = w_idx * wd;
              let mut s_bits: usize = 32 - (l_bits & 31);
              let mut o_bits: usize = wd;

              s_ptr = s_ptr.offset((l_bits / 32) as isize);

              output = (*s_ptr >> (32 - s_bits)) as u64;
              while o_bits > s_bits {
                o_bits -= s_bits;
                s_ptr = s_ptr.offset(1);
                output |= (*s_ptr as u64) << (wd - o_bits);
                s_bits = 32;
              }
            }
          }
          wrd_to_blk += (output & (!0 >> (64 - wd))) as usize;

          // Decode widths for all other levels
          for _ in 0..w_idx.count_ones() {
            let shift: usize = (w_idx.trailing_zeros() + 1) as usize;
            for _ in 0..shift {
              let wd: usize = base_wd + lvl;
              let len: usize = ((n_blks - (1 << lvl)) >> (lvl + 1)) + 1;
              lvl_head += utility::words_for_bits(wd * len);
              lvl += 1;
            }
            w_idx >>= shift;

            let wd: usize = base_wd + lvl;
            let len: usize = ((n_blks - (1 << lvl)) >> (lvl + 1)) + 1;
            unsafe {
              s_ptr = self.storage.as_ptr().offset(lvl_head as isize);
              if (w_idx & !127) + 128 <= len {
                // Width encoded using SIMD
                let l_bits: usize = (w_idx / 2) * wd;
                let w_bits: usize = 64 - (l_bits & 63);

                let mut w_ptr: *const u64 = s_ptr as *const u64;
                w_ptr = w_ptr.offset(((w_idx & 1) + (l_bits / 64) * 2) as isize);

                output = *w_ptr >> (64 - w_bits);
                if wd > w_bits {
                  w_ptr = w_ptr.offset(2);
                  output |= *w_ptr << w_bits;
                }
              } else {
                // Width encoded using u32
                let bits: usize = w_idx * wd;
                let mut s_bits: usize = 32 - (bits & 31);
                let mut o_bits: usize = wd;

                s_ptr = s_ptr.offset((bits / 32) as isize);

                output = (*s_ptr >> (32 - s_bits)) as u64;
                while o_bits > s_bits {
                  o_bits -= s_bits;
                  s_ptr = s_ptr.offset(1);
                  output |= (*s_ptr as u64) << (wd - o_bits);
                  s_bits = 32;
                }
              }
            }
            wrd_to_blk += (output & (!0 >> (64 - wd))) as usize;
          }
          wrd_to_blk = 4 * wrd_to_blk + 5 * s_blk;
        }

        // Include the header words
        wrd_to_blk += lvl_head;
        for a in lvl..n_blks.bits() {
          let wd: usize = base_wd + a;
          let len: usize = ((n_blks - (1 << a)) >> (a + 1)) + 1;
          wrd_to_blk += utility::words_for_bits(wd * len);
        }

        // Prepare return variable
        let mut output: Vec<$ty> = Vec::with_capacity((n_blks - s_blk + 1) << 7);
        let mut o_ptr: *mut $ty = output.as_mut_ptr();

        // Start block known, decode the range
        unsafe {
          s_ptr = self.storage.as_ptr().offset(wrd_to_blk as isize);

          // Block size is known for all but the final block
          for _ in 0..(n_blks - s_blk) {
            // Find the width of the block
            let wd: usize = ((*s_ptr & E_WIDTH_MASK) + 1) as usize;
            s_ptr = s_ptr.offset(1);

            // Decode the block
            pfor_codec::$dec_simd[wd - 1](s_ptr, o_ptr);
            s_ptr = s_ptr.offset(4 * wd as isize);
            o_ptr = o_ptr.offset(128);
          }

          // Final block
          let tail_wd: usize = ((*s_ptr & E_WIDTH_MASK) + 1) as usize;
          let mut o_left: usize = (((*s_ptr & E_ENTRY_MASK) >> 6) + 1) as usize;
          let o_len: usize = (n_blks << 7) + o_left;
          s_ptr = s_ptr.offset(1);

          // Checks a lower bound on the length
          if range.start > o_len {
            panic!(
              format!(
                "range start is {} but length is {}", range.start, o_len
              )
            )
          }
          if range.start == o_len {
            return Vec::new();
          }

          // Decode any runs of 128 integers
          if o_left == 128 {
            pfor_codec::$dec_simd[tail_wd - 1](s_ptr, o_ptr);
          } else {
            // Decode any runs of 32 integers
            for _ in 0..(o_left >> 5) {
              pfor_codec::$dec[tail_wd - 1][32 / $step - 1](s_ptr, o_ptr);
              s_ptr = s_ptr.offset(tail_wd as isize);
              o_ptr = o_ptr.offset(32);
            }
            o_left &= 31;

            // Decode any runs of step integers
            let mut s_bits: usize = 32;
            if o_left >= $step {
              let part = o_left - o_left % $step;
              pfor_codec::$dec[tail_wd - 1][part / $step - 1](s_ptr, o_ptr);
              s_ptr = s_ptr.offset(((part * tail_wd) / 32) as isize);
              o_ptr = o_ptr.offset(part as isize);
              o_left -= part;
              s_bits -= (part * tail_wd) & 31;
            }

            // If there are still entries...
            if o_left > 0 {
              let mut o_bits: usize;
              let mask: $ty = !0 >> ($ty::width() - tail_wd);

              // Decode any remaining integers one by one
              for _ in 0..(o_left - 1) {
                o_bits = tail_wd;

                // Decode anything in the available space
                let rsft = 32 - s_bits;
                *o_ptr = (*s_ptr >> rsft) as $ty;

                // While the available space is not enough...
                while o_bits > s_bits {
                  o_bits -= s_bits;
                  s_ptr = s_ptr.offset(1);
                  *o_ptr |= (*s_ptr as $ty) << (tail_wd - o_bits);
                  s_bits = 32;
                }
                s_bits -= o_bits;

                *o_ptr &= mask;
                o_ptr = o_ptr.offset(1);
                if s_bits == 0 {
                  s_ptr = s_ptr.offset(1);
                  s_bits = 32;
                }
              }
              // Final iteration moved out of for loop to avoid branching
              o_bits = tail_wd;

              // Decode anything in the available space
              let rsft = 32 - s_bits;
              *o_ptr = (*s_ptr >> rsft) as $ty;

              // While the available space is not enough...
              while o_bits > s_bits {
                o_bits -= s_bits;
                s_ptr = s_ptr.offset(1);
                *o_ptr |= (*s_ptr as $ty) << (tail_wd - o_bits);
                s_bits = 32;
              }

              *o_ptr &= mask;
            }
          }

          // Shift the entries into the desired range
          let src_sft: usize = range.start - (s_blk << 7);
          let mut o_src: *const $ty = output.as_ptr().offset(src_sft as isize);
          let mut o_snk: *mut $ty = output.as_mut_ptr();

          *o_snk = *o_src;
          for _ in 0..(o_len - range.start - 1) {
            o_src = o_src.offset(1);
            o_snk = o_snk.offset(1);
            *o_snk = *o_src;
          }
          output.set_len(o_len - range.start);
        }
        output
      }
    }

    impl Access<ops::RangeFull> for Binary<$ty> {
      type Output = Vec<$ty>;
      fn access(&self, _: ops::RangeFull) -> Vec<$ty> {
        self.decode().unwrap()
      }
    }
  )*)
}

access_impl!{
  (u8: 16, DECODE_U8, DECODE_SIMD_U8)
  (u16: 16, DECODE_U16, DECODE_SIMD_U16)
  (u32: 16, DECODE_U32, DECODE_SIMD_U32)
  (u64: 16, DECODE_U64, DECODE_SIMD_U64)
}
