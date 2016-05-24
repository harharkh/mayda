// Copyright 2016 Jeremy Mason
//
// Licensed under the MIT license <LICENSE or
// http://opensource.org/licenses/MIT>. This file may not be copied, modified,
// or distributed except according to those terms.

//! Patched encoding of integer arrays. Designed for moderate compression,
//! random access, and efficient decoding.
//!
//! # Performance
//!
//! The compression of a block of 128 values decays with the logarithm of the
//! maximum absolute value in the block. Ideally, the probability distributions
//! of the values are uniform on intervals bounded by zero for unsigned
//! integers, or on intervals centered on zero for signed integers.
//! 
//! Random access via the `Access` trait is an `O(log(idx))` operation, where
//! `idx` is the value of the index (not the length of the array). The memory
//! overhead of this is less than a tenth of a bit per encoded integer.
//!
//! Encoding and decoding of unsigned integers and decoding of signed integers
//! is done in place. Encoding of signed integers uses a temporary copy of the
//! input slice, increasing the required memory.
//!
//! Encoding and decoding of signed integers is generally half as fast as for
//! unsigned integers.
//!
//! # Examples
//!
//! ```
//! use pfor::utility::{Access, Encodable};
//! use pfor::patched::Patched;
//!
//! let input: Vec<u32> = vec![1, 4, 2, 8, 5, 7];
//! let mut bin = Patched::new();
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
use std::mem;
use std::ops;

use pfor_codec;
use utility::{self, Bits, Encodable, Access};

const E_WIDTH: u32 = 0x0000003f;
const E_COUNT: u32 = 0x00001fc0;
const X_WIDTH: u32 = 0x0007e000;
const X_COUNT: u32 = 0x03f80000;
const I_WIDTH: u32 = 0x1c000000;
const S_WIDTH: u32 = 0x20000000;

/// The type of a patched encoded integer array.
pub struct Patched<B> {
  storage: Box<[u32]>,
  phantom: PhantomData<B>
}

impl<B: Bits> Patched<B> {
  /// Creates an empty Patched.
  ///
  /// # Examples
  /// ```
  /// use std::mem;
  /// use pfor::patched::Patched;
  /// use pfor::utility::Encodable;
  ///
  /// let mut bin = Patched::new();
  ///
  /// let input: Vec<u32> = vec![1, 4, 2, 8, 5, 7];
  /// bin.encode(&input);
  ///
  /// let bytes = mem::size_of_val(&bin);
  /// assert_eq!(bytes, 16);
  /// ```
  pub fn new() -> Self {
    Patched {
      storage: Box::new([0; 0]),
      phantom: PhantomData
    }
  }

  /// Exposes the word storage of the Patched.
  ///
  /// # Examples
  /// ```
  /// use pfor::patched::Patched;
  /// use pfor::utility::Encodable;
  ///
  /// let mut bin = Patched::new();
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

  /// Exposes the word storage of the Patched. Probably unsafe.
  pub unsafe fn mut_storage(&mut self) -> &mut Box<[u32]> {
    &mut self.storage
  }

  /// Returns the width of the encoded integer type.
  ///
  /// # Examples
  /// ```
  /// use pfor::patched::Patched;
  /// use pfor::utility::Encodable;
  ///
  /// let mut bin = Patched::new();
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

/// The private interface of an Encodable type. The purpose of this trait is
/// to reduce code duplication. The signature of _decode_final is due to a bug
/// in the parser.
trait EncodablePrivate<B: Bits> {
  unsafe fn _encode(&[B]) -> Result<Vec<u32>, super::Error>;
  unsafe fn _decode(&[u32]) -> Result<Vec<B>, super::Error>;
  unsafe fn _decode_final(_: *const u32, _: *mut B);
}

/// Default is only for unimplemented types, should not be reachable.
impl<B> EncodablePrivate<B> for Patched<B> where B: Bits {
  default unsafe fn _encode(_: &[B]) -> Result<Vec<u32>, super::Error> {
    Err(super::Error::new("Encodable not implemented for this type"))
  }

  default unsafe fn _decode(_: &[u32]) -> Result<Vec<B>, super::Error> {
    Err(super::Error::new("Encodable not implemented for this type"))
  }

  default unsafe fn _decode_final(_: *const u32, _: *mut B) {
    panic!("Encodable not implemented for this type");
  }
}

impl<B> Encodable<B> for Patched<B> where B: Bits {
  fn encode(&mut self, input: &[B]) -> Result<(), super::Error> {
    let storage: Vec<u32> = unsafe {
      try!(Patched::<B>::_encode(input))
    };
    self.storage = storage.into_boxed_slice();
    Ok(())
  }

  fn decode(&self) -> Result<Vec<B>, super::Error> {
    unsafe {
      Patched::<B>::_decode(&*self.storage)
    }
  }
}

macro_rules! encodable_unsigned {
  ($(($ty: ident: $step: expr,
      $enc: ident, $dec: ident,
      $enc_simd: ident, $dec_simd: ident,
      $enc_zz: ident, $dec_zz: ident))*) => ($(
    impl EncodablePrivate<$ty> for Patched<$ty> {
      unsafe fn _encode(input: &[$ty]) -> Result<Vec<u32>, super::Error> {
        // Nothing to do
        if input.is_empty() { return Ok(Vec::new()) }
        
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

        let mut i_left: usize = input.len() - (n_blks << 7);
        let mut scratch: Vec<$ty> = input.to_vec();

        let mut shifts: Vec<$ty> = Vec::with_capacity(n_blks);
        let mut shift_ptr: *mut $ty = shifts.as_mut_ptr();
        for a in 0..n_blks {
          let slice: &myt [$ty] = &mut scratch[(a << 7)..((a + 1) << 7)];
          *shift_ptr = utility::select_m(slice, 63);
          shift_ptr = shift_ptr.offset(1);
        }
        shifts.set_len(n_blks);
        let mut shift_ptr: *const $ty = shifts.as_ptr();

        let slice: &mut [$ty] = &mut scratch[(n_blks << 7)..];
        let tail_shift: $ty = utility::select_m(slice, i_left >> 1);

        scratch.copy_from_slice(input);
        let mut scratch_ptr: *mut $ty = scratch.as_mut_ptr();
        for _ in 0..n_blks {
          pfor_codec::$enc_zz(scratch_ptr, 128, *shift_ptr);
          scratch_ptr = scratch_ptr.offset(128);
          shift_ptr = shift_ptr.offset(1);
        }
        pfor_codec::$enc_zz(scratch_ptr, i_left, tail_shift);
        let mut scratch_ptr: *const $ty = scratch.as_ptr();

        let mut widths: Vec<usize> = Vec::with_capacity(n_blks);
        let mut width_ptr: *mut usize = widths.as_mut_ptr();
        let mut words_1: Vec<u64> = Vec::with_capacity(n_blks);
        let mut word_1_ptr: *mut u64 = words_1.as_mut_ptr();
        for _ in 0..n_blks {
          let mut bit_dist: Vec<usize> = vec![0; $ty::width()];
          for a in 0..128 {
            bit_dist[(*scratch_ptr.offset(a)).bits()] += 1;
          }
          scratch_ptr = scratch_ptr.offset(128);
          let max_wd: usize = bit_dist.iter().rposition(|x| x != 0);

          let mut sum: usize = bit_dist[0];
          let mut words_for_wd: Vec<usize> = Vec::with_capacity(max_wd);
          let mut wfw_ptr: *mut usize = words_for_wd.as_mut_ptr();
          for wd in 1...max_n {
            sum += bit_dist[wd];
            let x_num = 128 - sum;
            *wfw_ptr = 4 * wd
              + utility::words_for_bits(sum.bits() * x_num)
              + utility::words_for_bits((max_wd - wd) * x_num);
          }
          words_for_wd.set_len(max_wd);
          let (wd_1, wrds_1) = words_for_wd.iter()
            .enumerate()
            .fold((0, usize::MAX) |(a, b), &(c, d)|
              if d <= b { (c, d) } else { (a, b) }
            );
          *width_ptr = wd_1 + 1;
          *word_1_ptr = wrds_1;
        }
        widths.set_len(n_blks);
        words_1.set_len(n_blks);

        let mut bit_dist: Vec<usize> = vec![0; $ty::width()];
        for a in 0..i_left {
          bit_dist[(*scratch_ptr.offset(a)).bits()] += 1;
        }
        scratch_ptr = scratch.as_ptr();
        let max_wd: usize = bit_dist.iter().rposition(|x| x != 0);

        let mut sum: usize = bit_dist[0];
        let mut words_for_wd: Vec<usize> = Vec::with_capacity(max_wd);
        let mut wfw_ptr: *mut usize = words_for_wd.as_mut_ptr();
        for wd in 1...max_n {
          sum += bit_dist[wd];
          let x_num = i_left - sum;
          *wfw_ptr = utility::words_for_bits(wd * i_left)
            + utility::words_for_bits(sum.bits() * x_num)
            + utility::words_for_bits((max_wd - wd) * x_num);
        }
        words_for_wd.set_len(max_wd);
        let (wd_1, words_1) = words_for_wd.iter()
          .enumerate()
          .fold((0, usize::MAX) |(a, b), &(c, d)|
            if d <= b { (c, d) } else { (a, b) }
          );
        let tail_wd: usize = wd_1 + 1;
        let tail_words: usize = words_1 + 1;

        // Construct index header
        let w_ptr: *mut u64 = words_1.as_ptr();
        let mut lvls: Vec<Vec<u64>> = Vec::with_capacity(n_lvls);
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
        
        // Lengths of index header and blocks
        let base_wd: usize = ($ty::width() + 2).bits();
        let w_words: usize = lvls.iter()
          .enumerate()
          .map(|(a, x)| utility::words_for_bits((base_wd + a) * x.len()))
          .sum::<usize>();
        let b_words: usize = 2 * n_blks +
          + words_1.iter().sum::<u64>() as usize + 1 + tail_words;
        let s_len: usize = 1 + w_words + b_words;

        // Construct self.storage
        let mut storage: Vec<u32> = Vec::with_capacity(s_len);
        let mut s_ptr: *mut u32 = storage.as_mut_ptr();

        // Patched header
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

        Ok(storage)
      }

      unsafe fn _decode(storage: &[u32]) -> Result<Vec<$ty>, super::Error> {
        // Nothing to do
        if storage.is_empty() { return Ok(Vec::new()) }

        // Read patched header
        let n_blks: usize = (storage[0] >> 2) as usize;
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
        let mut s_ptr: *const u32 = storage.as_ptr();
        let mut o_ptr: *mut $ty = output.as_mut_ptr();
        s_ptr = s_ptr.offset(1 + w_words as isize);

        // Block size is known for all but the final block
        for _ in 0..n_blks {
          // Find the width of the block
          let wd: usize = ((*s_ptr & WIDTH_MASK) + 1) as usize;
          s_ptr = s_ptr.offset(1);

          // Decode the block
          pfor_codec::$dec_simd[wd - 1](s_ptr, o_ptr);
          s_ptr = s_ptr.offset(4 * wd as isize);
          o_ptr = o_ptr.offset(128);
        }

        // Final block
        let o_left: usize = (((*s_ptr & ENTRIES_MASK) >> 6) + 1) as usize;
        let o_len: usize = (n_blks << 7) + o_left;
        Patched::<$ty>::_decode_final(s_ptr, o_ptr);

        // Set the length of output AFTER everything is initialized
        output.set_len(o_len);

        Ok(output)
      }

      unsafe fn _decode_final(s_ptr: *const u32, o_ptr: *mut $ty) {
        let mut s_ptr = s_ptr;
        let mut o_ptr = o_ptr;

        let wd: usize = ((*s_ptr & WIDTH_MASK) + 1) as usize;
        let mut left: usize = (((*s_ptr & ENTRIES_MASK) >> 6) + 1) as usize;
        s_ptr = s_ptr.offset(1);

        // Decode any runs of 128 integers
        if left == 128 {
          pfor_codec::$dec_simd[wd - 1](s_ptr, o_ptr);
        } else {
          // Decode any runs of 32 integers
          for _ in 0..(left >> 5) {
            pfor_codec::$dec[wd - 1][32 / $step - 1](s_ptr, o_ptr);
            s_ptr = s_ptr.offset(wd as isize);
            o_ptr = o_ptr.offset(32);
          }
          left &= 31;

          // Decode any runs of step integers
          let mut s_bits: usize = 32;
          if left >= $step {
            let part = left - left % $step;
            pfor_codec::$dec[wd - 1][part / $step - 1](s_ptr, o_ptr);
            s_ptr = s_ptr.offset(((part * wd) / 32) as isize);
            o_ptr = o_ptr.offset(part as isize);
            left -= part;
            s_bits -= (part * wd) & 31;
          }

          // If there are still entries...
          if left > 0 {
            let mut o_bits: usize;
            let mask: $ty = !0 >> ($ty::width() - wd);

            // Decode any remaining integers one by one
            for _ in 0..(left - 1) {
              o_bits = wd;

              // Decode anything in the available space
              let rsft = 32 - s_bits;
              *o_ptr = (*s_ptr >> rsft) as $ty;

              // While the available space is not enough...
              while o_bits > s_bits {
                o_bits -= s_bits;
                s_ptr = s_ptr.offset(1);
                *o_ptr |= (*s_ptr as $ty) << (wd - o_bits);
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
            // Final iteration moved out of for loop to avoid branch
            o_bits = wd;

            // Decode anything in the available space
            let rsft = 32 - s_bits;
            *o_ptr = (*s_ptr >> rsft) as $ty;

            // While the available space is not enough...
            while o_bits > s_bits {
              o_bits -= s_bits;
              s_ptr = s_ptr.offset(1);
              *o_ptr |= (*s_ptr as $ty) << (wd - o_bits);
              s_bits = 32;
            }

            *o_ptr &= mask;
          }
        }
      }
    }
  )*)
}

encodable_unsigned!{
  (u8: 16,
   ENCODE_U8, DECODE_U8,
   ENCODE_SIMD_U8, DECODE_SIMD_U8,
   encode_zz_u8, decode_zz_u8)
  (u16: 16,
   ENCODE_U16, DECODE_U16,
   ENCODE_SIMD_U16, DECODE_SIMD_U16
   encode_zz_u16, decode_zz_u16)
  (u32: 16,
   ENCODE_U32, DECODE_U32,
   ENCODE_SIMD_U32, DECODE_SIMD_U32
   encode_zz_u32, decode_zz_u32)
  (u64: 16,
   ENCODE_U64, DECODE_U64,
   ENCODE_SIMD_U64, DECODE_SIMD_U64
   encode_zz_u64, decode_zz_u64)
}

macro_rules! encodable_signed {
  ($(($it: ident, $ut: ident: $enc_zz: ident, $dec_zz: ident))*) => ($(
    impl EncodablePrivate<$it> for Patched<$it> {
      unsafe fn _encode(input: &[$it]) -> Result<Vec<u32>, super::Error> {
        let mut scratch: Vec<$ut> = mem::transmute(input.to_vec());
        let ptr: *mut $ut = scratch.as_mut_ptr();
        let len: usize = scratch.len();
        pfor_codec::$enc_zz(ptr, len);
        Patched::<$ut>::_encode(&scratch)
      }

      unsafe fn _decode(storage: &[u32]) -> Result<Vec<$it>, super::Error> {
        let mut scratch: Vec<$ut> = try!(Patched::<$ut>::_decode(storage));
        let ptr: *mut $ut = scratch.as_mut_ptr();
        let len: usize = scratch.len();
        pfor_codec::$dec_zz(ptr, len);
        Ok(mem::transmute(scratch))
      }

      unsafe fn _decode_final(s_ptr: *const u32, o_ptr: *mut $it) {
        Patched::<$ut>::_decode_final(s_ptr, o_ptr as *mut $ut)
      }
    }
  )*)
}

encodable_signed!{
  (i8, u8: encode_zz_u8, decode_zz_u8)
  (i16, u16: encode_zz_u16, decode_zz_u16)
  (i32, u32: encode_zz_u32, decode_zz_u32)
  (i64, u64: encode_zz_u64, decode_zz_u64)
}

/// The private interface of an Access type. The purpose of this trait is to
/// reduce code duplication.
trait AccessPrivate<Idx> {
  type Output;
  unsafe fn _access(&[u32], Idx) -> Self::Output;
}

macro_rules! access_default {
  ($(($idx: ty, $output: ty))*) => ($(
    impl<B> AccessPrivate<$idx> for Patched<B> where B: Bits {
      type Output = $output;
      default unsafe fn _access(_: &[u32], _: $idx) -> $output {
        panic!("Access not implemented for this type");
      }
    }
  )*)
}

access_default!{
  (usize, B)
  (ops::Range<usize>, Vec<B>)
  (ops::RangeFrom<usize>, Vec<B>)
}

macro_rules! access {
  ($(($idx: ty, $output: ty))*) => ($(
    impl<B> Access<$idx> for Patched<B> where B: Bits {
      type Output = $output;
      fn access(&self, index: $idx) -> $output {
        unsafe {
          Patched::<B>::_access(&*self.storage, index)
        }
      }
    }
  )*)
}

access!{
  (usize, B)
  (ops::Range<usize>, Vec<B>)
  (ops::RangeFrom<usize>, Vec<B>)
}

impl<B> Access<ops::RangeTo<usize>> for Patched<B> where B: Bits {
  type Output = Vec<B>;
  fn access(&self, range: ops::RangeTo<usize>) -> Vec<B> {
    self.access(0..range.end)
  }
}

impl<B> Access<ops::RangeFull> for Patched<B> where B: Bits {
  type Output = Vec<B>;
  fn access(&self, _: ops::RangeFull) -> Vec<B> {
    self.decode().unwrap()
  }
}

/// Calculates the offset in words to the start of the block. Not intended to
///
/// be used outside of the implementation of Access.
fn words_to_block(n_blks: usize, blk: usize, ty_wd: usize, s_head: *const u32) -> usize {
  // Find the block containing the index
  let base_wd: usize = (ty_wd - 1).bits();
  let mut lvl: usize = 0;
  let mut lvl_head: usize = 1;
  let mut wrd_to_blk: usize = 0;
  let mut s_ptr: *const u32;

  if blk > 0 {
    let mut w_idx: usize = blk;
    let mut output: u64;

    // Initial iteration moved out of loop to avoid branch
    // REMOVING THIS INCREASES INDEXING TIME BY AT LEAST 15 PERCENT
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
    unsafe {
      s_ptr = s_head.offset(lvl_head as isize);
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
        s_ptr = s_head.offset(lvl_head as isize);
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

  wrd_to_blk
}

macro_rules! access_unsigned {
  ($(($ty: ident: $step: expr, $dec: ident, $dec_simd: ident))*) => ($(
    impl AccessPrivate<usize> for Patched<$ty> {
      unsafe fn _access(storage: &[u32], index: usize) -> $ty {
        if storage.is_empty() {
          panic!(format!("index is {} but length is 0", index))
        }

        let n_blks: usize = (storage[0] >> 2) as usize;
        let blk: usize = index >> 7;
        if blk > n_blks {
          let len_bnd: usize = (n_blks + 1) << 7;
          panic!(format!("index is {} but length < {}", index, len_bnd))
        }

        // Find the block containing the range start
        let ty_wd: usize = $ty::width();
        let mut s_ptr: *const u32 = storage.as_ptr();
        let wrd_to_blk: usize = words_to_block(n_blks, blk, ty_wd, s_ptr);

        // Block found, decode the value
        s_ptr = s_ptr.offset(wrd_to_blk as isize);
        let wd: usize = ((*s_ptr & WIDTH_MASK) + 1) as usize;
        let left: usize = (((*s_ptr & ENTRIES_MASK) >> 6) + 1) as usize;
        s_ptr = s_ptr.offset(1);

        let idx: usize = index & 127;
        if idx >= left {
          let len: usize = index - idx + left;
          panic!(format!("index is {} but length is {}", index, len))
        }

        let mut output: $ty;
        if left == 128 {
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

    impl AccessPrivate<ops::Range<usize>> for Patched<$ty> {
      unsafe fn _access(storage: &[u32], range: ops::Range<usize>) -> Vec<$ty> {
        if range.end < range.start {
          panic!(format!("range start is {} but range end is {}", range.start, range.end))
        }
        if storage.is_empty() {
          if range.start > 0 {
            panic!(format!("range start is {} but length is 0", range.start))
          }
          if range.end > 0 {
            panic!(format!("range end is {} but length is 0", range.end))
          }
        }

        let n_blks: usize = (storage[0] >> 2) as usize;
        let s_blk: usize = range.start >> 7;
        if s_blk > n_blks {
          let len_bnd: usize = (n_blks + 1) << 7;
          panic!(format!("range start is {} but length < {}", range.start, len_bnd))
        }
        let e_blk: usize = range.end >> 7;
        if e_blk > n_blks {
          let len_bnd: usize = (n_blks + 1) << 7;
          panic!(format!("range end is {} but length < {}", range.end, len_bnd))
        }

        // Find the block containing the range start
        let mut s_ptr: *const u32 = storage.as_ptr();
        let wrd_to_blk: usize = words_to_block(n_blks, s_blk, $ty::width(), s_ptr);

        // Prepare return variable
        let mut output: Vec<$ty> = Vec::with_capacity((e_blk - s_blk + 1) << 7);
        let mut o_ptr: *mut $ty = output.as_mut_ptr();

        // Start block known, decode the range
        s_ptr = storage.as_ptr().offset(wrd_to_blk as isize);

        // Block size is known for all but the final block
        for _ in 0..(e_blk - s_blk) {
          // Find the width of the block
          let wd: usize = ((*s_ptr & WIDTH_MASK) + 1) as usize;
          s_ptr = s_ptr.offset(1);

          // Decode the block
          pfor_codec::$dec_simd[wd - 1](s_ptr, o_ptr);
          s_ptr = s_ptr.offset(4 * wd as isize);
          o_ptr = o_ptr.offset(128);
        }

        // Final block
        let left: usize = (((*s_ptr & ENTRIES_MASK) >> 6) + 1) as usize;

        // Checks a lower bound on the length
        let len_bnd: usize = (e_blk << 7) + left;
        if range.start > len_bnd {
          panic!(format!("range start is {} but length is {}", range.start, len_bnd))
        }
        if range.end > len_bnd {
          panic!(format!("range end is {} but length is {}", range.end, len_bnd))
        }
        if range.start == range.end {
          return Vec::new();
        }

        // Decode final block
        Patched::<$ty>::_decode_final(s_ptr, o_ptr);

        // Shift the entries into the desired range
        let sft: usize = range.start - (s_blk << 7);
        let mut src: *const $ty = output.as_ptr().offset(sft as isize);
        let mut snk: *mut $ty = output.as_mut_ptr();

        *snk = *src;
        for _ in range.start..(range.end - 1) {
          src = src.offset(1);
          snk = snk.offset(1);
          *snk = *src;
        }
        output.set_len(range.end - range.start);
        output
      }
    }

    impl AccessPrivate<ops::RangeFrom<usize>> for Patched<$ty> {
      unsafe fn _access(storage: &[u32], range: ops::RangeFrom<usize>) -> Vec<$ty> {
        if storage.is_empty() {
          if range.start > 0 {
            panic!(format!("range start is {} but length is 0", range.start))
          }
        }

        let n_blks: usize = (storage[0] >> 2) as usize;
        let s_blk: usize = range.start >> 7;
        if s_blk > n_blks {
          let len_bnd: usize = (n_blks + 1) << 7;
          panic!(format!("range start is {} but length < {}", range.start, len_bnd))
        }

        // Find the block containing the range start
        let mut s_ptr: *const u32 = storage.as_ptr();
        let wrd_to_blk: usize = words_to_block(n_blks, s_blk, $ty::width(), s_ptr);

        // Prepare return variable
        let mut output: Vec<$ty> = Vec::with_capacity((n_blks - s_blk + 1) << 7);
        let mut o_ptr: *mut $ty = output.as_mut_ptr();

        // Start block known, decode the range
        s_ptr = storage.as_ptr().offset(wrd_to_blk as isize);

        // Block size is known for all but the final block
        for _ in 0..(n_blks - s_blk) {
          // Find the width of the block
          let wd: usize = ((*s_ptr & WIDTH_MASK) + 1) as usize;
          s_ptr = s_ptr.offset(1);

          // Decode the block
          pfor_codec::$dec_simd[wd - 1](s_ptr, o_ptr);
          s_ptr = s_ptr.offset(4 * wd as isize);
          o_ptr = o_ptr.offset(128);
        }

        // Final block
        let left: usize = (((*s_ptr & ENTRIES_MASK) >> 6) + 1) as usize;
        let len: usize = (n_blks << 7) + left;

        // Check a lower bound on the length
        if range.start > len {
          panic!(format!("range start is {} but length is {}", range.start, len))
        }
        if range.start == len {
          return Vec::new();
        }

        // Decode final block
        Patched::<$ty>::_decode_final(s_ptr, o_ptr);

        // Shift the entries into the desired range
        let sft: usize = range.start - (s_blk << 7);
        let mut src: *const $ty = output.as_ptr().offset(sft as isize);
        let mut snk: *mut $ty = output.as_mut_ptr();

        *snk = *src;
        for _ in 0..(len - range.start - 1) {
          src = src.offset(1);
          snk = snk.offset(1);
          *snk = *src;
        }
        output.set_len(len - range.start);
        output
      }
    }
  )*)
}

access_unsigned!{
  (u8: 16, DECODE_U8, DECODE_SIMD_U8)
  (u16: 16, DECODE_U16, DECODE_SIMD_U16)
  (u32: 16, DECODE_U32, DECODE_SIMD_U32)
  (u64: 16, DECODE_U64, DECODE_SIMD_U64)
}

macro_rules! access_signed {
  ($(($it: ident, $ut: ident: $dec_zz: ident))*) => ($(
    impl AccessPrivate<usize> for Patched<$it> {
      unsafe fn _access(storage: &[u32], index: usize) -> $it {
        let val: $ut = Patched::<$ut>::_access(storage, index);
        ((val >> 1) ^ (!(val & 1)).wrapping_add(1)) as $it
      }
    }

    impl AccessPrivate<ops::Range<usize>> for Patched<$it> {
      unsafe fn _access(storage: &[u32], range: ops::Range<usize>) -> Vec<$it> {
        let mut scratch: Vec<$ut> = Patched::<$ut>::_access(storage, range);
        let ptr: *mut $ut = scratch.as_mut_ptr();
        let len: usize = scratch.len();
        pfor_codec::$dec_zz(ptr, len);
        mem::transmute(scratch)
      }
    }

    impl AccessPrivate<ops::RangeFrom<usize>> for Patched<$it> {
      unsafe fn _access(storage: &[u32], range: ops::RangeFrom<usize>) -> Vec<$it> {
        let mut scratch: Vec<$ut> = Patched::<$ut>::_access(storage, range);
        let ptr: *mut $ut = scratch.as_mut_ptr();
        let len: usize = scratch.len();
        pfor_codec::$dec_zz(ptr, len);
        mem::transmute(scratch)
      }
    }
  )*)
}

access_signed!{
  (i8, u8: decode_zz_u8)
  (i16, u16: decode_zz_u16)
  (i32, u32: decode_zz_u32)
  (i64, u64: decode_zz_u64)
}
