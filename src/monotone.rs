// Copyright 2016 Jeremy Mason
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

//! `Monotone` encoding of integer arrays. Intended for cases where the entries
//! are monotonically increasing. Implemented for all primitive integer types.  
//!
//! This type is specifically intended for arrays with monotone increasing
//! entries. A blocks of entries is transformed into an offset and an array of
//! differences of successive entries, and the array of differences is encoded.
//! Compression decays with the maximum magnitude of the difference of
//! successive entries.
//!
//! # Examples
//!
//! ```
//! use mayda::{Access, Encode, Monotone};
//!
//! let input: Vec<u32> = vec![1, 5, 7, 15, 20, 27];
//! let mut bits = Monotone::new();
//! bits.encode(&input).unwrap();
//!
//! let length = bits.len();
//! assert_eq!(length, 6);
//!
//! let output = bits.decode();
//! assert_eq!(input, output);
//!
//! let value = bits.access(4);
//! assert_eq!(value, 20);
//!
//! let range = bits.access(1..4);
//! assert_eq!(range, vec![5, 7, 15]); 
//! ```

use std::marker::PhantomData;
use std::{mem, ops, ptr, usize};

use mayda_codec;
use utility::{self, Bits, Encode, Access, AccessInto};

const E_WIDTH: u32 = 0x0000007f;
const E_COUNT: u32 = 0x00007f80;

/// The type of a monotone encoded integer array. Designed for moderate
/// compression and efficient decoding through the `Encode` trait, and
/// efficient random access through the `Access` and `AccessInto` traits.
///
/// Support is provided for arrays with as many as (2^37 - 2^7) entries, or
/// about 512 GiB of `u32`s. If your application requires more than that, you
/// should probably be designing your own data structure anyway.
///
/// # Examples
///
/// ```
/// use mayda::{Access, Encode, Monotone};
///
/// let input: Vec<u32> = vec![1, 5, 7, 15, 20, 27];
/// let mut bits = Monotone::new();
/// bits.encode(&input).unwrap();
///
/// let length = bits.len();
/// assert_eq!(length, 6);
///
/// let output = bits.decode();
/// assert_eq!(input, output);
///
/// let value = bits.access(4);
/// assert_eq!(value, 20);
///
/// let range = bits.access(1..4);
/// assert_eq!(range, vec![5, 7, 15]); 
/// ```
///
/// # Performance
///
/// Decoding does not allocate except for the return value, and decodes around
/// 7.5 GiB/s of decoded integers on difficult inputs. Encoding allocates `O(n)`
/// memory (`n` in the length of the array), and encodes around 4.5 GiB/s of
/// decoded integers. Run `cargo bench --bench monotone` for performance
/// numbers on your setup.
///
/// The performance (speed and compression) degrades gradually as the number of
/// entries falls below 128.
///
/// # Safety
///
/// As a general rule, you **should not** decode or access `Monotone` objects
/// from untrusted sources.
///
/// A `Monotone` object performs unsafe pointer operations during encoding and
/// decoding. Changing the header information with `mut_storage` can cause data
/// to be written to or read from arbitrary addresses in memory.
///
/// That said, the situation is the same for any of the data structures in the
/// standard library (consider the `set_len` method of a `Vec`).
#[derive(Clone, Debug, Default, Hash, PartialEq, PartialOrd)]
pub struct Monotone<B> {
  storage: Box<[u32]>,
  phantom: PhantomData<B>
}

impl<B: Bits> Monotone<B> {
  /// Creates an empty `Monotone` object.
  ///
  /// # Examples
  /// ```
  /// use mayda::{Encode, Monotone};
  ///
  /// let input: Vec<u32> = vec![1, 5, 7, 15, 20, 27];
  /// let mut bits = Monotone::new();
  /// bits.encode(&input).unwrap();
  ///
  /// let bytes = std::mem::size_of_val(bits.storage());
  /// assert_eq!(bytes, 16);
  /// ```
  #[inline]
  pub fn new() -> Self {
    Monotone {
      storage: Box::new([0; 0]),
      phantom: PhantomData
    }
  }

  /// Creates a `Monotone` object that encodes the slice.
  ///
  /// # Examples
  /// ```
  /// use mayda::{Encode, Monotone};
  ///
  /// let input: Vec<u32> = vec![1, 5, 7, 15, 20, 27];
  /// let bits = Monotone::from_slice(&input).unwrap();
  ///
  /// let output = bits.decode();
  /// assert_eq!(input, output);
  /// ```
  #[inline]
  pub fn from_slice(slice: &[B]) -> Result<Self, super::Error> {
    let mut bits = Self::new();
    match bits.encode(slice) {
      Err(error) => Err(error),
      Ok(()) => Ok(bits)
    }
  }

  /// Returns true when there are no encoded entries.
  ///
  /// # Examples
  /// ```
  /// use mayda::Monotone;
  ///
  /// let mut bits = Monotone::<u32>::new();
  /// assert_eq!(bits.is_empty(), true);
  /// ```
  #[inline]
  pub fn is_empty(&self) -> bool {
    self.storage.is_empty()
  }

  /// Returns the number of encoded entries. Note that since the length has to
  /// be calculated, `Monotone::len()` is more expensive than `Slice::len()`.
  ///
  /// # Examples
  /// ```
  /// use mayda::{Encode, Monotone};
  ///
  /// let input: Vec<u32> = vec![1, 5, 7, 15, 20, 27];
  /// let mut bits = Monotone::new();
  /// bits.encode(&input).unwrap();
  ///
  /// assert_eq!(bits.len(), 6);
  /// ```
  pub fn len(&self) -> usize {
    if self.storage.is_empty() { return 0 }

    let s_ptr: *const u32 = self.storage.as_ptr();
    let n_blks: usize = unsafe { (*s_ptr >> 2) as usize };

    let ty_wd: u32 = B::width();
    let wrd_to_blk: usize = words_to_block(n_blks, n_blks, ty_wd, s_ptr);
    let left: usize = unsafe {
      ((*s_ptr.offset(wrd_to_blk as isize) & E_COUNT) >> 7) as usize
    };

    (n_blks << 7) + left
  }

  /// Exposes the word storage of the `Monotone` object.
  ///
  /// # Examples
  /// ```
  /// use mayda::{Encode, Monotone};
  ///
  /// let input: Vec<u32> = vec![1, 5, 7, 15, 20, 27];
  /// let mut bits = Monotone::new();
  /// bits.encode(&input).unwrap();
  ///
  /// let storage = bits.storage();
  /// assert_eq!(storage.len(), 4);
  /// ```
  #[inline]
  pub fn storage(&self) -> &[u32] {
    &self.storage
  }

  /// Exposes the mutable word storage of the `Monotone` object.
  ///
  /// # Safety
  ///
  /// A `Monotone` object performs unsafe pointer operations during encoding
  /// and decoding. Changing the header information can cause data to be
  /// written to or read from arbitrary addresses in memory. 
  #[inline]
  pub unsafe fn mut_storage(&mut self) -> &mut Box<[u32]> {
    &mut self.storage
  }

  /// Returns the width of the encoded integer type.
  ///
  /// # Examples
  /// ```
  /// use mayda::{Encode, Monotone};
  ///
  /// let input: Vec<u32> = vec![1, 5, 7, 15, 20, 27];
  /// let mut bits = Monotone::new();
  /// bits.encode(&input).unwrap();
  ///
  /// assert_eq!(bits.required_width(), 32);
  /// ```
  #[inline]
  pub fn required_width(&self) -> u32 {
    B::width()
  }
}

////////////////////////////////////////////////////////////////////////////////
// HIC SUNT LEONES
////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////
// Implementations of Encode
////////////////////////////////////////////////////////////////////////////////

impl<B: Bits> Encode<B> for Monotone<B> {
  fn encode(&mut self, input: &[B]) -> Result<(), super::Error> {
    let storage: Vec<u32> = unsafe { try!(Monotone::<B>::_encode(input)) };
    self.storage = storage.into_boxed_slice();
    Ok(())
  }

  fn decode(&self) -> Vec<B> {
    // Nothing to do
    if self.storage.is_empty() { return Vec::new() }

    let s_ptr: *const u32 = self.storage.as_ptr();
    let n_blks: usize = unsafe { (*s_ptr >> 2) as usize };
    let len_bnd: usize = (n_blks + 1) << 7;
    let mut output: Vec<B> = Vec::with_capacity(len_bnd);

    unsafe {
      output.set_len(len_bnd);
      let length: usize = Monotone::<B>::_decode(&*self.storage, n_blks, &mut *output);
      output.set_len(length);
    }

    output
  }

  fn decode_into(&self, output: &mut [B]) -> usize {
    if self.storage.is_empty() {
      return 0
    }

    let s_ptr: *const u32 = self.storage.as_ptr();
    let n_blks: usize = unsafe { (*s_ptr >> 2) as usize };
    let len_bnd: usize = n_blks << 7;
    if output.len() <= len_bnd {
      panic!(
        format!("source length is > {} but slice length is {}", len_bnd, output.len())
      );
    }

    unsafe { Monotone::<B>::_decode(&*self.storage, n_blks, output) }
  }
}

/// The private interface of an `Encode` type. Allows the implementation to
/// be shared for different types.
trait EncodePrivate<B: Bits> {
  /// Encodes a slice.
  unsafe fn _encode(&[B]) -> Result<Vec<u32>, super::Error>;

  /// Decodes a slice.
  unsafe fn _decode(&[u32], usize, &mut [B]) -> usize;

  /// Encodes a block with 128 or fewer elements. Returns pointer to storage.
  unsafe fn _encode_tail(_: *const B, _: *mut u32, usize, u32) -> *mut u32;

  /// Decodes a block with 128 or fewer elements. Returns pointer to storage.
  unsafe fn _decode_tail(_: *const u32, _: *mut B, usize, u32) -> *const u32;
}

/// Default is only to catch unimplemented types. Should not be reachable.
impl<B: Bits> EncodePrivate<B> for Monotone<B> {
  default unsafe fn _encode(_: &[B]) -> Result<Vec<u32>, super::Error> {
    Err(super::Error::new("Encode not implemented for this type"))
  }

  default unsafe fn _decode(_: &[u32], _: usize, _: &mut [B]) -> usize {
    panic!("Encode not implemented for this type")
  }

  default unsafe fn _encode_tail(_: *const B, _: *mut u32, _: usize, _: u32) -> *mut u32 {
    panic!("Encode not implemented for this type");
  }

  default unsafe fn _decode_tail(_: *const u32, _: *mut B, _: usize, _: u32) -> *const u32 {
    panic!("Encode not implemented for this type");
  }
}

macro_rules! encodable_unsigned {
  ($(($ty: ident: $step: expr,
      $enc: ident, $dec: ident,
      $enc_simd: ident, $dec_simd: ident,
      $enc_delta: ident))*) => ($(
    impl EncodePrivate<$ty> for Monotone<$ty> {
      unsafe fn _encode(input: &[$ty]) -> Result<Vec<u32>, super::Error> {
        // Nothing to do
        if input.is_empty() { return Ok(Vec::new()) }
        
        // Allow arrays of 2^37 entries (512 GiB of u32)
        let n_blks: usize = (input.len() - 1) >> 7;
        let n_lvls: usize = n_blks.bits() as usize;
        if n_lvls > 30 {
          return Err(super::Error::new("exceeded internal capacity"))
        }
        let mut e_counts: Vec<usize> = vec![128; n_blks + 1];
        e_counts[n_blks] = input.len() - (n_blks << 7);

        // Internal representation of ty
        let ty_wd: u32 = $ty::width();
        let ty_wrd: usize = utility::words_for_bits(ty_wd);
        let flag: u32 = match ty_wd {
          8 => utility::U8_FLAG,
          16 => utility::U16_FLAG,
          32 => utility::U32_FLAG,
          64 => utility::U64_FLAG,
          _ => unreachable!()
        };

        let mut scratch: Vec<$ty> = input.to_vec();
        let mut shifts: Vec<$ty> = Vec::with_capacity(n_blks + 1);
        let mut c_ptr: *mut $ty = scratch.as_mut_ptr();
        let shift_ptr: *mut $ty = shifts.as_mut_ptr();

        // Construct and apply shifts
        for (a, &e_cnt) in e_counts.iter().enumerate() {
          mayda_codec::$enc_delta(c_ptr, e_cnt);
          *shift_ptr.offset(a as isize) = *c_ptr;
          *c_ptr = 0;
          c_ptr = c_ptr.offset(e_cnt as isize);
        }
        c_ptr = scratch.as_mut_ptr();
        
        // Quantity used for the headers
        let mut e_widths: Vec<u32> = Vec::with_capacity(n_blks + 1);
        let e_wd_ptr: *mut u32 = e_widths.as_mut_ptr();

        // Find widths of all blocks
        let mut blk_max: $ty;
        for (a, &e_cnt) in e_counts.iter().enumerate() {
          blk_max = 0;
          for _ in 0..e_cnt {
            blk_max |= *c_ptr;
            c_ptr = c_ptr.offset(1);
          }
          *e_wd_ptr.offset(a as isize) = blk_max.bits();
        }
        e_widths.set_len(n_blks + 1);
        c_ptr = scratch.as_mut_ptr();

        // Construct index header
        let mut lvls: Vec<Vec<u64>> = Vec::with_capacity(n_lvls);
        for a in 0..(n_lvls as isize) {
          let length: usize = (n_blks + (1 << a)) >> (a + 1);
          let mut lvl: Vec<u64> = Vec::with_capacity(length);
          for b in (0..(length as isize)).map(|x| x << (a + 1)) {
            let mut acc: u64 = 0;
            for c in 0..(1 << a) {
              acc += *e_wd_ptr.offset(b + c) as u64;
            }
            lvl.push(acc);
          }
          lvls.push(lvl);
        }
        
        // Lengths of index header and blocks
        let base_wd: u32 = ty_wd.bits();
        let mut h_words: usize = 0;
        for (a, x) in lvls.iter().enumerate() {
          let bits: u32 = (base_wd + a as u32) * x.len() as u32;
          h_words += utility::words_for_bits(bits);
        }
        let b_words: usize = (n_blks + 1) * (1 + ty_wrd) +
          4 * e_widths[..n_blks].iter().sum::<u32>() as usize +
          utility::words_for_bits(e_counts[n_blks] as u32 * e_widths[n_blks]);

        // Construct storage
        let s_len: usize = 1 + h_words + b_words;
        let mut storage: Vec<u32> = Vec::with_capacity(s_len);
        let mut s_ptr: *mut u32 = storage.as_mut_ptr();

        // Write Monotone header
        *s_ptr =
          (n_blks as u32) << 2 |
          flag;
        s_ptr = s_ptr.offset(1);

        // Write index header
        for (a, lvl) in lvls.iter().enumerate() {
          let l_wd: u32 = base_wd + a as u32;
          let l_blks: usize = (lvl.len() - 1) >> 7;

          let mut l_ptr: *const u64 = lvl.as_ptr();
          for _ in 0..l_blks {
            mayda_codec::ENCODE_SIMD_U64[l_wd as usize](l_ptr, s_ptr);
            l_ptr = l_ptr.offset(128);
            s_ptr = s_ptr.offset((l_wd << 2) as isize);
          }

          let l_left: usize = lvl.len() - (l_blks << 7);
          s_ptr = Monotone::<u64>::_encode_tail(l_ptr, s_ptr, l_left, l_wd);
        }

        // Write the input
        for (a, &e_cnt) in e_counts.iter().enumerate() {
          let e_wd: u32 = *e_wd_ptr.offset(a as isize);

          // Write block header
          *s_ptr = 
            (e_cnt as u32) << 7 |
            e_wd;
          s_ptr = s_ptr.offset(1);

          // Write the block
          s_ptr = Monotone::<$ty>::_encode_tail(c_ptr, s_ptr, e_cnt, e_wd);
          c_ptr = c_ptr.offset(e_cnt as isize);

          // Write the shift. Notice that some bits can be left unitialized.
          *(s_ptr as *mut $ty) = *shift_ptr.offset(a as isize);
          s_ptr = s_ptr.offset(ty_wrd as isize);
        }

        // Set the length of storage AFTER everything is initialized
        storage.set_len(s_len);
        Ok(storage)
      }

      unsafe fn _decode(storage: &[u32], n_blks: usize, output: &mut [$ty]) -> usize {
        // Internal representation of ty
        let ty_wd: u32 = $ty::width();
        let ty_wrd: usize = utility::words_for_bits(ty_wd);

        // Length of index header
        let n_lvls: u32 = n_blks.bits();
        let base_wd: u32  = ty_wd.bits();
        let mut h_words: usize = 0;
        for a in 0..n_lvls {
          let len: usize = (n_blks + (1 << a)) >> (a + 1);
          h_words += utility::words_for_bits((base_wd + a) * len as u32);
        }

        // Avoid memory initialization, bounds checking, etc.
        let mut s_ptr: *const u32 = storage.as_ptr();
        s_ptr = s_ptr.offset(1 + h_words as isize);
        let mut o_ptr: *mut $ty = output.as_mut_ptr();

        // Block size is known for all but the final block
        for _ in 0..n_blks {
          // Find the width of the block
          let e_wd: u32 = *s_ptr & E_WIDTH;
          s_ptr = s_ptr.offset(1);

          // Decode the block
          mayda_codec::$dec_simd[e_wd as usize](s_ptr, o_ptr);
          s_ptr = s_ptr.offset((e_wd << 2) as isize);

          let mut acc: $ty = *(s_ptr as *const $ty);
          s_ptr = s_ptr.offset(ty_wrd as isize);
          for a in 0..128 {
            acc = acc.wrapping_add(*o_ptr.offset(a));
            *o_ptr.offset(a) = acc;
          }

          o_ptr = o_ptr.offset(128);
        }

        // Final block
        let e_wd: u32 = *s_ptr & E_WIDTH;
        let left: usize = ((*s_ptr & E_COUNT) >> 7) as usize;
        s_ptr = s_ptr.offset(1);

        let length: usize = (n_blks << 7) + left;
        if output.len() < length {
          panic!(
            format!("source length is {} but slice length is {}", length, output.len())
          );
        }

        s_ptr = Monotone::<$ty>::_decode_tail(s_ptr, o_ptr, left, e_wd);

        let mut acc: $ty = *(s_ptr as *const $ty);
        for a in 0..(left as isize) {
          acc = acc.wrapping_add(*o_ptr.offset(a));
          *o_ptr.offset(a) = acc;
        }

        length
      }

      unsafe fn _encode_tail(mut c_ptr: *const $ty,
                             mut s_ptr: *mut u32,
                             e_cnt: usize,
                             e_wd: u32) -> *mut u32 {
        // Encode a run of 128 integers and return
        if e_cnt == 128 {
          mayda_codec::$enc_simd[e_wd as usize](c_ptr, s_ptr);
          return s_ptr.offset(4 * e_wd as isize)
        }

        // Encode a short run and return
        if e_cnt < $step {
          *s_ptr = 0;
          let mut s_bits: u32 = 32;
          let mut i_bits: u32;
          for a in 0..e_cnt {
            i_bits = e_wd;

            // Encode in the available space
            let lsft: u32 = 32 - s_bits;
            *s_ptr |= (*c_ptr as u32) << lsft;

            // While the available space is not enough...
            while s_bits < i_bits {
              i_bits -= s_bits;
              s_ptr = s_ptr.offset(1);
              *s_ptr = (*c_ptr >> (e_wd - i_bits)) as u32;
              s_bits = 32;
            }
            s_bits -= i_bits;

            if a < e_cnt - 1 {
              c_ptr = c_ptr.offset(1);
              if s_bits == 0 {
                s_ptr = s_ptr.offset(1);
                *s_ptr = 0;
                s_bits = 32;
              }
            }
          }
          return { if s_bits < 32 { s_ptr.offset(1) } else { s_ptr } }
        }

        // Encode any runs of 32 integers
        for _ in 0..(e_cnt >> 5) {
          mayda_codec::$enc[e_wd as usize][32 / $step - 1](c_ptr, s_ptr);
          c_ptr = c_ptr.offset(32);
          s_ptr = s_ptr.offset(e_wd as isize);
        }
        let mut e_cnt: usize = e_cnt & 31;

        // Encode any runs of step integers
        let mut s_bits: u32 = 32;
        if e_cnt >= $step {
          let part: usize = e_cnt - e_cnt % $step;
          let bits: u32 = part as u32 * e_wd;
          mayda_codec::$enc[e_wd as usize][(part / $step - 1) as usize](c_ptr, s_ptr);
          c_ptr = c_ptr.offset(part as isize);
          s_ptr = s_ptr.offset((bits >> 5) as isize);
          s_bits -= bits & 31;
          e_cnt -= part;
        }

        // Encode any leftover integers one by one
        if e_cnt > 0 {
          if s_bits == 32 { *s_ptr = 0; }
          let mut i_bits: u32;
          for a in 0..e_cnt {
            i_bits = e_wd;

            // Encode in the available space
            let lsft: u32 = 32 - s_bits;
            *s_ptr |= (*c_ptr as u32) << lsft;

            // While the available space is not enough...
            while s_bits < i_bits {
              i_bits -= s_bits;
              s_ptr = s_ptr.offset(1);
              *s_ptr = (*c_ptr >> (e_wd - i_bits)) as u32;
              s_bits = 32;
            }
            s_bits -= i_bits;

            if a < e_cnt - 1 {
              c_ptr = c_ptr.offset(1);
              if s_bits == 0 {
                s_ptr = s_ptr.offset(1);
                *s_ptr = 0;
                s_bits = 32;
              }
            }
          }
        }
        if s_bits < 32 { s_ptr.offset(1) } else { s_ptr }
      }

      unsafe fn _decode_tail(mut s_ptr: *const u32,
                             mut o_ptr: *mut $ty,
                             e_cnt: usize,
                             e_wd: u32) -> *const u32 {
        // Decode a run of 128 integers and return
        if e_cnt == 128 {
          mayda_codec::$dec_simd[e_wd as usize](s_ptr, o_ptr);
          return s_ptr.offset(4 * e_wd as isize)
        }

        // Decode a short run and return
        if e_cnt < $step {
          let mut s_bits: u32 = 32;
          let mut o_bits: u32;
          let mask: $ty = {
            if e_wd > 0 { !0 >> ($ty::width() - e_wd) } else { 0 }
          };

          // Decode any remaining integers one by one
          for _ in 0..(e_cnt - 1) {
            o_bits = e_wd;

            // Decode anything in the available space
            let rsft: u32 = 32 - s_bits;
            *o_ptr = (*s_ptr >> rsft) as $ty;

            // While the available space is not enough...
            while o_bits > s_bits {
              o_bits -= s_bits;
              s_ptr = s_ptr.offset(1);
              *o_ptr |= (*s_ptr as $ty) << (e_wd - o_bits);
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
          // Final iteration moved out of loop to avoid branching
          o_bits = e_wd;

          // Decode anything in the available space
          let rsft: u32 = 32 - s_bits;
          *o_ptr = (*s_ptr >> rsft) as $ty;

          // While the available space is not enough...
          while o_bits > s_bits {
            o_bits -= s_bits;
            s_ptr = s_ptr.offset(1);
            *o_ptr |= (*s_ptr as $ty) << (e_wd - o_bits);
            s_bits = 32;
          }
          s_bits -= o_bits;

          *o_ptr &= mask;
          return { if s_bits < 32 { s_ptr.offset(1) } else { s_ptr } }
        }

        // Decode any runs of 32 integers
        for _ in 0..(e_cnt >> 5) {
          mayda_codec::$dec[e_wd as usize][32 / $step - 1](s_ptr, o_ptr);
          s_ptr = s_ptr.offset(e_wd as isize);
          o_ptr = o_ptr.offset(32);
        }
        let mut e_cnt: usize = e_cnt & 31;

        // Decode any runs of step integers
        let mut s_bits: u32 = 32;
        if e_cnt >= $step {
          let part: usize = e_cnt - e_cnt % $step;
          let bits: u32 = part as u32 * e_wd;
          mayda_codec::$dec[e_wd as usize][(part / $step - 1) as usize](s_ptr, o_ptr);
          s_ptr = s_ptr.offset((bits >> 5) as isize);
          o_ptr = o_ptr.offset(part as isize);
          s_bits -= bits & 31;
          e_cnt -= part;
        }

        // Decode any leftover integers one by one
        if e_cnt > 0 {
          let mut o_bits: u32;
          let mask: $ty = {
            if e_wd > 0 { !0 >> ($ty::width() - e_wd) } else { 0 }
          };

          // Decode any remaining integers one by one
          for _ in 0..(e_cnt - 1) {
            o_bits = e_wd;

            // Decode anything in the available space
            let rsft: u32 = 32 - s_bits;
            *o_ptr = (*s_ptr >> rsft) as $ty;

            // While the available space is not enough...
            while o_bits > s_bits {
              o_bits -= s_bits;
              s_ptr = s_ptr.offset(1);
              *o_ptr |= (*s_ptr as $ty) << (e_wd - o_bits);
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
          // Final iteration moved out of loop to avoid branching
          o_bits = e_wd;

          // Decode anything in the available space
          let rsft: u32 = 32 - s_bits;
          *o_ptr = (*s_ptr >> rsft) as $ty;

          // While the available space is not enough...
          while o_bits > s_bits {
            o_bits -= s_bits;
            s_ptr = s_ptr.offset(1);
            *o_ptr |= (*s_ptr as $ty) << (e_wd - o_bits);
            s_bits = 32;
          }
          s_bits -= o_bits;

          *o_ptr &= mask;
        }
        if s_bits < 32 { s_ptr.offset(1) } else { s_ptr }
      }
    }
  )*)
}

encodable_unsigned!{
  (u8: 8,
   ENCODE_U8, DECODE_U8,
   ENCODE_SIMD_U8, DECODE_SIMD_U8,
   encode_delta_u8)
  (u16: 8,
   ENCODE_U16, DECODE_U16,
   ENCODE_SIMD_U16, DECODE_SIMD_U16,
   encode_delta_u16)
  (u32: 8,
   ENCODE_U32, DECODE_U32,
   ENCODE_SIMD_U32, DECODE_SIMD_U32,
   encode_delta_u32)
  (u64: 8,
   ENCODE_U64, DECODE_U64,
   ENCODE_SIMD_U64, DECODE_SIMD_U64,
   encode_delta_u64)
}

#[cfg(target_pointer_width = "16")]
impl EncodePrivate<usize> for Monotone<usize> {
  #[inline]
  unsafe fn _encode(storage: &[usize]) -> Result<Vec<u32>, super::Error> {
    Monotone::<u16>::_encode(mem::transmute(storage))
  }

  #[inline]
  unsafe fn _decode(storage: &[u32], n_blks: usize, output: &mut [usize]) -> usize {
    Monotone::<u16>::_decode(storage, n_blks, mem::transmute(output))
  }
}

#[cfg(target_pointer_width = "32")]
impl EncodePrivate<usize> for Monotone<usize> {
  #[inline]
  unsafe fn _encode(storage: &[usize]) -> Result<Vec<u32>, super::Error> {
    Monotone::<u32>::_encode(mem::transmute(storage))
  }

  #[inline]
  unsafe fn _decode(storage: &[u32], n_blks: usize, output: &mut [usize]) -> usize {
    Monotone::<u32>::_decode(storage, n_blks, mem::transmute(output))
  }
}

#[cfg(target_pointer_width = "64")]
impl EncodePrivate<usize> for Monotone<usize> {
  #[inline]
  unsafe fn _encode(storage: &[usize]) -> Result<Vec<u32>, super::Error> {
    Monotone::<u64>::_encode(mem::transmute(storage))
  }

  #[inline]
  unsafe fn _decode(storage: &[u32], n_blks: usize, output: &mut [usize]) -> usize {
    Monotone::<u64>::_decode(storage, n_blks, mem::transmute(output))
  }
}

macro_rules! encodable_signed {
  ($(($it: ident: $ut: ident, $enc_delta: ident))*) => ($(
    impl EncodePrivate<$it> for Monotone<$it> {
      unsafe fn _encode(input: &[$it]) -> Result<Vec<u32>, super::Error> {
        // Nothing to do
        if input.is_empty() { return Ok(Vec::new()) }
        
        // Allow arrays of 2^37 entries (512 GiB of u32)
        let n_blks: usize = (input.len() - 1) >> 7;
        let n_lvls: usize = n_blks.bits() as usize;
        if n_lvls > 30 {
          return Err(super::Error::new("exceeded internal capacity"))
        }
        let mut e_counts: Vec<usize> = vec![128; n_blks + 1];
        e_counts[n_blks] = input.len() - (n_blks << 7);

        // Internal representation of ty
        let ty_wd: u32 = $ut::width();
        let ty_wrd: usize = utility::words_for_bits(ty_wd);
        let flag: u32 = match ty_wd {
          8 => utility::U8_FLAG,
          16 => utility::U16_FLAG,
          32 => utility::U32_FLAG,
          64 => utility::U64_FLAG,
          _ => unreachable!()
        };

        let mut scratch: Vec<$it> = input.to_vec();
        let mut shifts: Vec<$it> = Vec::with_capacity(n_blks + 1);
        let mut c_ptr: *mut $it = scratch.as_mut_ptr();
        let shift_ptr: *mut $it = shifts.as_mut_ptr();

        // Construct and apply shifts
        for (a, &e_cnt) in e_counts.iter().enumerate() {
          mayda_codec::$enc_delta(c_ptr as *mut $ut, e_cnt);
          *shift_ptr.offset(a as isize) = *c_ptr;
          *c_ptr = 0;
          c_ptr = c_ptr.offset(e_cnt as isize);
        }

        // Transmute to unsigned. This and the use of the signed type for the 
        // calculation of the shifts is the only difference with the unsigned
        // implementation. Hope to eventually share the following parts.
        let mut scratch: Vec<$ut> = mem::transmute(scratch);
        let mut c_ptr: *mut $ut = scratch.as_mut_ptr();
        let shift_ptr: *mut $ut = shift_ptr as *mut $ut;
        
        // Quantity used for the headers
        let mut e_widths: Vec<u32> = Vec::with_capacity(n_blks + 1);
        let e_wd_ptr: *mut u32 = e_widths.as_mut_ptr();

        // Find widths of all blocks
        let mut blk_max: $ut;
        for (a, &e_cnt) in e_counts.iter().enumerate() {
          blk_max = 0;
          for _ in 0..e_cnt {
            blk_max |= *c_ptr;
            c_ptr = c_ptr.offset(1);
          }
          *e_wd_ptr.offset(a as isize) = blk_max.bits();
        }
        e_widths.set_len(n_blks + 1);
        c_ptr = scratch.as_mut_ptr();

        // Construct index header
        let mut lvls: Vec<Vec<u64>> = Vec::with_capacity(n_lvls);
        for a in 0..(n_lvls as isize) {
          let length: usize = (n_blks + (1 << a)) >> (a + 1);
          let mut lvl: Vec<u64> = Vec::with_capacity(length);
          for b in (0..(length as isize)).map(|x| x << (a + 1)) {
            let mut acc: u64 = 0;
            for c in 0..(1 << a) {
              acc += *e_wd_ptr.offset(b + c) as u64;
            }
            lvl.push(acc);
          }
          lvls.push(lvl);
        }
        
        // Lengths of index header and blocks
        let base_wd: u32 = ty_wd.bits();
        let mut h_words: usize = 0;
        for (a, x) in lvls.iter().enumerate() {
          let bits: u32 = (base_wd + a as u32) * x.len() as u32;
          h_words += utility::words_for_bits(bits);
        }
        let b_words: usize = (n_blks + 1) * (1 + ty_wrd) +
          4 * e_widths[..n_blks].iter().sum::<u32>() as usize +
          utility::words_for_bits(e_counts[n_blks] as u32 * e_widths[n_blks]);

        // Construct storage
        let s_len: usize = 1 + h_words + b_words;
        let mut storage: Vec<u32> = Vec::with_capacity(s_len);
        let mut s_ptr: *mut u32 = storage.as_mut_ptr();

        // Write Monotone header
        *s_ptr =
          (n_blks as u32) << 2 |
          flag;
        s_ptr = s_ptr.offset(1);

        // Write index header
        for (a, lvl) in lvls.iter().enumerate() {
          let l_wd: u32 = base_wd + a as u32;
          let l_blks: usize = (lvl.len() - 1) >> 7;

          let mut l_ptr: *const u64 = lvl.as_ptr();
          for _ in 0..l_blks {
            mayda_codec::ENCODE_SIMD_U64[l_wd as usize](l_ptr, s_ptr);
            l_ptr = l_ptr.offset(128);
            s_ptr = s_ptr.offset((l_wd << 2) as isize);
          }

          let l_left: usize = lvl.len() - (l_blks << 7);
          s_ptr = Monotone::<u64>::_encode_tail(l_ptr, s_ptr, l_left, l_wd);
        }

        // Write the input
        for (a, &e_cnt) in e_counts.iter().enumerate() {
          let e_wd: u32 = *e_wd_ptr.offset(a as isize);

          // Write block header
          *s_ptr = 
            (e_cnt as u32) << 7 |
            e_wd;
          s_ptr = s_ptr.offset(1);

          // Write the block
          s_ptr = Monotone::<$ut>::_encode_tail(c_ptr, s_ptr, e_cnt, e_wd);
          c_ptr = c_ptr.offset(e_cnt as isize);

          // Write the shift. Notice that some bits can be left unitialized.
          *(s_ptr as *mut $ut) = *shift_ptr.offset(a as isize);
          s_ptr = s_ptr.offset(ty_wrd as isize);
        }

        // Set the length of storage AFTER everything is initialized
        storage.set_len(s_len);
        Ok(storage)
      }

      #[inline]
      unsafe fn _decode(storage: &[u32], n_blks: usize, output: &mut [$it]) -> usize {
        Monotone::<$ut>::_decode(storage, n_blks, mem::transmute(output))
      }
    }
  )*)
}

encodable_signed!{
  (i8: u8, encode_delta_u8)
  (i16: u16, encode_delta_u16)
  (i32: u32, encode_delta_u32)
  (i64: u64, encode_delta_u64)
}

#[cfg(target_pointer_width = "16")]
impl EncodePrivate<isize> for Monotone<isize> {
  #[inline]
  unsafe fn _encode(storage: &[isize]) -> Result<Vec<u32>, super::Error> {
    Monotone::<i16>::_encode(mem::transmute(storage))
  }

  #[inline]
  unsafe fn _decode(storage: &[u32], n_blks: usize, output: &mut [isize]) -> usize {
    Monotone::<u16>::_decode(storage, n_blks, left, mem::transmute(output))
  }
}

#[cfg(target_pointer_width = "32")]
impl EncodePrivate<isize> for Monotone<isize> {
  #[inline]
  unsafe fn _encode(storage: &[isize]) -> Result<Vec<u32>, super::Error> {
    Monotone::<i32>::_encode(mem::transmute(storage))
  }

  #[inline]
  unsafe fn _decode(storage: &[u32], n_blks: usize, output: &mut [isize]) -> usize {
    Monotone::<u32>::_decode(storage, n_blks, left, mem::transmute(output))
  }
}

#[cfg(target_pointer_width = "64")]
impl EncodePrivate<isize> for Monotone<isize> {
  #[inline]
  unsafe fn _encode(storage: &[isize]) -> Result<Vec<u32>, super::Error> {
    Monotone::<i64>::_encode(mem::transmute(storage))
  }

  #[inline]
  unsafe fn _decode(storage: &[u32], n_blks: usize, output: &mut [isize]) -> usize {
    Monotone::<u64>::_decode(storage, n_blks, mem::transmute(output))
  }
}

////////////////////////////////////////////////////////////////////////////////
// Implementations of Access
////////////////////////////////////////////////////////////////////////////////

// Private traits

trait AccessOne<B: Bits> {
  /// The method for the range access operation.
  unsafe fn _access_one(&[u32], usize) -> B;
}

trait AccessMany<B: Bits, Range> {
  /// The method for the range access operation.
  unsafe fn _access_many(&[u32], usize, Range, &mut [B]) -> usize;
}

// Defaults

impl<B: Bits> AccessOne<B> for Monotone<B> {
  default unsafe fn _access_one(_: &[u32], _: usize) -> B {
    panic!("Access not implemented for this type");
  }
}

impl<B: Bits> AccessMany<B, ops::Range<usize>> for Monotone<B> {
  default unsafe fn _access_many(_: &[u32],
                                 _: usize,
                                 _: ops::Range<usize>,
                                 _: &mut [B]) -> usize {
    panic!("Access not implemented for this type");
  }
}

impl<B: Bits> AccessMany<B, ops::RangeFrom<usize>> for Monotone<B> {
  default unsafe fn _access_many(_: &[u32],
                                 _: usize,
                                 _: ops::RangeFrom<usize>,
                                 _: &mut [B]) -> usize {
    panic!("Access not implemented for this type");
  }
}

// External interface

impl<B: Bits> Access<usize> for Monotone<B> {
  type Output = B;

  #[inline]
  fn access(&self, index: usize) -> B {
    unsafe { Monotone::<B>::_access_one(&*self.storage, index) }
  }
}

impl<B: Bits> Access<ops::Range<usize>> for Monotone<B> {
  type Output = Vec<B>;

  fn access(&self, range: ops::Range<usize>) -> Vec<B> {
    if range.end < range.start {
      panic!(format!("range start is {} but range end is {}", range.start, range.end))
    }
    if self.storage.is_empty() {
      if range.start > 0 {
        panic!(format!("range start is {} but length is 0", range.start))
      }
      if range.end > 0 {
        panic!(format!("range end is {} but length is 0", range.end))
      }
      return Vec::new();
    }

    let s_ptr: *const u32 = self.storage.as_ptr();
    let n_blks: usize = unsafe { (*s_ptr >> 2) as usize };
    let o_length: usize = range.end - range.start;
    let mut output: Vec<B> = Vec::with_capacity(o_length);

    unsafe {
      output.set_len(o_length);
      Monotone::<B>::_access_many(&*self.storage, n_blks, range, &mut *output);
    }

    output
  }
}

impl<B: Bits> Access<ops::RangeFrom<usize>> for Monotone<B> {
  type Output = Vec<B>;

  fn access(&self, range: ops::RangeFrom<usize>) -> Vec<B> {
    if self.storage.is_empty() {
      if range.start > 0 {
        panic!(format!("range start is {} but length is 0", range.start))
      }
      return Vec::new();
    }

    let s_ptr: *const u32 = self.storage.as_ptr();
    let n_blks: usize = unsafe { (*s_ptr >> 2) as usize };
    let len_bnd: usize = (n_blks + 1) << 7;
    let mut output: Vec<B> = Vec::with_capacity(len_bnd);

    unsafe {
      output.set_len(len_bnd);
      let length: usize = Monotone::<B>::_access_many(
        &*self.storage, n_blks, range, &mut *output
      );
      output.set_len(length);
    }

    output
  }
}

impl<B: Bits> Access<ops::RangeTo<usize>> for Monotone<B> {
  type Output = Vec<B>;

  #[inline]
  fn access(&self, range: ops::RangeTo<usize>) -> Vec<B> {
    self.access(0..range.end)
  }
}

impl<B: Bits> Access<ops::RangeFull> for Monotone<B> {
  type Output = Vec<B>;

  #[inline]
  fn access(&self, _: ops::RangeFull) -> Vec<B> {
    self.decode()
  }
}

impl<B: Bits> Access<ops::RangeInclusive<usize>> for Monotone<B> {
  type Output = Vec<B>;

  #[inline]
  fn access(&self, range: ops::RangeInclusive<usize>) -> Vec<B> {
    match range {
      ops::RangeInclusive::Empty { .. } => Vec::new(),
      ops::RangeInclusive::NonEmpty { end, .. } if end == usize::MAX =>
        panic!("attempted to index slice up to maximum usize"),
      ops::RangeInclusive::NonEmpty { start, end } =>
        self.access(start..(end + 1))
    }
  }
}

impl<B: Bits> Access<ops::RangeToInclusive<usize>> for Monotone<B> {
  type Output = Vec<B>;

  #[inline]
  fn access(&self, range: ops::RangeToInclusive<usize>) -> Vec<B> {
    self.access(0...range.end)
  }
}

impl<B: Bits> AccessInto<ops::Range<usize>, B> for Monotone<B> {
  fn access_into(&self, range: ops::Range<usize>, output: &mut [B]) -> usize {
    if range.end < range.start {
      panic!(format!("range start is {} but range end is {}", range.start, range.end))
    }
    if self.storage.is_empty() {
      if range.start > 0 {
        panic!(format!("range start is {} but length is 0", range.start))
      }
      if range.end > 0 {
        panic!(format!("range end is {} but length is 0", range.end))
      }
      return 0;
    }

    let s_ptr: *const u32 = self.storage.as_ptr();
    unsafe {
      let n_blks: usize = (*s_ptr >> 2) as usize;
      Monotone::<B>::_access_many(&*self.storage, n_blks, range, output)
    }
  }
}

impl<B: Bits> AccessInto<ops::RangeFrom<usize>, B> for Monotone<B> {
  fn access_into(&self, range: ops::RangeFrom<usize>, output: &mut [B]) -> usize {
    if self.storage.is_empty() {
      if range.start > 0 {
        panic!(format!("range start is {} but length is 0", range.start))
      }
      return 0;
    }

    let s_ptr: *const u32 = self.storage.as_ptr();
    unsafe {
      let n_blks: usize = (*s_ptr >> 2) as usize;
      Monotone::<B>::_access_many(&*self.storage, n_blks, range, &mut *output)
    }
  }
}

impl<B: Bits> AccessInto<ops::RangeTo<usize>, B> for Monotone<B> {
  #[inline]
  fn access_into(&self, range: ops::RangeTo<usize>, output: &mut [B]) -> usize {
    self.access_into(0..range.end, output)
  }
}

impl<B: Bits> AccessInto<ops::RangeFull, B> for Monotone<B> {
  #[inline]
  fn access_into(&self, _: ops::RangeFull, output: &mut [B]) -> usize {
    self.decode_into(output)
  }
}

impl<B: Bits> AccessInto<ops::RangeInclusive<usize>, B> for Monotone<B> {
  #[inline]
  fn access_into(&self, range: ops::RangeInclusive<usize>, output: &mut [B]) -> usize {
    match range {
      ops::RangeInclusive::Empty { .. } => 0,
      ops::RangeInclusive::NonEmpty { end, .. } if end == usize::MAX =>
        panic!("attempted to index slice up to maximum usize"),
      ops::RangeInclusive::NonEmpty { start, end } =>
        self.access_into(start..(end + 1), output)
    }
  }
}

impl<B: Bits> AccessInto<ops::RangeToInclusive<usize>, B> for Monotone<B> {
  #[inline]
  fn access_into(&self, range: ops::RangeToInclusive<usize>, output: &mut [B]) -> usize {
    self.access_into(0...range.end, output)
  }
}

// Actual implementations

/// Calculates the offset in words to the start of the block. Not intended to
/// be used outside the implementation of `Access`.
fn words_to_block(n_blks: usize, blk: usize, ty_wd: u32, s_head: *const u32) -> usize {
  let ty_wrd: usize = utility::words_for_bits(ty_wd);

  let base_wd: u32 = ty_wd.bits();
  let mut lvl: u32 = 0;
  let mut lvl_head: usize = 1;
  let mut wrd_to_blk: usize = 0;
  let mut s_ptr: *const u32;

  if blk > 0 {
    let mut w_idx: usize = blk;
    let mut output: u64;

    // Initial iteration moved out of loop to avoid branch
    let shift: u32 = w_idx.trailing_zeros() + 1;
    for _ in 1..shift {
      let l_wd: u32 = base_wd + lvl;
      let len: usize = (n_blks + (1 << lvl)) >> (lvl + 1);
      lvl_head += utility::words_for_bits(l_wd * len as u32);
      lvl += 1;
    }
    w_idx >>= shift;

    let l_wd: u32 = base_wd + lvl;
    let len: usize = (n_blks + (1 << lvl)) >> (lvl + 1);
    unsafe {
      s_ptr = s_head.offset(lvl_head as isize);
      if (w_idx & !127) + 128 <= len {
        // Width encoded using SIMD
        let l_bits: u32 = (w_idx as u32 >> 1) * l_wd;
        let w_bits: u32 = 64 - (l_bits & 63);

        let mut w_ptr: *const u64 = s_ptr as *const u64;
        let w_sft: u32 = ((l_bits >> 5) & !1) | (w_idx as u32 & 1); 
        w_ptr = w_ptr.offset(w_sft as isize);

        output = *w_ptr >> (l_bits & 63);
        if l_wd > w_bits {
          output |= *w_ptr.offset(2) << w_bits;
        }
      } else {
        // Width encoded using u32
        let l_bits: u32 = w_idx as u32 * l_wd;
        let mut s_bits: u32 = 32 - (l_bits & 31);
        let mut o_bits: u32 = l_wd;

        s_ptr = s_ptr.offset((l_bits >> 5) as isize);

        output = (*s_ptr >> (l_bits & 31)) as u64;
        while o_bits > s_bits {
          o_bits -= s_bits;
          s_ptr = s_ptr.offset(1);
          output |= (*s_ptr as u64) << (l_wd - o_bits);
          s_bits = 32;
        }
      }
    }
    wrd_to_blk += (output & (!0 >> (64 - l_wd))) as usize;

    // Decode widths for all other levels
    for _ in 0..w_idx.count_ones() {
      let shift: u32 = w_idx.trailing_zeros() + 1;
      for _ in 0..shift {
        let l_wd: u32 = base_wd + lvl;
        let len: usize = (n_blks + (1 << lvl)) >> (lvl + 1);
        lvl_head += utility::words_for_bits(l_wd * len as u32);
        lvl += 1;
      }
      w_idx >>= shift;

      let l_wd: u32 = base_wd + lvl;
      let len: usize = (n_blks + (1 << lvl)) >> (lvl + 1);
      unsafe {
        s_ptr = s_head.offset(lvl_head as isize);
        if (w_idx & !127) + 128 <= len {
          // Width encoded using SIMD
          let l_bits: u32 = (w_idx as u32 >> 1) * l_wd;
          let w_bits: u32 = 64 - (l_bits & 63);

          let mut w_ptr: *const u64 = s_ptr as *const u64;
          let w_sft: u32 = ((l_bits >> 5) & !1) | (w_idx as u32 & 1); 
          w_ptr = w_ptr.offset(w_sft as isize);

          output = *w_ptr >> (l_bits & 63);
          if l_wd > w_bits {
            output |= *w_ptr.offset(2) << w_bits;
          }
        } else {
          // Width encoded using u32
          let l_bits: u32 = w_idx as u32 * l_wd;
          let mut s_bits: u32 = 32 - (l_bits & 31);
          let mut o_bits: u32 = l_wd;

          s_ptr = s_ptr.offset((l_bits >> 5) as isize);

          output = (*s_ptr >> (l_bits & 31)) as u64;
          while o_bits > s_bits {
            o_bits -= s_bits;
            s_ptr = s_ptr.offset(1);
            output |= (*s_ptr as u64) << (l_wd - o_bits);
            s_bits = 32;
          }
        }
      }
      wrd_to_blk += (output & (!0 >> (64 - l_wd))) as usize;
    }
    wrd_to_blk = blk * (1 + ty_wrd) + (wrd_to_blk << 2);
  }

  // Include the header words
  wrd_to_blk += lvl_head;
  for a in lvl..n_blks.bits() {
    let l_wd: u32 = base_wd + a;
    let len: usize = (n_blks + (1 << a)) >> (a + 1);
    wrd_to_blk += utility::words_for_bits(l_wd * len as u32);
  }

  wrd_to_blk
}

macro_rules! access_unsigned {
  ($(($ty: ident: $step: expr, $dec: ident, $dec_simd: ident))*) => ($(
    impl AccessOne<$ty> for Monotone<$ty> {
      unsafe fn _access_one(storage: &[u32], index: usize) -> $ty {
        if storage.is_empty() {
          panic!(format!("index is {} but length is 0", index))
        }

        let mut s_ptr: *const u32 = storage.as_ptr();
        let n_blks: usize = (*s_ptr >> 2) as usize;
        let blk: usize = index >> 7;
        if blk > n_blks {
          let len_bnd: usize = (n_blks + 1) << 7;
          panic!(format!("index is {} but length < {}", index, len_bnd))
        }

        // Find the block containing the range start
        let ty_wd: u32 = $ty::width();
        let wrd_to_blk: usize = words_to_block(n_blks, blk, ty_wd, s_ptr);

        // Block found, decode the block
        s_ptr = s_ptr.offset(wrd_to_blk as isize);

        let e_wd: u32 = *s_ptr & E_WIDTH;
        let left: usize = ((*s_ptr & E_COUNT) >> 7) as usize;
        s_ptr = s_ptr.offset(1);

        let idx: u8 = (index & 127) as u8;
        if idx as usize >= left {
          let len: usize = index - idx as usize + left;
          panic!(format!("index is {} but length is {}", index, len))
        }

        let mut scratch: Vec<$ty> = Vec::with_capacity(left);
        let c_ptr: *mut $ty = scratch.as_mut_ptr();

        s_ptr = Monotone::<$ty>::_decode_tail(s_ptr, c_ptr, left, e_wd);

        let mut acc: $ty = *(s_ptr as *const $ty);
        for a in 1..(idx as isize + 1) {
          acc = acc.wrapping_add(*c_ptr.offset(a));
        }
        acc
      }
    }

    impl AccessMany<$ty, ops::Range<usize>> for Monotone<$ty> {
      unsafe fn _access_many(storage: &[u32], n_blks: usize,
                             range: ops::Range<usize>, output: &mut [$ty]) -> usize {
        let s_blk: usize = range.start >> 7;
        if s_blk > n_blks {
          let len_bnd: usize = (n_blks + 1) << 7;
          panic!(format!("range start is {} but length < {}", range.start, len_bnd))
        }
        let e_blk: usize = range.end.saturating_sub(1) >> 7;
        if e_blk > n_blks {
          let len_bnd: usize = (n_blks + 1) << 7;
          panic!(format!("range end is {} but length < {}", range.end, len_bnd))
        }
        let o_length: usize = range.end - range.start;
        if output.len() < o_length {
          panic!(
            format!("range length is {} but slice length is {}", o_length, output.len())
          );
        }
        let lwr: usize = range.start - (s_blk << 7);
        let upr: usize = range.end - (e_blk << 7);

        let ty_wd: u32 = $ty::width();
        let ty_wrd: usize = utility::words_for_bits(ty_wd);

        // Find the block containing the range start
        let mut s_ptr: *const u32 = storage.as_ptr();
        let wrd_to_blk: usize = words_to_block(n_blks, s_blk, ty_wd, s_ptr);
        s_ptr = s_ptr.offset(wrd_to_blk as isize);

        // Prepare return variable
        let mut scratch: [$ty; 128] = [0; 128];
        let c_ptr: *mut $ty = scratch.as_mut_ptr();
        let mut o_ptr: *mut $ty = output.as_mut_ptr();

        // Start block known, decode the range
        if s_blk == e_blk {
          // Find the width of the block
          let e_wd: u32 = *s_ptr & E_WIDTH;
          let left: usize = ((*s_ptr & E_COUNT) >> 7) as usize;
          s_ptr = s_ptr.offset(1);

          // Checks a lower bound on the length
          let len_bnd: usize = (e_blk << 7) + left;
          if range.start > len_bnd {
            panic!(format!("range start is {} but length is {}", range.start, len_bnd))
          }
          if range.end > len_bnd {
            panic!(format!("range end is {} but length is {}", range.end, len_bnd))
          }
          if range.start == range.end {
            return 0;
          }

          // Decode the block
          s_ptr = Monotone::<$ty>::_decode_tail(s_ptr, c_ptr, left, e_wd);

          let mut acc: $ty = *(s_ptr as *const $ty);
          for a in 0..(upr as isize) {
            acc = acc.wrapping_add(*c_ptr.offset(a));
            *c_ptr.offset(a) = acc;
          }

          ptr::copy_nonoverlapping(c_ptr.offset(lwr as isize), o_ptr, o_length);

          o_length
        } else {
          // Initial block
          let e_wd: u32 = *s_ptr & E_WIDTH;
          s_ptr = s_ptr.offset(1);

          // Decode initial block
          mayda_codec::$dec_simd[e_wd as usize](s_ptr, c_ptr);
          s_ptr = s_ptr.offset((e_wd << 2) as isize);

          let mut acc: $ty = *(s_ptr as *const $ty);
          s_ptr = s_ptr.offset(ty_wrd as isize);
          for a in 0..128 {
            acc = acc.wrapping_add(*c_ptr.offset(a));
            *c_ptr.offset(a) = acc;
          }

          let count: usize = 128 - lwr;
          ptr::copy_nonoverlapping(c_ptr.offset(lwr as isize), o_ptr, count);
          o_ptr = o_ptr.offset(count as isize);

          // Block size is known for all but the final block
          for _ in 0..(e_blk - s_blk - 1) {
            // Find the width of the block
            let e_wd: u32 = *s_ptr & E_WIDTH;
            s_ptr = s_ptr.offset(1);

            // Decode the block
            mayda_codec::$dec_simd[e_wd as usize](s_ptr, o_ptr);
            s_ptr = s_ptr.offset((e_wd << 2) as isize);

            let mut acc: $ty = *(s_ptr as *const $ty);
            s_ptr = s_ptr.offset(ty_wrd as isize);
            for a in 0..128 {
              acc = acc.wrapping_add(*o_ptr.offset(a));
              *o_ptr.offset(a) = acc;
            }

            o_ptr = o_ptr.offset(128);
          }

          // Final block
          let e_wd: u32 = *s_ptr & E_WIDTH;
          let left: usize = ((*s_ptr & E_COUNT) >> 7) as usize;
          s_ptr = s_ptr.offset(1);

          // Checks a lower bound on the length
          let len_bnd: usize = (e_blk << 7) + left;
          if range.end > len_bnd {
            panic!(format!("range end is {} but length is {}", range.end, len_bnd))
          }

          // Decode final block
          s_ptr = Monotone::<$ty>::_decode_tail(s_ptr, c_ptr, left, e_wd);

          let mut acc: $ty = *(s_ptr as *const $ty);
          for a in 0..(upr as isize) {
            acc = acc.wrapping_add(*c_ptr.offset(a));
            *c_ptr.offset(a) = acc;
          }

          ptr::copy_nonoverlapping(c_ptr, o_ptr, upr);

          o_length
        }
      }
    }

    impl AccessMany<$ty, ops::RangeFrom<usize>> for Monotone<$ty> {
      unsafe fn _access_many(storage: &[u32], n_blks: usize,
                             range: ops::RangeFrom<usize>, output: &mut [$ty]) -> usize {
        let s_blk: usize = range.start >> 7;
        if s_blk > n_blks {
          let len_bnd: usize = (n_blks + 1) << 7;
          panic!(format!("range start is {} but length < {}", range.start, len_bnd))
        }
        let lwr: usize = range.start - (s_blk << 7);

        let ty_wd: u32 = $ty::width();
        let ty_wrd: usize = utility::words_for_bits(ty_wd);

        // Find the block containing the range start
        let mut s_ptr: *const u32 = storage.as_ptr();
        let wrd_to_blk: usize = words_to_block(n_blks, s_blk, ty_wd, s_ptr);
        s_ptr = s_ptr.offset(wrd_to_blk as isize);

        // Prepare return variable
        let mut scratch: [$ty; 128] = [0; 128];
        let c_ptr: *mut $ty = scratch.as_mut_ptr();
        let mut o_ptr: *mut $ty = output.as_mut_ptr();

        // Start block known, decode the range
        if s_blk == n_blks {
          // Find the width of the block
          let e_wd: u32 = *s_ptr & E_WIDTH;
          let left: usize = ((*s_ptr & E_COUNT) >> 7) as usize;
          s_ptr = s_ptr.offset(1);

          // Checks the length of storage
          let s_length: usize = (n_blks << 7) + left;
          if range.start > s_length {
            panic!(format!("range start is {} but length is {}", range.start, s_length))
          }
          let o_length: usize = s_length - range.start;
          if output.len() < o_length {
            panic!(
              format!("range length is {} but slice length is {}", o_length, output.len())
            );
          }
          if range.start == s_length {
            return 0;
          }

          // Decode the block
          s_ptr = Monotone::<$ty>::_decode_tail(s_ptr, c_ptr, left, e_wd);

          let mut acc: $ty = *(s_ptr as *const $ty);
          for a in 0..(left as isize) {
            acc = acc.wrapping_add(*c_ptr.offset(a));
            *c_ptr.offset(a) = acc;
          }

          ptr::copy_nonoverlapping(c_ptr.offset(lwr as isize), o_ptr, o_length);

          o_length
        } else {
          // Checks the length of storage
          let len_bnd: usize = (n_blks << 7) - range.start;
          if output.len() < len_bnd {
            panic!(
              format!("range length is > {} but slice length is {}", len_bnd, output.len())
            );
          }

          // Initial block
          let e_wd: u32 = *s_ptr & E_WIDTH;
          s_ptr = s_ptr.offset(1);

          // Decode initial block
          mayda_codec::$dec_simd[e_wd as usize](s_ptr, c_ptr);
          s_ptr = s_ptr.offset((e_wd << 2) as isize);

          let mut acc: $ty = *(s_ptr as *const $ty);
          s_ptr = s_ptr.offset(ty_wrd as isize);
          for a in 0..128 {
            acc = acc.wrapping_add(*c_ptr.offset(a));
            *c_ptr.offset(a) = acc;
          }

          let count: usize = 128 - lwr;
          ptr::copy_nonoverlapping(c_ptr.offset(lwr as isize), o_ptr, count);
          o_ptr = o_ptr.offset(count as isize);

          // Block size is known for all but the final block
          for _ in 0..(n_blks - s_blk - 1) {
            // Find the width of the block
            let e_wd: u32 = *s_ptr & E_WIDTH;
            s_ptr = s_ptr.offset(1);

            // Decode the block
            mayda_codec::$dec_simd[e_wd as usize](s_ptr, o_ptr);
            s_ptr = s_ptr.offset((e_wd << 2) as isize);

            let mut acc: $ty = *(s_ptr as *const $ty);
            s_ptr = s_ptr.offset(ty_wrd as isize);
            for a in 0..128 {
              acc = acc.wrapping_add(*o_ptr.offset(a));
              *o_ptr.offset(a) = acc;
            }

            o_ptr = o_ptr.offset(128);
          }

          // Final block
          let e_wd: u32 = *s_ptr & E_WIDTH;
          let left: usize = ((*s_ptr & E_COUNT) >> 7) as usize;
          s_ptr = s_ptr.offset(1);

          // Checks the length of storage
          let o_length: usize = (n_blks << 7) + left - range.start;
          if output.len() < o_length {
            panic!(
              format!("range length is {} but slice length is {}", o_length, output.len())
            );
          }

          // Decode final block
          s_ptr = Monotone::<$ty>::_decode_tail(s_ptr, c_ptr, left, e_wd);

          let mut acc: $ty = *(s_ptr as *const $ty);
          for a in 0..(left as isize) {
            acc = acc.wrapping_add(*c_ptr.offset(a));
            *c_ptr.offset(a) = acc;
          }

          ptr::copy_nonoverlapping(c_ptr, o_ptr, left);

          o_length
        }
      }
    }
  )*)
}

access_unsigned!{
  (u8: 8, DECODE_U8, DECODE_SIMD_U8)
  (u16: 8, DECODE_U16, DECODE_SIMD_U16)
  (u32: 8, DECODE_U32, DECODE_SIMD_U32)
  (u64: 8, DECODE_U64, DECODE_SIMD_U64)
}

macro_rules! access_signed {
  ($(($it: ident, $ut: ident))*) => ($(
    impl AccessOne<$it> for Monotone<$it> {
      #[inline]
      unsafe fn _access_one(storage: &[u32], index: usize) -> $it {
        Monotone::<$ut>::_access_one(storage, index) as $it
      }
    }

    impl AccessMany<$it, ops::Range<usize>> for Monotone<$it> {
      #[inline]
      unsafe fn _access_many(storage: &[u32], n_blks: usize,
                             range: ops::Range<usize>, output: &mut [$it]) -> usize {
        Monotone::<$ut>::_access_many(storage, n_blks, range, mem::transmute(output))
      }
    }

    impl AccessMany<$it, ops::RangeFrom<usize>> for Monotone<$it> {
      #[inline]
      unsafe fn _access_many(storage: &[u32], n_blks: usize,
                             range: ops::RangeFrom<usize>, output: &mut [$it]) -> usize {
        Monotone::<$ut>::_access_many(storage, n_blks, range, mem::transmute(output))
      }
    }
  )*)
}

access_signed!{
  (i8, u8)
  (i16, u16)
  (i32, u32)
  (i64, u64)
}

#[cfg(target_pointer_width = "16")]
access_signed!{
  (usize, u16)
  (isize, u16)
}

#[cfg(target_pointer_width = "32")]
access_signed!{
  (usize, u32)
  (isize, u32)
}

#[cfg(target_pointer_width = "64")]
access_signed!{
  (usize, u64)
  (isize, u64)
}
