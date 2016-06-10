// Copyright 2016 Jeremy Mason
//
// Licensed under the MIT license <LICENSE or
// http://opensource.org/licenses/MIT>. This file may not be copied, modified,
// or distributed except according to those terms.

//! `Monotone` encoding of integer arrays. Intended for cases where the entries
//! are monotonically increasing. Implemented for all primitive integer types.  
//!
//! Compression decays with the maximum magnitude of the difference of
//! successive entries.
//!
//! # Examples
//!
//! ```
//! use mayda::{Access, Encodable, Monotone};
//!
//! let input: Vec<u32> = vec![1, 5, 7, 15, 20, 27];
//! let mut bits = Monotone::new();
//! bits.encode(&input);
//!
//! let output = bits.decode().unwrap();
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
use utility::{self, Bits, Encodable, Access};

const E_WIDTH: u32 = 0x0000007f;
const E_COUNT: u32 = 0x00007f80;

/// The type of a monotone encoded integer array. Designed for moderate
/// compression and efficient decoding through the `Encodable` trait, and
/// efficient random access through the `Access` trait.
///
/// Support is provided for arrays with as many as 2^37 entries, or 512 GiB of
/// `u32`s. If your application requires more than that, you should probably
/// be designing your own data structure anyway.
///
/// # Examples
///
/// ```
/// use mayda::{Access, Encodable, Monotone};
///
/// let input: Vec<u32> = vec![1, 5, 7, 15, 20, 27];
/// let mut bits = Monotone::new();
/// bits.encode(&input);
///
/// let output = bits.decode().unwrap();
/// assert_eq!(input, output);
///
/// let value = bits.access(4);
/// assert_eq!(value, 20);
///
/// let range = bits.access(1..4);
/// assert_eq!(range, vec![5, 7, 15]); 
/// ```
///
/// # Indexing
///
/// Indexing a `Monotone` object is not a simple pointer offset. The header of
/// a `Monotone` object effectively encodes the relative offsets to every
/// block, with the result that random access via the `Access` trait is an
/// `O(log(idx))` operation, where `idx` is the value of the index (not the
/// length of the array). The overhead of the header is around a tenth of a bit
/// per encoded integer.
///
/// If you need to access several nearby entries, consider accessing the range
/// and indexing the returned vector for performance.
///
/// # Performance
///
/// Decoding does not allocate except for the return value, and decodes around
/// 7.5 GiB/s of decoded integers. Encoding allocates `O(n)` memory (`n` in the
/// length of the array), and encodes around 4.5 GiB/s of decoded integers. Run
/// `cargo bench --bench monotone` for performance numbers on your setup.
///
/// The performance (speed and compression) degrades gradually as the number of
/// entries falls below 128.
///
/// # Safety
///
/// As a general rule, DO NOT decode or access `Monotone` objects from
/// untrusted sources.
///
/// A `Monotone` object performs unsafe pointer operations during encoding and
/// decoding. Changing the header information with `mut_storage()` can cause
/// data to be written to or read from arbitrary addresses in memory.
///
/// That said, the situation is the same for `Vec`.
///
/// # Algorithm
///
/// The compression algorithm relies on the observation that for many integer
/// arrays, the probability distribution of a block of 128 entries is not
/// uniform over all values that can be represented by the integer type. For
/// example, an array of indices into a second array with 256 entries has
/// entries that are bounded below by 0 and above by 255. This requires only
/// eight bits per entry, rather than the 32 or 64 generally set aside for a
/// usize index. The basic idea of the compression algorithm is to represent
/// all of the entries in a block with a single minimum necessary bit width. 
/// This allows SIMD operations to be used to accelerate encoding and decoding.
///
/// The `Monotone` encoding is specifically intended for arrays with monotone
/// increasing entries. A blocks of entries is transformed into an offset and
/// an array of differences of successive entries, and the array of differences
/// is encoded by the approach above. The compression depends only on the 
/// largest entry in the difference array, but should generally be better than 
/// for either the `Uniform` or `Unimodal` encodings.
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
  /// use std::mem;
  /// use mayda::{Encodable, Monotone};
  ///
  /// let mut bits = Monotone::new();
  ///
  /// let input: Vec<u32> = vec![1, 5, 7, 15, 20, 27];
  /// bits.encode(&input);
  ///
  /// let bytes = mem::size_of_val(&bits);
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
  /// use std::mem;
  /// use mayda::{Encodable, Monotone};
  ///
  /// let input: Vec<u32> = vec![1, 5, 7, 15, 20, 27];
  /// let bits = Monotone::from_slice(&input).unwrap();
  ///
  /// let output = bits.decode().unwrap();
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

  /// Returns the number of encoded entries.
  ///
  /// # Examples
  /// ```
  /// use mayda::{Encodable, Monotone};
  ///
  /// let mut bits = Monotone::new();
  ///
  /// let input: Vec<u32> = vec![1, 5, 7, 15, 20, 27];
  /// bits.encode(&input);
  ///
  /// assert_eq!(bits.len(), 6);
  /// ```
  pub fn len(&self) -> usize {
    if self.storage.is_empty() { return 0 }

    let n_blks: usize = (self.storage[0] >> 2) as usize;
    let mut length: usize = n_blks << 7;

    let mut s_ptr: *const u32 = self.storage.as_ptr();
    let wrd_to_blk: usize = words_to_block(n_blks, n_blks, B::width(), s_ptr);
    unsafe {
      s_ptr = s_ptr.offset(wrd_to_blk as isize);
      length += ((*s_ptr & E_COUNT) >> 7) as usize;
    }

    length
  }

  /// Exposes the word storage of the `Monotone` object.
  ///
  /// # Examples
  /// ```
  /// use mayda::{Encodable, Monotone};
  ///
  /// let mut bits = Monotone::new();
  ///
  /// let input: Vec<u32> = vec![1, 5, 7, 15, 20, 27];
  /// bits.encode(&input);
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
  /// use mayda::{Encodable, Monotone};
  ///
  /// let mut bits = Monotone::new();
  ///
  /// let input: Vec<u32> = vec![1, 5, 7, 15, 20, 27];
  /// bits.encode(&input);
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
// Implementations of Encodable
////////////////////////////////////////////////////////////////////////////////

impl<B: Bits> Encodable<B> for Monotone<B> {
  fn encode(&mut self, input: &[B]) -> Result<(), super::Error> {
    let storage: Vec<u32> = unsafe { try!(Monotone::<B>::_encode(input)) };
    self.storage = storage.into_boxed_slice();
    Ok(())
  }

  fn decode(&self) -> Result<Vec<B>, super::Error> {
    unsafe { Monotone::<B>::_decode(&*self.storage) }
  }
}

/// The private interface of an `Encodable` type. Allows the implementation to
/// be shared for different types.
trait EncodablePrivate<B: Bits> {
  /// Encodes a slice.
  unsafe fn _encode(&[B]) -> Result<Vec<u32>, super::Error>;

  /// Decodes a slice.
  unsafe fn _decode(&[u32]) -> Result<Vec<B>, super::Error>;

  /// Encodes a block with 128 or fewer elements. Returns pointer to storage.
  unsafe fn _encode_tail(_: *const B, _: *mut u32, usize, u32) -> *mut u32;

  /// Decodes a block with 128 or fewer elements. Returns pointer to storage.
  unsafe fn _decode_tail(_: *const u32, _: *mut B, usize, u32) -> *const u32;
}

/// Default is only to catch unimplemented types. Should not be reachable.
impl<B: Bits> EncodablePrivate<B> for Monotone<B> {
  default unsafe fn _encode(_: &[B]) -> Result<Vec<u32>, super::Error> {
    Err(super::Error::new("Encodable not implemented for this type"))
  }

  default unsafe fn _decode(_: &[u32]) -> Result<Vec<B>, super::Error> {
    Err(super::Error::new("Encodable not implemented for this type"))
  }

  default unsafe fn _encode_tail(_: *const B, _: *mut u32, _: usize, _: u32) -> *mut u32 {
    panic!("Encodable not implemented for this type");
  }

  default unsafe fn _decode_tail(_: *const u32, _: *mut B, _: usize, _: u32) -> *const u32 {
    panic!("Encodable not implemented for this type");
  }
}

macro_rules! encodable_unsigned {
  ($(($ty: ident: $step: expr,
      $enc: ident, $dec: ident,
      $enc_simd: ident, $dec_simd: ident,
      $enc_delta: ident))*) => ($(
    impl EncodablePrivate<$ty> for Monotone<$ty> {
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
          let length: usize = ((n_blks - (1 << a)) >> (a + 1)) + 1;
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
            s_ptr = s_ptr.offset(4 * l_wd as isize);
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

      unsafe fn _decode(storage: &[u32]) -> Result<Vec<$ty>, super::Error> {
        // Nothing to do
        if storage.is_empty() { return Ok(Vec::new()) }

        // Internal representation of ty
        let ty_wd: u32 = $ty::width();
        let ty_wrd: usize = utility::words_for_bits(ty_wd);

        // Read Monotone header
        let n_blks: usize = (storage[0] >> 2) as usize;
        let mut output: Vec<$ty> = Vec::with_capacity((n_blks + 1) << 7);

        // Length of index header
        let n_lvls: u32 = n_blks.bits();
        let base_wd: u32  = ty_wd.bits();
        let mut h_words: usize = 0;
        for a in 0..n_lvls {
          let len: usize = ((n_blks - (1 << a)) >> (a + 1)) + 1;
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
          s_ptr = s_ptr.offset(4 * e_wd as isize);

          let mut acc: $ty = *(s_ptr as *const $ty);
          s_ptr = s_ptr.offset(ty_wrd as isize);

          for _ in 0..128 {
            acc = acc.wrapping_add(*o_ptr);
            *o_ptr = acc;
            o_ptr = o_ptr.offset(1);
          }
        }

        // Final block
        let e_wd: u32 = *s_ptr & E_WIDTH;
        let left: usize = ((*s_ptr & E_COUNT) >> 7) as usize;
        s_ptr = s_ptr.offset(1);

        s_ptr = Monotone::<$ty>::_decode_tail(s_ptr, o_ptr, left, e_wd);

        let mut acc: $ty = *(s_ptr as *const $ty);
        for _ in 0..left {
          acc = acc.wrapping_add(*o_ptr);
          *o_ptr = acc;
          o_ptr = o_ptr.offset(1);
        }

        // Set the length of output AFTER everything is initialized
        output.set_len((n_blks << 7) + left);
        Ok(output)
      }

      unsafe fn _encode_tail(c_ptr: *const $ty,
                             s_ptr: *mut u32,
                             e_cnt: usize,
                             e_wd: u32) -> *mut u32 {
        // Encode a run of 128 integers and return
        if e_cnt == 128 {
          mayda_codec::$enc_simd[e_wd as usize](c_ptr, s_ptr);
          return s_ptr.offset(4 * e_wd as isize)
        }

        let mut c_ptr: *const $ty = c_ptr;
        let mut s_ptr: *mut u32 = s_ptr;

        // Encode a short run and return
        if e_cnt < $step {
          *s_ptr = 0;
          let mut s_bits: u32 = 32;
          let mut i_bits: u32;
          for a in 0..e_cnt {
            i_bits = e_wd;

            // Encode in the available space
            let lsft = 32 - s_bits;
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
          s_ptr = s_ptr.offset((bits / 32) as isize);
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
            let lsft = 32 - s_bits;
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

      unsafe fn _decode_tail(s_ptr: *const u32,
                             o_ptr: *mut $ty,
                             e_cnt: usize,
                             e_wd: u32) -> *const u32 {
        // Decode a run of 128 integers and return
        if e_cnt == 128 {
          mayda_codec::$dec_simd[e_wd as usize](s_ptr, o_ptr);
          return s_ptr.offset(4 * e_wd as isize)
        }

        let mut s_ptr: *const u32 = s_ptr;
        let mut o_ptr: *mut $ty = o_ptr;

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
          s_ptr = s_ptr.offset((bits / 32) as isize);
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

#[cfg(target_pointer_width = "32")]
impl EncodablePrivate<usize> for Monotone<usize> {
  #[inline]
  unsafe fn _encode(storage: &[usize]) -> Result<Vec<u32>, super::Error> {
    Monotone::<u32>::_encode(mem::transmute(storage))
  }

  #[inline]
  unsafe fn _decode(storage: &[u32]) -> Result<Vec<usize>, super::Error> {
    let scratch: Vec<u32> = try!(Monotone::<u32>::_decode(storage));
    Ok(mem::transmute(scratch))
  }
}

#[cfg(target_pointer_width = "64")]
impl EncodablePrivate<usize> for Monotone<usize> {
  #[inline]
  unsafe fn _encode(storage: &[usize]) -> Result<Vec<u32>, super::Error> {
    Monotone::<u64>::_encode(mem::transmute(storage))
  }

  #[inline]
  unsafe fn _decode(storage: &[u32]) -> Result<Vec<usize>, super::Error> {
    let scratch: Vec<u64> = try!(Monotone::<u64>::_decode(storage));
    Ok(mem::transmute(scratch))
  }
}

macro_rules! encodable_signed {
  ($(($it: ident: $ut: ident, $enc_delta: ident))*) => ($(
    impl EncodablePrivate<$it> for Monotone<$it> {
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
          let length: usize = ((n_blks - (1 << a)) >> (a + 1)) + 1;
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
            s_ptr = s_ptr.offset(4 * l_wd as isize);
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
      unsafe fn _decode(storage: &[u32]) -> Result<Vec<$it>, super::Error> {
        let scratch: Vec<$ut> = try!(Monotone::<$ut>::_decode(storage));
        Ok(mem::transmute(scratch))
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

#[cfg(target_pointer_width = "32")]
impl EncodablePrivate<isize> for Monotone<isize> {
  #[inline]
  unsafe fn _encode(storage: &[isize]) -> Result<Vec<u32>, super::Error> {
    Monotone::<i32>::_encode(mem::transmute(storage))
  }

  #[inline]
  unsafe fn _decode(storage: &[u32]) -> Result<Vec<isize>, super::Error> {
    let scratch: Vec<u32> = try!(Monotone::<u32>::_decode(storage));
    Ok(mem::transmute(scratch))
  }
}

#[cfg(target_pointer_width = "64")]
impl EncodablePrivate<isize> for Monotone<isize> {
  #[inline]
  unsafe fn _encode(storage: &[isize]) -> Result<Vec<u32>, super::Error> {
    Monotone::<i64>::_encode(mem::transmute(storage))
  }

  #[inline]
  unsafe fn _decode(storage: &[u32]) -> Result<Vec<isize>, super::Error> {
    let scratch: Vec<u64> = try!(Monotone::<u64>::_decode(storage));
    Ok(mem::transmute(scratch))
  }
}

////////////////////////////////////////////////////////////////////////////////
// Implementations of Access
////////////////////////////////////////////////////////////////////////////////

/// The private interface of an `Access` type. Allows the implementation to be
/// shared for different types.
trait AccessPrivate<Idx> {
  /// The type returned by the access operation.
  type Output;

  /// The method for the access `foo.access(bar)` operation.
  unsafe fn _access(&[u32], Idx) -> Self::Output;
}

macro_rules! access_default {
  ($(($idx: ty, $output: ty))*) => ($(
    impl<B: Bits> AccessPrivate<$idx> for Monotone<B> {
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
    impl<B: Bits> Access<$idx> for Monotone<B> {
      type Output = $output;

      #[inline]
      fn access(&self, index: $idx) -> $output {
        unsafe { Monotone::<B>::_access(&*self.storage, index) }
      }
    }
  )*)
}

access!{
  (usize, B)
  (ops::Range<usize>, Vec<B>)
  (ops::RangeFrom<usize>, Vec<B>)
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
    self.decode().unwrap()
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

/// Calculates the offset in words to the start of the block. Not intended to
/// be used outside the implementation of `Access`.
fn words_to_block(n_blks: usize, blk: usize, ty_wd: u32, s_head: *const u32) -> usize {
  let ty_wrd: usize = utility::words_for_bits(ty_wd);

  // Find the block containing the index
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
      let len: usize = ((n_blks - (1 << lvl)) >> (lvl + 1)) + 1;
      lvl_head += utility::words_for_bits(l_wd * len as u32);
      lvl += 1;
    }
    w_idx >>= shift;

    let l_wd: u32 = base_wd + lvl;
    let len: usize = ((n_blks - (1 << lvl)) >> (lvl + 1)) + 1;
    unsafe {
      s_ptr = s_head.offset(lvl_head as isize);
      if (w_idx & !127) + 128 <= len {
        // Width encoded using SIMD
        let l_bits: u32 = (w_idx as u32 / 2) * l_wd;
        let w_bits: u32 = 64 - (l_bits & 63);

        let mut w_ptr: *const u64 = s_ptr as *const u64;
        w_ptr = w_ptr.offset(((w_idx as u32 & 1) + (l_bits / 64) * 2) as isize);

        output = *w_ptr >> (64 - w_bits);
        if l_wd > w_bits {
          w_ptr = w_ptr.offset(2);
          output |= *w_ptr << w_bits;
        }
      } else {
        // Width encoded using u32
        let l_bits: u32 = w_idx as u32 * l_wd;
        let mut s_bits: u32 = 32 - (l_bits & 31);
        let mut o_bits: u32 = l_wd;

        s_ptr = s_ptr.offset((l_bits / 32) as isize);

        output = (*s_ptr >> (32 - s_bits)) as u64;
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
        let len: usize = ((n_blks - (1 << lvl)) >> (lvl + 1)) + 1;
        lvl_head += utility::words_for_bits(l_wd * len as u32);
        lvl += 1;
      }
      w_idx >>= shift;

      let l_wd: u32 = base_wd + lvl;
      let len: usize = ((n_blks - (1 << lvl)) >> (lvl + 1)) + 1;
      unsafe {
        s_ptr = s_head.offset(lvl_head as isize);
        if (w_idx & !127) + 128 <= len {
          // Width encoded using SIMD
          let l_bits: u32 = (w_idx as u32 / 2) * l_wd;
          let w_bits: u32 = 64 - (l_bits & 63);

          let mut w_ptr: *const u64 = s_ptr as *const u64;
          w_ptr = w_ptr.offset(((w_idx as u32 & 1) + (l_bits / 64) * 2) as isize);

          output = *w_ptr >> (64 - w_bits);
          if l_wd > w_bits {
            w_ptr = w_ptr.offset(2);
            output |= *w_ptr << w_bits;
          }
        } else {
          // Width encoded using u32
          let bits: u32 = w_idx as u32 * l_wd;
          let mut s_bits: u32 = 32 - (bits & 31);
          let mut o_bits: u32 = l_wd;

          s_ptr = s_ptr.offset((bits / 32) as isize);

          output = (*s_ptr >> (32 - s_bits)) as u64;
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
    wrd_to_blk = blk * (1 + ty_wrd) + 4 * wrd_to_blk;
  }

  // Include the header words
  wrd_to_blk += lvl_head;
  for a in lvl..n_blks.bits() {
    let l_wd: u32 = base_wd + a;
    let len: usize = ((n_blks - (1 << a)) >> (a + 1)) + 1;
    wrd_to_blk += utility::words_for_bits(l_wd * len as u32);
  }

  wrd_to_blk
}

macro_rules! access_unsigned {
  ($(($ty: ident: $step: expr, $dec: ident, $dec_simd: ident))*) => ($(
    impl AccessPrivate<usize> for Monotone<$ty> {
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
        let ty_wd: u32 = $ty::width();
        let mut s_ptr: *const u32 = storage.as_ptr();
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

    impl AccessPrivate<ops::Range<usize>> for Monotone<$ty> {
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
        let ty_wd: u32 = $ty::width();
        let ty_wrd: usize = utility::words_for_bits(ty_wd);
        let mut s_ptr: *const u32 = storage.as_ptr();
        let wrd_to_blk: usize = words_to_block(n_blks, s_blk, ty_wd, s_ptr);

        // Prepare return variable
        let mut output: Vec<$ty> = Vec::with_capacity((e_blk - s_blk + 1) << 7);
        let mut o_ptr: *mut $ty = output.as_mut_ptr();

        // Start block known, decode the range
        s_ptr = storage.as_ptr().offset(wrd_to_blk as isize);

        // Block size is known for all but the final block
        for _ in 0..(e_blk - s_blk) {
          // Find the width of the block
          let e_wd: u32 = *s_ptr & E_WIDTH;
          s_ptr = s_ptr.offset(1);

          // Decode the block
          mayda_codec::$dec_simd[e_wd as usize](s_ptr, o_ptr);
          s_ptr = s_ptr.offset(4 * e_wd as isize);

          let mut acc: $ty = *(s_ptr as *const $ty);
          s_ptr = s_ptr.offset(ty_wrd as isize);

          for _ in 0..128 {
            acc = acc.wrapping_add(*o_ptr);
            *o_ptr = acc;
            o_ptr = o_ptr.offset(1);
          }
        }

        // Final block
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
          return Vec::new();
        }

        // Decode final block
        s_ptr = Monotone::<$ty>::_decode_tail(s_ptr, o_ptr, left, e_wd);

        let mut acc: $ty = *(s_ptr as *const $ty);
        for _ in 0..left {
          acc = acc.wrapping_add(*o_ptr);
          *o_ptr = acc;
          o_ptr = o_ptr.offset(1);
        }

        // Shift the entries into the desired range
        let sft: usize = range.start - (s_blk << 7);
        let src: *const $ty = output.as_ptr().offset(sft as isize);
        let snk: *mut $ty = output.as_mut_ptr();
        ptr::copy(src, snk, range.end - range.start);
        output.set_len(range.end - range.start);

        output
      }
    }

    impl AccessPrivate<ops::RangeFrom<usize>> for Monotone<$ty> {
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
        let ty_wd: u32 = $ty::width();
        let ty_wrd: usize = utility::words_for_bits(ty_wd);
        let mut s_ptr: *const u32 = storage.as_ptr();
        let wrd_to_blk: usize = words_to_block(n_blks, s_blk, ty_wd, s_ptr);

        // Prepare return variable
        let mut output: Vec<$ty> = Vec::with_capacity((n_blks - s_blk + 1) << 7);
        let mut o_ptr: *mut $ty = output.as_mut_ptr();

        // Start block known, decode the range
        s_ptr = storage.as_ptr().offset(wrd_to_blk as isize);

        // Block size is known for all but the final block
        for _ in 0..(n_blks - s_blk) {
          // Find the width of the block
          let e_wd: u32 = *s_ptr & E_WIDTH;
          s_ptr = s_ptr.offset(1);

          // Decode the block
          mayda_codec::$dec_simd[e_wd as usize](s_ptr, o_ptr);
          s_ptr = s_ptr.offset(4 * e_wd as isize);

          let mut acc: $ty = *(s_ptr as *const $ty);
          s_ptr = s_ptr.offset(ty_wrd as isize);

          for _ in 0..128 {
            acc = acc.wrapping_add(*o_ptr);
            *o_ptr = acc;
            o_ptr = o_ptr.offset(1);
          }
        }

        // Final block
        let e_wd: u32 = *s_ptr & E_WIDTH;
        let left: usize = ((*s_ptr & E_COUNT) >> 7) as usize;
        s_ptr = s_ptr.offset(1);

        // Check a lower bound on the length
        let len: usize = (n_blks << 7) + left;
        if range.start > len {
          panic!(format!("range start is {} but length is {}", range.start, len))
        }
        if range.start == len {
          return Vec::new();
        }

        // Decode final block
        s_ptr = Monotone::<$ty>::_decode_tail(s_ptr, o_ptr, left, e_wd);

        let mut acc: $ty = *(s_ptr as *const $ty);
        for _ in 0..left {
          acc = acc.wrapping_add(*o_ptr);
          *o_ptr = acc;
          o_ptr = o_ptr.offset(1);
        }

        // Shift the entries into the desired range
        let sft: usize = range.start - (s_blk << 7);
        let src: *const $ty = output.as_ptr().offset(sft as isize);
        let snk: *mut $ty = output.as_mut_ptr();
        ptr::copy(src, snk, len - range.start);
        output.set_len(len - range.start);

        output
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
    impl AccessPrivate<usize> for Monotone<$it> {
      #[inline]
      unsafe fn _access(storage: &[u32], index: usize) -> $it {
        Monotone::<$ut>::_access(storage, index) as $it
      }
    }

    impl AccessPrivate<ops::Range<usize>> for Monotone<$it> {
      #[inline]
      unsafe fn _access(storage: &[u32], range: ops::Range<usize>) -> Vec<$it> {
        mem::transmute(Monotone::<$ut>::_access(storage, range))
      }
    }

    impl AccessPrivate<ops::RangeFrom<usize>> for Monotone<$it> {
      #[inline]
      unsafe fn _access(storage: &[u32], range: ops::RangeFrom<usize>) -> Vec<$it> {
        mem::transmute(Monotone::<$ut>::_access(storage, range))
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
