// Copyright 2016 Jeremy Mason
//
// Licensed under the MIT license <LICENSE or
// http://opensource.org/licenses/MIT>. This file may not be copied, modified,
// or distributed except according to those terms.

#![feature(test)]
#![feature(inclusive_range_syntax)]

#![allow(non_snake_case)]

extern crate mayda;
extern crate test;

use mayda::utility::{Access, Encodable};
use mayda::bit_packed::BitPacked;
use test::Bencher;

macro_rules! encode_bench {
  ($(($t: ty: $value: expr, $length: expr, $name: ident))*) => ($(
    #[bench]
    fn $name(b: &mut Bencher) {
      let mut bin = BitPacked::new();
      let input: Vec<$t> = vec![$value; $length];
      b.iter(|| {
        bin.encode(&input).unwrap();
      });
      let output = bin.decode().unwrap();
      assert_eq!(input, output);
    }
  )*)
}

encode_bench!{
  (u32: 1, 15, en_u32_1_15)
  (u32: 1, 16, en_u32_1_16)
  (u32: 3, 31, en_u32_3_31)
  (u32: 3, 32, en_u32_3_32)
  (u32: 5, 127, en_u32_5_127)
  (u32: 5, 128, en_u32_5_128)
  (u32: 7, 32768, en_u32_7_32768)
  (u8: std::u8::MAX / 2, 32768, en_u8_MAX2_32768)
  (u16: std::u16::MAX / 2, 32768, en_u16_MAX2_32768)
  (u32: std::u32::MAX / 2, 32768, en_u32_MAX2_32768)
  (u64: std::u64::MAX / 2, 32768, en_u64_MAX2_32768)
  (i32: 1, 15, en_i32_1_15)
  (i32: 1, 16, en_i32_1_16)
  (i32: 3, 31, en_i32_3_31)
  (i32: 3, 32, en_i32_3_32)
  (i32: 5, 127, en_i32_5_127)
  (i32: 5, 128, en_i32_5_128)
  (i32: 7, 32768, en_i32_7_32768)
  (i8: std::i8::MAX / 2, 32768, en_i8_MAX2_32768)
  (i16: std::i16::MAX / 2, 32768, en_i16_MAX2_32768)
  (i32: std::i32::MAX / 2, 32768, en_i32_MAX2_32768)
  (i64: std::i64::MAX / 2, 32768, en_i64_MAX2_32768)
}

macro_rules! decode_bench {
  ($(($t: ty: $value: expr, $length: expr, $name: ident))*) => ($(
    #[bench]
    fn $name(b: &mut Bencher) {
      let mut bin = BitPacked::new();
      let input: Vec<$t> = vec![$value; $length];
      bin.encode(&input).unwrap();
      let mut output = Vec::new();
      b.iter(|| {
        output = bin.decode().unwrap();
      });
      assert_eq!(input, output);
    }
  )*)
} 

decode_bench!{
  (u32: 2, 15, de_u32_2_15)
  (u32: 2, 16, de_u32_2_16)
  (u32: 4, 31, de_u32_4_31)
  (u32: 4, 32, de_u32_4_32)
  (u32: 6, 127, de_u32_6_127)
  (u32: 6, 128, de_u32_6_128)
  (u32: 8, 32768, de_u32_8_32768)
  (u8: std::u8::MAX / 2, 32768, de_u8_MAX2_32768)
  (u16: std::u16::MAX / 2, 32768, de_u16_MAX2_32768)
  (u32: std::u32::MAX / 2, 32768, de_u32_MAX2_32768)
  (u64: std::u64::MAX / 2, 32768, de_u64_MAX2_32768)
  (i32: 2, 15, de_i32_2_15)
  (i32: 2, 16, de_i32_2_16)
  (i32: 4, 31, de_i32_4_31)
  (i32: 4, 32, de_i32_4_32)
  (i32: 6, 127, de_i32_6_127)
  (i32: 6, 128, de_i32_6_128)
  (i32: 8, 32768, de_i32_8_32768)
  (i8: std::i8::MAX / 2, 32768, de_i8_MAX2_32768)
  (i16: std::i16::MAX / 2, 32768, de_i16_MAX2_32768)
  (i32: std::i32::MAX / 2, 32768, de_i32_MAX2_32768)
  (i64: std::i64::MAX / 2, 32768, de_i64_MAX2_32768)
}

macro_rules! indexing_bench {
  ($(($t: ty: $max: expr, $idx: expr, $name: ident))*) => ($(
    #[bench]
    fn $name(b: &mut Bencher) {
      let mut bin = BitPacked::new();
      let input: Vec<$t> = (0...$max).collect();
      bin.encode(&input).unwrap();
      let mut v: $t = 0;
      b.iter(|| {
        v = bin.access($idx);
      });
      assert_eq!(v, $idx as $t);
    }
  )*)
}

indexing_bench!{
  (u8: 127, 127, idx_u8_127_127)
  (u16: 32767, 32767, idx_u16_32767_32767)
  (u32: 65535, 65535, idx_u32_65535_65535)
  (u64: 65535, 65535, idx_u64_65535_65535)
  (i8: 127, 127, idx_i8_127_127)
  (i16: 32767, 32767, idx_i16_32767_32767)
  (i32: 65535, 65535, idx_i32_65535_65535)
  (i64: 65535, 65535, idx_i64_65535_65535)
}

macro_rules! range_bench {
  ($(($t: ty: $max: expr, $idx: expr, $name: ident))*) => ($(
    #[bench]
    fn $name(b: &mut Bencher) {
      let mut bin = BitPacked::new();
      let input: Vec<$t> = (0...$max).collect();
      bin.encode(&input).unwrap();
      let mut vec: Vec<$t> = Vec::new();
      b.iter(|| {
        vec = bin.access($idx);
      });
      assert_eq!(&input[$idx], &vec[..]);
    }
  )*)
}

range_bench!{
  (u8: 127, 0..10, r_u8_127_0_10)
  (u16: 32767, 0..10, r_u16_32767_0_10)
  (u32: 65535, 0..10, r_u32_65535_0_10)
  (u64: 65535, 0..10, r_u64_65535_0_10)
  (i8: 127, 0..10, r_i8_127_0_10)
  (i16: 32767, 0..10, r_i16_32767_0_10)
  (i32: 65535, 0..10, r_i32_65535_0_10)
  (i64: 65535, 0..10, r_i64_65535_0_10)
}
