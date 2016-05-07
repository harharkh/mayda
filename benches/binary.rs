// Copyright 2016 Jeremy Mason
//
// Licensed under the MIT license <LICENSE or
// http://opensource.org/licenses/MIT>. This file may not be copied, modified,
// or distributed except according to those terms.

#![feature(test)]

#![allow(non_snake_case)]

extern crate pfor;
extern crate test;

use pfor::utility::Encodable;
use pfor::binary::Binary;
use test::Bencher;

macro_rules! encode_bench {
  ($(($t: ty: $value: expr, $length: expr, $name: ident))*) => ($(
    #[bench]
    fn $name(b: &mut Bencher) {
      let mut bin = Binary::new();
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
}

macro_rules! decode_bench {
  ($(($t: ty: $value: expr, $length: expr, $name: ident))*) => ($(
    #[bench]
    fn $name(b: &mut Bencher) {
      let mut bin = Binary::new();
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
}

macro_rules! vector_bench {
  ($(($t: ty: $value: expr, $length: expr, $name: ident))*) => ($(
    #[bench]
    fn $name(b: &mut Bencher) {
      let mut input: Vec<$t> = Vec::new();
      b.iter(|| {
        input = vec![$value; $length];
      });
      let output = vec![$value; $length];
      assert_eq!(input, output);
    }
  )*)
}

vector_bench!{
  (u32: 1, 32, vt_u32_1_32)
  (u32: 3, 65536, vt_u32_3_65536)
  (u32: std::u32::MAX, 65536, vt_u32_MAX_65536)
}
