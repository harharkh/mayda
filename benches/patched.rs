// Copyright 2016 Jeremy Mason
//
// Licensed under the MIT license <LICENSE or
// http://opensource.org/licenses/MIT>. This file may not be copied, modified,
// or distributed except according to those terms.

#![feature(test)]
#![feature(inclusive_range_syntax)]

#![allow(non_snake_case)]

extern crate mayda;
extern crate rand;
extern crate test;

use mayda::utility::{Access, Encodable};
use mayda::patched::Patched;
use rand::distributions::{IndependentSample, Range};
use test::Bencher;

fn random_outliers<T>(min1: T, max1: T, min2: T, max2: T) -> Vec<T>
  where T: PartialOrd + rand::distributions::range::SampleRange {
  let length1: usize = 16384;
  let length2: usize = 1024;

  let mut output: Vec<T> = Vec::new();
  let val = Range::new(min1, max1);
  let mut rng = rand::thread_rng();
  for _ in 0..length1 {
    output.push(val.ind_sample(&mut rng));
  }
  let idx = Range::new(0, length1);
  let val = Range::new(min2, max2);
  for _ in 0..length2 {
    output[idx.ind_sample(&mut rng)] = val.ind_sample(&mut rng);
  }
  output
}

macro_rules! encode_bench {
  ($(($t: ty: $value: expr, $length: expr, $name: ident))*) => ($(
    #[bench]
    fn $name(b: &mut Bencher) {
      let mut bin = Patched::new();
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
  (i32: 1, 15, en_i32_1_15)
  (i32: 1, 16, en_i32_1_16)
  (i32: 3, 31, en_i32_3_31)
  (i32: 3, 32, en_i32_3_32)
  (i32: 5, 127, en_i32_5_127)
  (i32: 5, 128, en_i32_5_128)
  (i32: 7, 32768, en_i32_7_32768)
}

macro_rules! random_encode_bench {
  ($(($t: ty:
      $min1: expr, $max1: expr,
      $min2: expr, $max2: expr,
      $name: ident))*) => ($(
    #[bench]
    fn $name(b: &mut Bencher) {
      let mut bin = Patched::new();
      let input: Vec<$t> = random_outliers($min1, $max1, $min2, $max2);
      b.iter(|| {
        bin.encode(&input).unwrap();
      });
      let output = bin.decode().unwrap();
      assert_eq!(input, output);
    }
  )*)
}

random_encode_bench!{
  (u8: 0, 16, 16, std::u8::MAX, ren_u8_16284_1024)
  (u16: 0, 32, 32, std::u16::MAX, ren_u16_16284_1024)
  (u32: 0, 64, 64, std::u32::MAX, ren_u32_16284_1024)
  (u64: 0, 128, 128, std::u64::MAX, ren_u64_16284_1024)
  (i8: -16, 16, std::i8::MIN, std::i8::MAX, ren_i8_16284_1024)
  (i16: -32, 32, std::i16::MIN, std::i16::MAX, ren_i16_16284_1024)
  (i32: -64, 64, std::i32::MIN, std::i32::MAX, ren_i32_16284_1024)
  (i64: -128, 128, std::i64::MIN, std::i64::MAX, ren_i64_16284_1024)
}

macro_rules! decode_bench {
  ($(($t: ty: $value: expr, $length: expr, $name: ident))*) => ($(
    #[bench]
    fn $name(b: &mut Bencher) {
      let mut bin = Patched::new();
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
  (i32: 2, 15, de_i32_2_15)
  (i32: 2, 16, de_i32_2_16)
  (i32: 4, 31, de_i32_4_31)
  (i32: 4, 32, de_i32_4_32)
  (i32: 6, 127, de_i32_6_127)
  (i32: 6, 128, de_i32_6_128)
  (i32: 8, 32768, de_i32_8_32768)
}

macro_rules! random_decode_bench {
  ($(($t: ty:
      $min1: expr, $max1: expr,
      $min2: expr, $max2: expr,
      $name: ident))*) => ($(
    #[bench]
    fn $name(b: &mut Bencher) {
      let mut bin = Patched::new();
      let input: Vec<$t> = random_outliers($min1, $max1, $min2, $max2);
      bin.encode(&input).unwrap();
      let mut output = Vec::new();
      b.iter(|| {
        output = bin.decode().unwrap();
      });
      assert_eq!(input, output);
    }
  )*)
}

random_decode_bench!{
  (u8: 0, 16, 16, std::u8::MAX, rde_u8_16284_1024)
  (u16: 0, 32, 32, std::u16::MAX, rde_u16_16284_1024)
  (u32: 0, 64, 64, std::u32::MAX, rde_u32_16284_1024)
  (u64: 0, 128, 128, std::u64::MAX, rde_u64_16284_1024)
  (i8: -16, 16, std::i8::MIN, std::i8::MAX, rde_i8_16284_1024)
  (i16: -32, 32, std::i16::MIN, std::i16::MAX, rde_i16_16284_1024)
  (i32: -64, 64, std::i32::MIN, std::i32::MAX, rde_i32_16284_1024)
  (i64: -128, 128, std::i64::MIN, std::i64::MAX, rde_i64_16284_1024)
}

macro_rules! indexing_bench {
  ($(($t: ty: $max: expr, $idx: expr, $name: ident))*) => ($(
    #[bench]
    fn $name(b: &mut Bencher) {
      let mut bin = Patched::new();
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
      let mut bin = Patched::new();
      let input: Vec<$t> = (0...$max).collect(); bin.encode(&input).unwrap();
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
