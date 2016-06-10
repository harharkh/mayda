// Copyright 2016 Jeremy Mason
//
// Licensed under the MIT license <LICENSE or
// http://opensource.org/licenses/MIT>. This file may not be copied, modified,
// or distributed except according to those terms.

#![feature(inclusive_range_syntax)]

#![allow(non_snake_case)]

extern crate mayda;
extern crate rand;

use mayda::{Access, Encodable, Monotone};
use rand::distributions::{IndependentSample, Range};

fn rand_increasing<T>(min: T, max: T, length: usize) -> Vec<T>
  where T: Ord + rand::distributions::range::SampleRange {
  let mut output: Vec<T> = Vec::with_capacity(length);
  let val = Range::new(min, max);
  let mut rng = rand::thread_rng();
  for _ in 0..length {
    output.push(val.ind_sample(&mut rng));
  }
  output.sort();
  output
}

macro_rules! random_values {
  ($(($t: ty: $min: expr, $max: expr, $length: expr, $name: ident))*) => ($(
    #[test]
    fn $name() {
      let mut bin = Monotone::new();
      let input: Vec<$t> = rand_increasing($min, $max, $length);
      println!("{:?}", input);
      bin.encode(&input).unwrap();
      for a in bin.storage() { println!("{:032b}", a); }
      let output = bin.decode().unwrap();
      println!("{:?}", output);
      assert_eq!(input, output);
    }
  )*)
}

random_values!{
  (u8: 0, 16, 0, rv_u8_0_16_0)
  (u8: 0, 16, 1, rv_u8_0_16_1)
  (u8: 0, 16, 2, rv_u8_0_16_2)
  (u8: 0, 16, 3, rv_u8_0_16_3)
  (u8: 0, 16, 4, rv_u8_0_16_4)
  (u8: 0, 16, 5, rv_u8_0_16_5)
  (u8: 0, 16, 7, rv_u8_0_16_7)
  (u8: 0, 16, 8, rv_u8_0_16_8)
  (u8: 0, 16, 9, rv_u8_0_16_9)
  (u8: 0, 16, 15, rv_u8_0_16_15)
  (u8: 0, 16, 16, rv_u8_0_16_16)
  (u8: 0, 16, 17, rv_u8_0_16_17)
  (u8: 0, 16, 31, rv_u8_0_16_31)
  (u8: 0, 16, 32, rv_u8_0_16_32)
  (u8: 0, 16, 33, rv_u8_0_16_33)
  (u8: 0, 64, 127, rv_u8_0_64_127)
  (u8: 0, 64, 128, rv_u8_0_64_128)
  (u8: 0, 64, 129, rv_u8_0_64_129)
  (u8: 0, 128, 511, rv_u8_0_128_511)
  (u8: 0, 128, 512, rv_u8_0_128_512)
  (u8: 0, 128, 513, rv_u8_0_128_513)
  (u8: 0, std::u8::MAX, 1024, rv_u8_0_MAX_1024)
  (i8: -8, 8, 0, rv_i8_8_8_0)
  (i8: -8, 8, 1, rv_i8_8_8_1)
  (i8: -8, 8, 2, rv_i8_8_8_2)
  (i8: -8, 8, 3, rv_i8_8_8_3)
  (i8: -8, 8, 4, rv_i8_8_8_4)
  (i8: -8, 8, 5, rv_i8_8_8_5)
  (i8: -8, 8, 7, rv_i8_8_8_7)
  (i8: -8, 8, 8, rv_i8_8_8_8)
  (i8: -8, 8, 9, rv_i8_8_8_9)
  (i8: -8, 8, 15, rv_i8_8_8_15)
  (i8: -8, 8, 16, rv_i8_8_8_16)
  (i8: -8, 8, 17, rv_i8_8_8_17)
  (i8: -8, 8, 31, rv_i8_8_8_31)
  (i8: -8, 8, 32, rv_i8_8_8_32)
  (i8: -8, 8, 33, rv_i8_8_8_33)
  (i8: -32, 32, 127, rv_i8_32_32_127)
  (i8: -32, 32, 128, rv_i8_32_32_128)
  (i8: -32, 32, 129, rv_i8_32_32_129)
  (i8: -64, 64, 511, rv_i8_64_64_511)
  (i8: -64, 64, 512, rv_i8_64_64_512)
  (i8: -64, 64, 513, rv_i8_64_64_513)
  (i8: std::i8::MIN, std::i8::MAX, 1024, rv_i8_MIN_MAX_1024)
}

random_values!{
  (u16: 0, 16, 0, rv_u16_0_16_0)
  (u16: 0, 16, 1, rv_u16_0_16_1)
  (u16: 0, 16, 2, rv_u16_0_16_2)
  (u16: 0, 16, 3, rv_u16_0_16_3)
  (u16: 0, 16, 4, rv_u16_0_16_4)
  (u16: 0, 16, 5, rv_u16_0_16_5)
  (u16: 0, 16, 7, rv_u16_0_16_7)
  (u16: 0, 16, 8, rv_u16_0_16_8)
  (u16: 0, 16, 9, rv_u16_0_16_9)
  (u16: 0, 16, 15, rv_u16_0_16_15)
  (u16: 0, 16, 16, rv_u16_0_16_16)
  (u16: 0, 16, 17, rv_u16_0_16_17)
  (u16: 0, 16, 31, rv_u16_0_16_31)
  (u16: 0, 16, 32, rv_u16_0_16_32)
  (u16: 0, 16, 33, rv_u16_0_16_33)
  (u16: 0, 64, 127, rv_u16_0_64_127)
  (u16: 0, 64, 128, rv_u16_0_64_128)
  (u16: 0, 64, 129, rv_u16_0_64_129)
  (u16: 0, 128, 511, rv_u16_0_128_511)
  (u16: 0, 128, 512, rv_u16_0_128_512)
  (u16: 0, 128, 513, rv_u16_0_128_513)
  (u16: 0, std::u16::MAX, 1024, rv_u16_0_MAX_1024)
  (i16: -8, 8, 0, rv_i16_8_8_0)
  (i16: -8, 8, 1, rv_i16_8_8_1)
  (i16: -8, 8, 2, rv_i16_8_8_2)
  (i16: -8, 8, 3, rv_i16_8_8_3)
  (i16: -8, 8, 4, rv_i16_8_8_4)
  (i16: -8, 8, 5, rv_i16_8_8_5)
  (i16: -8, 8, 7, rv_i16_8_8_7)
  (i16: -8, 8, 8, rv_i16_8_8_8)
  (i16: -8, 8, 9, rv_i16_8_8_9)
  (i16: -8, 8, 15, rv_i16_8_8_15)
  (i16: -8, 8, 16, rv_i16_8_8_16)
  (i16: -8, 8, 17, rv_i16_8_8_17)
  (i16: -8, 8, 31, rv_i16_8_8_31)
  (i16: -8, 8, 32, rv_i16_8_8_32)
  (i16: -8, 8, 33, rv_i16_8_8_33)
  (i16: -32, 32, 127, rv_i16_32_32_127)
  (i16: -32, 32, 128, rv_i16_32_32_128)
  (i16: -32, 32, 129, rv_i16_32_32_129)
  (i16: -64, 64, 511, rv_i16_64_64_511)
  (i16: -64, 64, 512, rv_i16_64_64_512)
  (i16: -64, 64, 513, rv_i16_64_64_513)
  (i16: std::i16::MIN, std::i16::MAX, 1024, rv_i16_MIN_MAX_1024)
}

random_values!{
  (u32: 0, 16, 0, rv_u32_0_16_0)
  (u32: 0, 16, 1, rv_u32_0_16_1)
  (u32: 0, 16, 2, rv_u32_0_16_2)
  (u32: 0, 16, 3, rv_u32_0_16_3)
  (u32: 0, 16, 4, rv_u32_0_16_4)
  (u32: 0, 16, 5, rv_u32_0_16_5)
  (u32: 0, 16, 7, rv_u32_0_16_7)
  (u32: 0, 16, 8, rv_u32_0_16_8)
  (u32: 0, 16, 9, rv_u32_0_16_9)
  (u32: 0, 16, 15, rv_u32_0_16_15)
  (u32: 0, 16, 16, rv_u32_0_16_16)
  (u32: 0, 16, 17, rv_u32_0_16_17)
  (u32: 0, 16, 31, rv_u32_0_16_31)
  (u32: 0, 16, 32, rv_u32_0_16_32)
  (u32: 0, 16, 33, rv_u32_0_16_33)
  (u32: 0, 64, 127, rv_u32_0_64_127)
  (u32: 0, 64, 128, rv_u32_0_64_128)
  (u32: 0, 64, 129, rv_u32_0_64_129)
  (u32: 0, 128, 511, rv_u32_0_128_511)
  (u32: 0, 128, 512, rv_u32_0_128_512)
  (u32: 0, 128, 513, rv_u32_0_128_513)
  (u32: 0, std::u32::MAX, 1024, rv_u32_0_MAX_1024)
  (i32: -8, 8, 0, rv_i32_8_8_0)
  (i32: -8, 8, 1, rv_i32_8_8_1)
  (i32: -8, 8, 2, rv_i32_8_8_2)
  (i32: -8, 8, 3, rv_i32_8_8_3)
  (i32: -8, 8, 4, rv_i32_8_8_4)
  (i32: -8, 8, 5, rv_i32_8_8_5)
  (i32: -8, 8, 7, rv_i32_8_8_7)
  (i32: -8, 8, 8, rv_i32_8_8_8)
  (i32: -8, 8, 9, rv_i32_8_8_9)
  (i32: -8, 8, 15, rv_i32_8_8_15)
  (i32: -8, 8, 16, rv_i32_8_8_16)
  (i32: -8, 8, 17, rv_i32_8_8_17)
  (i32: -8, 8, 31, rv_i32_8_8_31)
  (i32: -8, 8, 32, rv_i32_8_8_32)
  (i32: -8, 8, 33, rv_i32_8_8_33)
  (i32: -32, 32, 127, rv_i32_32_32_127)
  (i32: -32, 32, 128, rv_i32_32_32_128)
  (i32: -32, 32, 129, rv_i32_32_32_129)
  (i32: -64, 64, 511, rv_i32_64_64_511)
  (i32: -64, 64, 512, rv_i32_64_64_512)
  (i32: -64, 64, 513, rv_i32_64_64_513)
  (i32: std::i32::MIN, std::i32::MAX, 1024, rv_i32_MIN_MAX_1024)
}

random_values!{
  (u64: 0, 16, 0, rv_u64_0_16_0)
  (u64: 0, 16, 1, rv_u64_0_16_1)
  (u64: 0, 16, 2, rv_u64_0_16_2)
  (u64: 0, 16, 3, rv_u64_0_16_3)
  (u64: 0, 16, 4, rv_u64_0_16_4)
  (u64: 0, 16, 5, rv_u64_0_16_5)
  (u64: 0, 16, 7, rv_u64_0_16_7)
  (u64: 0, 16, 8, rv_u64_0_16_8)
  (u64: 0, 16, 9, rv_u64_0_16_9)
  (u64: 0, 16, 15, rv_u64_0_16_15)
  (u64: 0, 16, 16, rv_u64_0_16_16)
  (u64: 0, 16, 17, rv_u64_0_16_17)
  (u64: 0, 16, 31, rv_u64_0_16_31)
  (u64: 0, 16, 32, rv_u64_0_16_32)
  (u64: 0, 16, 33, rv_u64_0_16_33)
  (u64: 0, 64, 127, rv_u64_0_64_127)
  (u64: 0, 64, 128, rv_u64_0_64_128)
  (u64: 0, 64, 129, rv_u64_0_64_129)
  (u64: 0, 128, 511, rv_u64_0_128_511)
  (u64: 0, 128, 512, rv_u64_0_128_512)
  (u64: 0, 128, 513, rv_u64_0_128_513)
  (u64: 0, std::u64::MAX, 1024, rv_u64_0_MAX_1024)
  (i64: -8, 8, 0, rv_i64_8_8_0)
  (i64: -8, 8, 1, rv_i64_8_8_1)
  (i64: -8, 8, 2, rv_i64_8_8_2)
  (i64: -8, 8, 3, rv_i64_8_8_3)
  (i64: -8, 8, 4, rv_i64_8_8_4)
  (i64: -8, 8, 5, rv_i64_8_8_5)
  (i64: -8, 8, 7, rv_i64_8_8_7)
  (i64: -8, 8, 8, rv_i64_8_8_8)
  (i64: -8, 8, 9, rv_i64_8_8_9)
  (i64: -8, 8, 15, rv_i64_8_8_15)
  (i64: -8, 8, 16, rv_i64_8_8_16)
  (i64: -8, 8, 17, rv_i64_8_8_17)
  (i64: -8, 8, 31, rv_i64_8_8_31)
  (i64: -8, 8, 32, rv_i64_8_8_32)
  (i64: -8, 8, 33, rv_i64_8_8_33)
  (i64: -32, 32, 127, rv_i64_32_32_127)
  (i64: -32, 32, 128, rv_i64_32_32_128)
  (i64: -32, 32, 129, rv_i64_32_32_129)
  (i64: -64, 64, 511, rv_i64_64_64_511)
  (i64: -64, 64, 512, rv_i64_64_64_512)
  (i64: -64, 64, 513, rv_i64_64_64_513)
  (i64: std::i64::MIN, std::i64::MAX, 1024, rv_i64_MIN_MAX_1024)
}

// Verify that methods provided by u64 or u32
random_values!{
  (usize: 0, std::usize::MAX, 1024, cv_usize_0_MAX_1024)
  (isize: std::isize::MIN, std::isize::MAX, 1024, cv_isize_MIN_MAX_1024)
}

macro_rules! increasing_values {
  ($(($t: ty: $min: expr, $max: expr, $name: ident))*) => ($(
    #[test]
    fn $name() {
      let mut bin = Monotone::new();
      let input: Vec<$t> = ($min...$max).collect();
      println!("{:?}", input);
      bin.encode(&input).unwrap();
      for a in bin.storage() { println!("{:032b}", a); }
      let output = bin.decode().unwrap();
      println!("{:?}", output);
      assert_eq!(input, output);
    }
  )*)
}

increasing_values!{
  (u8: 0, 255, iv_u8_0_255)
  (u16: 0, 255, iv_u16_0_255)
  (u32: 0, 255, iv_u32_0_255)
  (u64: 0, 255, iv_u64_0_255)
  (usize: 0, 255, iv_usize_0_255)
  (i8: -128, 127, iv_i8_128_127)
  (i16: -128, 127, iv_i16_128_127)
  (i32: -128, 127, iv_i32_128_127)
  (i64: -128, 127, iv_i64_128_127)
  (isize: -128, 127, iv_isize_128_127)
}

macro_rules! indexing {
  ($(($t: ty: $min: expr, $max: expr, $length: expr, $name: ident))*) => ($(
    #[test]
    fn $name() {
      let mut bin = Monotone::new();
      let input: Vec<$t> = rand_increasing($min, $max, $length);
      println!("{:?}", input);
      bin.encode(&input).unwrap();
      for a in bin.storage() { println!("{:032b}", a); }
      for a in 0..$length {
        let b = bin.access(a);
        println!("{} {}", input[a], b);
        assert_eq!(input[a], b);
      }
    }
  )*)
}

indexing!{
  (u8: 0, std::u8::MAX, 1024, idx_u8_0_MAX_1024)
  (u16: 0, std::u16::MAX, 1024, idx_u16_0_MAX_1024)
  (u32: 0, std::u32::MAX, 1024, idx_u32_0_MAX_1024)
  (u64: 0, std::u64::MAX, 1024, idx_u64_0_MAX_1024)
  (usize: 0, std::usize::MAX, 1024, idx_usize_0_MAX_1024)
  (i8: std::i8::MIN, std::i8::MAX, 1024, idx_i8_MIN_MAX_1024)
  (i16: std::i16::MIN, std::i16::MAX, 1024, idx_i16_MIN_MAX_1024)
  (i32: std::i32::MIN, std::i32::MAX, 1024, idx_i32_MIN_MAX_1024)
  (i64: std::i64::MIN, std::i64::MAX, 1024, idx_i64_MIN_MAX_1024)
  (isize: std::isize::MIN, std::isize::MAX, 1024, idx_isize_MIN_MAX_1024)
}

macro_rules! indexing_panic {
  ($(($t: ty: $length: expr, $idx: expr, $name: ident))*) => ($(
    #[test]
    #[should_panic]
    fn $name() {
      let mut bin = Monotone::new();
      let input: Vec<$t> = vec![0; $length];
      println!("{:?}", input);
      bin.encode(&input).unwrap();
      for a in bin.storage() { println!("{:032b}", a); }
      bin.access($idx);
    }
  )*)
}

indexing_panic!{
  (u8: 0, 1, idx_pan_u8_0_1)
  (u8: 1, 2, idx_pan_u8_1_2)
  (u8: 1, 128, idx_pan_u8_1_128)
  (u16: 0, 1, idx_pan_u16_0_1)
  (u16: 1, 2, idx_pan_u16_1_2)
  (u16: 1, 128, idx_pan_u16_1_128)
  (u32: 0, 1, idx_pan_u32_0_1)
  (u32: 1, 2, idx_pan_u32_1_2)
  (u32: 1, 128, idx_pan_u32_1_128)
  (u64: 0, 1, idx_pan_u64_0_1)
  (u64: 1, 2, idx_pan_u64_1_2)
  (u64: 1, 128, idx_pan_u64_1_128)
  (i8: 0, 1, idx_pan_i8_0_1)
  (i8: 1, 2, idx_pan_i8_1_2)
  (i8: 1, 128, idx_pan_i8_1_128)
  (i16: 0, 1, idx_pan_i16_0_1)
  (i16: 1, 2, idx_pan_i16_1_2)
  (i16: 1, 128, idx_pan_i16_1_128)
  (i32: 0, 1, idx_pan_i32_0_1)
  (i32: 1, 2, idx_pan_i32_1_2)
  (i32: 1, 128, idx_pan_i32_1_128)
  (i64: 0, 1, idx_pan_i64_0_1)
  (i64: 1, 2, idx_pan_i64_1_2)
  (i64: 1, 128, idx_pan_i64_1_128)
}

macro_rules! range {
  ($(($t: ty: $min: expr, $max: expr, $length: expr, $width: expr, $name: ident))*) => ($(
    #[test]
    fn $name() {
      let mut bin = Monotone::new();
      let input = rand_increasing($min, $max, $length);
      println!("{:?}", input);
      bin.encode(&input).unwrap();
      for a in bin.storage() { println!("{:032b}", a); }
      for a in 0..($length - $width) {
        let vec = bin.access(a..($width + a));
        println!("{:?} {:?}", &input[a..($width + a)], &vec[..]);
        assert_eq!(&input[a..($width + a)], &vec[..]);
      }
    }
  )*)
}

range!{
  (u8: 0, std::u8::MAX, 1024, 15, r_u8_0_MAX_1024_15)
  (u16: 0, std::u16::MAX, 1024, 15, r_u16_0_MAX_1024_15)
  (u32: 0, std::u32::MAX, 1024, 15, r_u32_0_MAX_1024_15)
  (u64: 0, std::u64::MAX, 1024, 15, r_u64_0_MAX_1024_15)
  (usize: 0, std::usize::MAX, 1024, 15, r_usize_0_MAX_1024_15)
  (i8: std::i8::MIN, std::i8::MAX, 1024, 15, r_i8_MIN_MAX_1024_15)
  (i16: std::i16::MIN, std::i16::MAX, 1024, 15, r_i16_MIN_MAX_1024_15)
  (i32: std::i32::MIN, std::i32::MAX, 1024, 15, r_i32_MIN_MAX_1024_15)
  (i64: std::i64::MIN, std::i64::MAX, 1024, 15, r_i64_MIN_MAX_1024_15)
  (isize: std::isize::MIN, std::isize::MAX, 1024, 15, r_isize_MIN_MAX_1024_15)
}

macro_rules! range_panic {
  ($(($t: ty: $length: expr, $range: expr, $name: ident))*) => ($(
    #[test]
    #[should_panic]
    fn $name() {
      let mut bin = Monotone::new();
      let input: Vec<$t> = vec![0; $length];
      println!("{:?}", input);
      bin.encode(&input).unwrap();
      for a in bin.storage() { println!("{:032b}", a); }
      bin.access($range);
    }
  )*)
}

range_panic!{
  (u8: 0, 0..1, r_pan_u8_0_0_1)
  (u8: 0, 1..1, r_pan_u8_0_1_1)
  (u8: 1, 0..2, r_pan_u8_1_0_2)
  (u8: 1, 2..2, r_pan_u8_1_2_2)
  (u8: 2, 1..0, r_pan_u8_2_1_0)
  (u8: 2, 127..128, r_pan_u8_2_127_128)
  (u8: 2, 128..129, r_pan_u8_2_128_129)
  (u16: 0, 0..1, r_pan_u16_0_0_1)
  (u16: 0, 1..1, r_pan_u16_0_1_1)
  (u16: 1, 0..2, r_pan_u16_1_0_2)
  (u16: 1, 2..2, r_pan_u16_1_2_2)
  (u16: 2, 1..0, r_pan_u16_2_1_0)
  (u16: 2, 127..128, r_pan_u16_2_127_128)
  (u16: 2, 128..129, r_pan_u16_2_128_129)
  (u32: 0, 0..1, r_pan_u32_0_0_1)
  (u32: 0, 1..1, r_pan_u32_0_1_1)
  (u32: 1, 0..2, r_pan_u32_1_0_2)
  (u32: 1, 2..2, r_pan_u32_1_2_2)
  (u32: 2, 1..0, r_pan_u32_2_1_0)
  (u32: 2, 127..128, r_pan_u32_2_127_128)
  (u32: 2, 128..129, r_pan_u32_2_128_129)
  (u64: 0, 0..1, r_pan_u64_0_0_1)
  (u64: 0, 1..1, r_pan_u64_0_1_1)
  (u64: 1, 0..2, r_pan_u64_1_0_2)
  (u64: 1, 2..2, r_pan_u64_1_2_2)
  (u64: 2, 1..0, r_pan_u64_2_1_0)
  (u64: 2, 127..128, r_pan_u64_2_127_128)
  (u64: 2, 128..129, r_pan_u64_2_128_129)
  (i8: 0, 0..1, r_pan_i8_0_0_1)
  (i8: 0, 1..1, r_pan_i8_0_1_1)
  (i8: 1, 0..2, r_pan_i8_1_0_2)
  (i8: 1, 2..2, r_pan_i8_1_2_2)
  (i8: 2, 1..0, r_pan_i8_2_1_0)
  (i8: 2, 127..128, r_pan_i8_2_127_128)
  (i8: 2, 128..129, r_pan_i8_2_128_129)
  (i16: 0, 0..1, r_pan_i16_0_0_1)
  (i16: 0, 1..1, r_pan_i16_0_1_1)
  (i16: 1, 0..2, r_pan_i16_1_0_2)
  (i16: 1, 2..2, r_pan_i16_1_2_2)
  (i16: 2, 1..0, r_pan_i16_2_1_0)
  (i16: 2, 127..128, r_pan_i16_2_127_128)
  (i16: 2, 128..129, r_pan_i16_2_128_129)
  (i32: 0, 0..1, r_pan_i32_0_0_1)
  (i32: 0, 1..1, r_pan_i32_0_1_1)
  (i32: 1, 0..2, r_pan_i32_1_0_2)
  (i32: 1, 2..2, r_pan_i32_1_2_2)
  (i32: 2, 1..0, r_pan_i32_2_1_0)
  (i32: 2, 127..128, r_pan_i32_2_127_128)
  (i32: 2, 128..129, r_pan_i32_2_128_129)
  (i64: 0, 0..1, r_pan_i64_0_0_1)
  (i64: 0, 1..1, r_pan_i64_0_1_1)
  (i64: 1, 0..2, r_pan_i64_1_0_2)
  (i64: 1, 2..2, r_pan_i64_1_2_2)
  (i64: 2, 1..0, r_pan_i64_2_1_0)
  (i64: 2, 127..128, r_pan_i64_2_127_128)
  (i64: 2, 128..129, r_pan_i64_2_128_129)
}

macro_rules! range_to {
  ($(($t: ty: $min: expr, $max: expr, $length: expr, $name: ident))*) => ($(
    #[test]
    fn $name() {
      let mut bin = Monotone::new();
      let input: Vec<$t> = rand_increasing($min, $max, $length);
      println!("{:?}", input);
      bin.encode(&input).unwrap();
      for a in bin.storage() { println!("{:032b}", a); }
      for a in 0..$length {
        let vec = bin.access(..a);
        println!("{:?} {:?}", &input[..a], &vec[..]);
        assert_eq!(input[..a], vec[..]);
      }
    }
  )*)
}

range_to!{
  (u8: 0, std::u8::MAX, 1024, rt_u8_0_MAX_1024)
  (u16: 0, std::u16::MAX, 1024, rt_u16_0_MAX_1024)
  (u32: 0, std::u32::MAX, 1024, rt_u32_0_MAX_1024)
  (u64: 0, std::u64::MAX, 1024, rt_u64_0_MAX_1024)
  (usize: 0, std::usize::MAX, 1024, rt_usize_0_MAX_1024)
  (i8: std::i8::MIN, std::i8::MAX, 1024, rt_i8_MIN_MAX_1024)
  (i16: std::i16::MIN, std::i16::MAX, 1024, rt_i16_MIN_MAX_1024)
  (i32: std::i32::MIN, std::i32::MAX, 1024, rt_i32_MIN_MAX_1024)
  (i64: std::i64::MIN, std::i64::MAX, 1024, rt_i64_MIN_MAX_1024)
  (isize: std::isize::MIN, std::isize::MAX, 1024, rt_isize_MIN_MAX_1024)
}

macro_rules! range_from {
  ($(($t: ty: $min: expr, $max: expr, $length: expr, $name: ident))*) => ($(
    #[test]
    fn $name() {
      let mut bin = Monotone::new();
      let input: Vec<$t> = rand_increasing($min, $max, $length);
      println!("{:?}", input);
      bin.encode(&input).unwrap();
      for a in bin.storage() { println!("{:032b}", a); }
      for a in 0..$length {
        let vec = bin.access(a..);
        println!("{:?} {:?}", &input[a..], &vec[..]);
        assert_eq!(input[a..], vec[..]);
      }
    }
  )*)
}

range_from!{
  (u8: 0, std::u8::MAX, 1024, rf_u8_0_MAX_1024)
  (u16: 0, std::u16::MAX, 1024, rf_u16_0_MAX_1024)
  (u32: 0, std::u32::MAX, 1024, rf_u32_0_MAX_1024)
  (u64: 0, std::u64::MAX, 1024, rf_u64_0_MAX_1024)
  (usize: 0, std::usize::MAX, 1024, rf_usize_0_MAX_1024)
  (i8: std::i8::MIN, std::i8::MAX, 1024, rf_i8_MIN_MAX_1024)
  (i16: std::i16::MIN, std::i16::MAX, 1024, rf_i16_MIN_MAX_1024)
  (i32: std::i32::MIN, std::i32::MAX, 1024, rf_i32_MIN_MAX_1024)
  (i64: std::i64::MIN, std::i64::MAX, 1024, rf_i64_MIN_MAX_1024)
  (isize: std::isize::MIN, std::isize::MAX, 1024, rf_isize_MIN_MAX_1024)
}

macro_rules! range_full {
  ($(($t: ty: $min: expr, $max: expr, $length: expr, $name: ident))*) => ($(
    #[test]
    fn $name() {
      let mut bin = Monotone::new();
      let input: Vec<$t> = rand_increasing($min, $max, $length);
      println!("{:?}", input);
      bin.encode(&input).unwrap();
      for a in bin.storage() { println!("{:032b}", a); }
      let vec = bin.access(..);
      println!("{:?}", vec);
      assert_eq!(input[..], vec[..]);
    }
  )*)
}

range_full!{
  (u8: 0, std::u8::MAX, 1024, ru_u8_0_MAX_1024)
  (u16: 0, std::u16::MAX, 1024, ru_u16_0_MAX_1024)
  (u32: 0, std::u32::MAX, 1024, ru_u32_0_MAX_1024)
  (u64: 0, std::u64::MAX, 1024, ru_u64_0_MAX_1024)
  (usize: 0, std::usize::MAX, 1024, ru_usize_0_MAX_1024)
  (i8: std::i8::MIN, std::i8::MAX, 1024, ru_i8_MIN_MAX_1024)
  (i16: std::i16::MIN, std::i16::MAX, 1024, ru_i16_MIN_MAX_1024)
  (i32: std::i32::MIN, std::i32::MAX, 1024, ru_i32_MIN_MAX_1024)
  (i64: std::i64::MIN, std::i64::MAX, 1024, ru_i64_MIN_MAX_1024)
  (isize: std::isize::MIN, std::isize::MAX, 1024, ru_isize_MIN_MAX_1024)
}

macro_rules! range_inclusive {
  ($(($t: ty: $min: expr, $max: expr, $length: expr, $width: expr, $name: ident))*) => ($(
    #[test]
    fn $name() {
      let mut bin = Monotone::new();
      let input: Vec<$t> = rand_increasing($min, $max, $length);
      println!("{:?}", input);
      bin.encode(&input).unwrap();
      for a in bin.storage() { println!("{:032b}", a); }
      for a in 0..($length - $width - 1) {
        let vec = bin.access(a...($width + a));
        println!("{:?} {:?}", &input[a...($width + a)], &vec[..]);
        assert_eq!(&input[a...($width + a)], &vec[..]);
      }
    }
  )*)
}

range_inclusive!{
  (u8: 0, std::u8::MAX, 1024, 15, ri_u8_0_MAX_1024_15)
  (u16: 0, std::u16::MAX, 1024, 15, ri_u16_0_MAX_1024_15)
  (u32: 0, std::u32::MAX, 1024, 15, ri_u32_0_MAX_1024_15)
  (u64: 0, std::u64::MAX, 1024, 15, ri_u64_0_MAX_1024_15)
  (usize: 0, std::usize::MAX, 1024, 15, ri_usize_0_MAX_1024_15)
  (i8: std::i8::MIN, std::i8::MAX, 1024, 15, ri_i8_MIN_MAX_1024_15)
  (i16: std::i16::MIN, std::i16::MAX, 1024, 15, ri_i16_MIN_MAX_1024_15)
  (i32: std::i32::MIN, std::i32::MAX, 1024, 15, ri_i32_MIN_MAX_1024_15)
  (i64: std::i64::MIN, std::i64::MAX, 1024, 15, ri_i64_MIN_MAX_1024_15)
  (isize: std::isize::MIN, std::isize::MAX, 1024, 15, ri_isize_MIN_MAX_1024_15)
}
