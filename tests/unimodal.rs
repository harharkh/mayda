// Copyright 2016 Jeremy Mason
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

#![feature(inclusive_range_syntax)]

#![allow(non_snake_case)]

extern crate mayda;
extern crate num;
extern crate rand;

use mayda::{Access, Encode, Unimodal};
use num::{Bounded, FromPrimitive, ToPrimitive};
use rand::distributions::{IndependentSample, Range, Normal};

fn rand_outliers<T>(mean: T, std_dev: T, length: usize) -> Vec<T>
  where T: PartialOrd +
           Bounded +
           FromPrimitive +
           ToPrimitive +
           rand::distributions::range::SampleRange {
  let mut output: Vec<T> = Vec::with_capacity(length);
  if length > 0 {
    let val = Normal::new(mean.to_f64().unwrap(), std_dev.to_f64().unwrap());
    let mut rng = rand::thread_rng();
    for _ in 0..length {
      output.push(FromPrimitive::from_f64(val.ind_sample(&mut rng)).unwrap());
    }
    let idx = Range::new(0, length);
    let val = Range::new(Bounded::min_value(), Bounded::max_value());
    for _ in 0..(length / 16) {
      output[idx.ind_sample(&mut rng)] = val.ind_sample(&mut rng);
    }
  }
  output
}

macro_rules! random_values {
  ($(($t: ty: $mean: expr, $std_dev: expr, $length: expr, $name: ident))*) => ($(
    #[test]
    fn $name() {
      let mut bin = Unimodal::new();
      let input: Vec<$t> = rand_outliers($mean, $std_dev, $length);
      println!("{:?}", input);
      bin.encode(&input).unwrap();
      for a in bin.storage() { println!("{:032b}", a); }
      let output = bin.decode();
      println!("{:?}", output);
      assert_eq!(input, output);
    }
  )*)
}

random_values!{
  (u8: 128, 16, 0, rv_u8_128_16_0)
  (u8: 128, 16, 1, rv_u8_128_16_1)
  (u8: 128, 16, 2, rv_u8_128_16_2)
  (u8: 128, 16, 3, rv_u8_128_16_3)
  (u8: 128, 16, 4, rv_u8_128_16_4)
  (u8: 128, 16, 5, rv_u8_128_16_5)
  (u8: 128, 16, 7, rv_u8_128_16_7)
  (u8: 128, 16, 8, rv_u8_128_16_8)
  (u8: 128, 16, 9, rv_u8_128_16_9)
  (u8: 128, 16, 15, rv_u8_128_16_15)
  (u8: 128, 16, 16, rv_u8_128_16_16)
  (u8: 128, 16, 17, rv_u8_128_16_17)
  (u8: 128, 16, 31, rv_u8_128_16_31)
  (u8: 128, 16, 32, rv_u8_128_16_32)
  (u8: 128, 16, 33, rv_u8_128_16_33)
  (u8: 128, 16, 127, rv_u8_128_16_127)
  (u8: 128, 16, 128, rv_u8_128_16_128)
  (u8: 128, 16, 129, rv_u8_128_16_129)
  (u8: 128, 16, 511, rv_u8_128_16_511)
  (u8: 128, 16, 512, rv_u8_128_16_512)
  (u8: 128, 16, 513, rv_u8_128_16_513)
  (u8: 128, 16, 1024, rv_u8_128_16_1024)
  (i8: 0, 16, 0, rv_i8_0_16_0)
  (i8: 0, 16, 1, rv_i8_0_16_1)
  (i8: 0, 16, 2, rv_i8_0_16_2)
  (i8: 0, 16, 3, rv_i8_0_16_3)
  (i8: 0, 16, 4, rv_i8_0_16_4)
  (i8: 0, 16, 5, rv_i8_0_16_5)
  (i8: 0, 16, 7, rv_i8_0_16_7)
  (i8: 0, 16, 8, rv_i8_0_16_8)
  (i8: 0, 16, 9, rv_i8_0_16_9)
  (i8: 0, 16, 15, rv_i8_0_16_15)
  (i8: 0, 16, 16, rv_i8_0_16_16)
  (i8: 0, 16, 17, rv_i8_0_16_17)
  (i8: 0, 16, 31, rv_i8_0_16_31)
  (i8: 0, 16, 32, rv_i8_0_16_32)
  (i8: 0, 16, 33, rv_i8_0_16_33)
  (i8: 0, 16, 127, rv_i8_0_16_127)
  (i8: 0, 16, 128, rv_i8_0_16_128)
  (i8: 0, 16, 129, rv_i8_0_16_129)
  (i8: 0, 16, 511, rv_i8_0_16_511)
  (i8: 0, 16, 512, rv_i8_0_16_512)
  (i8: 0, 16, 513, rv_i8_0_16_513)
  (i8: 0, 16, 1024, rv_i8_0_16_1024)
}

random_values!{
  (u16: 1024, 32, 0, rv_u16_1024_32_0)
  (u16: 1024, 32, 1, rv_u16_1024_32_1)
  (u16: 1024, 32, 2, rv_u16_1024_32_2)
  (u16: 1024, 32, 3, rv_u16_1024_32_3)
  (u16: 1024, 32, 4, rv_u16_1024_32_4)
  (u16: 1024, 32, 5, rv_u16_1024_32_5)
  (u16: 1024, 32, 7, rv_u16_1024_32_7)
  (u16: 1024, 32, 8, rv_u16_1024_32_8)
  (u16: 1024, 32, 9, rv_u16_1024_32_9)
  (u16: 1024, 32, 15, rv_u16_1024_32_15)
  (u16: 1024, 32, 16, rv_u16_1024_32_16)
  (u16: 1024, 32, 17, rv_u16_1024_32_17)
  (u16: 1024, 32, 31, rv_u16_1024_32_31)
  (u16: 1024, 32, 32, rv_u16_1024_32_32)
  (u16: 1024, 32, 33, rv_u16_1024_32_33)
  (u16: 1024, 32, 127, rv_u16_1024_32_127)
  (u16: 1024, 32, 128, rv_u16_1024_32_128)
  (u16: 1024, 32, 129, rv_u16_1024_32_129)
  (u16: 1024, 32, 511, rv_u16_1024_32_511)
  (u16: 1024, 32, 512, rv_u16_1024_32_512)
  (u16: 1024, 32, 513, rv_u16_1024_32_513)
  (u16: 1024, 32, 1024, rv_u16_1024_32_1024)
  (i16: 0, 32, 0, rv_i16_0_32_0)
  (i16: 0, 32, 1, rv_i16_0_32_1)
  (i16: 0, 32, 2, rv_i16_0_32_2)
  (i16: 0, 32, 3, rv_i16_0_32_3)
  (i16: 0, 32, 4, rv_i16_0_32_4)
  (i16: 0, 32, 5, rv_i16_0_32_5)
  (i16: 0, 32, 7, rv_i16_0_32_7)
  (i16: 0, 32, 8, rv_i16_0_32_8)
  (i16: 0, 32, 9, rv_i16_0_32_9)
  (i16: 0, 32, 15, rv_i16_0_32_15)
  (i16: 0, 32, 16, rv_i16_0_32_16)
  (i16: 0, 32, 17, rv_i16_0_32_17)
  (i16: 0, 32, 31, rv_i16_0_32_31)
  (i16: 0, 32, 32, rv_i16_0_32_32)
  (i16: 0, 32, 33, rv_i16_0_32_33)
  (i16: 0, 32, 127, rv_i16_0_32_127)
  (i16: 0, 32, 128, rv_i16_0_32_128)
  (i16: 0, 32, 129, rv_i16_0_32_129)
  (i16: 0, 32, 511, rv_i16_0_32_511)
  (i16: 0, 32, 512, rv_i16_0_32_512)
  (i16: 0, 32, 513, rv_i16_0_32_513)
  (i16: 0, 32, 1024, rv_i16_0_32_1024)
}

random_values!{
  (u32: 1024, 32, 0, rv_u32_1024_32_0)
  (u32: 1024, 32, 1, rv_u32_1024_32_1)
  (u32: 1024, 32, 2, rv_u32_1024_32_2)
  (u32: 1024, 32, 3, rv_u32_1024_32_3)
  (u32: 1024, 32, 4, rv_u32_1024_32_4)
  (u32: 1024, 32, 5, rv_u32_1024_32_5)
  (u32: 1024, 32, 7, rv_u32_1024_32_7)
  (u32: 1024, 32, 8, rv_u32_1024_32_8)
  (u32: 1024, 32, 9, rv_u32_1024_32_9)
  (u32: 1024, 32, 15, rv_u32_1024_32_15)
  (u32: 1024, 32, 16, rv_u32_1024_32_16)
  (u32: 1024, 32, 17, rv_u32_1024_32_17)
  (u32: 1024, 32, 31, rv_u32_1024_32_31)
  (u32: 1024, 32, 32, rv_u32_1024_32_32)
  (u32: 1024, 32, 33, rv_u32_1024_32_33)
  (u32: 1024, 32, 127, rv_u32_1024_32_127)
  (u32: 1024, 32, 128, rv_u32_1024_32_128)
  (u32: 1024, 32, 129, rv_u32_1024_32_129)
  (u32: 1024, 32, 511, rv_u32_1024_32_511)
  (u32: 1024, 32, 512, rv_u32_1024_32_512)
  (u32: 1024, 32, 513, rv_u32_1024_32_513)
  (u32: 1024, 32, 1024, rv_u32_1024_32_1024)
  (i32: 0, 32, 0, rv_i32_0_32_0)
  (i32: 0, 32, 1, rv_i32_0_32_1)
  (i32: 0, 32, 2, rv_i32_0_32_2)
  (i32: 0, 32, 3, rv_i32_0_32_3)
  (i32: 0, 32, 4, rv_i32_0_32_4)
  (i32: 0, 32, 5, rv_i32_0_32_5)
  (i32: 0, 32, 7, rv_i32_0_32_7)
  (i32: 0, 32, 8, rv_i32_0_32_8)
  (i32: 0, 32, 9, rv_i32_0_32_9)
  (i32: 0, 32, 15, rv_i32_0_32_15)
  (i32: 0, 32, 16, rv_i32_0_32_16)
  (i32: 0, 32, 17, rv_i32_0_32_17)
  (i32: 0, 32, 31, rv_i32_0_32_31)
  (i32: 0, 32, 32, rv_i32_0_32_32)
  (i32: 0, 32, 33, rv_i32_0_32_33)
  (i32: 0, 32, 127, rv_i32_0_32_127)
  (i32: 0, 32, 128, rv_i32_0_32_128)
  (i32: 0, 32, 129, rv_i32_0_32_129)
  (i32: 0, 32, 511, rv_i32_0_32_511)
  (i32: 0, 32, 512, rv_i32_0_32_512)
  (i32: 0, 32, 513, rv_i32_0_32_513)
  (i32: 0, 32, 1024, rv_i32_0_32_1024)
}

random_values!{
  (u64: 1024, 32, 0, rv_u64_1024_32_0)
  (u64: 1024, 32, 1, rv_u64_1024_32_1)
  (u64: 1024, 32, 2, rv_u64_1024_32_2)
  (u64: 1024, 32, 3, rv_u64_1024_32_3)
  (u64: 1024, 32, 4, rv_u64_1024_32_4)
  (u64: 1024, 32, 5, rv_u64_1024_32_5)
  (u64: 1024, 32, 7, rv_u64_1024_32_7)
  (u64: 1024, 32, 8, rv_u64_1024_32_8)
  (u64: 1024, 32, 9, rv_u64_1024_32_9)
  (u64: 1024, 32, 15, rv_u64_1024_32_15)
  (u64: 1024, 32, 16, rv_u64_1024_32_16)
  (u64: 1024, 32, 17, rv_u64_1024_32_17)
  (u64: 1024, 32, 31, rv_u64_1024_32_31)
  (u64: 1024, 32, 32, rv_u64_1024_32_32)
  (u64: 1024, 32, 33, rv_u64_1024_32_33)
  (u64: 1024, 32, 127, rv_u64_1024_32_127)
  (u64: 1024, 32, 128, rv_u64_1024_32_128)
  (u64: 1024, 32, 129, rv_u64_1024_32_129)
  (u64: 1024, 32, 511, rv_u64_1024_32_511)
  (u64: 1024, 32, 512, rv_u64_1024_32_512)
  (u64: 1024, 32, 513, rv_u64_1024_32_513)
  (u64: 1024, 32, 1024, rv_u64_1024_32_1024)
  (i64: 0, 32, 0, rv_i64_0_32_0)
  (i64: 0, 32, 1, rv_i64_0_32_1)
  (i64: 0, 32, 2, rv_i64_0_32_2)
  (i64: 0, 32, 3, rv_i64_0_32_3)
  (i64: 0, 32, 4, rv_i64_0_32_4)
  (i64: 0, 32, 5, rv_i64_0_32_5)
  (i64: 0, 32, 7, rv_i64_0_32_7)
  (i64: 0, 32, 8, rv_i64_0_32_8)
  (i64: 0, 32, 9, rv_i64_0_32_9)
  (i64: 0, 32, 15, rv_i64_0_32_15)
  (i64: 0, 32, 16, rv_i64_0_32_16)
  (i64: 0, 32, 17, rv_i64_0_32_17)
  (i64: 0, 32, 31, rv_i64_0_32_31)
  (i64: 0, 32, 32, rv_i64_0_32_32)
  (i64: 0, 32, 33, rv_i64_0_32_33)
  (i64: 0, 32, 127, rv_i64_0_32_127)
  (i64: 0, 32, 128, rv_i64_0_32_128)
  (i64: 0, 32, 129, rv_i64_0_32_129)
  (i64: 0, 32, 511, rv_i64_0_32_511)
  (i64: 0, 32, 512, rv_i64_0_32_512)
  (i64: 0, 32, 513, rv_i64_0_32_513)
  (i64: 0, 32, 1024, rv_i64_0_32_1024)
}

// Verify that methods provided by u64 or u32
random_values!{
  (usize: 16384, 1024, 1024, cv_usize_16384_1024_1024)
  (isize: 0, 1024, 1024, cv_isize_0_1024_1024)
}

macro_rules! increasing_values {
  ($(($t: ty: $min: expr, $max: expr, $name: ident))*) => ($(
    #[test]
    fn $name() {
      let mut bin = Unimodal::new();
      let input: Vec<$t> = ($min...$max).collect();
      println!("{:?}", input);
      bin.encode(&input).unwrap();
      for a in bin.storage() { println!("{:032b}", a); }
      let output = bin.decode();
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
  ($(($t: ty: $mean: expr, $std_dev: expr, $length: expr, $name: ident))*) => ($(
    #[test]
    fn $name() {
      let mut bin = Unimodal::new();
      let input: Vec<$t> = rand_outliers($mean, $std_dev, $length);
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
  (u8: 128, 16, 1024, idx_u8_128_16_1024)
  (u16: 1024, 32, 1024, idx_u16_1024_32_1024)
  (u32: 1024, 32, 1024, idx_u32_1024_32_1024)
  (u64: 1024, 32, 1024, idx_u64_1024_32_1024)
  (usize: 1024, 32, 1024, idx_usize_1024_32_1024)
  (i8: 0, 16, 1024, idx_i8_0_16_1024)
  (i16: 0, 32, 1024, idx_i16_0_32_1024)
  (i32: 0, 32, 1024, idx_i32_0_32_1024)
  (i64: 0, 32, 1024, idx_i64_0_32_1024)
  (isize: 0, 32, 1024, idx_isize_0_32_1024)
}

macro_rules! indexing_panic {
  ($(($t: ty: $length: expr, $idx: expr, $name: ident))*) => ($(
    #[test]
    #[should_panic]
    fn $name() {
      let mut bin = Unimodal::new();
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
  ($(($t: ty: $mean: expr, $std_dev: expr, $length: expr, $width: expr, $name: ident))*) => ($(
    #[test]
    fn $name() {
      let mut bin = Unimodal::new();
      let input: Vec<$t> = rand_outliers($mean, $std_dev, $length);
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
  (u8: 128, 16, 1024, 15, r_u8_128_16_1024_15)
  (u16: 1024, 32, 1024, 15, r_u16_1024_32_1024_15)
  (u32: 1024, 32, 1024, 15, r_u32_1024_32_1024_15)
  (u64: 1024, 32, 1024, 15, r_u64_1024_32_1024_15)
  (usize: 1024, 32, 1024, 15, r_usize_1024_32_1024_15)
  (i8: 0, 16, 1024, 15, r_i8_0_16_1024_15)
  (i16: 0, 32, 1024, 15, r_i16_0_32_1024_15)
  (i32: 0, 32, 1024, 15, r_i32_0_32_1024_15)
  (i64: 0, 32, 1024, 15, r_i64_0_32_1024_15)
  (isize: 0, 32, 1024, 15, r_isize_0_32_1024_15)
}

macro_rules! range_panic {
  ($(($t: ty: $length: expr, $range: expr, $name: ident))*) => ($(
    #[test]
    #[should_panic]
    fn $name() {
      let mut bin = Unimodal::new();
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
  ($(($t: ty: $mean: expr, $std_dev: expr, $length: expr, $name: ident))*) => ($(
    #[test]
    fn $name() {
      let mut bin = Unimodal::new();
      let input: Vec<$t> = rand_outliers($mean, $std_dev, $length);
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
  (u8: 128, 16, 1024, rt_u8_128_16_1024)
  (u16: 1024, 32, 1024, rt_u16_1024_32_1024)
  (u32: 1024, 32, 1024, rt_u32_1024_32_1024)
  (u64: 1024, 32, 1024, rt_u64_1024_32_1024)
  (usize: 1024, 32, 1024, rt_usize_1024_32_1024)
  (i8: 0, 16, 1024, rt_i8_0_16_1024)
  (i16: 0, 32, 1024, rt_i16_0_32_1024)
  (i32: 0, 32, 1024, rt_i32_0_32_1024)
  (i64: 0, 32, 1024, rt_i64_0_32_1024)
  (isize: 0, 32, 1024, rt_isize_0_32_1024)
}

macro_rules! range_from {
  ($(($t: ty: $mean: expr, $std_dev: expr, $length: expr, $name: ident))*) => ($(
    #[test]
    fn $name() {
      let mut bin = Unimodal::new();
      let input: Vec<$t> = rand_outliers($mean, $std_dev, $length);
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
  (u8: 128, 16, 1024, rf_u8_128_16_1024)
  (u16: 1024, 32, 1024, rf_u16_1024_32_1024)
  (u32: 1024, 32, 1024, rf_u32_1024_32_1024)
  (u64: 1024, 32, 1024, rf_u64_1024_32_1024)
  (usize: 1024, 32, 1024, rf_usize_1024_32_1024)
  (i8: 0, 16, 1024, rf_i8_0_16_1024)
  (i16: 0, 32, 1024, rf_i16_0_32_1024)
  (i32: 0, 32, 1024, rf_i32_0_32_1024)
  (i64: 0, 32, 1024, rf_i64_0_32_1024)
  (isize: 0, 32, 1024, rf_isize_0_32_1024)
}

macro_rules! range_full {
  ($(($t: ty: $mean: expr, $std_dev: expr, $length: expr, $name: ident))*) => ($(
    #[test]
    fn $name() {
      let mut bin = Unimodal::new();
      let input: Vec<$t> = rand_outliers($mean, $std_dev, $length);
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
  (u8: 128, 16, 1024, ru_u8_128_16_1024)
  (u16: 1024, 32, 1024, ru_u16_1024_32_1024)
  (u32: 1024, 32, 1024, ru_u32_1024_32_1024)
  (u64: 1024, 32, 1024, ru_u64_1024_32_1024)
  (usize: 1024, 32, 1024, ru_usize_1024_32_1024)
  (i8: 0, 16, 1024, ru_i8_0_16_1024)
  (i16: 0, 32, 1024, ru_i16_0_32_1024)
  (i32: 0, 32, 1024, ru_i32_0_32_1024)
  (i64: 0, 32, 1024, ru_i64_0_32_1024)
  (isize: 0, 32, 1024, ru_isize_0_32_1024)
}

macro_rules! range_inclusive {
  ($(($t: ty: $mean: expr, $std_dev: expr, $length: expr, $width: expr, $name: ident))*) => ($(
    #[test]
    fn $name() {
      let mut bin = Unimodal::new();
      let input: Vec<$t> = rand_outliers($mean, $std_dev, $length);
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
  (u8: 128, 16, 1024, 15, ri_u8_128_16_1024_15)
  (u16: 1024, 32, 1024, 15, ri_u16_1024_32_1024_15)
  (u32: 1024, 32, 1024, 15, ri_u32_1024_32_1024_15)
  (u64: 1024, 32, 1024, 15, ri_u64_1024_32_1024_15)
  (usize: 1024, 32, 1024, 15, ri_usize_1024_32_1024_15)
  (i8: 0, 16, 1024, 15, ri_i8_0_16_1024_15)
  (i16: 0, 32, 1024, 15, ri_i16_0_32_1024_15)
  (i32: 0, 32, 1024, 15, ri_i32_0_32_1024_15)
  (i64: 0, 32, 1024, 15, ri_i64_0_32_1024_15)
  (isize: 0, 32, 1024, 15, ri_isize_0_32_1024_15)
}
