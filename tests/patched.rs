// Copyright 2016 Jeremy Mason
//
// Licensed under the MIT license <LICENSE or
// http://opensource.org/licenses/MIT>. This file may not be copied, modified,
// or distributed except according to those terms.

#![feature(inclusive_range_syntax)]

#![allow(non_snake_case)]

extern crate pfor;
extern crate rand;

use pfor::utility::{Encodable, Access};
use pfor::patched::Patched;
use rand::distributions::{IndependentSample, Range};

macro_rules! constant_values {
  ($(($t: ty: $value: expr, $length: expr, $name: ident))*) => ($(
    #[test]
    fn $name() {
      let mut bin = Patched::new();
      let input: Vec<$t> = vec![$value; $length];
      bin.encode(&input).unwrap();
      let output = bin.decode().unwrap();
      println!("{:?}", input);
      for a in bin.storage() {
        println!("{:032b}", a);
      }
      println!("{:?}", output);
      assert_eq!(input, output);
    }
  )*)
}

constant_values!{
  (u8: 0, 0, cv_u8_0_0)
  (u8: 1, 1, cv_u8_1_1)
  (u8: 2, 2, cv_u8_2_2)
  (u8: 3, 3, cv_u8_3_3)
  (u8: 4, 4, cv_u8_4_4)
  (u8: 5, 5, cv_u8_5_5)
  (u8: 6, 6, cv_u8_6_6)
  (u8: 7, 7, cv_u8_7_7)
  (u8: 8, 8, cv_u8_8_8)
  (u8: 9, 9, cv_u8_9_9)
  (u8: 0, 10, cv_u8_0_10)
  (u8: 1, 11, cv_u8_1_11)
  (u8: 2, 12, cv_u8_2_12)
  (u8: 3, 13, cv_u8_3_13)
  (u8: 4, 14, cv_u8_4_14)
  (u8: 5, 15, cv_u8_5_15)
  (u8: 6, 16, cv_u8_6_16)
  (u8: 7, 17, cv_u8_7_17)
  (u8: 8, 18, cv_u8_8_18)
  (u8: 9, 19, cv_u8_9_19)
  (u8: 0, 20, cv_u8_0_20)
  (u8: 1, 21, cv_u8_1_21)
  (u8: 2, 22, cv_u8_2_22)
  (u8: 3, 23, cv_u8_3_23)
  (u8: 4, 24, cv_u8_4_24)
  (u8: 5, 25, cv_u8_5_25)
  (u8: 6, 26, cv_u8_6_26)
  (u8: 7, 27, cv_u8_7_27)
  (u8: 8, 28, cv_u8_8_28)
  (u8: 9, 29, cv_u8_9_29)
  (u8: 0, 30, cv_u8_0_30)
  (u8: 1, 31, cv_u8_1_31)
  (u8: 2, 32, cv_u8_2_32)
  /*(i8: 0, 0, cv_i8_0_0)
  (i8: 1, 1, cv_i8_1_1)
  (i8: 2, 2, cv_i8_2_2)
  (i8: 3, 3, cv_i8_3_3)
  (i8: 4, 4, cv_i8_4_4)
  (i8: 5, 5, cv_i8_5_5)
  (i8: 6, 6, cv_i8_6_6)
  (i8: 7, 7, cv_i8_7_7)
  (i8: 8, 8, cv_i8_8_8)
  (i8: 9, 9, cv_i8_9_9)
  (i8: 0, 10, cv_i8_0_10)
  (i8: 1, 11, cv_i8_1_11)
  (i8: 2, 12, cv_i8_2_12)
  (i8: 3, 13, cv_i8_3_13)
  (i8: 4, 14, cv_i8_4_14)
  (i8: 5, 15, cv_i8_5_15)
  (i8: 6, 16, cv_i8_6_16)
  (i8: 7, 17, cv_i8_7_17)
  (i8: 8, 18, cv_i8_8_18)
  (i8: 9, 19, cv_i8_9_19)
  (i8: 0, 20, cv_i8_0_20)
  (i8: 1, 21, cv_i8_1_21)
  (i8: 2, 22, cv_i8_2_22)
  (i8: 3, 23, cv_i8_3_23)
  (i8: 4, 24, cv_i8_4_24)
  (i8: 5, 25, cv_i8_5_25)
  (i8: 6, 26, cv_i8_6_26)
  (i8: 7, 27, cv_i8_7_27)
  (i8: 8, 28, cv_i8_8_28)
  (i8: 9, 29, cv_i8_9_29)
  (i8: 0, 30, cv_i8_0_30)
  (i8: 1, 31, cv_i8_1_31)
  (i8: 2, 32, cv_i8_2_32)*/
}

constant_values!{
  (u16: 0, 0, cv_u16_0_0)
  (u16: 1, 1, cv_u16_1_1)
  (u16: 2, 2, cv_u16_2_2)
  (u16: 3, 3, cv_u16_3_3)
  (u16: 4, 4, cv_u16_4_4)
  (u16: 5, 5, cv_u16_5_5)
  (u16: 6, 6, cv_u16_6_6)
  (u16: 7, 7, cv_u16_7_7)
  (u16: 8, 8, cv_u16_8_8)
  (u16: 9, 9, cv_u16_9_9)
  (u16: 0, 10, cv_u16_0_10)
  (u16: 1, 11, cv_u16_1_11)
  (u16: 2, 12, cv_u16_2_12)
  (u16: 3, 13, cv_u16_3_13)
  (u16: 4, 14, cv_u16_4_14)
  (u16: 5, 15, cv_u16_5_15)
  (u16: 6, 16, cv_u16_6_16)
  (u16: 7, 17, cv_u16_7_17)
  (u16: 8, 18, cv_u16_8_18)
  (u16: 9, 19, cv_u16_9_19)
  (u16: 0, 20, cv_u16_0_20)
  (u16: 1, 21, cv_u16_1_21)
  (u16: 2, 22, cv_u16_2_22)
  (u16: 3, 23, cv_u16_3_23)
  (u16: 4, 24, cv_u16_4_24)
  (u16: 5, 25, cv_u16_5_25)
  (u16: 6, 26, cv_u16_6_26)
  (u16: 7, 27, cv_u16_7_27)
  (u16: 8, 28, cv_u16_8_28)
  (u16: 9, 29, cv_u16_9_29)
  (u16: 0, 30, cv_u16_0_30)
  (u16: 1, 31, cv_u16_1_31)
  (u16: 2, 32, cv_u16_2_32)
  /*(i16: 0, 0, cv_i16_0_0)
  (i16: 1, 1, cv_i16_1_1)
  (i16: 2, 2, cv_i16_2_2)
  (i16: 3, 3, cv_i16_3_3)
  (i16: 4, 4, cv_i16_4_4)
  (i16: 5, 5, cv_i16_5_5)
  (i16: 6, 6, cv_i16_6_6)
  (i16: 7, 7, cv_i16_7_7)
  (i16: 8, 8, cv_i16_8_8)
  (i16: 9, 9, cv_i16_9_9)
  (i16: 0, 10, cv_i16_0_10)
  (i16: 1, 11, cv_i16_1_11)
  (i16: 2, 12, cv_i16_2_12)
  (i16: 3, 13, cv_i16_3_13)
  (i16: 4, 14, cv_i16_4_14)
  (i16: 5, 15, cv_i16_5_15)
  (i16: 6, 16, cv_i16_6_16)
  (i16: 7, 17, cv_i16_7_17)
  (i16: 8, 18, cv_i16_8_18)
  (i16: 9, 19, cv_i16_9_19)
  (i16: 0, 20, cv_i16_0_20)
  (i16: 1, 21, cv_i16_1_21)
  (i16: 2, 22, cv_i16_2_22)
  (i16: 3, 23, cv_i16_3_23)
  (i16: 4, 24, cv_i16_4_24)
  (i16: 5, 25, cv_i16_5_25)
  (i16: 6, 26, cv_i16_6_26)
  (i16: 7, 27, cv_i16_7_27)
  (i16: 8, 28, cv_i16_8_28)
  (i16: 9, 29, cv_i16_9_29)
  (i16: 0, 30, cv_i16_0_30)
  (i16: 1, 31, cv_i16_1_31)
  (i16: 2, 32, cv_i16_2_32)*/
}

constant_values!{
  (u32: 0, 0, cv_u32_0_0)
  (u32: 1, 1, cv_u32_1_1)
  (u32: 2, 2, cv_u32_2_2)
  (u32: 3, 3, cv_u32_3_3)
  (u32: 4, 4, cv_u32_4_4)
  (u32: 5, 5, cv_u32_5_5)
  (u32: 6, 6, cv_u32_6_6)
  (u32: 7, 7, cv_u32_7_7)
  (u32: 8, 8, cv_u32_8_8)
  (u32: 9, 9, cv_u32_9_9)
  (u32: 0, 10, cv_u32_0_10)
  (u32: 1, 11, cv_u32_1_11)
  (u32: 2, 12, cv_u32_2_12)
  (u32: 3, 13, cv_u32_3_13)
  (u32: 4, 14, cv_u32_4_14)
  (u32: 5, 15, cv_u32_5_15)
  (u32: 6, 16, cv_u32_6_16)
  (u32: 7, 17, cv_u32_7_17)
  (u32: 8, 18, cv_u32_8_18)
  (u32: 9, 19, cv_u32_9_19)
  (u32: 0, 20, cv_u32_0_20)
  (u32: 1, 21, cv_u32_1_21)
  (u32: 2, 22, cv_u32_2_22)
  (u32: 3, 23, cv_u32_3_23)
  (u32: 4, 24, cv_u32_4_24)
  (u32: 5, 25, cv_u32_5_25)
  (u32: 6, 26, cv_u32_6_26)
  (u32: 7, 27, cv_u32_7_27)
  (u32: 8, 28, cv_u32_8_28)
  (u32: 9, 29, cv_u32_9_29)
  (u32: 0, 30, cv_u32_0_30)
  (u32: 1, 31, cv_u32_1_31)
  (u32: 2, 32, cv_u32_2_32)
  /*(i32: 0, 0, cv_i32_0_0)
  (i32: 1, 1, cv_i32_1_1)
  (i32: 2, 2, cv_i32_2_2)
  (i32: 3, 3, cv_i32_3_3)
  (i32: 4, 4, cv_i32_4_4)
  (i32: 5, 5, cv_i32_5_5)
  (i32: 6, 6, cv_i32_6_6)
  (i32: 7, 7, cv_i32_7_7)
  (i32: 8, 8, cv_i32_8_8)
  (i32: 9, 9, cv_i32_9_9)
  (i32: 0, 10, cv_i32_0_10)
  (i32: 1, 11, cv_i32_1_11)
  (i32: 2, 12, cv_i32_2_12)
  (i32: 3, 13, cv_i32_3_13)
  (i32: 4, 14, cv_i32_4_14)
  (i32: 5, 15, cv_i32_5_15)
  (i32: 6, 16, cv_i32_6_16)
  (i32: 7, 17, cv_i32_7_17)
  (i32: 8, 18, cv_i32_8_18)
  (i32: 9, 19, cv_i32_9_19)
  (i32: 0, 20, cv_i32_0_20)
  (i32: 1, 21, cv_i32_1_21)
  (i32: 2, 22, cv_i32_2_22)
  (i32: 3, 23, cv_i32_3_23)
  (i32: 4, 24, cv_i32_4_24)
  (i32: 5, 25, cv_i32_5_25)
  (i32: 6, 26, cv_i32_6_26)
  (i32: 7, 27, cv_i32_7_27)
  (i32: 8, 28, cv_i32_8_28)
  (i32: 9, 29, cv_i32_9_29)
  (i32: 0, 30, cv_i32_0_30)
  (i32: 1, 31, cv_i32_1_31)
  (i32: 2, 32, cv_i32_2_32)*/
}

constant_values!{
  (u64: 0, 0, cv_u64_0_0)
  (u64: 1, 1, cv_u64_1_1)
  (u64: 2, 2, cv_u64_2_2)
  (u64: 3, 3, cv_u64_3_3)
  (u64: 4, 4, cv_u64_4_4)
  (u64: 5, 5, cv_u64_5_5)
  (u64: 6, 6, cv_u64_6_6)
  (u64: 7, 7, cv_u64_7_7)
  (u64: 8, 8, cv_u64_8_8)
  (u64: 9, 9, cv_u64_9_9)
  (u64: 0, 10, cv_u64_0_10)
  (u64: 1, 11, cv_u64_1_11)
  (u64: 2, 12, cv_u64_2_12)
  (u64: 3, 13, cv_u64_3_13)
  (u64: 4, 14, cv_u64_4_14)
  (u64: 5, 15, cv_u64_5_15)
  (u64: 6, 16, cv_u64_6_16)
  (u64: 7, 17, cv_u64_7_17)
  (u64: 8, 18, cv_u64_8_18)
  (u64: 9, 19, cv_u64_9_19)
  (u64: 0, 20, cv_u64_0_20)
  (u64: 1, 21, cv_u64_1_21)
  (u64: 2, 22, cv_u64_2_22)
  (u64: 3, 23, cv_u64_3_23)
  (u64: 4, 24, cv_u64_4_24)
  (u64: 5, 25, cv_u64_5_25)
  (u64: 6, 26, cv_u64_6_26)
  (u64: 7, 27, cv_u64_7_27)
  (u64: 8, 28, cv_u64_8_28)
  (u64: 9, 29, cv_u64_9_29)
  (u64: 0, 30, cv_u64_0_30)
  (u64: 1, 31, cv_u64_1_31)
  (u64: 2, 32, cv_u64_2_32)
  /*(i64: 0, 0, cv_i64_0_0)
  (i64: 1, 1, cv_i64_1_1)
  (i64: 2, 2, cv_i64_2_2)
  (i64: 3, 3, cv_i64_3_3)
  (i64: 4, 4, cv_i64_4_4)
  (i64: 5, 5, cv_i64_5_5)
  (i64: 6, 6, cv_i64_6_6)
  (i64: 7, 7, cv_i64_7_7)
  (i64: 8, 8, cv_i64_8_8)
  (i64: 9, 9, cv_i64_9_9)
  (i64: 0, 10, cv_i64_0_10)
  (i64: 1, 11, cv_i64_1_11)
  (i64: 2, 12, cv_i64_2_12)
  (i64: 3, 13, cv_i64_3_13)
  (i64: 4, 14, cv_i64_4_14)
  (i64: 5, 15, cv_i64_5_15)
  (i64: 6, 16, cv_i64_6_16)
  (i64: 7, 17, cv_i64_7_17)
  (i64: 8, 18, cv_i64_8_18)
  (i64: 9, 19, cv_i64_9_19)
  (i64: 0, 20, cv_i64_0_20)
  (i64: 1, 21, cv_i64_1_21)
  (i64: 2, 22, cv_i64_2_22)
  (i64: 3, 23, cv_i64_3_23)
  (i64: 4, 24, cv_i64_4_24)
  (i64: 5, 25, cv_i64_5_25)
  (i64: 6, 26, cv_i64_6_26)
  (i64: 7, 27, cv_i64_7_27)
  (i64: 8, 28, cv_i64_8_28)
  (i64: 9, 29, cv_i64_9_29)
  (i64: 0, 30, cv_i64_0_30)
  (i64: 1, 31, cv_i64_1_31)
  (i64: 2, 32, cv_i64_2_32)*/
}

constant_values!{
  (u8: 31, 127, cv_u8_31_127)
  (u8: 32, 128, cv_u8_32_128)
  (u8: 63, 129, cv_u8_63_129)
  (u8: 64, 511, cv_u8_64_511)
  (u8: 127, 512, cv_u8_127_512)
  (u8: 128, 513, cv_u8_128_513)
  (u8: std::u8::MAX, 256, cv_u8_MAX_256)
  (u16: 31, 127, cv_u16_31_127)
  (u16: 32, 128, cv_u16_32_128)
  (u16: 63, 129, cv_u16_63_129)
  (u16: 64, 511, cv_u16_64_511)
  (u16: 127, 512, cv_u16_127_512)
  (u16: 128, 513, cv_u16_128_513)
  (u16: std::u16::MAX, 256, cv_u16_MAX_256)
  (u32: 31, 127, cv_u32_31_127)
  (u32: 32, 128, cv_u32_32_128)
  (u32: 63, 129, cv_u32_63_129)
  (u32: 64, 511, cv_u32_64_511)
  (u32: 127, 512, cv_u32_127_512)
  (u32: 128, 513, cv_u32_128_513)
  (u32: std::u32::MAX, 256, cv_u32_MAX_256)
  (u64: 31, 127, cv_u64_31_127)
  (u64: 32, 128, cv_u64_32_128)
  (u64: 63, 129, cv_u64_63_129)
  (u64: 64, 511, cv_u64_64_511)
  (u64: 127, 512, cv_u64_127_512)
  (u64: 128, 513, cv_u64_128_513)
  (u64: std::u64::MAX, 256, cv_u64_MAX_256)
  /*(i8: 31, 127, cv_i8_31_127)
  (i8: 32, 128, cv_i8_32_128)
  (i8: 63, 129, cv_i8_63_129)
  (i8: 64, 511, cv_i8_64_511)
  (i8: 126, 512, cv_i8_126_512)
  (i8: 127, 513, cv_i8_127_513)
  (i8: std::i8::MAX, 256, cv_i8_MAX_256)
  (i16: 31, 127, cv_i16_31_127)
  (i16: 32, 128, cv_i16_32_128)
  (i16: 63, 129, cv_i16_63_129)
  (i16: 64, 511, cv_i16_64_511)
  (i16: 127, 512, cv_i16_127_512)
  (i16: 128, 513, cv_i16_128_513)
  (i16: std::i16::MAX, 256, cv_i16_MAX_256)
  (i32: 31, 127, cv_i32_31_127)
  (i32: 32, 128, cv_i32_32_128)
  (i32: 63, 129, cv_i32_63_129)
  (i32: 64, 511, cv_i32_64_511)
  (i32: 127, 512, cv_i32_127_512)
  (i32: 128, 513, cv_i32_128_513)
  (i32: std::i32::MAX, 256, cv_i32_MAX_256)
  (i64: 31, 127, cv_i64_31_127)
  (i64: 32, 128, cv_i64_32_128)
  (i64: 63, 129, cv_i64_63_129)
  (i64: 64, 511, cv_i64_64_511)
  (i64: 127, 512, cv_i64_127_512)
  (i64: 128, 513, cv_i64_128_513)
  (i64: std::i64::MAX, 256, cv_i64_MAX_256)*/
}

macro_rules! random_values {
  ($(($t: ty: $min: expr, $max: expr, $length: expr, $name: ident))*) => ($(
    #[test]
    fn $name() {
      let mut bin = Patched::new();
      let mut input: Vec<$t> = Vec::new();
      let between = Range::new($min, $max);
      let mut rng = rand::thread_rng();
      for _ in 0..$length {
        input.push(between.ind_sample(&mut rng));
      }
      bin.encode(&input).unwrap();
      let output = bin.decode().unwrap();
      println!("{:?}", input);
      for a in bin.storage() {
        println!("{:032b}", a);
      }
      println!("{:?}", output);
      assert_eq!(input, output);
    }
  )*)
}

random_values!{
  (u8: 0, std::u8::MAX, 1024, rv_u8_0_MAX_1024)
  (u16: 0, std::u16::MAX, 1024, rv_u16_0_MAX_1024)
  (u32: 0, std::u32::MAX, 1024, rv_u32_0_MAX_1024)
  (u64: 0, std::u64::MAX, 1024, rv_u64_0_MAX_1024)
  /*(i8: 0, std::i8::MAX, 1024, rv_i8_0_MAX_1024)
  (i16: 0, std::i16::MAX, 1024, rv_i16_0_MAX_1024)
  (i32: 0, std::i32::MAX, 1024, rv_i32_0_MAX_1024)
  (i64: 0, std::i64::MAX, 1024, rv_i64_0_MAX_1024)*/
}

macro_rules! increasing_values {
  ($(($t: ty: $min: expr, $max: expr, $name: ident))*) => ($(
    #[test]
    fn $name() {
      let mut bin = Patched::new();
      let input: Vec<$t> = ($min..$max).collect();
      bin.encode(&input).unwrap();
      let output = bin.decode().unwrap();
      println!("{:?}", input);
      for a in bin.storage() {
        println!("{:032b}", a);
      }
      println!("{:?}", output);
      assert_eq!(input, output);
    }
  )*)
}

increasing_values!{
  (u8: 0, 255, iv_u8_0_255)
  (u16: 0, 1027, iv_u16_0_1023)
  (u32: 0, 1023, iv_u32_0_1023)
  (u64: 0, 1023, iv_u64_0_1023)
  /*(i8: -128, 127, iv_i8_128_127)
  (i16: -512, 511, iv_i16_512_511)
  (i32: -512, 511, iv_i32_512_511)
  (i64: -512, 511, iv_i64_512_511)*/
}
/*
macro_rules! indexing {
  ($(($t: ty: $max: expr, $name: ident))*) => ($(
    #[test]
    fn $name() {
      let mut bin = Patched::new();
      let input: Vec<$t> = (0..$max).collect();
      bin.encode(&input).unwrap();
      println!("{:?}", input);
      for a in bin.storage() {
        println!("{:032b}", a);
      }
      for a in 0..$max {
        let b = bin.access(a);
        println!("{} {}", a, b);
        assert_eq!(a as $t, b);
      }
    }
  )*)
}

indexing!{
  (u8: 255, idx_u8_255)
  (u16: 1023, idx_u16_1023)
  (u32: 1023, idx_u32_1023)
  (u64: 1023, idx_u64_1023)
  (i8: 127, idx_i8_127)
  (i16: 1023, idx_i16_1023)
  (i32: 1023, idx_i32_1023)
  (i64: 1023, idx_i64_1023)
}

macro_rules! indexing_panic {
  ($(($t: ty: $length: expr, $idx: expr, $name: ident))*) => ($(
    #[test]
    #[should_panic]
    fn $name() {
      let mut bin = Patched::new();
      let input: Vec<$t> = vec![0; $length];
      bin.encode(&input).unwrap();
      println!("{:?}", input);
      for a in bin.storage() {
        println!("{:032b}", a);
      }
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
  ($(($t: ty: $max: expr, $width: expr, $name: ident))*) => ($(
    #[test]
    fn $name() {
      let mut bin = Patched::new();
      let input: Vec<$t> = (0..$max).collect();
      bin.encode(&input).unwrap();
      println!("{:?}", input);
      for a in bin.storage() {
        println!("{:032b}", a);
      }
      for a in 0..($max - $width) {
        let vec = bin.access(a..($width + a));
        println!("{:?} {:?}", &input[a..($width + a)], &vec[..]);
        assert_eq!(&input[a..($width + a)], &vec[..]);
      }
    }
  )*)
}

range!{
  (u8: 255, 16, r_u8_255_16)
  (u16: 1023, 16, r_u16_1023_16)
  (u32: 1023, 16, r_u32_1023_16)
  (u64: 1023, 16, r_u64_1023_16)
  (i8: 127, 16, r_i8_127_16)
  (i16: 1023, 16, r_i16_1023_16)
  (i32: 1023, 16, r_i32_1023_16)
  (i64: 1023, 16, r_i64_1023_16)
}

macro_rules! range_panic {
  ($(($t: ty: $length: expr, $range: expr, $name: ident))*) => ($(
    #[test]
    #[should_panic]
    fn $name() {
      let mut bin = Patched::new();
      let input: Vec<$t> = vec![0; $length];
      bin.encode(&input).unwrap();
      println!("{:?}", input);
      for a in bin.storage() {
        println!("{:032b}", a);
      }
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
  ($(($t: ty: $max: expr, $name: ident))*) => ($(
    #[test]
    fn $name() {
      let mut bin = Patched::new();
      let input: Vec<$t> = (0..$max).collect();
      bin.encode(&input).unwrap();
      println!("{:?}", input);
      for a in bin.storage() {
        println!("{:032b}", a);
      }
      for a in 0..$max {
        let vec = bin.access(..a);
        println!("{:?} {:?}", &input[..a], &vec[..]);
        assert_eq!(&input[..a], &vec[..]);
      }
    }
  )*)
}

range_to!{
  (u8: 255, rt_u8_255)
  (u16: 255, rt_u16_255)
  (u32: 255, rt_u32_255)
  (u64: 255, rt_u64_255)
  (i8: 127, rt_i8_127)
  (i16: 255, rt_i16_255)
  (i32: 255, rt_i32_255)
  (i64: 255, rt_i64_255)
}

macro_rules! range_from {
  ($(($t: ty: $max: expr, $name: ident))*) => ($(
    #[test]
    fn $name() {
      let mut bin = Patched::new();
      let input: Vec<$t> = (0..$max).collect();
      bin.encode(&input).unwrap();
      println!("{:?}", input);
      for a in bin.storage() {
        println!("{:032b}", a);
      }
      for a in 0...$max {
        let vec = bin.access(a..);
        println!("{:?} {:?}", &input[a..], &vec[..]);
        assert_eq!(&input[a..], &vec[..]);
      }
    }
  )*)
}

range_from!{
  (u8: 255, rf_u8_255)
  (u16: 255, rf_u16_255)
  (u32: 255, rf_u32_255)
  (u64: 255, rf_u64_255)
  (i8: 127, rf_i8_127)
  (i16: 255, rf_i16_255)
  (i32: 255, rf_i32_255)
  (i64: 255, rf_i64_255)
}

macro_rules! range_full {
  ($(($t: ty: $max: expr, $name: ident))*) => ($(
    #[test]
    fn $name() {
      let mut bin = Patched::new();
      let input: Vec<$t> = (0..$max).collect();
      bin.encode(&input).unwrap();
      let output = bin.access(..);
      println!("{:?}", input);
      for a in bin.storage() {
        println!("{:032b}", a);
      }
      println!("{:?}", output);
      assert_eq!(input, output);
    }
  )*)
}

range_full!{
  (u8: 255, ru_u8_255)
  (u16: 255, ru_u16_255)
  (u32: 255, ru_u32_255)
  (u64: 255, ru_u64_255)
  (i8: 127, ru_i8_127)
  (i16: 255, ru_i16_255)
  (i32: 255, ru_i32_255)
  (i64: 255, ru_i64_255)
}*/
