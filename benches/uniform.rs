// Copyright 2016 Jeremy Mason
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

#![feature(test)]

#![allow(non_snake_case)]

extern crate mayda;
extern crate rand;
extern crate test;

use mayda::{Access, AccessInto, Encode, Uniform};
use rand::distributions::{IndependentSample, Range};
use std::{u8, u16, u32, u64, i8, i16, i32, i64};
use test::Bencher;

fn rand_uniform<T>(min: T, max: T, length: usize) -> Vec<T>
  where T: PartialOrd + rand::distributions::range::SampleRange {
  let mut output: Vec<T> = Vec::with_capacity(length);
  let val = Range::new(min, max);
  let mut rng = rand::thread_rng();
  for _ in 0..length {
    output.push(val.ind_sample(&mut rng));
  }
  output
}

macro_rules! encode_bench {
  ($(($t: ty: $min: expr, $max: expr, $length: expr, $name: ident))*) => ($(
    #[bench]
    fn $name(b: &mut Bencher) {
      let mut bin = Uniform::new();
      let input: Vec<$t> = rand_uniform($min, $max, $length);
      b.iter(|| {
        bin.encode(&input).unwrap();
      });
      let output = bin.decode();
      assert_eq!(input, output);
    }
  )*)
}

encode_bench!{
  (u32: 0, u32::MAX, 15, en_u32_0_MAX_15)
  (u32: 0, u32::MAX, 16, en_u32_0_MAX_16)
  (u32: 0, u32::MAX, 31, en_u32_0_MAX_31)
  (u32: 0, u32::MAX, 32, en_u32_0_MAX_32)
  (u32: 0, u32::MAX, 127, en_u32_0_MAX_127)
  (u32: 0, u32::MAX, 128, en_u32_0_MAX_128)
  (u8: 0, u8::MAX, 32768, en_u8_0_MAX_32768)
  (u16: 0, u16::MAX, 32768, en_u16_0_MAX_32768)
  (u32: 0, u32::MAX, 32768, en_u32_0_MAX_32768)
  (u64: 0, u64::MAX, 32768, en_u64_0_MAX_32768)
  (i32: i32::MIN, i32::MAX, 15, en_i32_MIN_MAX_15)
  (i32: i32::MIN, i32::MAX, 16, en_i32_MIN_MAX_16)
  (i32: i32::MIN, i32::MAX, 31, en_i32_MIN_MAX_31)
  (i32: i32::MIN, i32::MAX, 32, en_i32_MIN_MAX_32)
  (i32: i32::MIN, i32::MAX, 127, en_i32_MIN_MAX_127)
  (i32: i32::MIN, i32::MAX, 128, en_i32_MIN_MAX_128)
  (i8: i8::MIN, i8::MAX, 32768, en_i8_MIN_MAX_32768)
  (i16: i16::MIN, i16::MAX, 32768, en_i16_MIN_MAX_32768)
  (i32: i32::MIN, i32::MAX, 32768, en_i32_MIN_MAX_32768)
  (i64: i64::MIN, i64::MAX, 32768, en_i64_MIN_MAX_32768)
}

macro_rules! decode_bench {
  ($(($t: ty: $min: expr, $max: expr, $length: expr, $name: ident))*) => ($(
    #[bench]
    fn $name(b: &mut Bencher) {
      let mut bin = Uniform::new();
      let input: Vec<$t> = rand_uniform($min, $max, $length);
      bin.encode(&input).unwrap();
      let mut output = vec![0; $length];
      b.iter(|| {
        bin.decode_into(&mut *output);
      });
      assert_eq!(input, output);
    }
  )*)
} 

decode_bench!{
  (u32: 0, u32::MAX, 15, de_u32_0_MAX_15)
  (u32: 0, u32::MAX, 16, de_u32_0_MAX_16)
  (u32: 0, u32::MAX, 31, de_u32_0_MAX_31)
  (u32: 0, u32::MAX, 32, de_u32_0_MAX_32)
  (u32: 0, u32::MAX, 127, de_u32_0_MAX_127)
  (u32: 0, u32::MAX, 128, de_u32_0_MAX_128)
  (u8: 0, u8::MAX, 32768, de_u8_0_MAX_32768)
  (u16: 0, u16::MAX, 32768, de_u16_0_MAX_32768)
  (u32: 0, u32::MAX, 32768, de_u32_0_MAX_32768)
  (u64: 0, u64::MAX, 32768, de_u64_0_MAX_32768)
  (i32: i32::MIN, i32::MAX, 15, de_i32_MIN_MAX_15)
  (i32: i32::MIN, i32::MAX, 16, de_i32_MIN_MAX_16)
  (i32: i32::MIN, i32::MAX, 31, de_i32_MIN_MAX_31)
  (i32: i32::MIN, i32::MAX, 32, de_i32_MIN_MAX_32)
  (i32: i32::MIN, i32::MAX, 127, de_i32_MIN_MAX_127)
  (i32: i32::MIN, i32::MAX, 128, de_i32_MIN_MAX_128)
  (i8: i8::MIN, i8::MAX, 32768, de_i8_MIN_MAX_32768)
  (i16: i16::MIN, i16::MAX, 32768, de_i16_MIN_MAX_32768)
  (i32: i32::MIN, i32::MAX, 32768, de_i32_MIN_MAX_32768)
  (i64: i64::MIN, i64::MAX, 32768, de_i64_MIN_MAX_32768)
}

macro_rules! indexing_bench {
  ($(($t: ty: $min: expr, $max: expr, $length: expr, $idx: expr, $name: ident))*) => ($(
    #[bench]
    fn $name(b: &mut Bencher) {
      let mut bin = Uniform::new();
      let input: Vec<$t> = rand_uniform($min, $max, $length);
      bin.encode(&input).unwrap();
      let mut v: $t = 0;
      b.iter(|| {
        v = bin.access($idx);
      });
      assert_eq!(input[$idx], v);
    }
  )*)
}

indexing_bench!{
  (u8: 0, u8::MAX, 32768, 128, idx_u8_0_MAX_32768_128)
  (u16: 0, u16::MAX, 32768, 128, idx_u16_0_MAX_32768_128)
  (u32: 0, u32::MAX, 32768, 128, idx_u32_0_MAX_32768_128)
  (u64: 0, u64::MAX, 32768, 128, idx_u64_0_MAX_32768_128)
  (u8: 0, u8::MAX, 32768, 32767, idx_u8_0_MAX_32768_32767)
  (u16: 0, u16::MAX, 32768, 32767, idx_u16_0_MAX_32768_32767)
  (u32: 0, u32::MAX, 32768, 32767, idx_u32_0_MAX_32768_32767)
  (u64: 0, u64::MAX, 32768, 32767, idx_u64_0_MAX_32768_32767)
}

macro_rules! range_bench {
  ($(($t: ty: $min: expr, $max: expr, $length: expr, $lwr: expr, $upr: expr, $name: ident))*) => ($(
    #[bench]
    fn $name(b: &mut Bencher) {
      let mut bin = Uniform::new();
      let input: Vec<$t> = rand_uniform($min, $max, $length);
      bin.encode(&input).unwrap();
      let mut output = vec![0; $upr - $lwr];
      b.iter(|| {
        bin.access_into($lwr..$upr, &mut *output);
      });
      assert_eq!(&input[$lwr..$upr], &output[..]);
    }
  )*)
}

range_bench!{
  (u8: 0, u8::MAX, 1024, 892, 900, r_u8_0_MAX_1024_892_900)
  (u16: 0, u16::MAX, 1024, 892, 900, r_u16_0_MAX_1024_892_900)
  (u32: 0, u32::MAX, 1024, 892, 900, r_u32_0_MAX_1024_892_900)
  (u64: 0, u64::MAX, 1024, 892, 900, r_u64_0_MAX_1024_892_900)
  (i8: i8::MIN, i8::MAX, 1024, 892, 900, r_i8_MIN_MAX_1024_892_900)
  (i16: i16::MIN, i16::MAX, 1024, 892, 900, r_i16_MIN_MAX_1024_892_900)
  (i32: i32::MIN, i32::MAX, 1024, 892, 900, r_i32_MIN_MAX_1024_892_900)
  (i64: i64::MIN, i64::MAX, 1024, 892, 900, r_i64_MIN_MAX_1024_892_900)
}
