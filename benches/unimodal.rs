// Copyright 2016 Jeremy Mason
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

#![feature(test)]

extern crate mayda;
extern crate num;
extern crate rand;
extern crate test;

use mayda::{Access, AccessInto, Encode, Unimodal};
use num::{Bounded, FromPrimitive, ToPrimitive};
use rand::distributions::{IndependentSample, Range, Normal};
use test::Bencher;

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

macro_rules! encode_bench {
  ($(($t: ty: $mean: expr, $std_dev: expr, $length: expr, $name: ident))*) => ($(
    #[bench]
    fn $name(b: &mut Bencher) {
      let mut bin = Unimodal::new();
      let input: Vec<$t> = rand_outliers($mean, $std_dev, $length);
      b.iter(|| {
        bin.encode(&input).unwrap();
      });
      let output = bin.decode();
      assert_eq!(input, output);
    }
  )*)
}

encode_bench!{
  (u32: 1024, 32, 15, en_u32_1024_32_15)
  (u32: 1024, 32, 16, en_u32_1024_32_16)
  (u32: 1024, 32, 31, en_u32_1024_32_31)
  (u32: 1024, 32, 32, en_u32_1024_32_32)
  (u32: 1024, 32, 127, en_u32_1024_32_127)
  (u32: 1024, 32, 128, en_u32_1024_32_128)
  (u8: 128, 16, 32768, en_u8_128_16_32768)
  (u16: 1024, 32, 32768, en_u16_1024_32_32768)
  (u32: 1024, 32, 32768, en_u32_1024_32_32768)
  (u64: 1024, 32, 32768, en_u64_1024_32_32768)
  (i32: 0, 32, 15, en_i32_0_32_15)
  (i32: 0, 32, 16, en_i32_0_32_16)
  (i32: 0, 32, 31, en_i32_0_32_31)
  (i32: 0, 32, 32, en_i32_0_32_32)
  (i32: 0, 32, 127, en_i32_0_32_127)
  (i32: 0, 32, 128, en_i32_0_32_128)
  (i8: 0, 16, 32768, en_i8_0_16_32768)
  (i16: 0, 32, 32768, en_i16_0_32_32768)
  (i32: 0, 32, 32768, en_i32_0_32_32768)
  (i64: 0, 32, 32768, en_i64_0_32_32768)
}

macro_rules! decode_bench {
  ($(($t: ty: $mean: expr, $std_dev: expr, $length: expr, $name: ident))*) => ($(
    #[bench]
    fn $name(b: &mut Bencher) {
      let mut bin = Unimodal::new();
      let input: Vec<$t> = rand_outliers($mean, $std_dev, $length);
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
  (u32: 1024, 32, 15, de_u32_1024_32_15)
  (u32: 1024, 32, 16, de_u32_1024_32_16)
  (u32: 1024, 32, 31, de_u32_1024_32_31)
  (u32: 1024, 32, 32, de_u32_1024_32_32)
  (u32: 1024, 32, 127, de_u32_1024_32_127)
  (u32: 1024, 32, 128, de_u32_1024_32_128)
  (u8: 128, 16, 32768, de_u8_128_16_32768)
  (u16: 1024, 32, 32768, de_u16_1024_32_32768)
  (u32: 1024, 32, 32768, de_u32_1024_32_32768)
  (u64: 1024, 32, 32768, de_u64_1024_32_32768)
  (i32: 0, 32, 15, de_i32_0_32_15)
  (i32: 0, 32, 16, de_i32_0_32_16)
  (i32: 0, 32, 31, de_i32_0_32_31)
  (i32: 0, 32, 32, de_i32_0_32_32)
  (i32: 0, 32, 127, de_i32_0_32_127)
  (i32: 0, 32, 128, de_i32_0_32_128)
  (i8: 0, 16, 32768, de_i8_0_16_32768)
  (i16: 0, 32, 32768, de_i16_0_32_32768)
  (i32: 0, 32, 32768, de_i32_0_32_32768)
  (i64: 0, 32, 32768, de_i64_0_32_32768)
}

macro_rules! indexing_bench {
  ($(($t: ty: $mean: expr, $std_dev: expr, $length: expr, $idx: expr, $name: ident))*) => ($(
    #[bench]
    fn $name(b: &mut Bencher) {
      let mut bin = Unimodal::new();
      let input: Vec<$t> = rand_outliers($mean, $std_dev, $length);
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
  (u8: 128, 16, 32768, 128, idx_u8_128_16_32768_128)
  (u16: 1024, 32, 32768, 128, idx_u16_1024_32_32768_128)
  (u32: 1024, 32, 32768, 128, idx_u32_1024_32_32768_128)
  (u64: 1024, 32, 32768, 128, idx_u64_1024_32_32768_128)
  (u8: 128, 16, 32768, 32767, idx_u8_128_16_32768_32767)
  (u16: 1024, 32, 32768, 32767, idx_u16_1024_32_32768_32767)
  (u32: 1024, 32, 32768, 32767, idx_u32_1024_32_32768_32767)
  (u64: 1024, 32, 32768, 32767, idx_u64_1024_32_32768_32767)
}

macro_rules! range_bench {
  ($(($t: ty: $mean: expr, $std_dev: expr, $length: expr, $lwr: expr, $upr: expr, $name: ident))*) => ($(
    #[bench]
    fn $name(b: &mut Bencher) {
      let mut bin = Unimodal::new();
      let input: Vec<$t> = rand_outliers($mean, $std_dev, $length);
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
  (u8: 128, 16, 1024, 892, 900, r_u8_128_16_1024_892_900)
  (u16: 1024, 32, 1024, 892, 900, r_u16_1024_32_1024_892_900)
  (u32: 1024, 32, 1024, 892, 900, r_u32_1024_32_1024_892_900)
  (u64: 1024, 32, 1024, 892, 900, r_u64_1024_32_1024_892_900)
  (i8: 0, 16, 1024, 892, 900, r_i8_0_16_1024_892_900)
  (i16: 0, 32, 1024, 892, 900, r_i16_0_32_1024_892_900)
  (i32: 0, 32, 1024, 892, 900, r_i32_0_32_1024_892_900)
  (i64: 0, 32, 1024, 892, 900, r_i64_0_32_1024_892_900)
}
