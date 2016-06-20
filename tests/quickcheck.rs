// Copyright 2016 Jeremy Mason
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

#![feature(inclusive_range_syntax)]
#![feature(plugin)]
#![plugin(quickcheck_macros)]

extern crate mayda;
extern crate quickcheck;

use mayda::{Access, AccessInto, Encode, Monotone, Uniform, Unimodal};

macro_rules! encode_decode {
  ($(($mayda_ty: ident: $int_ty: ty, $name: ident))*) => ($(
    #[quickcheck]
    fn $name(input: Vec<$int_ty>) -> bool {
      let mut bin = $mayda_ty::new();
      bin.encode(&input).unwrap();
      input == bin.decode()
    }
  )*)
}

encode_decode!{
  (Monotone: u8, enc_dec_mon_u8)
  (Monotone: u16, enc_dec_mon_u16)
  (Monotone: u32, enc_dec_mon_u32)
  (Monotone: u64, enc_dec_mon_u64)
  (Monotone: usize, enc_dec_mon_usize)
  (Monotone: i8, enc_dec_mon_i8)
  (Monotone: i16, enc_dec_mon_i16)
  (Monotone: i32, enc_dec_mon_i32)
  (Monotone: i64, enc_dec_mon_i64)
  (Monotone: isize, enc_dec_mon_isize)
}

encode_decode!{
  (Uniform: u8, enc_dec_unf_u8)
  (Uniform: u16, enc_dec_unf_u16)
  (Uniform: u32, enc_dec_unf_u32)
  (Uniform: u64, enc_dec_unf_u64)
  (Uniform: usize, enc_dec_unf_usize)
  (Uniform: i8, enc_dec_unf_i8)
  (Uniform: i16, enc_dec_unf_i16)
  (Uniform: i32, enc_dec_unf_i32)
  (Uniform: i64, enc_dec_unf_i64)
  (Uniform: isize, enc_dec_unf_isize)
}

encode_decode!{
  (Unimodal: u8, enc_dec_umd_u8)
  (Unimodal: u16, enc_dec_umd_u16)
  (Unimodal: u32, enc_dec_umd_u32)
  (Unimodal: u64, enc_dec_umd_u64)
  (Unimodal: usize, enc_dec_umd_usize)
  (Unimodal: i8, enc_dec_umd_i8)
  (Unimodal: i16, enc_dec_umd_i16)
  (Unimodal: i32, enc_dec_umd_i32)
  (Unimodal: i64, enc_dec_umd_i64)
  (Unimodal: isize, enc_dec_umd_isize)
}

macro_rules! encode_f_decode_i {
  ($(($mayda_ty: ident: $int_ty: ty, $name: ident))*) => ($(
    #[quickcheck]
    fn $name(input: Vec<$int_ty>) -> bool {
      let bin = $mayda_ty::from_slice(&*input).unwrap();
      let mut output: Vec<$int_ty> = vec![0; input.len()];
      bin.decode_into(&mut *output);
      input == output
    }
  )*)
}

encode_f_decode_i!{
  (Monotone: u8, enc_f_dec_i_mon_u8)
  (Monotone: u16, enc_f_dec_i_mon_u16)
  (Monotone: u32, enc_f_dec_i_mon_u32)
  (Monotone: u64, enc_f_dec_i_mon_u64)
  (Monotone: usize, enc_f_dec_i_mon_usize)
  (Monotone: i8, enc_f_dec_i_mon_i8)
  (Monotone: i16, enc_f_dec_i_mon_i16)
  (Monotone: i32, enc_f_dec_i_mon_i32)
  (Monotone: i64, enc_f_dec_i_mon_i64)
  (Monotone: isize, enc_f_dec_i_mon_isize)
}

encode_f_decode_i!{
  (Uniform: u8, enc_f_dec_i_unf_u8)
  (Uniform: u16, enc_f_dec_i_unf_u16)
  (Uniform: u32, enc_f_dec_i_unf_u32)
  (Uniform: u64, enc_f_dec_i_unf_u64)
  (Uniform: usize, enc_f_dec_i_unf_usize)
  (Uniform: i8, enc_f_dec_i_unf_i8)
  (Uniform: i16, enc_f_dec_i_unf_i16)
  (Uniform: i32, enc_f_dec_i_unf_i32)
  (Uniform: i64, enc_f_dec_i_unf_i64)
  (Uniform: isize, enc_f_dec_i_unf_isize)
}

encode_f_decode_i!{
  (Unimodal: u8, enc_f_dec_i_umd_u8)
  (Unimodal: u16, enc_f_dec_i_umd_u16)
  (Unimodal: u32, enc_f_dec_i_umd_u32)
  (Unimodal: u64, enc_f_dec_i_umd_u64)
  (Unimodal: usize, enc_f_dec_i_umd_usize)
  (Unimodal: i8, enc_f_dec_i_umd_i8)
  (Unimodal: i16, enc_f_dec_i_umd_i16)
  (Unimodal: i32, enc_f_dec_i_umd_i32)
  (Unimodal: i64, enc_f_dec_i_umd_i64)
  (Unimodal: isize, enc_f_dec_i_umd_isize)
}

macro_rules! indexing {
  ($(($mayda_ty: ident: $int_ty: ty, $name: ident))*) => ($(
    #[quickcheck]
    fn $name(input: Vec<$int_ty>) -> bool {
      let mut bin = $mayda_ty::new();
      bin.encode(&input).unwrap();
      for a in 0..input.len() {
        if input[a] != bin.access(a) {
          return false
        }
      }
      true
    }
  )*)
}

indexing!{
  (Monotone: u8, idx_mon_u8)
  (Monotone: u16, idx_mon_u16)
  (Monotone: u32, idx_mon_u32)
  (Monotone: u64, idx_mon_u64)
  (Monotone: usize, idx_mon_usize)
  (Monotone: i8, idx_mon_i8)
  (Monotone: i16, idx_mon_i16)
  (Monotone: i32, idx_mon_i32)
  (Monotone: i64, idx_mon_i64)
  (Monotone: isize, idx_mon_isize)
}

indexing!{
  (Uniform: u8, idx_unf_u8)
  (Uniform: u16, idx_unf_u16)
  (Uniform: u32, idx_unf_u32)
  (Uniform: u64, idx_unf_u64)
  (Uniform: usize, idx_unf_usize)
  (Uniform: i8, idx_unf_i8)
  (Uniform: i16, idx_unf_i16)
  (Uniform: i32, idx_unf_i32)
  (Uniform: i64, idx_unf_i64)
  (Uniform: isize, idx_unf_isize)
}

indexing!{
  (Unimodal: u8, idx_umd_u8)
  (Unimodal: u16, idx_umd_u16)
  (Unimodal: u32, idx_umd_u32)
  (Unimodal: u64, idx_umd_u64)
  (Unimodal: usize, idx_umd_usize)
  (Unimodal: i8, idx_umd_i8)
  (Unimodal: i16, idx_umd_i16)
  (Unimodal: i32, idx_umd_i32)
  (Unimodal: i64, idx_umd_i64)
  (Unimodal: isize, idx_umd_isize)
}

macro_rules! range {
  ($(($mayda_ty: ident: $int_ty: ty, $name: ident))*) => ($(
    #[quickcheck]
    fn $name(input: Vec<$int_ty>, lwr: usize, upr: usize) -> bool {
      let mut bin = $mayda_ty::new();
      bin.encode(&input).unwrap();
      if input.len() > 0 {
        let mut lwr = lwr % input.len();
        let mut upr = upr % (input.len() + 1);
        if lwr > upr { std::mem::swap(&mut lwr, &mut upr); }
        if input[lwr..upr] != *bin.access(lwr..upr) {
          return false
        }
      }
      true
    }
  )*)
}

range!{
  (Monotone: u8, r_mon_u8)
  (Monotone: u16, r_mon_u16)
  (Monotone: u32, r_mon_u32)
  (Monotone: u64, r_mon_u64)
  (Monotone: usize, r_mon_usize)
  (Monotone: i8, r_mon_i8)
  (Monotone: i16, r_mon_i16)
  (Monotone: i32, r_mon_i32)
  (Monotone: i64, r_mon_i64)
  (Monotone: isize, r_mon_isize)
}

range!{
  (Uniform: u8, r_unf_u8)
  (Uniform: u16, r_unf_u16)
  (Uniform: u32, r_unf_u32)
  (Uniform: u64, r_unf_u64)
  (Uniform: usize, r_unf_usize)
  (Uniform: i8, r_unf_i8)
  (Uniform: i16, r_unf_i16)
  (Uniform: i32, r_unf_i32)
  (Uniform: i64, r_unf_i64)
  (Uniform: isize, r_unf_isize)
}

range!{
  (Unimodal: u8, r_umd_u8)
  (Unimodal: u16, r_umd_u16)
  (Unimodal: u32, r_umd_u32)
  (Unimodal: u64, r_umd_u64)
  (Unimodal: usize, r_umd_usize)
  (Unimodal: i8, r_umd_i8)
  (Unimodal: i16, r_umd_i16)
  (Unimodal: i32, r_umd_i32)
  (Unimodal: i64, r_umd_i64)
  (Unimodal: isize, r_umd_isize)
}

macro_rules! range_from {
  ($(($mayda_ty: ident: $int_ty: ty, $name: ident))*) => ($(
    #[quickcheck]
    fn $name(input: Vec<$int_ty>) -> bool {
      let mut bin = $mayda_ty::new();
      bin.encode(&input).unwrap();
      for a in 0..input.len() {
        if input[a..] != *bin.access(a..) {
          return false
        }
      }
      true
    }
  )*)
}

range_from!{
  (Monotone: u8, rf_mon_u8)
  (Monotone: u16, rf_mon_u16)
  (Monotone: u32, rf_mon_u32)
  (Monotone: u64, rf_mon_u64)
  (Monotone: usize, rf_mon_usize)
  (Monotone: i8, rf_mon_i8)
  (Monotone: i16, rf_mon_i16)
  (Monotone: i32, rf_mon_i32)
  (Monotone: i64, rf_mon_i64)
  (Monotone: isize, rf_mon_isize)
}

range_from!{
  (Uniform: u8, rf_unf_u8)
  (Uniform: u16, rf_unf_u16)
  (Uniform: u32, rf_unf_u32)
  (Uniform: u64, rf_unf_u64)
  (Uniform: usize, rf_unf_usize)
  (Uniform: i8, rf_unf_i8)
  (Uniform: i16, rf_unf_i16)
  (Uniform: i32, rf_unf_i32)
  (Uniform: i64, rf_unf_i64)
  (Uniform: isize, rf_unf_isize)
}

range_from!{
  (Unimodal: u8, rf_umd_u8)
  (Unimodal: u16, rf_umd_u16)
  (Unimodal: u32, rf_umd_u32)
  (Unimodal: u64, rf_umd_u64)
  (Unimodal: usize, rf_umd_usize)
  (Unimodal: i8, rf_umd_i8)
  (Unimodal: i16, rf_umd_i16)
  (Unimodal: i32, rf_umd_i32)
  (Unimodal: i64, rf_umd_i64)
  (Unimodal: isize, rf_umd_isize)
}

macro_rules! range_to {
  ($(($mayda_ty: ident: $int_ty: ty, $name: ident))*) => ($(
    #[quickcheck]
    fn $name(input: Vec<$int_ty>) -> bool {
      let mut bin = $mayda_ty::new();
      bin.encode(&input).unwrap();
      for a in 0..(input.len() + 1) {
        if input[..a] != *bin.access(..a) {
          return false
        }
      }
      true
    }
  )*)
}

range_to!{
  (Monotone: u8, rt_mon_u8)
  (Monotone: u16, rt_mon_u16)
  (Monotone: u32, rt_mon_u32)
  (Monotone: u64, rt_mon_u64)
  (Monotone: usize, rt_mon_usize)
  (Monotone: i8, rt_mon_i8)
  (Monotone: i16, rt_mon_i16)
  (Monotone: i32, rt_mon_i32)
  (Monotone: i64, rt_mon_i64)
  (Monotone: isize, rt_mon_isize)
}

range_to!{
  (Uniform: u8, rt_unf_u8)
  (Uniform: u16, rt_unf_u16)
  (Uniform: u32, rt_unf_u32)
  (Uniform: u64, rt_unf_u64)
  (Uniform: usize, rt_unf_usize)
  (Uniform: i8, rt_unf_i8)
  (Uniform: i16, rt_unf_i16)
  (Uniform: i32, rt_unf_i32)
  (Uniform: i64, rt_unf_i64)
  (Uniform: isize, rt_unf_isize)
}

range_to!{
  (Unimodal: u8, rt_umd_u8)
  (Unimodal: u16, rt_umd_u16)
  (Unimodal: u32, rt_umd_u32)
  (Unimodal: u64, rt_umd_u64)
  (Unimodal: usize, rt_umd_usize)
  (Unimodal: i8, rt_umd_i8)
  (Unimodal: i16, rt_umd_i16)
  (Unimodal: i32, rt_umd_i32)
  (Unimodal: i64, rt_umd_i64)
  (Unimodal: isize, rt_umd_isize)
}

macro_rules! range_inclusive {
  ($(($mayda_ty: ident: $int_ty: ty, $name: ident))*) => ($(
    #[quickcheck]
    fn $name(input: Vec<$int_ty>, lwr: usize, upr: usize) -> bool {
      let mut bin = $mayda_ty::new();
      bin.encode(&input).unwrap();
      if input.len() > 0 {
        let mut lwr = lwr % input.len();
        let mut upr = upr % input.len();
        if lwr > upr { std::mem::swap(&mut lwr, &mut upr); }
        if input[lwr...upr] != *bin.access(lwr...upr) {
          return false
        }
      }
      true
    }
  )*)
}

range_inclusive!{
  (Monotone: u8, rc_mon_u8)
  (Monotone: u16, rc_mon_u16)
  (Monotone: u32, rc_mon_u32)
  (Monotone: u64, rc_mon_u64)
  (Monotone: usize, rc_mon_usize)
  (Monotone: i8, rc_mon_i8)
  (Monotone: i16, rc_mon_i16)
  (Monotone: i32, rc_mon_i32)
  (Monotone: i64, rc_mon_i64)
  (Monotone: isize, rc_mon_isize)
}

range_inclusive!{
  (Uniform: u8, rc_unf_u8)
  (Uniform: u16, rc_unf_u16)
  (Uniform: u32, rc_unf_u32)
  (Uniform: u64, rc_unf_u64)
  (Uniform: usize, rc_unf_usize)
  (Uniform: i8, rc_unf_i8)
  (Uniform: i16, rc_unf_i16)
  (Uniform: i32, rc_unf_i32)
  (Uniform: i64, rc_unf_i64)
  (Uniform: isize, rc_unf_isize)
}

range_inclusive!{
  (Unimodal: u8, rc_umd_u8)
  (Unimodal: u16, rc_umd_u16)
  (Unimodal: u32, rc_umd_u32)
  (Unimodal: u64, rc_umd_u64)
  (Unimodal: usize, rc_umd_usize)
  (Unimodal: i8, rc_umd_i8)
  (Unimodal: i16, rc_umd_i16)
  (Unimodal: i32, rc_umd_i32)
  (Unimodal: i64, rc_umd_i64)
  (Unimodal: isize, rc_umd_isize)
}

macro_rules! range_into {
  ($(($mayda_ty: ident: $int_ty: ty, $name: ident))*) => ($(
    #[quickcheck]
    fn $name(input: Vec<$int_ty>, lwr: usize, upr: usize) -> bool {
      let mut bin = $mayda_ty::new();
      bin.encode(&input).unwrap();
      if input.len() > 0 {
        let mut lwr = lwr % input.len();
        let mut upr = upr % (input.len() + 1);
        if lwr > upr { std::mem::swap(&mut lwr, &mut upr); }
        let mut output: Vec<$int_ty> = vec![0; upr - lwr];
        bin.access_into(lwr..upr, &mut *output);
        if input[lwr..upr] != output[..] {
          return false
        }
      }
      true
    }
  )*)
}

range_into!{
  (Monotone: u8, ri_mon_u8)
  (Monotone: u16, ri_mon_u16)
  (Monotone: u32, ri_mon_u32)
  (Monotone: u64, ri_mon_u64)
  (Monotone: usize, ri_mon_usize)
  (Monotone: i8, ri_mon_i8)
  (Monotone: i16, ri_mon_i16)
  (Monotone: i32, ri_mon_i32)
  (Monotone: i64, ri_mon_i64)
  (Monotone: isize, ri_mon_isize)
}

range_into!{
  (Uniform: u8, ri_unf_u8)
  (Uniform: u16, ri_unf_u16)
  (Uniform: u32, ri_unf_u32)
  (Uniform: u64, ri_unf_u64)
  (Uniform: usize, ri_unf_usize)
  (Uniform: i8, ri_unf_i8)
  (Uniform: i16, ri_unf_i16)
  (Uniform: i32, ri_unf_i32)
  (Uniform: i64, ri_unf_i64)
  (Uniform: isize, ri_unf_isize)
}

range_into!{
  (Unimodal: u8, ri_umd_u8)
  (Unimodal: u16, ri_umd_u16)
  (Unimodal: u32, ri_umd_u32)
  (Unimodal: u64, ri_umd_u64)
  (Unimodal: usize, ri_umd_usize)
  (Unimodal: i8, ri_umd_i8)
  (Unimodal: i16, ri_umd_i16)
  (Unimodal: i32, ri_umd_i32)
  (Unimodal: i64, ri_umd_i64)
  (Unimodal: isize, ri_umd_isize)
}
