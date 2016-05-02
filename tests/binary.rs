#![allow(non_snake_case)]

extern crate pfor;

use pfor::utility::Encodable;
use pfor::binary::Binary;

macro_rules! constant_values {
  ($(($t: ty: $value: expr, $length: expr, $name: ident))*) => ($(
    #[test]
    fn $name() {
      let mut bin = Binary::new();
      let input: Vec<$t> = vec![$value; $length];
      bin.encode(&input);
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
  (u8: 0, 1, cv_u8_0_1)
  (u8: 1, 1, cv_u8_1_1)
  (u8: 31, 127, cv_u8_31_127)
  (u8: 32, 128, cv_u8_32_128)
  (u8: 63, 129, cv_u8_63_129)
  (u8: 64, 511, cv_u8_64_511)
  (u8: 127, 512, cv_u8_127_512)
  (u8: 128, 513, cv_u8_128_513)
  (u16: 0, 0, cv_u16_0_0)
  (u16: 0, 1, cv_u16_0_1)
  (u16: 1, 1, cv_u16_1_1)
  (u16: 31, 127, cv_u16_31_127)
  (u16: 32, 128, cv_u16_32_128)
  (u16: 63, 129, cv_u16_63_129)
  (u16: 64, 511, cv_u16_64_511)
  (u16: 127, 512, cv_u16_127_512)
  (u16: 128, 513, cv_u16_128_513)
  (u32: 0, 0, cv_u32_0_0)
  (u32: 0, 1, cv_u32_0_1)
  (u32: 1, 1, cv_u32_1_1)
  (u32: 31, 127, cv_u32_31_127)
  (u32: 32, 128, cv_u32_32_128)
  (u32: 63, 129, cv_u32_63_129)
  (u32: 64, 511, cv_u32_64_511)
  (u32: 127, 512, cv_u32_127_512)
  (u32: 128, 513, cv_u32_128_513)
  (u64: 0, 0, cv_u64_0_0)
  (u64: 0, 1, cv_u64_0_1)
  (u64: 1, 1, cv_u64_1_1)
  (u64: 31, 127, cv_u64_31_127)
  (u64: 32, 128, cv_u64_32_128)
  (u64: 63, 129, cv_u64_63_129)
  (u64: 64, 511, cv_u64_64_511)
  (u64: 127, 512, cv_u64_127_512)
  (u64: 128, 513, cv_u64_128_513)
}

constant_values!{
  (u8: 0, 0, cv_u8_3_0)
  (u8: 1, 1, cv_u8_3_1)
  (u8: 2, 2, cv_u8_3_2)
  (u8: 3, 3, cv_u8_3_3)
  (u8: 4, 4, cv_u8_3_4)
  (u8: 5, 5, cv_u8_3_5)
  (u8: 6, 6, cv_u8_3_6)
  (u8: 7, 7, cv_u8_3_7)
  (u8: 8, 8, cv_u8_3_8)
  (u8: 9, 9, cv_u8_3_9)
  (u8: 0, 10, cv_u8_3_10)
  (u8: 1, 11, cv_u8_3_11)
  (u8: 2, 12, cv_u8_3_12)
  (u8: 3, 13, cv_u8_3_13)
  (u8: 4, 14, cv_u8_3_14)
  (u8: 5, 15, cv_u8_3_15)
  (u8: 6, 16, cv_u8_3_16)
  (u8: 7, 17, cv_u8_3_17)
  (u8: 8, 18, cv_u8_3_18)
  (u8: 9, 19, cv_u8_3_19)
  (u8: 0, 20, cv_u8_3_20)
  (u8: 1, 21, cv_u8_3_21)
  (u8: 2, 22, cv_u8_3_22)
  (u8: 3, 23, cv_u8_3_23)
  (u8: 4, 24, cv_u8_3_24)
  (u8: 5, 25, cv_u8_3_25)
  (u8: 6, 26, cv_u8_3_26)
  (u8: 7, 27, cv_u8_3_27)
  (u8: 8, 28, cv_u8_3_28)
  (u8: 9, 29, cv_u8_3_29)
  (u8: 0, 30, cv_u8_3_30)
  (u8: 1, 31, cv_u8_3_31)
  (u8: 2, 32, cv_u8_3_32)
  (u16: 0, 0, cv_u16_3_0)
  (u16: 1, 1, cv_u16_3_1)
  (u16: 2, 2, cv_u16_3_2)
  (u16: 3, 3, cv_u16_3_3)
  (u16: 4, 4, cv_u16_3_4)
  (u16: 5, 5, cv_u16_3_5)
  (u16: 6, 6, cv_u16_3_6)
  (u16: 7, 7, cv_u16_3_7)
  (u16: 8, 8, cv_u16_3_8)
  (u16: 9, 9, cv_u16_3_9)
  (u16: 0, 10, cv_u16_3_10)
  (u16: 1, 11, cv_u16_3_11)
  (u16: 2, 12, cv_u16_3_12)
  (u16: 3, 13, cv_u16_3_13)
  (u16: 4, 14, cv_u16_3_14)
  (u16: 5, 15, cv_u16_3_15)
  (u16: 6, 16, cv_u16_3_16)
  (u16: 7, 17, cv_u16_3_17)
  (u16: 8, 18, cv_u16_3_18)
  (u16: 9, 19, cv_u16_3_19)
  (u16: 0, 20, cv_u16_3_20)
  (u16: 1, 21, cv_u16_3_21)
  (u16: 2, 22, cv_u16_3_22)
  (u16: 3, 23, cv_u16_3_23)
  (u16: 4, 24, cv_u16_3_24)
  (u16: 5, 25, cv_u16_3_25)
  (u16: 6, 26, cv_u16_3_26)
  (u16: 7, 27, cv_u16_3_27)
  (u16: 8, 28, cv_u16_3_28)
  (u16: 9, 29, cv_u16_3_29)
  (u16: 0, 30, cv_u16_3_30)
  (u16: 1, 31, cv_u16_3_31)
  (u16: 2, 32, cv_u16_3_32)
  (u32: 0, 0, cv_u32_3_0)
  (u32: 1, 1, cv_u32_3_1)
  (u32: 2, 2, cv_u32_3_2)
  (u32: 3, 3, cv_u32_3_3)
  (u32: 4, 4, cv_u32_3_4)
  (u32: 5, 5, cv_u32_3_5)
  (u32: 6, 6, cv_u32_3_6)
  (u32: 7, 7, cv_u32_3_7)
  (u32: 8, 8, cv_u32_3_8)
  (u32: 9, 9, cv_u32_3_9)
  (u32: 0, 10, cv_u32_3_10)
  (u32: 1, 11, cv_u32_3_11)
  (u32: 2, 12, cv_u32_3_12)
  (u32: 3, 13, cv_u32_3_13)
  (u32: 4, 14, cv_u32_3_14)
  (u32: 5, 15, cv_u32_3_15)
  (u32: 6, 16, cv_u32_3_16)
  (u32: 7, 17, cv_u32_3_17)
  (u32: 8, 18, cv_u32_3_18)
  (u32: 9, 19, cv_u32_3_19)
  (u32: 0, 20, cv_u32_3_20)
  (u32: 1, 21, cv_u32_3_21)
  (u32: 2, 22, cv_u32_3_22)
  (u32: 3, 23, cv_u32_3_23)
  (u32: 4, 24, cv_u32_3_24)
  (u32: 5, 25, cv_u32_3_25)
  (u32: 6, 26, cv_u32_3_26)
  (u32: 7, 27, cv_u32_3_27)
  (u32: 8, 28, cv_u32_3_28)
  (u32: 9, 29, cv_u32_3_29)
  (u32: 0, 30, cv_u32_3_30)
  (u32: 1, 31, cv_u32_3_31)
  (u32: 2, 32, cv_u32_3_32)
  (u64: 0, 0, cv_u64_3_0)
  (u64: 1, 1, cv_u64_3_1)
  (u64: 2, 2, cv_u64_3_2)
  (u64: 3, 3, cv_u64_3_3)
  (u64: 4, 4, cv_u64_3_4)
  (u64: 5, 5, cv_u64_3_5)
  (u64: 6, 6, cv_u64_3_6)
  (u64: 7, 7, cv_u64_3_7)
  (u64: 8, 8, cv_u64_3_8)
  (u64: 9, 9, cv_u64_3_9)
  (u64: 0, 10, cv_u64_3_10)
  (u64: 1, 11, cv_u64_3_11)
  (u64: 2, 12, cv_u64_3_12)
  (u64: 3, 13, cv_u64_3_13)
  (u64: 4, 14, cv_u64_3_14)
  (u64: 5, 15, cv_u64_3_15)
  (u64: 6, 16, cv_u64_3_16)
  (u64: 7, 17, cv_u64_3_17)
  (u64: 8, 18, cv_u64_3_18)
  (u64: 9, 19, cv_u64_3_19)
  (u64: 0, 20, cv_u64_3_20)
  (u64: 1, 21, cv_u64_3_21)
  (u64: 2, 22, cv_u64_3_22)
  (u64: 3, 23, cv_u64_3_23)
  (u64: 4, 24, cv_u64_3_24)
  (u64: 5, 25, cv_u64_3_25)
  (u64: 6, 26, cv_u64_3_26)
  (u64: 7, 27, cv_u64_3_27)
  (u64: 8, 28, cv_u64_3_28)
  (u64: 9, 29, cv_u64_3_29)
  (u64: 0, 30, cv_u64_3_30)
  (u64: 1, 31, cv_u64_3_31)
  (u64: 2, 32, cv_u64_3_32)
}

constant_values!{
  (u8: std::u8::MAX, 256, cv_u8_MAX_256)
  (u16: std::u16::MAX, 256, cv_u16_MAX_256)
  (u32: std::u32::MAX, 256, cv_u32_MAX_256)
  (u64: std::u64::MAX, 256, cv_u64_MAX_256)
}

macro_rules! wrong_width {
  ($(($t: ty: $value: expr, $length: expr, $name: ident))*) => ($(
    #[test]
    #[should_panic]
    fn $name() {
      let mut bin = Binary::new();
      let input: Vec<u64> = vec![$value as u64; $length];
      bin.encode(&input);
      let output: Vec<$t> = bin.decode().unwrap();
      for a in input.into_iter().zip(output.into_iter()) {
        assert_eq!(a.0, a.1 as u64);
      }
    }
  )*)
}

wrong_width!{
  (u8: std::u16::MAX, 256, ww_u8_u16_MAX_256)
  (u8: std::u32::MAX, 256, ww_u8_u32_MAX_256)
  (u8: std::u64::MAX, 256, ww_u8_u64_MAX_256)
  (u16: std::u32::MAX, 256, ww_u16_u32_MAX_256)
  (u16: std::u64::MAX, 256, ww_u16_u64_MAX_256)
  (u32: std::u64::MAX, 256, ww_u32_u64_MAX_256)
}

macro_rules! varied_values {
  ($(($t: ty: $name: ident))*) => ($(
    #[test]
    fn $name() {
      let mut bin = Binary::new();
      let input: Vec<$t> = vec![14, 28, 57, 28, 57, 14, 42, 85, 71];
      bin.encode(&input);
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

varied_values!{
  (u8: vv_u8_9)
  (u16: vv_u16_9)
  (u32: vv_u32_9)
  (u64: vv_u64_9)
}
