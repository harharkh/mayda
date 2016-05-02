#![feature(test)]

#![allow(non_snake_case)]

extern crate pfor;
extern crate test;

use pfor::utility::Encodable;
use pfor::binary::Binary;
use test::Bencher;

macro_rules! encode_bench {
  ($(($t: ty, $value: expr, $length: expr, $name: ident)),*) => ($(
    #[bench]
    fn $name(b: &mut Bencher) {
      let mut bin = Binary::new();
      let input: Vec<$t> = vec![$value; $length];
      b.iter(|| {
        bin.encode(&input);
      });
      let output = bin.decode().unwrap();
      assert_eq!(input, output);
    }
  )*)
}

macro_rules! decode_bench {
  ($(($t: ty, $value: expr, $length: expr, $name: ident)),*) => ($(
    #[bench]
    fn $name(b: &mut Bencher) {
      let mut bin = Binary::new();
      let input: Vec<$t> = vec![$value; $length];
      bin.encode(&input);
      let mut output = Vec::new();
      b.iter(|| {
        output = bin.decode().unwrap();
      });
      assert_eq!(input, output);
    }
  )*)
}

macro_rules! vector_bench {
  ($(($t: ty, $value: expr, $length: expr, $name: ident)),*) => ($(
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

encode_bench!{
  (u32, 1, 31, en_u32_1_31),
  (u32, 1, 32, en_u32_1_32),
  (u32, 3, 65535, en_u32_3_65535),
  (u32, 3, 65536, en_u32_3_65536),
  (u8, std::u8::MAX, 65536, en_u8_MAX_65536),
  (u16, std::u16::MAX, 65536, en_u16_MAX_65536),
  (u32, std::u32::MAX, 65536, en_u32_MAX_65536),
  (u64, std::u64::MAX, 65536, en_u64_MAX_65536)
}

decode_bench!{
  (u32, 2, 31, de_u32_2_31),
  (u32, 2, 32, de_u32_2_32),
  (u32, 4, 65535, de_u32_4_65535),
  (u32, 4, 65536, de_u32_4_65536),
  (u8, std::u8::MAX, 65536, de_u8_MAX_65536),
  (u16, std::u16::MAX, 65536, de_u16_MAX_65536),
  (u32, std::u32::MAX, 65536, de_u32_MAX_65536),
  (u64, std::u64::MAX, 65536, de_u64_MAX_65536)
}

vector_bench!{
  (u32, 1, 32, vt_u32_1_32),
  (u32, 3, 65536, vt_u32_3_65536),
  (u32, std::u32::MAX, 65536, vt_u32_MAX_65536)
}
