# mayda

[![Build Status](https://travis-ci.org/harharkh/mayda.svg)](https://travis-ci.org/harharkh/mayda)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)][MIT]

A Rust library to compress integer arrays (all primitive integer types are
supported). The design favors decompression speed and the ability to index the
compressed array over the compression ratio, on the principle that the runtime
penalty for using compressed arrays should be as small as possible.

This crate provides three variations on a single compression algorithm. The
[`Uniform`] type can decompress around five billion `u32`s per second, or 20
GiB/s of decompressed integers, on a 2.6 GHz Intel Core i7-6700HQ processor.
The [`Monotone`] and [`Unimodal`] types decompress at around half the speed,
but can have much better compression ratios depending on the distribution of
the integers.

Compiling `mayda` requires the **nightly** compiler (`repr_simd` is behind a
feature gate) and CPU support for the SSE2 instruction set (any Intel or AMD
processor manufactured after 2003). The basic approach is further described in
[Zukowski2006] and [Lemire2015].

### Documentation

The [module documentation][docs] provides further examples and some more
detailed descriptions of the algorithms involved.

### Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
mayda = "0.1"
```

and this to your crate root:

```rust
extern crate mayda;
```

### Example: encoding and decoding

The `Uniform` struct is recommended for general purpose integer compression.
Use the `Encodable` trait to encode and decode the array.

```rust
extern crate mayda;

use mayda::{Uniform, Encodable};

fn main() {
	// Integers in some interval of length 255, require one byte per integer
	let input: Vec<u32> = (0..128).map(|x| (x * 73) % 181 + 307).collect();

	let mut uniform = Uniform::new();
	uniform.encode(&input).unwrap();

	let i_bytes = std::mem::size_of_val(input.as_slice());
	let u_bytes = std::mem::size_of_val(uniform.storage());
	
	// 128 bytes for encoded entries, 12 bytes of overhead
	assert_eq!(i_bytes, 512);
	assert_eq!(u_bytes, 140);

	let output: Vec<u32> = uniform.decode().unwrap();
	assert_eq!(input, output);
}
```

### Example: indexing

Use the `Access` trait to index the compressed array. This is similar to `Index`,
but returns a vector instead of a slice.

```rust
extern crate mayda;

use mayda::{Uniform, Encodable, Access};

fn main() {
	// All primitive integer types supported
	let input: Vec<isize> = (-64..64).collect();

	let mut uniform = Uniform::new();
	uniform.encode(&input).unwrap();

	let val: isize = uniform.access(64);
	assert_eq!(val, 0);

	// Vector is returned to give ownership to the caller
	let range: Vec<isize> = uniform.access(..10);
	assert_eq!(range, (-64..-54).collect::<Vec<_>>());
}
```

### Performance

Consider the following three vectors:
```rust
extern crate rand;

use rand::distributions::{IndependentSample, Range, Normal};

let mut rng = rand::thread_rng();
let length: usize = 1024;

// `input1` contains random integers
let mut input1: Vec<u32> = Vec::with_capacity(length);
let range = Range::new(0, 1024);
for _ in 0..length {
  input1.push(range.ind_sample(&mut rng));
}

// `input2` contains monotone increasing integers
let mut input2: Vec<u32> = input1.clone();
input2.sort();

// `input3` contains Gaussian distributed integers with outliers
let mut input3: Vec<u32> = Vec::with_capacity(length);
let gaussian = Normal::new(4086., 128.);
for _ in 0..length {
  input3.push(gaussian.ind_sample(&mut rng) as u32);
}
let index = Range::new(0, length);
let outliers = Range::new(0, std::u32::MAX);
for _ in 0..(length / 16) {
  input3[index.ind_sample(&mut rng)] = outliers.ind_sample(&mut rng);
}
```

The performance of the [`Uniform`], [`Monotone`] and [`Unimodal`] types for
these three vectors on a 2.6 GHz Intel Core i7-6700HQ processor is given below.
Encoding and decoding speeds are reported in billions of integers per second,
time required to index the last entry is reported in nanoseconds, and
compression is reported as bits per integer. Native encoding and decoding
speeds allocate memory and perform a memcpy. The Shannon entropy is a
reasonable target for the bits per integer.

For `input1` the Shannon entropy is 10.00. `Uniform` is preferrable in every
respect for the general case.

|          | Encode (BInt/s) | Decode (BInt/s) | Index (ns) | Bits/Int |
|----------|-----------------|-----------------|------------|----------|
| Uniform  |       1.26      |       5.28      |     29     |   10.63  |
| Monotone |       1.19      |       2.45      |     68     |   32.63  |
| Unimodal |       0.21      |       2.13      |     53     |   11.16  |
| Native   |      14.03      |      14.03      |      0     |    32    |

For `input2` the Shannon entropy is 10.00, but the additional structure is used
by `Monotone` to improve compression.

|          | Encode (BInt/s) | Decode (BInt/s) | Index (ns) | Bits/Int |
|----------|-----------------|-----------------|------------|----------|
| Uniform  |       1.21      |       5.22      |     29     |   8.25   |
| Monotone |       1.25      |       2.41      |     68     |    3.5   |
| Unimodal |       0.24      |       2.35      |     52     |   8.13   |
| Native   |      14.03      |      14.03      |      0     |    32    |

For `input3` the Shannon entropy is 12.46, but compression is difficult due to
the presence of outliers. `Unimodal` gives the most robust compression.

|          | Encode (BInt/s) | Decode (BInt/s) | Index (ns) | Bits/Int |
|----------|-----------------|-----------------|------------|----------|
| Uniform  |       1.21      |       5.25      |     29     |   32.63  |
| Monotone |       1.16      |       2.45      |     66     |   32.63  |
| Unimodal |       0.18      |       1.61      |     63     |   12.50  |
| Native   |      14.03      |      14.03      |      0     |    32    |

## License

`mayda` is distributed under the terms of the [MIT] license. See LICENSE for
details.

[//]: #
   [`Uniform`]: <https://harharkh.github.io/mayda/mayda/uniform/index.html>
   [`Monotone`]: <https://harharkh.github.io/mayda/mayda/monotone/index.html>
   [`Unimodal`]: <https://harharkh.github.io/mayda/mayda/unimodal/index.html>
   [Zukowski2006]: <https://dx.doi.org/10.1109/ICDE.2006.150>
   [Lemire2015]: <https://arxiv.org/abs/1401.6399>
   [docs]: <https://harharkh.github.io/mayda/mayda/index.html>
   [MIT]: <https://opensource.org/licenses/MIT>
