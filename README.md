# bva

[![crates.io Version](https://img.shields.io/crates/v/bva.svg)](https://crates.io/crates/bva)
[![Rayon documentation](https://img.shields.io/docsrs/bva/latest)](https://docs.rs/bva)
![Build Status](https://github.com/haxelion/bva/actions/workflows/ci.yaml/badge.svg)
[![codecov](https://codecov.io/github/haxelion/bva/graph/badge.svg?token=UMXJD47JCY)](https://codecov.io/github/haxelion/bva)
![Minimum Rust 1.61](https://img.shields.io/badge/Rust-1.61+-red.svg)
[![LICENSE](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE)

This crate is for manipulating and doing arithmetics on bit vectors of fixed but arbitrary size.
They are meant to behave like CPU hardware registers with wrap-around on overflow.

This crate provides multiple implementations relying on different memory management strategies.

* The `Bvf` implementation uses statically sized arrays of unsigned integers as storage
  and thus has a fixed capacity but does not require dynamic memory allocation.
* The `Bvd` implementation uses a dynamically allocated array of
  integers as storage and therefore has a dynamic capacity and support resizing operations.
* The `Bv` implementation is capable of switching at runtime between the `Bvf` and `Bvd`
  implementations to try to minimize dynamic memory allocations whenever possible.

All of those implementations implement the `BitVector` trait and can be freely mixed together
and abstracted through generic traits.

The different bit vector types represent a vector of bits where the bit at index 0 is the least
significant bit and the bit at index `.len() - 1` is the most significant bit. There is no
notion of endianness for the bit vector themselves, endianness is only involved when reading or
writing a bit vector from or to memory.

Arithmetic operation can be applied to bit vectors of different types and different lengths.
The result will always have the type and the length of the left hand side operand. The right
hand side operand will be zero extended if needed. Operations will wrap-around in the case of
overflows. This should match the behavior of unsigned integer arithmetics on CPU registers.

# Examples

Bit vectors expose an API similar to Rust `std::collections::Vec`:
```rust
use bva::{Bit, BitVector, Bvd};

let mut bv = Bvd::with_capacity(128);
assert_eq!(bv.capacity(), 128);
bv.push(Bit::One);
bv.push(Bit::One);
bv.resize(16, Bit::Zero);
assert_eq!(bv.len(), 16);
assert_eq!(bv.first(), Some(Bit::One));
assert_eq!(bv.last(), Some(Bit::Zero));
let pop_count = bv.iter().fold(0u32, |acc, b| acc + u32::from(b));
assert_eq!(pop_count, 2);
```

Additionally, bit vector specific operations are available:
```rust
use bva::{Bit, BitVector, Bv32};

// While Bv32 has a capacity of 32 bits, it inherits the length of the u8.
let mut a = Bv32::try_from(0b111u8).unwrap();
a.rotr(2);
assert_eq!(a, Bv32::try_from(0b11000001u8).unwrap());
assert_eq!(a.get(7), Bit::One);
a.set(1, Bit::One);
assert_eq!(a, Bv32::try_from(0b11000011u8).unwrap());
assert_eq!(a.copy_range(1..7), Bv32::try_from(0b100001u8).unwrap());
```

Bit vectors behave like unsigned integers with wrap-around on overflow:
```rust
use bva::{Bit, BitVector, Bv32};

// Bv32 is a type alias for a Bvf with 32 bits of capacity.
let a = Bv32::ones(32);
let b = Bv32::try_from(1u32).unwrap();
assert_eq!(b.leading_zeros(), 31);
let c = a + b;
assert_eq!(c, Bv32::zeros(32));
```

Generic traits can be used to abstract over the different bit vector implementations:
```rust
use core::ops::AddAssign;
use bva::{Bit, BitVector, Bv, Bvd, Bvf};

fn fibonnaci<B: BitVector + for<'a> AddAssign<&'a B>>(n: usize) -> B {
    let mut f0 = B::zeros(1);
    let mut f1 = B::ones(1);
    if n == 0 {
        return f0;
    }

    for _ in 1..n {
        // Avoid overflow
        f0.resize(f1.significant_bits() + 1, Bit::Zero);
        // Addition is done in place
        f0 += &f1;
        // Swap f0 and f1
        std::mem::swap(&mut f0, &mut f1);
    }
    return f1;
}

assert_eq!(fibonnaci::<Bvf<u8, 2>>(15), Bvf::<u8, 2>::try_from(610u16).unwrap());
assert_eq!(fibonnaci::<Bvd>(18), Bvd::from(2584u32));
assert_eq!(fibonnaci::<Bv>(19), Bv::from(4181u32));
```

## Changelog

* 2024/07/07 - 0.3.0
    * Multiplication, division and modulo operations
    * Various helper functions
    * Much more rigorous testing reaching high code coverage.
* 2023/07/04 - 0.2.0
    * Major rewrite using const generics
    * Iterator support
* 2020/12/20 - 0.1.0
    * BitVector trait with fixed, dynamic and auto implementations.
    * Conversion between all the implementations
    * Basic arithmetic operations between the different implementations.
    * Reading and writing bit vector in various format.

## Roadmap

* Aiming for 100% code coverage.
* Signed operation support.
* Borrowing of bits and bit slice inside a bit vector.
* Numerical algorithms such as gcd, modular exponentiation, ...
* no-std support

## Why

None of the existing crate really satisfied me and I wanted an implementation capable of
minimizing dynamic memory allocations by automatically switching to fixed storage.
I also wanted a crate that was capable of doing arithmetics on arbitrarily sized bit vectors, not
just powers of two.
Also it was great practice for my rust macro writing skills.
