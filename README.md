# bva

[![crates.io Version](https://img.shields.io/crates/v/bva.svg)](https://crates.io/crates/bva)
[![Rayon documentation](https://img.shields.io/docsrs/bva/latest)](https://docs.rs/bva)
![Build Status](https://github.com/haxelion/bva/actions/workflows/ci.yaml/badge.svg)
[![codecov](https://codecov.io/github/haxelion/bva/graph/badge.svg?token=UMXJD47JCY)](https://codecov.io/github/haxelion/bva)
![Minimum Rust 1.61](https://img.shields.io/badge/Rust-1.61+-red.svg)
[![LICENSE](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE)

`bva` is a rust crate for manipulating and doing arithmetics on bit vectors of
fixed but arbitrary size. They are meant to behave like CPU hardware registers with wrap-around on overflow.

This crate emphasizes optimizing storage by providing alternative storage options.
The module `fixed` contains implementations using arrays of unsigned integers as storage and thus have a fixed capacity. The module `dynamic` contains an implementation using a dynamically allocated array of integers as storage and therefore has a dynamic capacity. The module `auto` contains an implementation capable of switching at runtime between a fixed or dynamic capacity implementation to try to minimize dynamic memory allocations. All of those implementations implement the `BitVector` trait and can be freely mixed together and used interchangeably via generic traits.

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
