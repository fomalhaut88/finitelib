//! `finitelib` is a library for advanced maths over finite groups, fields,
//! their extensions, multi precision operations and related things.
//!
//! At the moment the library supports:
//! * Finite groups
//! * Finite fields (prime - `GF(p)`, splitting - `GF(p^m)`, binary - `GF(2^m)`, Montgomery representation)
//! * Euclidean rings (including modular operations)
//! * Polynomials
//! * Multi precision operations over unsigned integers
//!     * Converting
//!     * Formatting
//!     * Basic operations: addition, subtraction, product, division, bitwise operations
//!     * Prime numbers: Fetmat test, Miller-Rabin test, Legendre symbol, Tonelli–Shanks algorithm

#![feature(test)]
#![feature(bigint_helper_methods)]
#![feature(iter_repeat_n)]

extern crate test;

pub mod utils;
pub mod group;
pub mod field;
pub mod ring;
pub mod bigi;
pub mod polynomial;
pub mod common;
pub mod gf;
pub mod prelude;
