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
//!     * Prime numbers: Fermat test, Miller-Rabin test, Legendre symbol, Tonelli–Shanks algorithm
//!
//! ## Usage
//!
//! Installation command:
//!
//! ```ignore
//! cargo add finitelib
//! ```
//!
//! Or add this to your `Cargo.toml`:
//!
//! ```toml
//! [dependencies]
//! finitelib = "0.1.5"
//! ```
//!
//! ## Basic example
//!
//! ```rust
//! use finitelib::prelude::*;
//! use finitelib::gf::prime::Prime as GF;
//!
//! // Define 256-bit unsigned integer type
//! type U256 = bigi_of_bits!(256);
//!
//! // Define an Euclidean ring over U256, that contains the correct basic
//! // math operations like addition, multiplication, Euclidean extended
//! // algorithm and so on.
//! let R256 = bigi_ring_for_bigi!(U256);
//!
//! // Define a 256-bit prime number
//! let p = U256::from_decimal("67096435317933606252190858377894931905843553631817376158639971807689379094463");
//!
//! // Define a finite field `GF(p)` with the prime characteristic `p`
//! let gf = GF::new(R256, p);
//!
//! // Define two arbitrary numbers
//! let a = U256::from(3);
//! let b = U256::from(2);
//!
//! // Perform division a / b inside the field
//! let c = gf.div(&a, &b).unwrap();
//!
//! // Print the result as a decimal string
//! println!("{:?}", c.to_decimal());
//!
//! // Perform multiplication
//! let d = gf.mul(&c, &b);
//!
//! // Since multiplication is opposite to division `d` must be equal to `a`
//! assert_eq!(d, a);
//! ```

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
