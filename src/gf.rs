//! This module contains implementations of Galois fields such that prime
//! field (`GF(p)`), splitting field (`GF(p^m)`), binary field (`GF(2^m)`).
//!
//! Example:
//! ```rust
//! use finitelib::prelude::*;
//! use finitelib::gf::prime::Prime;
//! use finitelib::common::rings::Ri64;
//! use finitelib::utils::int_to_bits_iter;
//!
//! let gfp = Prime::new(Ri64, 11);  // Characteristic 11
//!
//! assert_eq!(gfp.div(&5, &8).unwrap(), 2);  // 8 * 2 = 5 (mod 11)
//! assert_eq!(gfp.pow_scalar(&5, int_to_bits_iter(10)), 1);  // Fermat's little theorem
//! ```

pub mod prime;
pub mod splitting;
pub mod binary;
pub mod montgomery;
