//! Some common implementations for groups and fields over the standard integer
//! and float data types.
//!
//! ## Groups
//!
//! * `Gi8` (for `i8`)
//! * `Gi16` (for `i16`)
//! * `Gi32` (for `i32`)
//! * `Gi64` (for `i64`)
//! * `Gi128` (for `i128`)
//! * `Gu8` (for `u8`)
//! * `Gu16` (for `u16`)
//! * `Gu32` (for `u32`)
//! * `Gu64` (for `u64`)
//! * `Gu128` (for `u128`)
//! * `GAf32` (for `f32` by addition)
//! * `GAf64` (for `f64` by addition)
//! * `GMf32` (for `f32` by multiplication)
//! * `GMf64` (for `f64` by multiplication)
//!
//! Example:
//!
//! ```rust
//! use finitelib::prelude::*;
//! use finitelib::common::groups::Gi64;
//!
//! assert_eq!(Gi64.zero(), 0);
//! assert_eq!(Gi64.add(&3, &5), 8);
//! assert_eq!(Gi64.neg(&3), -3);
//! ```
//!
//! ## Fields
//!
//! * `Ff32` (for `f32`)
//! * `Ff64` (for `f64`)
//!
//! Example:
//!
//! ```rust
//! use finitelib::prelude::*;
//! use finitelib::common::fields::Ff64;
//!
//! assert_eq!(Ff64.zero(), 0.0);
//! assert_eq!(Ff64.one(), 1.0);
//! assert_eq!(Ff64.add(&3.0, &5.0), 8.0);
//! assert_eq!(Ff64.neg(&3.0), -3.0);
//! assert_eq!(Ff64.mul(&3.0, &5.0), 15.0);
//! assert_eq!(Ff64.inv(&4.0), Some(0.25));
//! assert_eq!(Ff64.inv(&0.0), None);
//! ```
//!
//! ## Rings
//!
//! * `Ri8` (for `i8`)
//! * `Ri16` (for `i16`)
//! * `Ri32` (for `i32`)
//! * `Ri64` (for `i64`)
//! * `Ri128` (for `i128`)
//! * `RXu8` (for `u8` by XOR operation)
//! * `RXu16` (for `u16` by XOR operation)
//! * `RXu32` (for `u32` by XOR operation)
//! * `RXu64` (for `u64` by XOR operation)
//! * `RXu128` (for `u128` by XOR operation)
//!
//! Example:
//!
//! ```rust
//! use finitelib::prelude::*;
//! use finitelib::common::rings::RXu32;
//!
//! let x = 178098;
//! let y = 2452;
//!
//! let (gcd, a, b) = RXu32.euclidean_extended(&x, &y);
//! 
//! assert_eq!(gcd, 2);
//! assert_eq!(a, 209);
//! assert_eq!(b, 16276);
//!
//! // x * a + y * b = gcd, according to Euclidean Extended Algorithm
//! // Note: since the ring RXu32 is over XOR operation, `+` is actually XOR
//! // and `*` is the XOR-based multiplication. This is used in binary
//! // Galois fields (`GF(2^m)`)
//! assert_eq!(RXu32.add(&RXu32.mul(&x, &a), &RXu32.mul(&y, &b)), gcd);
//! ```

pub mod groups;
pub mod fields;
pub mod rings;
