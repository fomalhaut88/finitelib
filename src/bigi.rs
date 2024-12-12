//! A module for multi precision arithmetic.
//!
//! The basic type for long unsigned integers (signed ones are not supported) 
//! is called `Bigi` that is a fixed size array of `u64`. Since it has
//! static data allocation, it gives better performance. The `Bigi` data type
//! can be accessed by `Bigi<N>` where `N` is a count of `u64` blocks
//! (for example `Bigi<4>` is a 256-bit unsigned integer data type) or by
//! the macro [bigi_of_bits](crate::bigi_of_bits) (for example
//! `bigi_of_bits!(256)` provides a 256-bit unsigned integer data type).
//!
//! Usage example:
//!
//! ```rust
//! use finitelib::bigi::prelude::*;
//!
//! type U2048 = bigi_of_bits!(2048);
//!
//! let a: U2048 = Bigi::from_decimal("129386561239752441239487256129561928457");
//! let b: U2048 = Bigi::from_decimal("912845701238565701928374012938470192834");
//!
//! let c = &a * &b;
//!
//! assert_eq!(c.to_decimal(), "118109966225748442091981144491374190381453162074572911916277590970985702077138");
//! ```

use std::{mem, iter};

use crate::utils;


pub mod format;
pub mod convert;
pub mod ops;
pub mod rings;
pub mod prime;
pub mod prelude;


/// Number of bytes in `u64` block (it is 8)
pub const BIGI_UNIT_BYTES: usize = mem::size_of::<u64>();

/// Number of bits in `u64` block (it is 64)
pub const BIGI_UNIT_BITS: usize = BIGI_UNIT_BYTES << 3;


/// Bigi basic structure that is a fixed size array of `u64`.
#[derive(Debug, Clone, PartialEq)]
pub struct Bigi<const N: usize>([u64; N]);


/// A macros that generates a Bigi data type calculating the size of the inner 
/// array from given number of bits that should be multiple of 64 (bit size
/// of `u64` unit).
///
/// ```rust
/// use finitelib::bigi::prelude::*;
///
/// type U2048 = bigi_of_bits!(2048);
///
/// assert_eq!(U2048::size(), 32);
/// assert_eq!(std::mem::size_of::<U2048>(), 256);
/// ```
#[macro_export]
macro_rules! bigi_of_bits {
    ($bits:expr) => {
        Bigi<{ $bits / BIGI_UNIT_BITS }>
    };
}


impl<const N: usize> Bigi<N> {
    /// New Bigi object from an array
    pub fn new(digits: [u64; N]) -> Self {
        Self(digits)
    }

    /// Number of `u64` digits.
    pub const fn size() -> usize {
        N
    }

    /// Minimum number (zero).
    pub fn min() -> Self {
        Self([0; N])
    }

    /// Maximum number (`2^(N * 64) - 1`).
    pub fn max() -> Self {
        Self([u64::MAX; N])
    }

    /// Represent as an array slice.
    pub fn as_array(&self) -> &[u64] {
        &self.0
    }

    /// Represent as an array mutable slice.
    pub fn as_array_mut(&mut self) -> &mut [u64] {
        &mut self.0
    }

    /// Returns `false` if the highest bit is `1`, otherwise it returns `true`.
    /// In other words, first bit is interpreted as a sign. Note: it does not
    /// impact on comparison.
    pub fn guess_sign(&self) -> bool {
        self.0[N - 1] >> (BIGI_UNIT_BITS - 1) == 0
    }

    /// Create a Bigi object from an iterator over `u64` values.
    pub fn from_iter<I: Iterator<Item = u64>>(it: I) -> Self {
        Self::new(it.collect::<Vec<u64>>().try_into().unwrap())
    }

    /// Iterate `u64` digits from lowest to highest.
    pub fn to_iter(&self) -> impl Iterator<Item = u64> {
        self.0.into_iter()
    }

    /// Get bit on `idx` place.
    pub fn bit_get(&self, idx: usize) -> bool {
        let (q, r) = Self::_bit_split_index(idx);
        self.0[q] & (1 << r) != 0
    }

    /// Set bit on `idx` place.
    pub fn bit_set(&mut self, idx: usize, bit: bool) {
        let (q, r) = Self::_bit_split_index(idx);
        if bit {
            self.0[q] |= 1 << r;
        } else {
            self.0[q] &= !(1 << r);
        }
    }

    /// Get bit length of the number.
    pub fn bit_len(&self) -> usize {
        let order = self._get_order();
        if order > 0 {
            (order - 1) * BIGI_UNIT_BITS + 
                utils::uint_bit_order(&self.0[order - 1])
        } else {
            0
        }
    }

    /// Iterate bits from lowest to highest.
    pub fn bit_iter(&self) -> impl Iterator<Item = bool> + '_ {
        let mut countdown = self.bit_len();

        let mut idx = 0;
        let mut digit_iter = utils::int_to_bits_iter(self.0[idx]);

        iter::from_fn(move || {
            if countdown == 0 {
                None
            } else {
                let bit = {
                    let mut res = digit_iter.next();

                    if res.is_none() {
                        idx += 1;
                        digit_iter = utils::int_to_bits_iter(self.0[idx]);
                        res = digit_iter.next();
                    }

                    res.unwrap()
                };

                countdown -= 1;

                Some(bit)
            }
        })
    }

    fn _bit_split_index(idx: usize) -> (usize, usize) {
        (idx / BIGI_UNIT_BITS, idx % BIGI_UNIT_BITS)
    }

    fn _get_order(&self) -> usize {
        for idx in (0..N).rev() {
            if self.0[idx] != 0 {
                return idx + 1;
            }
        }
        0
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use crate::signed::Signed;

    #[test]
    fn test_as_array() {
        let mut a = Bigi::new([25, 0, 0, 2]);

        assert_eq!(a.as_array()[3], 2);
        assert_eq!(a.as_array()[2], 0);

        a.as_array_mut()[2] = 10;

        assert_eq!(a.as_array()[2], 10);
        assert_eq!(a, Bigi::new([25, 0, 10, 2]));
    }

    #[test]
    fn test_guess_sign() {
        assert_eq!(Bigi::new([25, 1]).guess_sign(), true);
        assert_eq!(Bigi::new([25, u64::MAX]).guess_sign(), false);
        assert_eq!(Bigi::<2>::min().guess_sign(), true);
        assert_eq!(Bigi::<2>::max().guess_sign(), false);
    }

    #[test]
    fn test_bit_get() {
        let a = Bigi::new([25, 0, 0, 2]);

        assert_eq!(a.bit_get(0), true);
        assert_eq!(a.bit_get(1), false);
        assert_eq!(a.bit_get(2), false);
        assert_eq!(a.bit_get(3), true);
        assert_eq!(a.bit_get(4), true);
        assert_eq!(a.bit_get(64), false);
        assert_eq!(a.bit_get(128), false);
        assert_eq!(a.bit_get(192), false);
        assert_eq!(a.bit_get(193), true);
    }

    #[test]
    fn test_bit_set() {
        let mut a = Bigi::new([25, 0, 0, 2]);

        a.bit_set(67, true);
        assert_eq!(a, Bigi::new([25, 8, 0, 2]));

        a.bit_set(3, false);
        assert_eq!(a, Bigi::new([17, 8, 0, 2]));
    }

    #[test]
    fn test_bit_len() {
        assert_eq!(Bigi::new([25, 0, 0, 2]).bit_len(), 194);
        assert_eq!(Bigi::new([25, 0, 0, 0]).bit_len(), 5);
        assert_eq!(Bigi::new([0, 0, 25, 0]).bit_len(), 133);
    }

    #[test]
    fn test_bit_iter() {
        let a = Bigi::new([25, 0, 0, 2]);

        let bits = a.bit_iter().collect::<Vec<bool>>();

        assert_eq!(bits.len(), a.bit_len());

        assert_eq!(bits[0], true);
        assert_eq!(bits[1], false);
        assert_eq!(bits[2], false);
        assert_eq!(bits[3], true);
        assert_eq!(bits[4], true);
        assert_eq!(bits[64], false);
        assert_eq!(bits[128], false);
        assert_eq!(bits[192], false);
        assert_eq!(bits[193], true);

        assert_eq!(Bigi::<4>::min().bit_iter().collect::<Vec<bool>>(), vec![]);
    }

    #[test]
    fn test_bigi_of_bits() {
        type U2048 = bigi_of_bits!(2048);
        assert_eq!(mem::size_of::<U2048>(), 256);
        assert_eq!(U2048::size(), 32);
    }

    #[test]
    fn test_bigi_signed() {
        type U512 = bigi_of_bits!(512);
        type I512 = Signed<U512>;

        // a > 0
        let a: I512 = Bigi::<8>::from_decimal(
            "70011597082245702521290087447806528763417035600728176437530042129660745583227"
        ).into();

        // b < 0
        let b: I512 = Bigi::<8>::from_decimal(
            "31748292332736638260997326595003206151062806364501393100925672066615273796617"
        ).into();
        let b = -b;

        let c = &a * &b;
        
        assert_eq!(
            c.get().to_decimal(), 
            "2222748650848908031820938128993338719537265726594322509944619487708154171020933436409596870357396856024737376838906180914669746523938439158164990244543059"
        );
        assert!(c.is_negative());
    }
}
