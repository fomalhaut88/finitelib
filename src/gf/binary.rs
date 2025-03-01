//! Galios binary field `GF(2^m)`.
//!
//! Example for a multi precision case (the irreducible value taken from 
//! <https://poincare.matf.bg.ac.rs/~ezivkovm/publications/primpol1.pdf> for n=255 and k=3):
//! ```rust
//! use finitelib::prelude::*;
//! use finitelib::gf::binary::Binary;
//!
//! // Basic multi precision data type (256-bit integer)
//! type U256 = bigi_of_bits!(256);
//!
//! // Define the ring and irreducible value
//! let RX256 = bigi_xor_ring_for_bigi!(U256);
//! let irreducible = U256::from_decimal("57896044618658097711785492504343953926634992332820282019728796507556192190465");  // 1 + x^52 + x^255
//!
//! // Define the prime field
//! let gf = Binary::new(RX256, irreducible);
//!
//! // Perform division
//! let x = gf.div(&U256::from(5), &U256::from(12)).unwrap();
//! 
//! assert_eq!(x, U256::from_decimal("43422033463993573283839119378257965444976244249615211514796597380667144142848"));
//!
//! // Check the result
//! let y = gf.mul(&x, &U256::from(12));
//!
//! assert_eq!(y, U256::from(5));
//! ```

use crate::field::Field;
use crate::ring::EuclideanRing;


/// Binary field structure for the field `GF(2^m)` that contains the XOR ring 
/// and irreducible value.
///
/// See [crate::gf::binary] for the full example.
#[derive(Debug, Clone)]
pub struct Binary<R: EuclideanRing> {
    ring: R,
    irreducible: R::Item,
}


impl<R: EuclideanRing> Binary<R> {
    /// Create a binary field object from the given XOR ring and 
    /// the irreducible value.
    pub fn new(ring: R, irreducible: R::Item) -> Self {
        Self { ring, irreducible }
    }

    /// Get ring.
    pub fn ring(&self) -> &R {
        &self.ring
    }

    /// Get irreducible.
    pub fn irreducible(&self) -> &R::Item {
        &self.irreducible
    }
}


impl<R: EuclideanRing> Field for Binary<R> {
    type Item = R::Item;

    fn zero(&self) -> Self::Item {
        self.ring.zero()
    }

    fn one(&self) -> Self::Item {
        self.ring.one()
    }

    fn eq(&self, a: &Self::Item, b: &Self::Item) -> bool {
        self.ring.eq(a, b)
    }

    fn add(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
        self.ring.add(a, b)
    }

    fn sub(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
        self.ring.sub(a, b)
    }

    fn mul(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
        self.ring.mulrem(a, b, &self.irreducible)
    }

    fn neg(&self, a: &Self::Item) -> Self::Item {
        self.ring.neg(a)
    }

    fn inv(&self, a: &Self::Item) -> Option<Self::Item> {
        if self.ring.is_zero(a) {
            None
        } else {
            Some(self.ring.euclidean_extended(a, &self.irreducible).1)
        }
    }

    fn add_assign(&self, a: &mut Self::Item, b: &Self::Item) {
        self.ring.add_assign(a, b);
    }

    fn sub_assign(&self, a: &mut Self::Item, b: &Self::Item) {
        self.ring.sub_assign(a, b);
    }

    fn neg_assign(&self, a: &mut Self::Item) {
        self.ring.neg_assign(a);
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use test::Bencher;
    use rand::Rng;
    use crate::common::rings::{RXu32, RXu64};
    use crate::utils;

    #[test]
    fn test() {
        let bf = Binary::new(RXu32, 19);

        assert_eq!(bf.add(&12, &13), 1);
        assert_eq!(bf.mul(&11, &5), 1);
        assert_eq!(bf.inv(&11), Some(5));
        assert_eq!(bf.pow_scalar(&11, utils::int_to_bits_iter(15)), 1);
    }

    #[bench]
    fn bench_pow_scalar_degree32(b: &mut Bencher) {
        /*
             4 : 25
             8 : 395
            16 : 119255
            32 : 6765766665
        */
        let degree = 32;
        let mask = (1_u64 << degree) - 1;
        let bf = Binary::new(RXu64, 6765766665);

        let mut rng = rand::rng();
        let x: u64 = rng.random::<u64>() & mask;

        b.iter(|| {
            let y = bf.pow_scalar(&x, utils::int_to_bits_iter(mask));
            assert_eq!(y, 1);
        });
    }
}
