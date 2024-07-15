//! Montgomery representation of the prime field `GF(p)` 
//! (<https://en.wikipedia.org/wiki/Montgomery_modular_multiplication>).
//!
//! Example for a multi precision case:
//! ```rust
//! use finitelib::prelude::*;
//! use finitelib::gf::montgomery::Montgomery;
//!
//! // Basic multi precision data type (512-bit integer)
//! type U512 = bigi_of_bits!(512);
//!
//! // Define the ring
//! let R256 = bigi_ring_for_bigi!(U512);
//!
//! // Define the characteristic as a 256-bit prime
//! let characteristic = U512::from_decimal("67096435317933606252190858377894931905843553631817376158639971807689379094463");
//!
//! // Define GF(p) in the Montgomery representation
//! let gfm = Montgomery::new(R256, characteristic, 256);
//!
//! // Define two numbers
//! let a = U512::from(3);
//! let b = U512::from(2);
//!
//! // Convert into their Montgomery images
//! let am = gfm.convert_into(&a);
//! let bm = gfm.convert_into(&b);
//!
//! // Perform division
//! let cm = gfm.div(&am, &bm).unwrap();
//!
//! // Convert the result from its Montgomery image
//! let c = gfm.convert_from(&cm);
//!
//! assert_eq!(c, U512::from_decimal("33548217658966803126095429188947465952921776815908688079319985903844689547233"));
//!
//! // Check the result
//! assert_eq!(gfm.mul(&cm, &bm), am);
//! ```

use std::ops;

use crate::field::Field;
use crate::ring::EuclideanRing;


/// Galois prime field `GF(p)` in the Montgomery representation.
///
/// See [crate::gf::montgomery] for the full example.
#[derive(Debug, Clone)]
pub struct Montgomery<T, R> {
    ring: R,
    characteristic: T,
    power: usize,
    ni: T,
    one: T,
    mask: T,
    one3: T,
}


impl<T, R> Montgomery<T, R> where
        T: Clone + PartialEq + PartialOrd,
        for<'a> &'a T: ops::BitAnd<&'a T, Output = T> +
                       ops::Shl<usize, Output = T> +
                       ops::Shr<usize, Output = T>,
        R: EuclideanRing<Item = T> {
    /// Create Galois prime field `GF(p)` from the ring, prime characteristic
    /// and the power of 2 such that `characteristic < 2^power`.
    pub fn new(ring: R, characteristic: T, power: usize) -> Self {
        let mut r = &ring.one() << power;
        let mut ni = ring.euclidean_extended(&r, &characteristic).2;

        ring.neg_assign(&mut ni);

        // if ni < ring.zero() {
        //     ring.add_assign(&mut ni, &r);
        // }

        let mask = ring.sub(&r, &ring.one());
        ring.divrem(&mut r, &characteristic);
        let one = r.clone();

        let mut one3 = r.clone();
        for _ in 0..2 {
            one3 = &one3 << power;
            ring.divrem(&mut one3, &characteristic);
        }

        Self { ring, characteristic, power, ni, one, mask, one3 }
    }

    /// Convert the number into montgomery representation.
    pub fn convert_into(&self, a: &T) -> T {
        let mut r = a << self.power;
        self.ring.divrem(&mut r, &self.characteristic);
        r
    }

    /// Convert the number from montgomery representation.
    pub fn convert_from(&self, a: &T) -> T {
        self.mul(a, &self.ring.one())
    }
}


impl<T, R> Field for Montgomery<T, R> where 
        T: Clone + PartialEq + PartialOrd,
        for<'a> &'a T: ops::BitAnd<&'a T, Output = T> + 
                       ops::Shl<usize, Output = T> +
                       ops::Shr<usize, Output = T>,
        R: EuclideanRing<Item = T> {
    type Item = T;

    fn zero(&self) -> Self::Item {
        self.ring.zero()
    }

    fn one(&self) -> Self::Item {
        self.one.clone()
    }

    fn eq(&self, a: &Self::Item, b: &Self::Item) -> bool {
        self.ring.eq(a, b)
    }

    fn add(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
        let mut r = self.ring.add(a, b);
        if r >= self.characteristic {
            self.ring.sub_assign(&mut r, &self.characteristic);
        }
        r
    }

    fn sub(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
        if a >= b {
            self.ring.sub(a, b)
        } else {
            let mut r = self.ring.sub(&self.characteristic, b);
            self.ring.add_assign(&mut r, a);
            r
        }
    }

    fn mul(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
        let t = self.ring.mul(a, b);

        let mut u = &self.ring.add(
            &t,
            &self.ring.mul(
                &(&self.ring.mul(&t, &self.ni) & &self.mask),
                &self.characteristic
            )
        ) >> self.power;

        while u >= self.characteristic {
            self.ring.sub_assign(&mut u, &self.characteristic);
        }

        u
    }

    fn neg(&self, a: &Self::Item) -> Self::Item {
        if a == &self.zero() {
            self.zero()
        } else {
            self.ring.sub(&self.characteristic, a)
        }
    }

    fn inv(&self, a: &Self::Item) -> Option<Self::Item> {
        if a == &self.zero() {
            None
        } else {
            let i = self.ring.euclidean_extended(a, &self.characteristic).1;
            Some(self.mul(&self.one3, &i))
        }
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::rings::{Ri32, Ri64};
    use crate::utils;
    use test::Bencher;
    use rand::Rng;

    #[test]
    fn test() {
        let characteristic = 17;
        let power = utils::uint_bit_order(&characteristic);

        let mgr = Montgomery::new(Ri32, characteristic, power);

        let a = 11;

        assert_eq!(
            mgr.pow_scalar(&a, utils::int_to_bits_iter(characteristic - 1)),
            mgr.one()
        );
        
        assert_eq!(
            mgr.mul(&a, &mgr.inv(&a).unwrap()),
            mgr.one()
        );
    }

    #[bench]
    fn bench_i16_add(b: &mut Bencher) {
        let characteristic: i64 = 65129;  // 1682592883
        let power = utils::uint_bit_order(&characteristic);

        let mgr = Montgomery::new(Ri64, characteristic, power);

        let mut rng = rand::thread_rng();

        b.iter(|| {
            let x = rng.gen::<i64>().abs() % characteristic;
            let y = rng.gen::<i64>().abs() % characteristic;

            let _z = mgr.add(&x, &y);
        });
    }

    #[bench]
    fn bench_i16_mul(b: &mut Bencher) {
        let characteristic: i64 = 65129;
        let power = utils::uint_bit_order(&characteristic);

        let mgr = Montgomery::new(Ri64, characteristic, power);

        let mut rng = rand::thread_rng();

        b.iter(|| {
            let x = rng.gen::<i64>().abs() % characteristic;
            let y = rng.gen::<i64>().abs() % characteristic;

            let _z = mgr.mul(&x, &y);
        });
    }

    #[bench]
    fn bench_i16_inv(b: &mut Bencher) {
        let characteristic: i64 = 65129;
        let power = utils::uint_bit_order(&characteristic);

        let mgr = Montgomery::new(Ri64, characteristic, power);

        let mut rng = rand::thread_rng();

        b.iter(|| {
            let x = rng.gen::<i64>().abs() % characteristic;

            let _z = mgr.inv(&x);
        });
    }

    #[bench]
    fn bench_i16_pow_scalar(b: &mut Bencher) {
        let characteristic: i64 = 65129;
        let power = utils::uint_bit_order(&characteristic);

        let mgr = Montgomery::new(Ri64, characteristic, power);

        let mut rng = rand::thread_rng();

        let x = rng.gen::<i64>().abs() % characteristic;

        b.iter(|| {
            let y = mgr.pow_scalar(
                &x,
                utils::int_to_bits_iter(characteristic - 1)
            );
            assert_eq!(y, mgr.one());
        });
    }
}
