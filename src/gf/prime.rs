//! Galois field implementation of a prime characteristic and degree `1` 
//! ([Prime field](https://en.wikipedia.org/wiki/Characteristic_(algebra)#prime_field) `GF(p)`).
//!
//! Example for a multi precision case:
//! ```rust
//! use finitelib::prelude::*;
//! use finitelib::gf::prime::Prime;
//!
//! // Basic multi precision data type (256-bit integer)
//! type U256 = bigi_of_bits!(256);
//!
//! // Define the ring and characteristic
//! let R256 = bigi_ring_for_bigi!(U256);
//! let characteristic = U256::from_decimal("67096435317933606252190858377894931905843553631817376158639971807689379094463");
//!
//! // Define the prime field
//! let gf = Prime::new(R256, characteristic);
//!
//! // Perform division
//! let x = gf.div(&U256::from(3), &U256::from(2)).unwrap();
//!
//! assert_eq!(x, U256::from_decimal("33548217658966803126095429188947465952921776815908688079319985903844689547233"));
//!
//! // Check the result
//! let y = gf.mul(&x, &U256::from(2));
//!
//! assert_eq!(y, U256::from(3));
//! ```

use crate::field::Field;
use crate::ring::EuclideanRing;


/// Prime field structure that contains the ring and characteristic.
///
/// See [crate::gf::prime] for the full example.
#[derive(Debug, Clone)]
pub struct Prime<T, R> {
    ring: R,
    characteristic: T,
}


impl<T, R> Prime<T, R> {
    /// Create a prime field object from the ring and characteristic.
    pub fn new(ring: R, characteristic: T) -> Self {
        Self { ring, characteristic }
    }

    /// Get ring.
    pub fn ring(&self) -> &R {
        &self.ring
    }

    /// Get characteristic.
    pub fn characteristic(&self) -> &T {
        &self.characteristic
    }
}


impl<T, R> Field for Prime<T, R> where 
        T: Clone + PartialEq + PartialOrd,
        R: EuclideanRing<Item = T> {
    type Item = T;

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
        self.ring.addrem(a, b, &self.characteristic)
    }

    fn sub(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
        self.ring.subrem(a, b, &self.characteristic)
    }

    fn mul(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
        self.ring.mulrem(a, b, &self.characteristic)
    }

    fn div(&self, a: &Self::Item, b: &Self::Item) -> Option<Self::Item> {
        self.inv(b).map(|i| self.mul(a, &i))
    }

    fn neg(&self, a: &Self::Item) -> Self::Item {
        if self.ring.is_zero(a) {
            self.zero()
        } else {
            self.ring.sub(&self.characteristic, a)
        }
    }

    fn inv(&self, a: &Self::Item) -> Option<Self::Item> {
        if self.ring.is_zero(a) {
            None
        } else {
            let mut i = self.ring.euclidean_extended(a, &self.characteristic).1;

            // Normalize `i` if it is beyond `0 <= i < characteristic`,
            // because it means negative `i`: literal (`i < 0`) or overflowing
            // (`i >= characteristic`). In both cases adding `characteristic`
            // is enough.
            if (i < self.zero()) || (i >= self.characteristic) {
                self.ring.add_assign(&mut i, &self.characteristic);
            }

            Some(i)
        }
    }

    fn add_assign(&self, a: &mut Self::Item, b: &Self::Item) {
        self.ring.addrem_assign(a, b, &self.characteristic);
    }

    fn sub_assign(&self, a: &mut Self::Item, b: &Self::Item) {
        self.ring.subrem_assign(a, b, &self.characteristic);
    }

    fn mul_assign(&self, a: &mut Self::Item, b: &Self::Item) {
        self.ring.mulrem_assign(a, b, &self.characteristic);
    }

    fn div_assign(&self, a: &mut Self::Item, b: &Self::Item) {
        *a = self.div(a, b).unwrap();
    }

    fn neg_assign(&self, a: &mut Self::Item) {
        if !self.ring.is_zero(a) {
            *a = self.ring.sub(&self.characteristic, a);
        }
    }

    fn inv_assign(&self, a: &mut Self::Item) {
        *a = self.inv(a).unwrap();
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::rings::Ri64;
    use crate::utils;
    use crate::bigi::prelude::*;
    use test::Bencher;
    use rand::Rng;

    #[test]
    fn test() {
        let characteristic: i64 = 11;

        let gfp = Prime::new(Ri64, characteristic);

        assert_eq!(gfp.zero(), 0);
        assert_eq!(gfp.one(), 1);

        let x = 5;
        let y = 8;
        let z = gfp.div(&x, &y).unwrap();

        assert_eq!(gfp.mul(&y, &z), x);

        assert_eq!(
            gfp.pow_scalar(&x, utils::int_to_bits_iter(characteristic - 1)), 
            1
        );
        assert_eq!(
            gfp.pow_scalar(&y, utils::int_to_bits_iter(characteristic - 1)), 
            1
        );
        assert_eq!(
            gfp.pow_scalar(&z, utils::int_to_bits_iter(characteristic - 1)), 
            1
        );
    }

    #[test]
    fn test_bigi() {
        let characteristic = Bigi::<4>::from_decimal(
            "99893747326269902623342789505183727815353444030279517503290826441538462138393"
        );

        let gf = Prime::new(BigiRing::<4>, characteristic);

        let a = Bigi::<4>::from_decimal(
            "45913295509759029275871877517545102762287997160146069089066098115479219152497"
        );

        let i = gf.inv(&a).unwrap();

        assert_eq!(gf.mul(&a, &i), Bigi::from(1));
        assert_eq!(
            i.to_decimal(), 
            "27310768115836180878365239736455977992726003595217036692475308190755958661620"
        );
    }

    #[bench]
    fn bench_i16_gen(b: &mut Bencher) {
        let characteristic: i64 = 65129;  // 1682592883

        let mut rng = rand::rng();

        b.iter(|| {
            let _x = rng.random::<i64>().abs() % characteristic;
        });
    }

    #[bench]
    fn bench_i16_add(b: &mut Bencher) {
        let characteristic: i64 = 65129;
        let gfp = Prime::new(Ri64, characteristic);

        let mut rng = rand::rng();

        b.iter(|| {
            let x = rng.random::<i64>().abs() % characteristic;
            let y = rng.random::<i64>().abs() % characteristic;

            let _z = gfp.add(&x, &y);
        });
    }

    #[bench]
    fn bench_i16_mul(b: &mut Bencher) {
        let characteristic: i64 = 65129;
        let gfp = Prime::new(Ri64, characteristic);

        let mut rng = rand::rng();

        b.iter(|| {
            let x = rng.random::<i64>().abs() % characteristic;
            let y = rng.random::<i64>().abs() % characteristic;

            let _z = gfp.mul(&x, &y);
        });
    }

    #[bench]
    fn bench_i16_inv(b: &mut Bencher) {
        let characteristic: i64 = 65129;
        let gfp = Prime::new(Ri64, characteristic);

        let mut rng = rand::rng();

        b.iter(|| {
            let x = rng.random::<i64>().abs() % characteristic;

            let _z = gfp.inv(&x);
        });
    }

    #[bench]
    fn bench_i16_pow_scalar(b: &mut Bencher) {
        let characteristic: i64 = 65129;
        let gfp = Prime::new(Ri64, characteristic);

        let mut rng = rand::rng();

        let x = rng.random::<i64>().abs() % characteristic;

        b.iter(|| {
            let y = gfp.pow_scalar(
                &x,
                utils::int_to_bits_iter(characteristic - 1)
            );
            assert_eq!(y, 1);
        });
    }

    #[bench]
    fn bench_bigi_add(bencher: &mut Bencher) {
        let characteristic = Bigi::<4>::from_decimal(
            "99893747326269902623342789505183727815353444030279517503290826441538462138393"
        );

        let gf = Prime::new(BigiRing::<4>, characteristic);

        let a = Bigi::<4>::from_decimal(
            "45913295509759029275871877517545102762287997160146069089066098115479219152497"
        );

        let b = Bigi::<4>::from_decimal(
            "27310768115836180878365239736455977992726003595217036692475308190755958661620"
        );

        bencher.iter(|| {
            let _c = gf.add(&a, &b);
        });
    }

    #[bench]
    fn bench_bigi_sub(bencher: &mut Bencher) {
        let characteristic = Bigi::<4>::from_decimal(
            "99893747326269902623342789505183727815353444030279517503290826441538462138393"
        );

        let gf = Prime::new(BigiRing::<4>, characteristic);

        let a = Bigi::<4>::from_decimal(
            "45913295509759029275871877517545102762287997160146069089066098115479219152497"
        );

        let b = Bigi::<4>::from_decimal(
            "27310768115836180878365239736455977992726003595217036692475308190755958661620"
        );

        bencher.iter(|| {
            let _c = gf.sub(&a, &b);
        });
    }

    #[bench]
    fn bench_bigi_mul(bencher: &mut Bencher) {
        let characteristic = Bigi::<4>::from_decimal(
            "99893747326269902623342789505183727815353444030279517503290826441538462138393"
        );

        let gf = Prime::new(BigiRing::<4>, characteristic);

        let a = Bigi::<4>::from_decimal(
            "45913295509759029275871877517545102762287997160146069089066098115479219152497"
        );

        let b = Bigi::<4>::from_decimal(
            "27310768115836180878365239736455977992726003595217036692475308190755958661620"
        );

        bencher.iter(|| {
            let _c = gf.mul(&a, &b);
        });
    }

    #[bench]
    fn bench_bigi_inv(bencher: &mut Bencher) {
        let characteristic = Bigi::<4>::from_decimal(
            "99893747326269902623342789505183727815353444030279517503290826441538462138393"
        );

        let gf = Prime::new(BigiRing::<4>, characteristic);

        let a = Bigi::<4>::from_decimal(
            "45913295509759029275871877517545102762287997160146069089066098115479219152497"
        );

        bencher.iter(|| {
            let _i = gf.inv(&a).unwrap();
        });
    }

    #[bench]
    fn bench_bigi_pow_scalar(bencher: &mut Bencher) {
        let characteristic = Bigi::<4>::from_decimal(
            "99893747326269902623342789505183727815353444030279517503290826441538462138393"
        );

        let gf = Prime::new(BigiRing::<4>, characteristic.clone());

        let a = Bigi::<4>::from_decimal(
            "45913295509759029275871877517545102762287997160146069089066098115479219152497"
        );

        bencher.iter(|| {
            let b = gf.pow_scalar(&a, characteristic.bit_iter());
            assert_eq!(b, a);
        });
    }
}
