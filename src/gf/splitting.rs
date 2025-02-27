//! Galois field implementation of a prime characteristic and arbitraty degree
//! ([Splitting field](https://en.wikipedia.org/wiki/Splitting_field) `GF(p^m)`).
//!
//! Example for a multi precision case:
//! ```rust
//! use finitelib::prelude::*;
//! use finitelib::gf::prime::Prime;
//! use finitelib::gf::splitting::Splitting;
//!
//! // Basic multi precision data type (256-bit integer)
//! type U256 = bigi_of_bits!(256);
//!
//! // Define the ring, characteristic and irreducible polynomial
//! let R256 = bigi_ring_for_bigi!(U256);
//! let characteristic = U256::from_decimal("67096435317933606252190858377894931905843553631817376158639971807689379094463");
//! let irreducible = vec![U256::from(1), U256::from(0), U256::from(1)];  // 1 + x^2
//!
//! // Define prime field and splitting field
//! let gfp = Prime::new(R256, characteristic);
//! let gfs = Splitting::new(&gfp, irreducible);
//!
//! // Perform division
//! let x = gfs.div(
//!     &vec![U256::from(1), U256::from(2)],
//!     &vec![U256::from(3), U256::from(4)],
//! ).unwrap();
//!
//! assert_eq!(x, vec![U256::from_decimal("8051572238152032750262903005347391828701226435818085139036796616922725491336"), 
//!                    U256::from_decimal("56361005667064229251840321037431742800908585050726595973257576318459078439349")]);
//!
//! // Check the result
//! let y = gfs.mul(&x, &vec![U256::from(3), U256::from(4)]);
//!
//! assert_eq!(y, vec![U256::from(1), U256::from(2)]);
//! ```

use crate::ring::EuclideanRing;
use crate::field::Field;
use crate::polynomial::Polynomial;


/// Splitting field structure that contains polynomial object 
/// (for the necessary arithmetic), irreducible polynomial (as vector) and
/// the degree.
///
/// See [crate::gf::splitting] for the full example.
#[derive(Debug, Clone)]
pub struct Splitting<'a, T, F> {
    poly: Polynomial<'a, F>,
    irreducible: Vec<T>,
    degree: usize,
}


impl<'a, T, F> Splitting<'a, T, F> where
        T: Clone + PartialEq,
        F: Field<Item = T> {
    /// Create splitting field from the base field link and 
    /// irreducible polynomial. The degree is calculated and the degree of
    /// the irreducible polynomial.
    pub fn new(field: &'a F, irreducible: Vec<T>) -> Self {
        let poly = Polynomial::new(field);
        let degree = poly.degree(&irreducible).unwrap();
        Self { poly, irreducible, degree }
    }
}


impl<'a, T, F> Field for Splitting<'a, T, F> where 
        T: Clone + PartialEq,
        F: Field<Item = T> {
    type Item = Vec<T>;

    fn zero(&self) -> Self::Item {
        let mut r = self.poly.zero();
        self.poly.resize(&mut r, self.degree);
        r
    }

    fn one(&self) -> Self::Item {
        let mut r = self.poly.one();
        self.poly.resize(&mut r, self.degree);
        r
    }

    fn eq(&self, a: &Self::Item, b: &Self::Item) -> bool {
        self.poly.eq(a, b)
    }

    fn add(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
        self.poly.add(a, b)
    }

    fn sub(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
        self.poly.sub(a, b)
    }

    fn neg(&self, a: &Self::Item) -> Self::Item {
        self.poly.neg(a)
    }

    fn mul(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
        let mut r = self.poly.mul(a, b);
        self.poly.divrem(&mut r, &self.irreducible);
        self.poly.resize(&mut r, self.degree);
        r
    }

    fn inv(&self, a: &Self::Item) -> Option<Self::Item> {
        if self.poly.is_zero(a) {
            None
        } else {
            let (g, mut r, _) = self.poly.euclidean_extended(
                a, &self.irreducible
            );
            let i = self.poly.field().inv(&g[0]).unwrap();
            self.poly.mul_assign_const(&mut r, &i);
            self.poly.resize(&mut r, self.degree);
            Some(r)
        }
    }

    fn add_assign(&self, a: &mut Self::Item, b: &Self::Item) {
        self.poly.add_assign(a, b)
    }

    fn sub_assign(&self, a: &mut Self::Item, b: &Self::Item) {
        self.poly.sub_assign(a, b)
    }

    fn neg_assign(&self, a: &mut Self::Item) {
        self.poly.neg_assign(a)
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::rings::Ri64;
    use crate::utils;
    use crate::gf::prime::Prime;
    use test::Bencher;
    use rand::Rng;

    #[test]
    fn test() {
        let characteristic = 5;
        let irreducible = vec![2, 0, 1];

        let fld = Prime::new(Ri64, characteristic);
        let gfe = Splitting::new(&fld, irreducible);

        assert_eq!(gfe.zero(), vec![0, 0]);
        assert_eq!(gfe.one(), vec![1, 0]);
        assert_eq!(gfe.eq(&vec![2, 0], &vec![2, 0]), true);
        assert_eq!(gfe.eq(&vec![2, 4], &vec![2, 3]), false);
        assert_eq!(gfe.add(&vec![2, 3], &vec![2, 4]), vec![4, 2]);
        assert_eq!(gfe.sub(&vec![2, 3], &vec![2, 4]), vec![0, 4]);
        assert_eq!(gfe.neg(&vec![2, 3]), vec![3, 2]);
        assert_eq!(gfe.mul(&vec![2, 3], &vec![2, 4]), vec![0, 4]);
        assert_eq!(gfe.inv(&vec![2, 3]), Some(vec![1, 1]));
        assert_eq!(gfe.mul(&vec![2, 3], &vec![1, 1]), vec![1, 0]);

        assert!(
            gfe.pow_scalar(
                &vec![2, 3],
                utils::int_to_bits_iter(characteristic * characteristic - 1)
            ) == vec![1, 0]
        );
    }

    #[bench]
    fn bench_i32_gen(b: &mut Bencher) {
        let characteristic: i64 = 1682592883;

        let mut rng = rand::rng();

        b.iter(|| {
            let _x = vec![
                rng.random::<i64>().abs() % characteristic,
                rng.random::<i64>().abs() % characteristic,
            ];
        });
    }

    #[bench]
    fn bench_i32_add(b: &mut Bencher) {
        let characteristic = 1682592883;
        let irreducible = vec![1, 0, 1];

        let fld = Prime::new(Ri64, characteristic);
        let gfe = Splitting::new(&fld, irreducible);

        let mut rng = rand::rng();

        b.iter(|| {
            let x = vec![
                rng.random::<i64>().abs() % characteristic,
                rng.random::<i64>().abs() % characteristic,
            ];

            let y = vec![
                rng.random::<i64>().abs() % characteristic,
                rng.random::<i64>().abs() % characteristic,
            ];

            let _z = gfe.add(&x, &y);
        });
    }

    #[bench]
    fn bench_i32_mul(b: &mut Bencher) {
        let characteristic = 1682592883;
        let irreducible = vec![1, 0, 1];

        let fld = Prime::new(Ri64, characteristic);
        let gfe = Splitting::new(&fld, irreducible);

        let mut rng = rand::rng();

        b.iter(|| {
            let x = vec![
                rng.random::<i64>().abs() % characteristic,
                rng.random::<i64>().abs() % characteristic,
            ];

            let y = vec![
                rng.random::<i64>().abs() % characteristic,
                rng.random::<i64>().abs() % characteristic,
            ];

            let _z = gfe.mul(&x, &y);
        });
    }

    #[bench]
    fn bench_i32_inv(b: &mut Bencher) {
        let characteristic = 1682592883;
        let irreducible = vec![1, 0, 1];

        let fld = Prime::new(Ri64, characteristic);
        let gfe = Splitting::new(&fld, irreducible);

        let mut rng = rand::rng();

        b.iter(|| {
            let x = vec![
                rng.random::<i64>().abs() % characteristic,
                rng.random::<i64>().abs() % characteristic,
            ];
            let _z = gfe.inv(&x).unwrap();
        });
    }

    #[bench]
    fn bench_i32_pow_scalar(b: &mut Bencher) {
        let characteristic = 1682592883;
        let irreducible = vec![1, 0, 1];

        let fld = Prime::new(Ri64, characteristic);
        let gfe = Splitting::new(&fld, irreducible);

        let mut rng = rand::rng();

        b.iter(|| {
            let x = vec![
                rng.random::<i64>().abs() % characteristic,
                rng.random::<i64>().abs() % characteristic,
            ];
            let y = gfe.pow_scalar(
                &x,
                utils::int_to_bits_iter(characteristic * characteristic - 1)
            );
            assert_eq!(y, vec![1, 0]);
        });
    }
}
