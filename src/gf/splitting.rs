//! Galois field implementation of a prime characteristic and arbitraty degree.

use crate::ring::EuclideanRing;
use crate::field::Field;
use crate::polynomial::Polynomial;


#[derive(Debug, Clone)]
pub struct Splitting<T, F> {
    pub poly: Polynomial<F>,
    pub irreducible: Vec<T>,
    pub degree: usize,
}


impl<T, F> Splitting<T, F> where
        T: Clone + PartialEq,
        F: Field<Item = T> {
    pub fn new(field: F, irreducible: Vec<T>) -> Self {
        let poly = Polynomial::new(field);
        let degree = poly.degree(&irreducible).unwrap();
        Self { poly, irreducible, degree }
    }
}


impl<T, F> Field for Splitting<T, F> where 
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

        let gfe = Splitting::new(
            Prime::new(Ri64, characteristic),
            irreducible
        );

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

        let mut rng = rand::thread_rng();

        b.iter(|| {
            let _x = vec![
                rng.gen::<i64>().abs() % characteristic,
                rng.gen::<i64>().abs() % characteristic,
            ];
        });
    }

    #[bench]
    fn bench_i32_add(b: &mut Bencher) {
        let characteristic = 1682592883;
        let irreducible = vec![1, 0, 1];

        let gfe = Splitting::new(
            Prime::new(Ri64, characteristic),
            irreducible
        );

        let mut rng = rand::thread_rng();

        b.iter(|| {
            let x = vec![
                rng.gen::<i64>().abs() % characteristic,
                rng.gen::<i64>().abs() % characteristic,
            ];

            let y = vec![
                rng.gen::<i64>().abs() % characteristic,
                rng.gen::<i64>().abs() % characteristic,
            ];

            let _z = gfe.add(&x, &y);
        });
    }

    #[bench]
    fn bench_i32_mul(b: &mut Bencher) {
        let characteristic = 1682592883;
        let irreducible = vec![1, 0, 1];

        let gfe = Splitting::new(
            Prime::new(Ri64, characteristic),
            irreducible
        );

        let mut rng = rand::thread_rng();

        b.iter(|| {
            let x = vec![
                rng.gen::<i64>().abs() % characteristic,
                rng.gen::<i64>().abs() % characteristic,
            ];

            let y = vec![
                rng.gen::<i64>().abs() % characteristic,
                rng.gen::<i64>().abs() % characteristic,
            ];

            let _z = gfe.mul(&x, &y);
        });
    }

    #[bench]
    fn bench_i32_inv(b: &mut Bencher) {
        let characteristic = 1682592883;
        let irreducible = vec![1, 0, 1];

        let gfe = Splitting::new(
            Prime::new(Ri64, characteristic),
            irreducible
        );

        let mut rng = rand::thread_rng();

        b.iter(|| {
            let x = vec![
                rng.gen::<i64>().abs() % characteristic,
                rng.gen::<i64>().abs() % characteristic,
            ];
            let _z = gfe.inv(&x).unwrap();
        });
    }

    #[bench]
    fn bench_i32_pow_scalar(b: &mut Bencher) {
        let characteristic = 1682592883;
        let irreducible = vec![1, 0, 1];

        let gfe = Splitting::new(
            Prime::new(Ri64, characteristic),
            irreducible
        );

        let mut rng = rand::thread_rng();

        b.iter(|| {
            let x = vec![
                rng.gen::<i64>().abs() % characteristic,
                rng.gen::<i64>().abs() % characteristic,
            ];
            let y = gfe.pow_scalar(
                &x,
                utils::int_to_bits_iter(characteristic * characteristic - 1)
            );
            assert_eq!(y, vec![1, 0]);
        });
    }
}
