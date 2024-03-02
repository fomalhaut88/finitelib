//! This module implements operations over polynomials over a field. 
//!
//! A polynomial is represented as a vector of entities that are elements 
//! of a field.

use std::cmp;

use crate::field::Field;
use crate::ring::EuclideanRing;


/// Polynomial over a field that implements EuclideanRing so all te operations
/// over polynomials are available including addition, subtraction, 
/// multiplication, division with remainder, euclidean algorithm.
#[derive(Debug, Clone)]
pub struct Polynomial<F>(F);


impl<F> Polynomial<F> {
    pub fn new(field: F) -> Self {
        Self(field)
    }
}


impl<T, F> Polynomial<F> where 
        T: Clone, 
        F: Field<Item = T> {
    pub fn field(&self) -> &F {
        &self.0
    }

    pub fn degree(&self, a: &Vec<T>) -> Option<usize> {
        let mut size = a.len();
        while size > 0 {
            if !self.0.eq(&a[size - 1], &self.0.zero()) {
                break;
            }
            size -= 1;
        }
        if size == 0 { None } else { Some(size - 1) }
    }

    pub fn normalize(&self, a: &mut Vec<T>) {
        let size = self.degree(a)
            .map(|degree| degree + 1)
            .unwrap_or(0);
        a.truncate(size);
    }

    pub fn resize(&self, a: &mut Vec<T>, size: usize) {
        a.resize(size, self.0.zero());
    }

    pub fn mul_assign_const(&self, a: &mut Vec<T>, c: &T) {
        for e in a.iter_mut() {
            self.0.mul_assign(e, c);
        }
    }
}


impl<T, F> EuclideanRing for Polynomial<F>
        where T: Clone + PartialEq,
              F: Field<Item = T> {
    type Item = Vec<T>;

    fn zero(&self) -> Self::Item {
        vec![]
    }

    fn one(&self) -> Self::Item {
        vec![self.0.one()]
    }

    fn is_zero(&self, a: &Self::Item) -> bool {
        a.iter().all(|e| self.0.eq(e, &self.0.zero()))
    }

    fn eq(&self, a: &Self::Item, b: &Self::Item) -> bool {
        let min_size = cmp::min(a.len(), b.len());
        for idx in 0..min_size {
            if !self.0.eq(&a[idx], &b[idx]) {
                return false;
            }
        }
        for idx in min_size..a.len() {
            if !self.0.eq(&a[idx], &self.0.zero()) {
                return false;
            }
        }
        for idx in min_size..b.len() {
            if !self.0.eq(&b[idx], &self.0.zero()) {
                return false;
            }
        }
        true
    }

    fn add(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
        let mut r = a.clone();
        self.add_assign(&mut r, b);
        r
    }

    fn sub(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
        let mut r = a.clone();
        self.sub_assign(&mut r, b);
        r
    }

    fn mul(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
        if (a.len() != 0) && (b.len() != 0) {
            let r_size = a.len() + b.len() - 1;
            let mut r = vec![self.0.zero(); r_size];

            for cum in 0..r_size {
                for idx in 0..=cum {
                    if (idx < a.len()) && (cum - idx < b.len()) {
                        self.0.add_assign(
                            &mut r[cum],
                            &self.0.mul(&a[idx], &b[cum - idx])
                        );
                    }
                }
            }
            r
        } else {
            vec![]
        }
    }

    fn neg(&self, a: &Self::Item) -> Self::Item {
        let mut r = a.clone();
        self.neg_assign(&mut r);
        r
    }

    fn divrem(&self, a: &mut Self::Item, b: &Self::Item) -> Option<Self::Item> {
        if let Some(degree_b) = self.degree(b) {
            if let Some(degree_a) = self.degree(a) {
                if degree_a >= degree_b {
                    let degree_r = degree_a - degree_b;
                    let mut r = vec![self.0.zero(); degree_r + 1];
                    for idx in (0..=degree_r).rev() {
                        r[idx] = self.0.div(
                            &a[degree_b + idx], 
                            &b[degree_b]
                        ).unwrap();
                        for i in 0..=degree_b {
                            self.0.sub_assign(
                                &mut a[idx + i], 
                                &self.0.mul(&b[i], &r[idx])
                            );
                        }
                    }
                    Some(r)
                } else {
                    Some(vec![])
                }
            } else {
                Some(vec![])
            }
        } else {
            None
        }
    }

    fn add_assign(&self, a: &mut Self::Item, b: &Self::Item) {
        if b.len() > a.len() {
            a.resize(b.len(), self.0.zero());
        }
        for (idx, elem) in b.iter().enumerate() {
            self.0.add_assign(&mut a[idx], elem);
        }
    }

    fn sub_assign(&self, a: &mut Self::Item, b: &Self::Item) {
        if b.len() > a.len() {
            a.resize(b.len(), self.0.zero());
        }
        for (idx, elem) in b.iter().enumerate() {
            self.0.sub_assign(&mut a[idx], elem);
        }
    }

    fn neg_assign(&self, a: &mut Self::Item) {
        for elem in a.iter_mut() {
            self.0.neg_assign(elem);
        }
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::fields::{Ff32, Ff64};
    use test::Bencher;
    use rand::Rng;

    #[test]
    fn test_polynomial() {
        let pf32 = Polynomial::new(Ff32);

        assert_eq!(pf32.eq(&vec![3.5, 0.0], &vec![3.5]), true);
        assert_eq!(pf32.add(&vec![2.25, 1.125], &vec![3.5]), vec![5.75, 1.125]);
        assert_eq!(pf32.neg(&vec![2.25, 1.125]), vec![-2.25, -1.125]);
        assert_eq!(
            pf32.mul(&vec![1.5, 2.0], &vec![0.5, -1.0, 1.5]), 
            vec![0.75, -0.5, 0.25, 3.0]
        );
        assert_eq!(
            pf32.div(&vec![0.75, -0.5, 0.25, 3.0], &vec![1.5, 2.0]),
            Some(vec![0.5, -1.0, 1.5])
        );
        assert_eq!(
            pf32.rem(&vec![0.25, -0.5, 0.25, 3.0], &vec![1.5, 2.0]),
            Some(vec![-0.5, 0.0, 0.0, 0.0])
        );
    }

    #[bench]
    fn bench_neg(b: &mut Bencher) {
        let mut rng = rand::thread_rng();

        let pf64 = Polynomial::new(Ff64);
        let x = rng.gen::<[f64; 16]>().to_vec();

        b.iter(|| {
            let _y = pf64.neg(&x);
        });
    }

    #[bench]
    fn bench_neg_assign(b: &mut Bencher) {
        let mut rng = rand::thread_rng();

        let pf64 = Polynomial::new(Ff64);
        let mut x = rng.gen::<[f64; 16]>().to_vec();

        b.iter(|| {
            pf64.neg_assign(&mut x);
        });
    }

    #[bench]
    fn bench_add(b: &mut Bencher) {
        let mut rng = rand::thread_rng();

        let pf64 = Polynomial::new(Ff64);
        let x = rng.gen::<[f64; 16]>().to_vec();
        let y = rng.gen::<[f64; 16]>().to_vec();

        b.iter(|| {
            pf64.add(&x, &y);
        });
    }

    #[bench]
    fn bench_add_assign(b: &mut Bencher) {
        let mut rng = rand::thread_rng();

        let pf64 = Polynomial::new(Ff64);
        let mut x = rng.gen::<[f64; 16]>().to_vec();
        let y = rng.gen::<[f64; 16]>().to_vec();

        b.iter(|| {
            pf64.add_assign(&mut x, &y);
        });
    }

    #[bench]
    fn bench_mul(b: &mut Bencher) {
        let mut rng = rand::thread_rng();

        let pf64 = Polynomial::new(Ff64);
        let x = rng.gen::<[f64; 16]>().to_vec();
        let y = rng.gen::<[f64; 16]>().to_vec();

        b.iter(|| {
            pf64.mul(&x, &y);
        });
    }

    #[bench]
    fn bench_divrem(b: &mut Bencher) {
        let mut rng = rand::thread_rng();

        let pf64 = Polynomial::new(Ff64);
        let x = rng.gen::<[f64; 32]>().to_vec();
        let y = rng.gen::<[f64; 16]>().to_vec();

        b.iter(|| {
            let mut z = x.clone();
            pf64.divrem(&mut z, &y);
        });
    }
}
