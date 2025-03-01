//! A module that contains a trait for Euclidean rings.
//!
//! Euclidean rings are required in the cases where we naturally need
//! [The Euclidean Extended Algorithm](https://en.wikipedia.org/wiki/Extended_Euclidean_algorithm).
//! For example, to preform division in a finite field.
//!
//! Go to [EuclideanRing](crate::ring::EuclideanRing) to view the 
//! implementation example.

use std::mem;

use crate::utils;
use crate::group::Group;


/// Euclidean ring trait.
///
/// Example for `i64`:
///
/// ```rust
/// use finitelib::prelude::*;
///
/// struct RingForI64;
///
/// impl EuclideanRing for RingForI64 {
///     type Item = i64;
///
///     fn zero(&self) -> Self::Item {
///         0
///     }
///
///     fn one(&self) -> Self::Item {
///         1
///     }
///
///     fn eq(&self, a: &Self::Item, b: &Self::Item) -> bool {
///         a == b
///     }
///
///     fn add(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
///         a + b
///     }
///
///     fn mul(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
///         a * b
///     }
///
///     fn neg(&self, a: &Self::Item) -> Self::Item {
///         - a
///     }
///
///     fn divrem(&self, a: &mut Self::Item, b: &Self::Item) -> 
///             Option<Self::Item> {
///         if *b == 0 {
///             None
///         } else {
///             let q = a.div_euclid(*b);
///             *a -= q * b;
///             Some(q)
///         }
///     }
/// }
///
/// let (gcd, a, b) = RingForI64.euclidean_extended(&45, &33);
///
/// assert_eq!((gcd, a, b), (3, 3, -4));
/// assert_eq!(45 * a + 33 * b, gcd);
/// ```
pub trait EuclideanRing where 
        Self::Item: Clone + PartialEq {
    /// The type of the ring elements.
    type Item;

    /// Get the zero element of the ring (the identity by addition).
    fn zero(&self) -> Self::Item;

    /// Get the one element of the ring (the identity by multiplication).
    fn one(&self) -> Self::Item;

    /// Perform the equity operation in the ring.
    fn eq(&self, a: &Self::Item, b: &Self::Item) -> bool;

    /// Perform addition operation in the ring.
    fn add(&self, a: &Self::Item, b: &Self::Item) -> Self::Item;

    /// Perform multiplication operation in the ring.
    fn mul(&self, a: &Self::Item, b: &Self::Item) -> Self::Item;

    /// Get inversed element by addition.
    fn neg(&self, a: &Self::Item) -> Self::Item;

    /// Perform division with remainder.
    fn divrem(&self, a: &mut Self::Item, b: &Self::Item) -> Option<Self::Item>;

    /// Check the element has zero norm.
    fn is_zero(&self, a: &Self::Item) -> bool {
        a == &self.zero()
    }

    /// Perform multiplication in the group by a scalar given as an iterator 
    /// of bits according to [the double and add algorithm](https://en.wikipedia.org/wiki/Exponentiation_by_squaring).
    fn mul_scalar<I>(&self, a: &Self::Item, bits_iter: I) -> Self::Item 
            where I: Iterator<Item = bool> {
        utils::exp_by_sqr(a, bits_iter, || self.zero(), |a, b| self.add(a, b))
    }

    /// Perform multiplication in the group by a scalar given as an iterator 
    /// of bits according to [the exponentiation by squaring algorithm](https://en.wikipedia.org/wiki/Exponentiation_by_squaring).
    fn pow_scalar<I>(&self, a: &Self::Item, bits_iter: I) -> Self::Item 
            where I: Iterator<Item = bool> {
        utils::exp_by_sqr(a, bits_iter, || self.one(), |a, b| self.mul(a, b))
    }

    /// Perform `sub` operation. By default it is implemented through 
    /// `add` and `neg` but it can be overridden for optimization purposes.
    fn sub(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
        self.add(a, &self.neg(b))
    }

    /// Perform `div` operation. By default it is implemented through 
    /// `divrem` but it can be overridden for optimization purposes.
    fn div(&self, a: &Self::Item, b: &Self::Item) -> Option<Self::Item> {
        let mut r = a.clone();
        self.divrem(&mut r, b)
    }

    /// Perform `rem` operation. By default it is implemented through 
    /// `divrem` but it can be overridden for optimization purposes.
    fn rem(&self, a: &Self::Item, b: &Self::Item) -> Option<Self::Item> {
        let mut r = a.clone();
        self.divrem(&mut r, b).map(|_| r)
    }

    /// Perform `add_assign` operation. By default it is implemented through 
    /// `add` but it can be overridden for optimization purposes.
    fn add_assign(&self, a: &mut Self::Item, b: &Self::Item) {
        *a = self.add(a, b);
    }

    /// Perform `sub_assign` operation. By default it is implemented through 
    /// `sub` but it can be overridden for optimization purposes.
    fn sub_assign(&self, a: &mut Self::Item, b: &Self::Item) {
        *a = self.sub(a, b);
    }

    /// Perform `mul_assign` operation. By default it is implemented through 
    /// `mul` but it can be overridden for optimization purposes.
    fn mul_assign(&self, a: &mut Self::Item, b: &Self::Item) {
        *a = self.mul(a, b);
    }

    /// Perform `neg_assign` operation. By default it is implemented through 
    /// `neg` but it can be overridden for optimization purposes.
    fn neg_assign(&self, a: &mut Self::Item) {
        *a = self.neg(a);
    }

    /// Perform `mul_scalar_assign` operation. By default it is implemented  
    /// through `mul_scalar` but it can be overridden for optimization purposes.
    fn mul_scalar_assign<I>(&self, a: &mut Self::Item, bits_iter: I)
            where I: Iterator<Item = bool> {
        *a = self.mul_scalar(a, bits_iter);
    }

    /// Perform `pow_scalar_assign` operation. By default it is implemented  
    /// through `pow_scalar` but it can be overridden for optimization purposes.
    fn pow_scalar_assign<I>(&self, a: &mut Self::Item, bits_iter: I)
            where I: Iterator<Item = bool> {
        *a = self.pow_scalar(a, bits_iter);
    }

    /// Represent the field as a group by addition.
    fn as_add_group(&self) -> RingAddGroup<Self> {
        RingAddGroup {
            ring: self
        }
    }

    /// Find GCD by euclidean algorithm.
    fn euclidean(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
        let mut a = a.clone();
        let mut b = b.clone();
        while !self.is_zero(&b) {
            self.divrem(&mut a, &b);
            mem::swap(&mut a, &mut b);
        }
        a
    }

    /// An implementation of [the euclidean extended algorithm](https://en.wikipedia.org/wiki/Extended_Euclidean_algorithm).
    /// For given a and b it searches for x and y such that:
    /// a * x + b * y = GCD
    fn euclidean_extended(&self, a: &Self::Item, b: &Self::Item) -> 
            (Self::Item, Self::Item, Self::Item) {
        let mut a = a.clone();
        let mut b = b.clone();

        let (mut aa, mut ab) = (self.one(), self.zero());
        let (mut ba, mut bb) = (self.zero(), self.one());

        while !self.is_zero(&b) {
            let q = self.divrem(&mut a, &b).unwrap();

            self.sub_assign(&mut aa, &self.mul(&q, &ba));
            self.sub_assign(&mut ab, &self.mul(&q, &bb));

            mem::swap(&mut a, &mut b);
            mem::swap(&mut aa, &mut ba);
            mem::swap(&mut ab, &mut bb);
        }

        (a, aa, ab)
    }

    /// Modular addition. It can be overridden for optimization purposes.
    /// `a` and `b` are supposed to be: `0 <= a, b < m`.
    fn addrem(&self, a: &Self::Item, b: &Self::Item, m: &Self::Item) -> 
            Self::Item {
        let mut r = self.add(a, b);
        self.divrem(&mut r, m).unwrap();
        r
    }

    /// Modular subtraction. It can be overridden for optimization purposes.
    fn subrem(&self, a: &Self::Item, b: &Self::Item, m: &Self::Item) -> 
            Self::Item {
        let mut r = self.sub(a, b);
        self.divrem(&mut r, m).unwrap();
        r
    }

    /// Modular multiplication. It can be overridden for optimization purposes.
    /// `a` and `b` are supposed to be: `0 <= a,b < m`.
    fn mulrem(&self, a: &Self::Item, b: &Self::Item, m: &Self::Item) -> 
            Self::Item {
        let mut r = self.mul(a, b);
        self.divrem(&mut r, m).unwrap();
        r
    }

    /// Modular assigned addition. It can be overridden for optimization 
    /// purposes.
    /// `a` and `b` are supposed to be: `0 <= a,b < m`.
    fn addrem_assign(&self, a: &mut Self::Item, b: &Self::Item, 
            m: &Self::Item) {
        self.add_assign(a, b);
        self.divrem(a, m).unwrap();
    }

    /// Modular assigned subtraction. It can be overridden for optimization 
    /// purposes.
    /// `a` and `b` are supposed to be: `0 <= a,b < m`.
    fn subrem_assign(&self, a: &mut Self::Item, b: &Self::Item, 
            m: &Self::Item) {
        self.sub_assign(a, b);
        self.divrem(a, m).unwrap();
    }

    /// Modular assigned multiplication. It can be overridden for optimization 
    /// purposes.
    /// `a` and `b` are supposed to be: `0 <= a,b < m`.
    fn mulrem_assign(&self, a: &mut Self::Item, b: &Self::Item, 
            m: &Self::Item) {
        self.mul_assign(a, b);
        self.divrem(a, m).unwrap();
    }

    /// Modular multiplication by a scalar given as a bits iterator. 
    /// It can be overridden for optimization purposes.
    /// `a` is supposed to be: `0 <= a < m`.
    fn mulrem_scalar<I>(&self, a: &Self::Item, bits_iter: I, m: &Self::Item) -> 
            Self::Item where I: Iterator<Item = bool> {
        utils::exp_by_sqr(a, bits_iter, || self.zero(), 
                          |a, b| self.addrem(a, b, m))
    }

    /// Modular power by a scalar given as a bits iterator. 
    /// It can be overridden for optimization purposes.
    /// `a` is supposed to be: `0 <= a < m`.
    fn powrem_scalar<I>(&self, a: &Self::Item, bits_iter: I, m: &Self::Item) -> 
            Self::Item where I: Iterator<Item = bool> {
        utils::exp_by_sqr(a, bits_iter, || self.one(), 
                          |a, b| self.mulrem(a, b, m))
    }

    /// Modular assugned multiplication by a scalar given as a bits iterator. 
    /// It can be overridden for optimization purposes.
    /// `a` is supposed to be: `0 <= a < m`.
    fn mulrem_scalar_assign<I>(&self, a: &mut Self::Item, bits_iter: I, 
            m: &Self::Item) where I: Iterator<Item = bool> {
        *a = self.mulrem_scalar(a, bits_iter, m);
    }

    /// Modular assugned power by a scalar given as a bits iterator. 
    /// It can be overridden for optimization purposes.
    /// `a` is supposed to be: `0 <= a < m`.
    fn powrem_scalar_assign<I>(&self, a: &mut Self::Item, bits_iter: I, 
            m: &Self::Item) where I: Iterator<Item = bool> {
        *a = self.powrem_scalar(a, bits_iter, m);
    }
}


/// Addition group over an euclidean ring
pub struct RingAddGroup<'a, R: ?Sized> {
    ring: &'a R,
}


impl<'a, R: EuclideanRing> Group for RingAddGroup<'a, R> {
    type Item = R::Item;

    fn zero(&self) -> Self::Item {
        self.ring.zero()
    }

    fn eq(&self, a: &Self::Item, b: &Self::Item) -> bool {
        self.ring.eq(a, b)
    }

    fn add(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
        self.ring.add(a, b)
    }

    fn neg(&self, a: &Self::Item) -> Self::Item {
        self.ring.neg(a)
    }

    fn mul_scalar<I>(&self, a: &Self::Item, bits_iter: I) -> Self::Item 
            where I: Iterator<Item = bool> {
        self.ring.mul_scalar(a, bits_iter)
    }

    fn sub(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
        self.ring.sub(a, b)
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

    fn mul_scalar_assign<I>(&self, a: &mut Self::Item, bits_iter: I)
            where I: Iterator<Item = bool> {
        self.ring.mul_scalar_assign(a, bits_iter);
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    struct Ri64;

    impl EuclideanRing for Ri64 {
        type Item = i64;

        fn zero(&self) -> Self::Item {
            0
        }

        fn one(&self) -> Self::Item {
            1
        }

        fn eq(&self, a: &Self::Item, b: &Self::Item) -> bool {
            a == b
        }

        fn add(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
            a + b
        }

        fn mul(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
            a * b
        }

        fn neg(&self, a: &Self::Item) -> Self::Item {
            - a
        }

        fn divrem(&self, a: &mut Self::Item, b: &Self::Item) -> 
                Option<Self::Item> {
            if *b == 0 {
                None
            } else {
                let q = a.div_euclid(*b);
                *a -= q * b;
                Some(q)
            }
        }
    }

    #[test]
    fn test_euclidean() {
        let gcd = Ri64.euclidean(&45, &33);
        assert_eq!(gcd, 3);
    }

    #[test]
    fn test_euclidean_extended() {
        let (gcd, a, b) = Ri64.euclidean_extended(&45, &33);
        assert_eq!((gcd, a, b), (3, 3, -4));
        assert_eq!(45 * a + 33 * b, gcd);
    }
}
