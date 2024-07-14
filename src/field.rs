//! A module that contains a trait for mathematical field objects.
//!
//! Go to [Field](crate::field::Field) to view the implementation example.

use crate::utils;
use crate::group::Group;


/// A trait for a field over the type `Item`.
///
/// Use example:
///
/// ```
/// use finitelib::field::Field;
/// use finitelib::ring::EuclideanRing;
/// use finitelib::common::rings::Ri64;
///
/// struct GF(u64);
/// 
/// impl Field for GF {
///     type Item = u64;
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
///         (a + b) % self.0
///     }
///
///     fn mul(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
///         (a * b) % self.0
///     }
///
///     fn neg(&self, a: &Self::Item) -> Self::Item {
///         if *a == 0 { 0 } else { self.0 - *a }
///     }
///
///     fn inv(&self, a: &Self::Item) -> Option<Self::Item> {
///         if *a == 0 {
///             None
///         } else {
///             let mut b = Ri64.euclidean_extended(
///                 &(*a as i64), &(self.0 as i64)
///             ).1;
///             Some(b.rem_euclid(self.0 as i64) as u64)
///         }
///     }
/// }
///
/// let gf11 = GF(11);
///
/// assert_eq!(gf11.zero(), 0);
/// assert_eq!(gf11.one(), 1);
/// assert_eq!(gf11.eq(&5, &5), true);
/// assert_eq!(gf11.add(&7, &8), 4);
/// assert_eq!(gf11.mul(&7, &8), 1);
/// assert_eq!(gf11.neg(&7), 4);
/// assert_eq!(gf11.neg(&0), 0);
/// assert_eq!(gf11.inv(&7), Some(8));
/// assert_eq!(gf11.inv(&1), Some(1));
/// assert_eq!(gf11.inv(&0), None);
/// assert_eq!(gf11.mul_scalar(&7, [true, false, true].into_iter()), 2);
/// assert_eq!(gf11.pow_scalar(&7, [true, false, true].into_iter()), 10);
/// ```
pub trait Field where 
        Self::Item: Clone {
    /// The type of the field elements.
    type Item;

    /// Get the zero element of the field (the identity by addition).
    fn zero(&self) -> Self::Item;

    /// Get the one element of the field (the identity by multiplication).
    fn one(&self) -> Self::Item;

    /// Perform the equity operation in the field.
    fn eq(&self, a: &Self::Item, b: &Self::Item) -> bool;

    /// Perform addition operation in the field.
    fn add(&self, a: &Self::Item, b: &Self::Item) -> Self::Item;

    /// Perform multiplication operation in the field.
    fn mul(&self, a: &Self::Item, b: &Self::Item) -> Self::Item;

    /// Get inversed element by addition.
    fn neg(&self, a: &Self::Item) -> Self::Item;

    /// Get inversed element by multiplication.
    fn inv(&self, a: &Self::Item) -> Option<Self::Item>;

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
    /// `mul` and `inv` but it can be overridden for optimization purposes.
    fn div(&self, a: &Self::Item, b: &Self::Item) -> Option<Self::Item> {
        self.inv(b).map(|i| self.mul(a, &i))
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

    /// Perform `div_assign` operation. By default it is implemented through 
    /// `div` but it can be overridden for optimization purposes.
    fn div_assign(&self, a: &mut Self::Item, b: &Self::Item) {
        *a = self.div(a, b).unwrap();
    }

    /// Perform `neg_assign` operation. By default it is implemented through 
    /// `neg` but it can be overridden for optimization purposes.
    fn neg_assign(&self, a: &mut Self::Item) {
        *a = self.neg(a);
    }

    /// Perform `inv_assign` operation. By default it is implemented through 
    /// `inv` but it can be overridden for optimization purposes.
    fn inv_assign(&self, a: &mut Self::Item) {
        *a = self.inv(a).unwrap();
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
    fn as_add_group(&self) -> AddGroup<Self> {
        AddGroup {
            field: self
        }
    }

    /// Represent the field as a group by multiplication.
    fn as_mul_group(&self) -> MulGroup<Self> {
        MulGroup {
            field: self
        }
    }
}


/// Addition group over a field.
///
/// Example:
///
/// ```rust
/// use finitelib::prelude::*;
/// use finitelib::common::fields::Ff64;
///
/// let g_add = Ff64.as_add_group();
///
/// assert_eq!(g_add.zero(), 0.0);
/// assert_eq!(g_add.add(&3.0, &5.0), 8.0);
/// ```
pub struct AddGroup<'a, F: ?Sized> {
    field: &'a F,
}


impl<'a, F: Field> Group for AddGroup<'a, F> {
    type Item = F::Item;

    fn zero(&self) -> Self::Item {
        self.field.zero()
    }

    fn eq(&self, a: &Self::Item, b: &Self::Item) -> bool {
        self.field.eq(a, b)
    }

    fn add(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
        self.field.add(a, b)
    }

    fn neg(&self, a: &Self::Item) -> Self::Item {
        self.field.neg(a)
    }

    fn mul_scalar<I>(&self, a: &Self::Item, bits_iter: I) -> Self::Item 
            where I: Iterator<Item = bool> {
        self.field.mul_scalar(a, bits_iter)
    }

    fn sub(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
        self.field.sub(a, b)
    }

    fn add_assign(&self, a: &mut Self::Item, b: &Self::Item) {
        self.field.add_assign(a, b);
    }

    fn sub_assign(&self, a: &mut Self::Item, b: &Self::Item) {
        self.field.sub_assign(a, b);
    }

    fn neg_assign(&self, a: &mut Self::Item) {
        self.field.neg_assign(a);
    }

    fn mul_scalar_assign<I>(&self, a: &mut Self::Item, bits_iter: I)
            where I: Iterator<Item = bool> {
        self.field.mul_scalar_assign(a, bits_iter);
    }
}


/// Multiplication group over a field.
///
/// Example:
///
/// ```rust
/// use finitelib::prelude::*;
/// use finitelib::common::fields::Ff64;
///
/// let g_mul = Ff64.as_mul_group();
///
/// assert_eq!(g_mul.zero(), 1.0);
/// assert_eq!(g_mul.add(&3.0, &5.0), 15.0);
/// ```
pub struct MulGroup<'a, F: ?Sized> {
    field: &'a F,
}


impl<'a, F: Field> Group for MulGroup<'a, F> {
    type Item = F::Item;

    fn zero(&self) -> Self::Item {
        self.field.one()
    }

    fn eq(&self, a: &Self::Item, b: &Self::Item) -> bool {
        self.field.eq(a, b)
    }

    fn add(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
        self.field.mul(a, b)
    }

    fn neg(&self, a: &Self::Item) -> Self::Item {
        self.field.inv(a).unwrap()
    }

    fn mul_scalar<I>(&self, a: &Self::Item, bits_iter: I) -> Self::Item 
            where I: Iterator<Item = bool> {
        self.field.pow_scalar(a, bits_iter)
    }

    fn sub(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
        self.field.div(a, b).unwrap()
    }

    fn add_assign(&self, a: &mut Self::Item, b: &Self::Item) {
        self.field.mul_assign(a, b);
    }

    fn sub_assign(&self, a: &mut Self::Item, b: &Self::Item) {
        self.field.div_assign(a, b);
    }

    fn neg_assign(&self, a: &mut Self::Item) {
        self.field.inv_assign(a);
    }

    fn mul_scalar_assign<I>(&self, a: &mut Self::Item, bits_iter: I)
            where I: Iterator<Item = bool> {
        self.field.pow_scalar_assign(a, bits_iter);
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::fields::Ff32;

    #[test]
    fn test_as_add_group() {
        let g_add = Ff32.as_add_group();
        assert_eq!(g_add.zero(), 0.0);
        assert_eq!(g_add.eq(&3.5, &3.5), true);
        assert_eq!(g_add.add(&3.5, &1.5), 5.0);
        assert_eq!(g_add.neg(&3.5), -3.5);
    }

    #[test]
    fn test_as_mul_group() {
        let g_mul = Ff32.as_mul_group();
        assert_eq!(g_mul.zero(), 1.0);
        assert_eq!(g_mul.eq(&3.5, &3.5), true);
        assert_eq!(g_mul.add(&3.5, &1.5), 5.25);
        assert_eq!(g_mul.neg(&0.5), 2.0);
    }
}
