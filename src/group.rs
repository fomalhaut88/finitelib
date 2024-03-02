//! A module that contains a trait for mathematical group objects.

use crate::utils;


/// A trait for a group over the type `Item`.
///
/// Use example:
///
/// ```
/// use finitelib::group::Group;
///
/// struct AddGroup(u64);
/// 
/// impl Group for AddGroup {
///     type Item = u64;
///
///     fn zero(&self) -> Self::Item {
///         0
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
///     fn neg(&self, a: &Self::Item) -> Self::Item {
///         if *a == 0 { 0 } else { self.0 - *a }
///     }
/// }
///
/// let g12 = AddGroup(12);
///
/// assert_eq!(g12.zero(), 0);
/// assert_eq!(g12.add(&7, &8), 3);
/// assert_eq!(g12.eq(&5, &5), true);
/// assert_eq!(g12.neg(&7), 5);
/// assert_eq!(g12.neg(&0), 0);
/// assert_eq!(g12.mul_scalar(&7, [true, false, true].into_iter()), 11);
/// ```
pub trait Group where 
        Self::Item: Clone {
    /// The type of the group elements.
    type Item;

    /// Get identity element of the group.
    fn zero(&self) -> Self::Item;

    /// Perform the equity operation in the group.
    fn eq(&self, a: &Self::Item, b: &Self::Item) -> bool;

    /// Perform addition operation in the group.
    fn add(&self, a: &Self::Item, b: &Self::Item) -> Self::Item;

    /// Get inversed element.
    fn neg(&self, a: &Self::Item) -> Self::Item;

    /// Perform multiplication in the group by a scalar given as an iterator 
    /// of bits according to [the double and add algorithm](https://en.wikipedia.org/wiki/Exponentiation_by_squaring).
    fn mul_scalar<I>(&self, a: &Self::Item, bits_iter: I) -> Self::Item 
            where I: Iterator<Item = bool> {
        utils::exp_by_sqr(a, bits_iter, || self.zero(), |a, b| self.add(a, b))
    }

    /// Perform `sub` operation. By default it is implemented through 
    /// `add` and `neg` but it can be overridden for optimization purposes.
    fn sub(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
        self.add(a, &self.neg(b))
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
}
