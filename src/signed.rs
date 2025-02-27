//! `Signed` is a wrapper that attaches a sign bit to a type that is supposed 
//! to be unsigned originally.
//!
//! It overrides basic math operations considering the sign. The sign `true`
//! corresponds to positive, `false` - to negative. Note, zero can be positive 
//! or negative and they are not equal to each other (so probably it is a good 
//! idea to override `PartialOrd` for any particular case).
//!
//! ```rust
//! use finitelib::signed::Signed;
//!
//! type I8 = Signed<u8>;
//! 
//! let a = I8::from(25);
//! let b = - I8::from(36);
//!
//! let c = a + b;
//!
//! assert_eq!(c, - I8::from(11));
//! ```

use std::{cmp, ops, fmt};


/// `Signed` wrapper over an unsigned data type.
#[derive(Debug, PartialEq)]
pub struct Signed<T>(T, bool);


impl<T> Signed<T> {
    /// Create a new signed instance setting the initial sign (`true` 
    /// for positive, `false` for negative).
    pub fn new(x: T, sign: bool) -> Self {
        Self(x, sign)
    }

    /// Reference to the original value.
    pub fn unwrap(&self) -> &T {
        &self.0
    }

    /// Mutable reference to the original value.
    pub fn unwrap_mut(&mut self) -> &mut T {
        &mut self.0
    }

    /// The sign.
    pub fn sign(&self) -> bool {
        self.1
    }

    /// Mutable sign.
    pub fn sign_mut(&mut self) -> &mut bool {
        &mut self.1
    }

    /// `true` if positive else `false`.
    pub fn is_positive(&self) -> bool {
        self.1
    }

    /// `true` if negative else `false`.
    pub fn is_negative(&self) -> bool {
        !self.1
    }

    /// Set sign to the instance.
    pub fn set_sign(&mut self, sign: bool) {
        self.1 = sign;
    }
}


impl<T: Clone> Clone for Signed<T> {
    fn clone(&self) -> Self {
        Self::new(self.0.clone(), self.1)
    }
}


impl<T: Copy> Copy for Signed<T> {}


impl<T> From<T> for Signed<T> {
    fn from(x: T) -> Self {
        Self::new(x, true)
    }
}


impl<T: fmt::Display> fmt::Display for Signed<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s = if self.1 { '+' } else { '-' };
        write!(f, "{}{}", s, self.0)
    }
}


impl<T: PartialEq + PartialOrd> PartialOrd for Signed<T> {
    fn partial_cmp(&self, rhs: &Self) -> Option<cmp::Ordering> {
        if self.1 == rhs.1 {
            let mut res = self.0.partial_cmp(&rhs.0)?;
            if !self.1 {
                res = res.reverse();
            }
            Some(res)
        } else {
            if self.1 {
                Some(cmp::Ordering::Greater)
            } else {
                Some(cmp::Ordering::Less)
            }
        }
    }
}


impl<T> ops::Not for Signed<T> where T: ops::Not<Output = T> {
    type Output = Signed<T>;

    fn not(self) -> Self::Output {
        Signed::<T>::new(!self.0, !self.1)
    }
}


impl<T> ops::Not for &Signed<T> where 
        for<'a> &'a T: ops::Not<Output = T> {
    type Output = Signed<T>;

    fn not(self) -> Self::Output {
        Signed::<T>::new(!&self.0, !self.1)
    }
}


impl<T> ops::BitAndAssign<Signed<T>> for Signed<T> where 
        T: ops::BitAndAssign<T> {
    fn bitand_assign(&mut self, rhs: Signed<T>) {
        self.0 &= rhs.0;
        self.1 &= rhs.1;
    }
}


impl<T> ops::BitAndAssign<&Signed<T>> for Signed<T> where 
        for<'a> T: ops::BitAndAssign<&'a T> {
    fn bitand_assign(&mut self, rhs: &Signed<T>) {
        self.0 &= &rhs.0;
        self.1 &= rhs.1;
    }
}


impl<T> ops::BitAnd<Signed<T>> for Signed<T> where 
        T: ops::BitAnd<Output = T> {
    type Output = Signed<T>;

    fn bitand(self, rhs: Signed<T>) -> Self::Output {
        Signed::<T>::new(
            self.0 & rhs.0,
            self.1 & rhs.1
        )
    }
}


// BUG: Due to the compiler issue this gives an error.
// impl<T> ops::BitAnd<&Signed<T>> for &Signed<T> where 
//         for<'a> &'a T: ops::BitAnd<&'a T, Output = T> {
//     type Output = Signed<T>;

//     fn bitand(self, rhs: &Signed<T>) -> Self::Output {
//         Signed::<T>::new(
//             &self.0 & &rhs.0,
//             self.1 & rhs.1
//         )
//     }
// }


impl<T> ops::BitOrAssign<Signed<T>> for Signed<T> where 
        T: ops::BitOrAssign<T> {
    fn bitor_assign(&mut self, rhs: Signed<T>) {
        self.0 |= rhs.0;
        self.1 |= rhs.1;
    }
}


impl<T> ops::BitOrAssign<&Signed<T>> for Signed<T> where 
        for<'a> T: ops::BitOrAssign<&'a T> {
    fn bitor_assign(&mut self, rhs: &Signed<T>) {
        self.0 |= &rhs.0;
        self.1 |= rhs.1;
    }
}


impl<T> ops::BitOr<Signed<T>> for Signed<T> where 
        T: ops::BitOr<Output = T> {
    type Output = Signed<T>;

    fn bitor(self, rhs: Signed<T>) -> Self::Output {
        Signed::<T>::new(
            self.0 | rhs.0,
            self.1 | rhs.1
        )
    }
}


impl<T> ops::BitOr<&Signed<T>> for &Signed<T> where 
        for<'a> &'a T: ops::BitOr<&'a T, Output = T> {
    type Output = Signed<T>;

    fn bitor(self, rhs: &Signed<T>) -> Self::Output {
        Signed::<T>::new(
            &self.0 | &rhs.0,
            self.1 | rhs.1
        )
    }
}


impl<T> ops::BitXorAssign<Signed<T>> for Signed<T> where 
        T: ops::BitXorAssign<T> {
    fn bitxor_assign(&mut self, rhs: Signed<T>) {
        self.0 ^= rhs.0;
        self.1 ^= rhs.1;
    }
}


impl<T> ops::BitXorAssign<&Signed<T>> for Signed<T> where 
        for<'a> T: ops::BitXorAssign<&'a T> {
    fn bitxor_assign(&mut self, rhs: &Signed<T>) {
        self.0 ^= &rhs.0;
        self.1 ^= rhs.1;
    }
}


impl<T> ops::BitXor<Signed<T>> for Signed<T> where 
        T: ops::BitXor<Output = T> {
    type Output = Signed<T>;

    fn bitxor(self, rhs: Signed<T>) -> Self::Output {
        Signed::<T>::new(
            self.0 ^ rhs.0,
            self.1 ^ rhs.1
        )
    }
}


impl<T> ops::BitXor<&Signed<T>> for &Signed<T> where 
        for<'a> &'a T: ops::BitXor<&'a T, Output = T> {
    type Output = Signed<T>;

    fn bitxor(self, rhs: &Signed<T>) -> Self::Output {
        Signed::<T>::new(
            &self.0 ^ &rhs.0,
            self.1 ^ rhs.1
        )
    }
}


impl<T> ops::ShlAssign<usize> for Signed<T> where
        T: ops::ShlAssign<usize> {
    fn shl_assign(&mut self, rhs: usize) {
        self.0 <<= rhs;
    }
}


impl<T> ops::Shl<usize> for Signed<T> where
        T: ops::Shl<usize, Output = T> {
    type Output = Signed<T>;

    fn shl(self, rhs: usize) -> Self::Output {
        Signed::<T>::new(
            self.0 << rhs,
            self.1
        )
    }
}


// BUG: Due to the compiler issue this gives an error.
// impl<T> ops::Shl<usize> for &Signed<T> where
//         for<'a> &'a T: ops::Shl<usize, Output = T> {
//     type Output = Signed<T>;

//     fn shl(self, rhs: usize) -> Self::Output {
//         Signed::<T>::new(
//             &self.0 << rhs,
//             self.1
//         )
//     }
// }


impl<T> ops::ShrAssign<usize> for Signed<T> where
        T: ops::ShrAssign<usize> {
    fn shr_assign(&mut self, rhs: usize) {
        self.0 >>= rhs;
    }
}


impl<T> ops::Shr<usize> for Signed<T> where
        T: ops::Shr<usize, Output = T> {
    type Output = Signed<T>;

    fn shr(self, rhs: usize) -> Self::Output {
        Signed::<T>::new(
            self.0 >> rhs,
            self.1
        )
    }
}


// BUG: Due to the compiler issue this gives an error.
// impl<T> ops::Shr<usize> for &Signed<T> where
//         for<'a> &'a T: ops::Shr<usize, Output = T> {
//     type Output = Signed<T>;

//     fn shr(self, rhs: usize) -> Self::Output {
//         Signed::<T>::new(
//             &self.0 >> rhs,
//             self.1
//         )
//     }
// }


impl<T> ops::Neg for Signed<T> {
    type Output = Signed<T>;

    fn neg(self) -> Self::Output {
        Signed::<T>::new(self.0, !self.1)
    }
}


impl<T: Clone> ops::Neg for &Signed<T> {
    type Output = Signed<T>;

    fn neg(self) -> Self::Output {
        Signed::<T>::new(self.0.clone(), !self.1)
    }
}


impl<T> ops::AddAssign<Signed<T>> for Signed<T> where 
        T: Clone + PartialOrd + ops::AddAssign<T> + ops::SubAssign<T> {
    fn add_assign(&mut self, rhs: Signed<T>) {
        if self.1 == rhs.1 {
            self.0 += rhs.0;
        } else if self.0 >= rhs.0 {
            self.0 -= rhs.0;
        } else {
            let mut t = rhs.0;
            t -= self.0.clone();
            self.0 = t;
            self.1 = !self.1;
        }
    }
}


impl<T> ops::AddAssign<&Signed<T>> for Signed<T> where
        for<'a> T: Clone + PartialOrd + ops::AddAssign<&'a T> + 
                   ops::SubAssign<&'a T> {
    fn add_assign(&mut self, rhs: &Signed<T>) {
        if self.1 == rhs.1 {
            self.0 += &rhs.0;
        } else if self.0 >= rhs.0 {
            self.0 -= &rhs.0;
        } else {
            let mut t = rhs.0.clone();
            t -= &self.0;
            self.0 = t;
            self.1 = !self.1;
        }
    }
}


impl<T> ops::Add<Signed<T>> for Signed<T> where 
        T: PartialOrd + ops::Add<Output = T> + ops::Sub<Output = T> {
    type Output = Signed<T>;

    fn add(self, rhs: Signed<T>) -> Self::Output {
        if self.1 == rhs.1 {
            Signed::<T>::new(
                self.0 + rhs.0,
                self.1
            )
        } else if self.0 >= rhs.0 {
            Signed::<T>::new(
                self.0 - rhs.0,
                self.1
            )
        } else {
            Signed::<T>::new(
                rhs.0 - self.0,
                !self.1
            )
        }
    }
}


impl<T> ops::Add<&Signed<T>> for &Signed<T> where 
        for<'a> &'a T: PartialOrd + ops::Add<&'a T, Output = T> + 
                       ops::Sub<&'a T, Output = T> {
    type Output = Signed<T>;

    fn add(self, rhs: &Signed<T>) -> Self::Output {
        if self.1 == rhs.1 {
            Signed::<T>::new(
                &self.0 + &rhs.0,
                self.1
            )
        } else if &self.0 >= &rhs.0 {
            Signed::<T>::new(
                &self.0 - &rhs.0,
                self.1
            )
        } else {
            Signed::<T>::new(
                &rhs.0 - &self.0,
                !self.1
            )
        }
    }
}


impl<T> ops::SubAssign<Signed<T>> for Signed<T> where 
        T: Clone + PartialOrd + ops::AddAssign<T> + ops::SubAssign<T> {
    fn sub_assign(&mut self, rhs: Signed<T>) {
        if self.1 != rhs.1 {
            self.0 += rhs.0;
        } else if self.0 >= rhs.0 {
            self.0 -= rhs.0;
        } else {
            let mut t = rhs.0;
            t -= self.0.clone();
            self.0 = t;
            self.1 = !self.1;
        }
    }
}


impl<T> ops::SubAssign<&Signed<T>> for Signed<T> where
        for<'a> T: Clone + PartialOrd + ops::AddAssign<&'a T> + 
                   ops::SubAssign<&'a T> {
    fn sub_assign(&mut self, rhs: &Signed<T>) {
        if self.1 != rhs.1 {
            self.0 += &rhs.0;
        } else if self.0 >= rhs.0 {
            self.0 -= &rhs.0;
        } else {
            let mut t = rhs.0.clone();
            t -= &self.0;
            self.0 = t;
            self.1 = !self.1;
        }
    }
}


impl<T> ops::Sub<Signed<T>> for Signed<T> where 
        T: PartialOrd + ops::Add<Output = T> + ops::Sub<Output = T> {
    type Output = Signed<T>;

    fn sub(self, rhs: Signed<T>) -> Self::Output {
        if self.1 != rhs.1 {
            Signed::<T>::new(
                self.0 + rhs.0,
                self.1
            )
        } else if self.0 >= rhs.0 {
            Signed::<T>::new(
                self.0 - rhs.0,
                self.1
            )
        } else {
            Signed::<T>::new(
                rhs.0 - self.0,
                !self.1
            )
        }
    }
}


impl<T> ops::Sub<&Signed<T>> for &Signed<T> where 
        for<'a> &'a T: PartialOrd + ops::Add<&'a T, Output = T> + 
                       ops::Sub<&'a T, Output = T> {
    type Output = Signed<T>;

    fn sub(self, rhs: &Signed<T>) -> Self::Output {
        if self.1 != rhs.1 {
            Signed::<T>::new(
                &self.0 + &rhs.0,
                self.1
            )
        } else if &self.0 >= &rhs.0 {
            Signed::<T>::new(
                &self.0 - &rhs.0,
                self.1
            )
        } else {
            Signed::<T>::new(
                &rhs.0 - &self.0,
                !self.1
            )
        }
    }
}


impl<T> ops::MulAssign<Signed<T>> for Signed<T> where 
        T: ops::MulAssign<T> {
    fn mul_assign(&mut self, rhs: Signed<T>) {
        self.0 *= rhs.0;
        self.1 = self.1 == rhs.1;
    }
}


impl<T> ops::MulAssign<&Signed<T>> for Signed<T> where
        for<'a> T: ops::MulAssign<&'a T> {
    fn mul_assign(&mut self, rhs: &Signed<T>) {
        self.0 *= &rhs.0;
        self.1 = self.1 == rhs.1;
    }
}


impl<T> ops::Mul<Signed<T>> for Signed<T> where 
        T: ops::Mul<Output = T> {
    type Output = Signed<T>;

    fn mul(self, rhs: Signed<T>) -> Self::Output {
        Signed::<T>::new(
            self.0 * rhs.0,
            self.1 == rhs.1
        )
    }
}


impl<T> ops::Mul<&Signed<T>> for &Signed<T> where 
        for<'a> &'a T: ops::Mul<&'a T, Output = T> {
    type Output = Signed<T>;

    fn mul(self, rhs: &Signed<T>) -> Self::Output {
        Signed::<T>::new(
            &self.0 * &rhs.0,
            self.1 == rhs.1
        )
    }
}


impl<T> ops::DivAssign<Signed<T>> for Signed<T> where 
        T: ops::DivAssign<T> {
    fn div_assign(&mut self, rhs: Signed<T>) {
        self.0 /= rhs.0;
        self.1 = self.1 == rhs.1;
    }
}


impl<T> ops::DivAssign<&Signed<T>> for Signed<T> where
        for<'a> T: ops::DivAssign<&'a T> {
    fn div_assign(&mut self, rhs: &Signed<T>) {
        self.0 /= &rhs.0;
        self.1 = self.1 == rhs.1;
    }
}


impl<T> ops::Div<Signed<T>> for Signed<T> where 
        T: ops::Div<Output = T> {
    type Output = Signed<T>;

    fn div(self, rhs: Signed<T>) -> Self::Output {
        Signed::<T>::new(
            self.0 / rhs.0,
            self.1 == rhs.1
        )
    }
}


impl<T> ops::Div<&Signed<T>> for &Signed<T> where 
        for<'a> &'a T: ops::Div<&'a T, Output = T> {
    type Output = Signed<T>;

    fn div(self, rhs: &Signed<T>) -> Self::Output {
        Signed::<T>::new(
            &self.0 / &rhs.0,
            self.1 == rhs.1
        )
    }
}


impl<T> ops::RemAssign<Signed<T>> for Signed<T> where 
        T: ops::RemAssign<T> {
    fn rem_assign(&mut self, rhs: Signed<T>) {
        self.0 %= rhs.0;
        self.1 = self.1 == rhs.1;
    }
}


impl<T> ops::RemAssign<&Signed<T>> for Signed<T> where
        for<'a> T: ops::RemAssign<&'a T> {
    fn rem_assign(&mut self, rhs: &Signed<T>) {
        self.0 %= &rhs.0;
        self.1 = self.1 == rhs.1;
    }
}


impl<T> ops::Rem<Signed<T>> for Signed<T> where 
        T: ops::Rem<Output = T> {
    type Output = Signed<T>;

    fn rem(self, rhs: Signed<T>) -> Self::Output {
        Signed::<T>::new(
            self.0 % rhs.0,
            self.1 == rhs.1
        )
    }
}


impl<T> ops::Rem<&Signed<T>> for &Signed<T> where 
        for<'a> &'a T: ops::Rem<&'a T, Output = T> {
    type Output = Signed<T>;

    fn rem(self, rhs: &Signed<T>) -> Self::Output {
        Signed::<T>::new(
            &self.0 % &rhs.0,
            self.1 == rhs.1
        )
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test() {
        type SignedU16 = Signed<u16>;

        let a: SignedU16 = 23.into();
        let b: SignedU16 = SignedU16::new(36, false);

        assert_eq!(a, a);
        assert_eq!(b, b);
        assert!(a > b);
        assert!(b < a);
        assert!(a >= a);
        assert!(a <= a);
        assert_eq!(&a, &a);
        assert!(&a > &b);

        assert_eq!(!b.clone(), SignedU16::new(65499, true));
        assert_eq!(!&a, SignedU16::new(65512, false));

        assert_eq!(a & b, SignedU16::new(4, false));
        // assert_eq!(&a & &b, SignedU16::new(4, false));

        assert_eq!(a | b, SignedU16::new(55, true));
        assert_eq!(&a | &b, SignedU16::new(55, true));

        assert_eq!(a ^ b, SignedU16::new(51, true));
        assert_eq!(&a ^ &b, SignedU16::new(51, true));

        assert_eq!(a << 2, SignedU16::new(92, true));
        // assert_eq!(&b << 2, SignedU16::new(144, true));
        assert_eq!(a >> 1, SignedU16::new(11, true));
        // assert_eq!(&b >> 1, SignedU16::new(18, false));

        assert_eq!(-a, SignedU16::new(23, false));
        assert_eq!(-&b, SignedU16::new(36, true));

        assert_eq!(a + b, SignedU16::new(13, false));
        assert_eq!(&a + &b, SignedU16::new(13, false));

        assert_eq!(a - b, SignedU16::new(59, true));
        assert_eq!(&a - &b, SignedU16::new(59, true));

        assert_eq!(a * b, SignedU16::new(828, false));
        assert_eq!(&a * &b, SignedU16::new(828, false));

        assert_eq!(b / a, SignedU16::new(1, false));
        assert_eq!(&b / &a, SignedU16::new(1, false));

        assert_eq!(b % a, SignedU16::new(13, false));
        assert_eq!(&b % &a, SignedU16::new(13, false));
    }
}
