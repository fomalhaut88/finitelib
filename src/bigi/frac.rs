//! Fractions over `Bigi` datatype, so it implements fraction arithmetics
//! with multipresision numerator and denominator.

use std::{cmp, ops, mem};

use crate::bigi::Bigi;
use crate::bigi::rings::BigiRing;
use crate::ring::EuclideanRing;


/// Fraction structure.
#[derive(Debug, PartialEq)]
pub struct Frac<const N: usize>(Bigi<N>, Bigi<N>, bool);


impl<const N: usize> Frac<N> {
    /// Create a fraction object from a numerator, denominator and sign (`true` 
    /// for positive, `false` for negative).
    pub fn new(numerator: Bigi<N>, denominator: Bigi<N>, sign: bool) -> Self {
        let mut instance = Self(numerator, denominator, sign);
        instance._reduce();
        instance
    }

    /// Get numerator.
    pub fn numerator(&self) -> &Bigi<N> {
        &self.0
    }

    /// Get denominator.
    pub fn denominator(&self) -> &Bigi<N> {
        &self.1
    }

    /// Get sign.
    pub fn sign(&self) -> bool {
        self.2
    }

    /// Invert the fraction.
    pub fn inv(&mut self) {
        mem::swap(&mut self.0, &mut self.1);
    }

    /// Divide numerator by denominator returning the result and the remainder.
    /// Sign is ignored.
    pub fn divide(&self) -> (Bigi<N>, Bigi<N>) {
        let mut rem = self.0.clone();
        let res = rem.divide(&self.1).unwrap();
        (res, rem)
    }

    fn _reduce(&mut self) {
        let gcd = BigiRing::<N>.euclidean(&self.0, &self.1);
        if gcd != BigiRing::<N>.one() {
            self.0 /= &gcd;
            self.1 /= &gcd;
        }
    }

    fn _frac_cmp(&self, rhs: &Self) -> cmp::Ordering {
        let left = self.0.mul_overflowing(&rhs.1);
        let right = rhs.0.mul_overflowing(&self.1);

        let res_ext = left.1.partial_cmp(&right.1).unwrap();

        if res_ext == cmp::Ordering::Equal {
            left.0.partial_cmp(&right.0).unwrap()   
        } else {
            res_ext
        }
    }
}


impl<const N: usize> Clone for Frac<N> {
    fn clone(&self) -> Self {
        Self::new(self.0.clone(), self.1.clone(), self.2)
    }
}


impl<const N: usize> ToString for Frac<N> {
    fn to_string(&self) -> String {
        let s = if self.2 { '+' } else { '-' };
        format!("{}{}/{}", s, self.0.to_decimal(), self.1.to_decimal())
    }
}


impl<const N: usize> From<Bigi<N>> for Frac<N> {
    fn from(x: Bigi<N>) -> Self {
        Self::new(x, Bigi::from(1), true)
    }
}


impl<const N: usize> From<u64> for Frac<N> {
    fn from(x: u64) -> Self {
        Self::new(Bigi::from(x), Bigi::from(1), true)
    }
}


impl<const N: usize> From<i64> for Frac<N> {
    fn from(x: i64) -> Self {
        if x >= 0 {
            Self::new(Bigi::from(x), Bigi::from(1), true)
        } else {
            Self::new(Bigi::from(-x), Bigi::from(1), false)
        }
    }
}


impl<const N: usize> From<(i64, u64)> for Frac<N> {
    fn from(x: (i64, u64)) -> Self {
        let (n, d) = x;
        if n >= 0 {
            Self::new(Bigi::from(n), Bigi::from(d), true)
        } else {
            Self::new(Bigi::from(-n), Bigi::from(d), false)
        }
    }
}


impl<const N: usize> PartialOrd for Frac<N> {
    fn partial_cmp(&self, rhs: &Self) -> Option<cmp::Ordering> {
        if (self.0 == Bigi::from(0)) && (rhs.0 == Bigi::from(0)) {
            Some(cmp::Ordering::Equal)
        } else if self.2 == rhs.2 {
            let mut res = self._frac_cmp(rhs);
            if !self.2 {
                res = res.reverse();
            }
            Some(res)
        } else {
            if self.2 {
                Some(cmp::Ordering::Greater)
            } else {
                Some(cmp::Ordering::Less)
            }
        }
    }
}


impl<const N: usize> ops::Neg for &Frac<N> {
    type Output = Frac<N>;

    fn neg(self) -> Self::Output {
        Frac::<N>::new(self.0.clone(), self.1.clone(), !self.2)
    }
}


impl<const N: usize> ops::Add<&Frac<N>> for &Frac<N> {
    type Output = Frac<N>;

    fn add(self, rhs: &Frac<N>) -> Self::Output {
        let denominator = &self.1 * &rhs.1;
        let left = &self.0 * &rhs.1;
        let right = &rhs.0 * &self.1;

        if self.2 == rhs.2 {
            Frac::<N>::new(&left + &right, denominator, self.2)
        } else {
            if &left > &right {
                Frac::<N>::new(&left - &right, denominator, self.2)
            } else {
                Frac::<N>::new(&right - &left, denominator, !self.2)
            }
        }
    }
}


impl<const N: usize> ops::Sub<&Frac<N>> for &Frac<N> {
    type Output = Frac<N>;

    fn sub(self, rhs: &Frac<N>) -> Self::Output {
        let denominator = &self.1 * &rhs.1;
        let left = &self.0 * &rhs.1;
        let right = &rhs.0 * &self.1;

        if self.2 != rhs.2 {
            Frac::<N>::new(&left + &right, denominator, self.2)
        } else {
            if &left > &right {
                Frac::<N>::new(&left - &right, denominator, self.2)
            } else {
                Frac::<N>::new(&right - &left, denominator, !self.2)
            }
        }
    }
}


impl<const N: usize> ops::Mul<&Frac<N>> for &Frac<N> {
    type Output = Frac<N>;

    fn mul(self, rhs: &Frac<N>) -> Self::Output {
        let numerator = &self.0 * &rhs.0;
        let denominator = &self.1 * &rhs.1;
        Frac::<N>::new(numerator, denominator, self.2 == rhs.2)
    }
}


impl<const N: usize> ops::Div<&Frac<N>> for &Frac<N> {
    type Output = Frac<N>;

    fn div(self, rhs: &Frac<N>) -> Self::Output {
        let numerator = &self.0 * &rhs.1;
        let denominator = &self.1 * &rhs.0;
        Frac::<N>::new(numerator, denominator, self.2 == rhs.2)
    }
}


impl<const N: usize> ops::AddAssign<&Frac<N>> for Frac<N> {
    fn add_assign(&mut self, rhs: &Frac<N>) {
        *self = &*self + rhs;
    }
}


impl<const N: usize> ops::SubAssign<&Frac<N>> for Frac<N> {
    fn sub_assign(&mut self, rhs: &Frac<N>) {
        *self = &*self - rhs;
    }
}


impl<const N: usize> ops::MulAssign<&Frac<N>> for Frac<N> {
    fn mul_assign(&mut self, rhs: &Frac<N>) {
        *self = &*self * rhs;
    }
}


impl<const N: usize> ops::DivAssign<&Frac<N>> for Frac<N> {
    fn div_assign(&mut self, rhs: &Frac<N>) {
        *self = &*self / rhs;
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        let q = Frac::<4>::new(Bigi::from(45), Bigi::from(33), false);
        assert_eq!(q.numerator(), &Bigi::from(15));
        assert_eq!(q.denominator(), &Bigi::from(11));
        assert_eq!(q.sign(), false);
    }

    #[test]
    fn test_to_string() {
        let q = Frac::<4>::new(Bigi::from(45), Bigi::from(33), false);
        assert_eq!(q.to_string(), "-15/11".to_string());
    }

    #[test]
    fn test_from() {
        let q = Frac::from(Bigi::<4>::from(45));
        assert_eq!(q.to_string(), "+45/1".to_string());

        let q = Frac::<4>::from(45u64);
        assert_eq!(q.to_string(), "+45/1".to_string());

        let q = Frac::<4>::from(-45i64);
        assert_eq!(q.to_string(), "-45/1".to_string());

        let q = Frac::<4>::from((-4, 6));
        assert_eq!(q.to_string(), "-2/3".to_string());
    }

    #[test]
    fn test_cmp() {
        let q1 = Frac::<4>::from((2, 3));
        let q2 = Frac::<4>::from((3, 5));
        assert_eq!(q1 > q2, true);
        assert_eq!(q1 < q2, false);
        assert_eq!(q2 > q1, false);
        assert_eq!(q2 < q1, true);
    }

    #[test]
    fn test_add() {
        let q1 = Frac::<4>::from((2, 3));
        let q2 = Frac::<4>::from((3, 5));

        assert_eq!((&q1 + &q2).to_string(), "+19/15".to_string());
        assert_eq!((&q1 + &(-&q2)).to_string(), "+1/15".to_string());
        assert_eq!((&(-&q1) + &q2).to_string(), "-1/15".to_string());
        assert_eq!((&(-&q1) + &(-&q2)).to_string(), "-19/15".to_string());
    }

    #[test]
    fn test_sub() {
        let q1 = Frac::<4>::from((2, 3));
        let q2 = Frac::<4>::from((3, 5));

        assert_eq!((&q1 - &q2).to_string(), "+1/15".to_string());
        assert_eq!((&q1 - &(-&q2)).to_string(), "+19/15".to_string());
        assert_eq!((&(-&q1) - &q2).to_string(), "-19/15".to_string());
        assert_eq!((&(-&q1) - &(-&q2)).to_string(), "-1/15".to_string());
    }

    #[test]
    fn test_mul() {
        let q1 = Frac::<4>::from((2, 3));
        let q2 = Frac::<4>::from((3, 5));
        assert_eq!((&q1 * &q2).to_string(), "+2/5".to_string());
    }

    #[test]
    fn test_div() {
        let q1 = Frac::<4>::from((2, 3));
        let q2 = Frac::<4>::from((-3, 5));
        assert_eq!((&q1 / &q2).to_string(), "-10/9".to_string());
    }
}
