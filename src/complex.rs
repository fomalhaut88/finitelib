//! Field for complex extension implemented as linear polynomials with the
//! irreducible `1 + x^2`.

use crate::field::Field;


/// Complex structure that implements the field.
pub struct Complex<F: Field>(F);


impl<F: Field> Field for Complex<F> {
    type Item = (F::Item, F::Item);

    fn zero(&self) -> Self::Item {
        (self.0.zero(), self.0.zero())
    }

    fn one(&self) -> Self::Item {
        (self.0.one(), self.0.zero())
    }

    fn eq(&self, a: &Self::Item, b: &Self::Item) -> bool {
        self.0.eq(&a.0, &b.0) && self.0.eq(&a.1, &b.1)
    }

    fn add(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
        (self.0.add(&a.0, &b.0), self.0.add(&a.1, &b.1))
    }

    fn add_assign(&self, a: &mut Self::Item, b: &Self::Item) {
        self.0.add_assign(&mut a.0, &b.0);
        self.0.add_assign(&mut a.1, &b.1);
    }

    fn sub(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
        (self.0.sub(&a.0, &b.0), self.0.sub(&a.1, &b.1))
    }

    fn sub_assign(&self, a: &mut Self::Item, b: &Self::Item) {
        self.0.sub_assign(&mut a.0, &b.0);
        self.0.sub_assign(&mut a.1, &b.1);
    }

    fn mul(&self, a: &Self::Item, b: &Self::Item) -> Self::Item {
        (
            self.0.sub(&self.0.mul(&a.0, &b.0), &self.0.mul(&a.1, &b.1)),
            self.0.add(&self.0.mul(&a.0, &b.1), &self.0.mul(&a.1, &b.0)),
        )
    }

    fn neg(&self, a: &Self::Item) -> Self::Item {
        (self.0.neg(&a.0), self.0.neg(&a.1))
    }

    fn neg_assign(&self, a: &mut Self::Item) {
        self.0.neg_assign(&mut a.0);
        self.0.neg_assign(&mut a.1);
    }

    fn inv(&self, a: &Self::Item) -> Option<Self::Item> {
        let mut r = a.clone();
        self.inv_assign(&mut r)?;
        Some(r)
    }

    fn inv_assign(&self, a: &mut Self::Item) -> Option<()> {
        let mut c = self.norm2(a);
        self.0.inv_assign(&mut c)?;
        self.0.mul_assign(&mut a.0, &c);
        self.0.mul_assign(&mut a.1, &c);
        self.0.neg_assign(&mut a.1);
        Some(())
    }
}


impl<F: Field> Complex<F> {
    /// Create a new complex field from the given underlied field.
    pub fn new(field: F) -> Self {
        Self(field)
    }

    /// L2 norm of the item.
    pub fn norm2(&self, a: &<Self as Field>::Item) -> F::Item {
        self.0.add(&self.0.mul(&a.0, &a.0), &self.0.mul(&a.1, &a.1))
    }

    /// Return conjugated item.
    pub fn conj(&self, a: &<Self as Field>::Item) -> <Self as Field>::Item {
        let mut b = a.clone();
        self.conj_assign(&mut b);
        b
    }

    /// Conjugate the item.
    pub fn conj_assign(&self, a: &mut <Self as Field>::Item) {
        a.1 = self.0.neg(&a.1);
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    use crate::common::fields::Ff64;

    #[test]
    fn test() {
        let c64 = Complex::<Ff64>::new(Ff64);

        let a = (-4.0, 3.0);

        assert_eq!(c64.zero(), (0.0, 0.0));
        assert_eq!(c64.one(), (1.0, 0.0));

        assert_eq!(c64.norm2(&a), 25.0);
        assert_eq!(c64.conj(&a), (-4.0, -3.0));
        assert_eq!(c64.neg(&a), (4.0, -3.0));
        assert_eq!(c64.inv(&a), Some((-0.16, -0.12)));
        assert_eq!(c64.inv(&c64.zero()), None);
    }

    #[test]
    fn test_add_sub() {
        let c64 = Complex::<Ff64>::new(Ff64);

        let a = (1.5, -0.75);
        let b = (2.5, 3.0);

        let c = c64.sub(&a, &b);
        let d = c64.add(&b, &c);

        assert_eq!(d, a);
    }

    #[test]
    fn test_mul_div() {
        let c64 = Complex::<Ff64>::new(Ff64);

        let a = (1.5, -0.75);
        let b = (2.5, 3.0);

        let c = c64.div(&a, &b).unwrap();
        let d = c64.mul(&b, &c);

        assert_eq!(d, a);
    }
}
