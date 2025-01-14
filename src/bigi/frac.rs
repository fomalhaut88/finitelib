//! Fractions over `Bigi` datatype, so it implements fraction arithmetics
//! with multipresision numerator and denominator.

use crate::bigi::Bigi;


/// Fraction structure.
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

    fn _reduce(&mut self) {}
}


// #[cfg(test)]
// mod tests {
//     use super::*;

//     #[test]
//     fn test() {}
// }
