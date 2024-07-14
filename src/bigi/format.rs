//! Formatting multi precision integers in multiple ways.
//!
//! Supported formats:
//! * Bytes
//! * Hex
//! * Decimal
//!
//! Decimal formatting works much slower than others due to obvious reasons.
//!
//! ```rust
//! use finitelib::bigi::prelude::*;
//!
//! type U256 = bigi_of_bits!(256);
//!
//! let x = U256::from_decimal("8141239184550609109798753412385769260814545419870769294510294857129857644534");
//!
//! assert_eq!(x.to_decimal(), "8141239184550609109798753412385769260814545419870769294510294857129857644534".to_string());
//! assert_eq!(x.to_hex(), "11FFC7309355A65913CF08F142718279FA43D3D9D1A855AFDAAAD4824A9FF7F6".to_string());
//! assert_eq!(x.to_bytes(), vec![246, 247, 159, 74, 130, 212, 170, 218, 175, 85, 168, 209, 217, 211, 67, 250, 121, 130, 113, 66, 241, 8, 207, 19, 89, 166, 85, 147, 48, 199, 255, 17]);
//! ```

use crate::bigi::{Bigi, BIGI_UNIT_BYTES};


impl<const N: usize> Bigi<N> {
    /// Converts the bigi into a vector of bytes.
    pub fn to_bytes(&self) -> Vec<u8> {
        self.0.iter()
            .map(|digit| digit.to_le_bytes())
            .collect::<Vec<[u8; BIGI_UNIT_BYTES]>>().concat()
    }

    /// Converts the bytes into a bigi.
    pub fn from_bytes(bytes: &[u8]) -> Self {
        Self::from_iter(
            bytes.chunks(BIGI_UNIT_BYTES)
                .map(|b| u64::from_le_bytes(b.try_into().unwrap()))
        )
    }

    /// Converts the bigi into a hex string.
    pub fn to_hex(&self) -> String {
        (0..N).rev().map(|idx| format!("{:016X}", self.0[idx]))
            .collect::<Vec<String>>().join("")
    }

    /// Converts the hex string into a bigi.
    pub fn from_hex(hex: &str) -> Self {
        const HEX_STEP: usize = BIGI_UNIT_BYTES * 2;
        Self::from_iter(
            (0..N).rev().map(
                |i| u64::from_str_radix(&hex[
                    HEX_STEP * i .. HEX_STEP * (i + 1)
                ], 16).unwrap()
            )
        )
    }

    /// Converts the bigi into a decimal string.
    pub fn to_decimal(&self) -> String {
        let mut self_copy = self.clone();
        let mut digit;
        let mut digit_vec = Vec::new();
        while self_copy > Self::min() {
            (self_copy, digit) = self_copy.divide_unit(10).unwrap();
            digit_vec.push(digit);
        }
        if digit_vec.len() > 0 {
            digit_vec.iter().rev().map(|d| d.to_string())
                .collect::<Vec<String>>().join("")
        } else {
            "0".to_string()
        }
    }

    /// Converts the decimal string into a bigi.
    pub fn from_decimal(dec: &str) -> Self {
        let mut res = Self::min();
        for digit in dec.chars().map(|c| c as u64 - '0' as u64) {
            res.mul_unit(10);
            res.add_unit(digit);
        }
        res
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bytes() {
        let a = Bigi::new([25, 0, 0, 2]);
        let bytes = a.to_bytes();
        let b = Bigi::<4>::from_bytes(&bytes);
        assert_eq!(a, b);
    }

    #[test]
    fn test_hex() {
        assert_eq!(
            Bigi::new([25, 0, 0, 2]).to_hex(), 
            "0000000000000002000000000000000000000000000000000000000000000019"
        );
        assert_eq!(
            Bigi::<4>::from_hex(
                "0000000000000002000000000000000000000000000000000000000000000019"
            ),
            Bigi::new([25, 0, 0, 2])
        );
    }

    #[test]
    fn test_decimal() {
        assert_eq!(
            Bigi::new([25, 0, 0, 2]).to_decimal(), 
            "12554203470773361527671578846415332832204710888928069025817"
        );
        assert_eq!(
            Bigi::<4>::from_decimal(
                "12554203470773361527671578846415332832204710888928069025817"
            ),
            Bigi::new([25, 0, 0, 2])
        );
        assert_eq!(
            Bigi::<4>::min().to_decimal(), 
            "0"
        );
        assert_eq!(
            Bigi::<4>::from_decimal(
                "0"
            ),
            Bigi::<4>::min()
        );
    }
}
