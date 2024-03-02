use crate::bigi::{Bigi, BIGI_UNIT_BYTES};


impl<const N: usize> Bigi<N> {
    pub fn to_bytes(&self) -> Vec<u8> {
        self.0.iter()
            .map(|digit| digit.to_le_bytes())
            .collect::<Vec<[u8; BIGI_UNIT_BYTES]>>().concat()
    }

    pub fn from_bytes(bytes: &[u8]) -> Self {
        Self::from_iter(
            bytes.chunks(BIGI_UNIT_BYTES)
                .map(|b| u64::from_le_bytes(b.try_into().unwrap()))
        )
    }

    pub fn to_hex(&self) -> String {
        (0..N).rev().map(|idx| format!("{:016X}", self.0[idx]))
            .collect::<Vec<String>>().join("")
    }

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

    pub fn from_decimal(hex: &str) -> Self {
        let mut res = Self::min();
        for digit in hex.chars().map(|c| c as u64 - '0' as u64) {
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
