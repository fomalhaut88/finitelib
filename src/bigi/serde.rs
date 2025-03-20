//! Serialization for `Bigi` using `serde`.

use std::fmt;

use serde::{Serializer, Serialize, Deserializer, Deserialize};
use serde::de;

use crate::bigi::Bigi;


impl<const N: usize> Serialize for Bigi<N> {
    fn serialize<S: Serializer>(&self, serializer: S) -> 
                                Result<S::Ok, S::Error> {
        serializer.serialize_str(&self.to_hex())
    }
}


struct BigiVisitor<const N: usize>;


impl<'de, const N: usize> de::Visitor<'de> for BigiVisitor<N> {
    type Value = Bigi<N>;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("HEX string of bigi")
    }

    fn visit_str<E: de::Error>(self, access: &str) -> 
                                  Result<Self::Value, E> {
        Ok(Bigi::from_hex(access))
    }
}


impl<'de, const N: usize> Deserialize<'de> for Bigi<N> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> 
                                         Result<Self, D::Error> {
        deserializer.deserialize_str(BigiVisitor::<N>)
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use serde_json;

    #[test]
    fn test() {
        let a = Bigi::<4>::from_hex(
            "9AC928E12B4D99D950ADB597704B79C53D4A80A48B98DD71B52417F00B678A7B"
        );

        let s = serde_json::to_string(&a).unwrap();
        assert_eq!(
            s, 
            "\"9AC928E12B4D99D950ADB597704B79C53D4A80A48B98DD71B52417F00B678A7B\""
        );

        let b: Bigi::<4> = serde_json::from_str(&s).unwrap();
        assert_eq!(a, b);
    }
}
