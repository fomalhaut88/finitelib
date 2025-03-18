//! Serialization for `Bigi` using `serde`.

use std::fmt;

use serde::{Serializer, Serialize, Deserializer, Deserialize};
use serde::ser::SerializeSeq;
use serde::de::{Visitor, SeqAccess};

use crate::bigi::Bigi;


impl<const N: usize> Serialize for Bigi<N> {
    fn serialize<S: Serializer>(&self, serializer: S) -> 
                                Result<S::Ok, S::Error> {
        let mut serializer_seq = serializer.serialize_seq(Some(N))?;
        for digit in self.0.iter() {
            serializer_seq.serialize_element(&digit)?;
        }
        serializer_seq.end()
    }
}


struct BigiVisitor<const N: usize>;


impl<'de, const N: usize> Visitor<'de> for BigiVisitor<N> {
    type Value = Bigi<N>;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("u64 digits of bigi")
    }

    fn visit_seq<S: SeqAccess<'de>>(self, mut access: S) -> 
                                    Result<Self::Value, S::Error> {
        let mut seq = Vec::<u64>::with_capacity(N);
        while let Some(digit) = access.next_element()? {
            seq.push(digit);
        }
        Ok(Bigi(seq.try_into().unwrap()))
    }
}


impl<'de, const N: usize> Deserialize<'de> for Bigi<N> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> 
                                         Result<Self, D::Error> {
        deserializer.deserialize_seq(BigiVisitor::<N>)
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use serde_json;

    #[test]
    fn test() {
        let a = Bigi::<4>::from_decimal(
            "70011597082245702521290087447806528763417035600728176437530042129660745583227"
        );

        let s = serde_json::to_string(&a).unwrap();
        assert_eq!(
            s, 
            "[13052583939777464955,4416483828795235697,5813502356033862085,11153490899719002585]"
                .to_string()
        );

        let b: Bigi::<4> = serde_json::from_str(&s).unwrap();
        assert_eq!(a, b);
    }
}
