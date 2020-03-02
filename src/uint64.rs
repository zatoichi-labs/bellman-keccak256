//! Circuit representation of a [`u64`], with helpers for the [`keccak256`]
//! gadgets.
//!

use bellman::gadgets::boolean::{AllocatedBit, Boolean};
// use bellman::gadgets::multieq::MultiEq;
use bellman::{ConstraintSystem, SynthesisError};//LinearCombination
use ff::{ScalarEngine};//PrimeField,Field
use std::fmt;

/// Represents an interpretation of 64 `Boolean` objects as an
/// unsigned integer.
#[derive(Clone)]
pub struct UInt64 {
    // Least significant bit first
    bits: Vec<Boolean>,
    value: Option<u64>,
}

impl UInt64 {
    /// Construct a constant `UInt64` from a `u64`
    pub fn constant(value: u64) -> Self {
        let mut bits = Vec::with_capacity(64);

        let mut tmp = value;
        for _ in 0..64 {
            if tmp & 1 == 1 {
                bits.push(Boolean::constant(true))
            } else {
                bits.push(Boolean::constant(false))
            }

            tmp >>= 1;
        }

        UInt64 {
            bits,
            value: Some(value),
        }
    }

    /// Allocate a `UInt64` in the constraint system
    pub fn alloc<E, CS>(mut cs: CS, value: Option<u64>) -> Result<Self, SynthesisError>
    where
        E: ScalarEngine,
        CS: ConstraintSystem<E>,
    {
        let values = match value {
            Some(mut val) => {
                let mut v = Vec::with_capacity(64);

                for _ in 0..64 {
                    v.push(Some(val & 1 == 1));
                    val >>= 1;
                }

                v
            }
            None => vec![None; 64],
        };

        let bits = values
            .into_iter()
            .enumerate()
            .map(|(i, v)| {
                Ok(Boolean::from(AllocatedBit::alloc(
                    cs.namespace(|| format!("allocated bit {}", i)),
                    v,
                )?))
            })
            .collect::<Result<Vec<_>, SynthesisError>>()?;

        Ok(UInt64 { bits, value })
    }

    pub fn into_bits_be(self) -> Vec<Boolean> {
        let mut ret = self.bits;
        ret.reverse();
        ret
    }

    pub fn from_bits_be(bits: &[Boolean]) -> Self {
        assert_eq!(bits.len(), 64);

        let mut value = Some(0u64);
        for b in bits {
            value.as_mut().map(|v| *v <<= 1);

            match b.get_value() {
                Some(true) => {
                    value.as_mut().map(|v| *v |= 1);
                }
                Some(false) => {}
                None => {
                    value = None;
                }
            }
        }

        UInt64 {
            value,
            bits: bits.iter().rev().cloned().collect(),
        }
    }

    /// Turns this `UInt64` into its little-endian byte order representation.
    pub fn into_bits(self) -> Vec<Boolean> {
        self.bits
    }

    /// Converts a little-endian byte order representation of bits into a
    /// `UInt64`.
    pub fn from_bits(bits: &[Boolean]) -> Self {
        assert_eq!(bits.len(), 64);

        let new_bits = bits.to_vec();

        let mut value = Some(0u64);
        for b in new_bits.iter().rev() {
            value.as_mut().map(|v| *v <<= 1);

            match *b {
                Boolean::Constant(b) => {
                    if b {
                        value.as_mut().map(|v| *v |= 1);
                    }
                }
                Boolean::Is(ref b) => match b.get_value() {
                    Some(true) => {
                        value.as_mut().map(|v| *v |= 1);
                    }
                    Some(false) => {}
                    None => value = None,
                },
                Boolean::Not(ref b) => match b.get_value() {
                    Some(false) => {
                        value.as_mut().map(|v| *v |= 1);
                    }
                    Some(true) => {}
                    None => value = None,
                },
            }
        }

        UInt64 {
            value,
            bits: new_bits,
        }
    }

    pub fn rotr(&self, by: usize) -> Self {
        let by = by % 64;

        let new_bits = self
            .bits
            .iter()
            .skip(by)
            .chain(self.bits.iter())
            .take(64)
            .cloned()
            .collect();

        UInt64 {
            bits: new_bits,
            value: self.value.map(|v| v.rotate_right(by as u32)),
        }
    }

    pub fn rotl(&self, by: usize) -> Self {
        //ROTL = 64 - ROTR
        let by = (64 - by) % 64;

        let new_bits = self
            .bits
            .iter()
            .skip(by)
            .chain(self.bits.iter())
            .take(64)
            .cloned()
            .collect();

        UInt64 {
            bits: new_bits,
            value: self.value.map(|v| v.rotate_right(by as u32)),
        }
    }

    /// XOR this `UInt64` with another `UInt64`
    pub fn xor<E, CS>(&self, mut cs: CS, other: &Self) -> Result<Self, SynthesisError>
    where
        E: ScalarEngine,
        CS: ConstraintSystem<E>,
    {
        let new_value = match (self.value, other.value) {
            (Some(a), Some(b)) => Some(a ^ b),
            _ => None,
        };

        let bits = self
            .bits
            .iter()
            .zip(other.bits.iter())
            .enumerate()
            .map(|(i, (a, b))| Boolean::xor(cs.namespace(|| format!("xor of bit {}", i)), a, b))
            .collect::<Result<_, _>>()?;

        Ok(UInt64 {
            bits,
            value: new_value,
        })
    }

    /// AND this `UInt64` with another `UInt64`
    pub fn and<E, CS>(&self, mut cs: CS, other: &Self) -> Result<Self, SynthesisError>
    where
        E: ScalarEngine,
        CS: ConstraintSystem<E>,
    {
        let new_value = match (self.value, other.value) {
            (Some(a), Some(b)) => Some(a & b),
            _ => None,
        };

        let bits = self
            .bits
            .iter()
            .zip(other.bits.iter())
            .enumerate()
            .map(|(i, (a, b))| Boolean::and(cs.namespace(|| format!("and of bit {}", i)), a, b))
            .collect::<Result<_, _>>()?;

        Ok(UInt64 {
            bits,
            value: new_value,
        })
    }

    /// NOT this `UInt64`
    pub fn not(&self) -> Self {
        let new_value = match self.value {
            Some(a) => Some(!a),
            _ => None,
        };

        let bits = self.bits.iter().map(|a| a.not()).collect();

        UInt64 {
            bits,
            value: new_value,
        }
    }
}

impl fmt::Display for UInt64 {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        let tmp = format!("{:#x}", self.value.unwrap());

        formatter.pad_integral(true, "UInt64 ", &tmp)
    }
}

impl std::fmt::Debug for UInt64 {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        let tmp = format!("{:#x}", self.value.unwrap());

        formatter.pad_integral(true, "UInt64 ", &tmp)
    }
}

#[cfg(test)]
mod test {
    use super::UInt64;
    use bellman::gadgets::boolean::Boolean;
    use bellman::gadgets::multieq::MultiEq;
    use bellman::gadgets::test::*;
    use bellman::ConstraintSystem;
    use ff::Field;
    use pairing::bls12_381::Bls12;
    use rand_core::{RngCore, SeedableRng};
    use rand_xorshift::XorShiftRng;

    #[test]
    fn test_uint64_from_bits_be() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..1000 {
            let v = (0..64)
                .map(|_| Boolean::constant(rng.next_u64() % 2 != 0))
                .collect::<Vec<_>>();

            let b = UInt64::from_bits_be(&v);

            for (i, bit) in b.bits.iter().enumerate() {
                match *bit {
                    Boolean::Constant(bit) => {
                        assert!(bit == ((b.value.unwrap() >> i) & 1 == 1));
                    }
                    _ => unreachable!(),
                }
            }

            let expected_to_be_same = b.into_bits_be();

            for x in v.iter().zip(expected_to_be_same.iter()) {
                match x {
                    (&Boolean::Constant(true), &Boolean::Constant(true)) => {}
                    (&Boolean::Constant(false), &Boolean::Constant(false)) => {}
                    _ => unreachable!(),
                }
            }
        }
    }

    #[test]
    fn test_uint64_from_bits() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..1000 {
            let v = (0..64)
                .map(|_| Boolean::constant(rng.next_u64() % 2 != 0))
                .collect::<Vec<_>>();

            let b = UInt64::from_bits(&v);

            for (i, bit) in b.bits.iter().enumerate() {
                match *bit {
                    Boolean::Constant(bit) => {
                        assert!(bit == ((b.value.unwrap() >> i) & 1 == 1));
                    }
                    _ => unreachable!(),
                }
            }

            let expected_to_be_same = b.into_bits();

            for x in v.iter().zip(expected_to_be_same.iter()) {
                match x {
                    (&Boolean::Constant(true), &Boolean::Constant(true)) => {}
                    (&Boolean::Constant(false), &Boolean::Constant(false)) => {}
                    _ => unreachable!(),
                }
            }
        }
    }

    #[test]
    fn test_uint64_xor() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..1000 {
            let mut cs = TestConstraintSystem::<Bls12>::new();

            let a = rng.next_u64();
            let b = rng.next_u64();
            let c = rng.next_u64();

            let mut expected = a ^ b ^ c;

            let a_bit = UInt64::alloc(cs.namespace(|| "a_bit"), Some(a)).unwrap();
            let b_bit = UInt64::constant(b);
            let c_bit = UInt64::alloc(cs.namespace(|| "c_bit"), Some(c)).unwrap();

            let r = a_bit.xor(cs.namespace(|| "first xor"), &b_bit).unwrap();
            let r = r.xor(cs.namespace(|| "second xor"), &c_bit).unwrap();

            assert!(cs.is_satisfied());

            assert!(r.value == Some(expected));

            for b in r.bits.iter() {
                match *b {
                    Boolean::Is(ref b) => {
                        assert!(b.get_value().unwrap() == (expected & 1 == 1));
                    }
                    Boolean::Not(ref b) => {
                        assert!(!b.get_value().unwrap() == (expected & 1 == 1));
                    }
                    Boolean::Constant(b) => {
                        assert!(b == (expected & 1 == 1));
                    }
                }

                expected >>= 1;
            }
        }
    }

    #[test]
    fn test_uint64_rotr() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        let mut num = rng.next_u64();

        let a = UInt64::constant(num);

        for i in 0..64 {
            let b = a.rotr(i);
            assert_eq!(a.bits.len(), b.bits.len());

            assert!(b.value.unwrap() == num);

            let mut tmp = num;
            for b in &b.bits {
                match *b {
                    Boolean::Constant(b) => {
                        assert_eq!(b, tmp & 1 == 1);
                    }
                    _ => unreachable!(),
                }

                tmp >>= 1;
            }

            num = num.rotate_right(1);
        }
    }

    #[test]
    fn test_uint64_shr() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..50 {
            for i in 0..60 {
                let num = rng.next_u64();
                let a = UInt64::constant(num).shr(i);
                let b = UInt64::constant(num.wrapping_shr(i as u32));

                assert_eq!(a.value.unwrap(), num.wrapping_shr(i as u32));

                assert_eq!(a.bits.len(), b.bits.len());
                for (a, b) in a.bits.iter().zip(b.bits.iter()) {
                    assert_eq!(a.get_value().unwrap(), b.get_value().unwrap());
                }
            }
        }
    }

    #[test]
    fn test_uint64_sha256_maj() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..1000 {
            let mut cs = TestConstraintSystem::<Bls12>::new();

            let a = rng.next_u64();
            let b = rng.next_u64();
            let c = rng.next_u64();

            let mut expected = (a & b) ^ (a & c) ^ (b & c);

            let a_bit = UInt64::alloc(cs.namespace(|| "a_bit"), Some(a)).unwrap();
            let b_bit = UInt64::constant(b);
            let c_bit = UInt64::alloc(cs.namespace(|| "c_bit"), Some(c)).unwrap();

            let r = UInt64::sha256_maj(&mut cs, &a_bit, &b_bit, &c_bit).unwrap();

            assert!(cs.is_satisfied());

            assert!(r.value == Some(expected));

            for b in r.bits.iter() {
                match b {
                    &Boolean::Is(ref b) => {
                        assert!(b.get_value().unwrap() == (expected & 1 == 1));
                    }
                    &Boolean::Not(ref b) => {
                        assert!(!b.get_value().unwrap() == (expected & 1 == 1));
                    }
                    &Boolean::Constant(b) => {
                        assert!(b == (expected & 1 == 1));
                    }
                }

                expected >>= 1;
            }
        }
    }

    #[test]
    fn test_uint64_sha256_ch() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..1000 {
            let mut cs = TestConstraintSystem::<Bls12>::new();

            let a = rng.next_u64();
            let b = rng.next_u64();
            let c = rng.next_u64();

            let mut expected = (a & b) ^ ((!a) & c);

            let a_bit = UInt64::alloc(cs.namespace(|| "a_bit"), Some(a)).unwrap();
            let b_bit = UInt64::constant(b);
            let c_bit = UInt64::alloc(cs.namespace(|| "c_bit"), Some(c)).unwrap();

            let r = UInt64::sha256_ch(&mut cs, &a_bit, &b_bit, &c_bit).unwrap();

            assert!(cs.is_satisfied());

            assert!(r.value == Some(expected));

            for b in r.bits.iter() {
                match b {
                    &Boolean::Is(ref b) => {
                        assert!(b.get_value().unwrap() == (expected & 1 == 1));
                    }
                    &Boolean::Not(ref b) => {
                        assert!(!b.get_value().unwrap() == (expected & 1 == 1));
                    }
                    &Boolean::Constant(b) => {
                        assert!(b == (expected & 1 == 1));
                    }
                }

                expected >>= 1;
            }
        }
    }
}
