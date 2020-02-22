use core::convert::{TryFrom, TryInto};

use bellman::gadgets::boolean::{AllocatedBit, Boolean};
use bellman::gadgets::multipack;
use bellman::gadgets::num::AllocatedNum;
use bellman::gadgets::sha256::sha256;
use bellman::groth16::Parameters;
use bellman::groth16::Proof as Groth16Proof;
use bellman::SynthesisError;
use bellman::{Circuit, ConstraintSystem}; //Variable
use ff::Field;
use ff::PrimeField;
use ff::PrimeFieldRepr;
use pairing::bls12_381::Bls12;
use pairing::Engine;

use crate::types::{Error, H256, H512};

#[derive(Clone)]
struct Sha3_256GadgetInput {
    /// Hash
    hash: H256,
    /// Preimage
    preimage: H512,
}

pub struct Sha3_256Gadget {
    input: Option<Sha3_256GadgetInput>,
}

impl Sha3_256Gadget {
    /// Used when generating setup parameters
    #[cfg(feature = "std")]
    pub fn default() -> Self {
        Self { input: None }
    }

    /// Used when generating a proof
    pub fn new(
        hash: H256,
        preimage: H512,
    ) -> Self {

        let input = Sha3_256GadgetInput {
            hash,
            preimage,
        };
        Self { input: Some(input) }
    }
}

pub type SetupParams = Parameters<Bls12>;
pub struct Proof(Vec<u8>);

impl TryInto<Groth16Proof<Bls12>> for Proof {
    type Error = Error;

    fn try_into(self) -> Result<Groth16Proof<Bls12>, Error> {
        Groth16Proof::<Bls12>::read(&self.0[..]).map_err(|e| Error::Io(e))
    }
}

impl TryFrom<Groth16Proof<Bls12>> for Proof {
    type Error = Error;

    fn try_from(params: Groth16Proof<Bls12>) -> Result<Self, Error> {
        let mut v = vec![];
        params.write(&mut v).map_err(|e| Error::Io(e))?;
        Ok(Self(v))
    }
}

impl Into<Vec<u8>> for Proof {
    fn into(self) -> Vec<u8> {
        self.0
    }
}

impl From<Vec<u8>> for Proof {
    fn from(params: Vec<u8>) -> Self {
        Self(params)
    }
}

impl AsRef<[u8]> for Proof {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

impl<E: Engine> Circuit<E> for Sha3_256Gadget {
    fn synthesize<CS: ConstraintSystem<E>>(self, mut cs: &mut CS) -> Result<(), SynthesisError> {
        //TODO: Implement
        panic!("Not implemented");
    }
}

#[cfg(test)]
mod test {
    use crate::types::H256; //Error, Secp256k1Point
                            // use ff::{BitIterator, Field, PrimeField};
                            // use pairing::bls12_381::{Bls12, Fr};
                            // use rand_core::SeedableRng;
                            // use rand_xorshift::XorShiftRng;
    use rand::Rng; //thread_rng

    use super::{AllocatedNum, Boolean};
    use bellman::{Circuit, ConstraintSystem}; //Variable
                                              // use crate::gadgets::test::*;
                                              // use hex::ToHex;
    use num_bigint::{BigInt, BigUint};
    use num_traits::{One, Zero};
    use std::str::FromStr;
    // use secp256k1::curve::Affine;
    // use secp256k1::curve::Field;
    use ff::PrimeField;
    use pairing::bls12_381::Bls12;
    use pairing::Engine;
    // use ff::PrimeFieldRepr;
    use bellman::gadgets::test::*;
    use ff::ScalarEngine; //BitIterator, Field

    #[test]
    fn test_() {
    }
}
