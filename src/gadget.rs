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

#[allow(clippy::unreadable_literal)]
const ROUND_CONSTANTS: [u64; 24] = [
    0x0000000000000001,
    0x0000000000008082,
    0x800000000000808A,
    0x8000000080008000,
    0x000000000000808B,
    0x0000000080000001,
    0x8000000080008081,
    0x8000000000008009,
    0x000000000000008A,
    0x0000000000000088,
    0x0000000080008009,
    0x000000008000000A,
    0x000000008000808B,
    0x800000000000008B,
    0x8000000000008089,
    0x8000000000008003,
    0x8000000000008002,
    0x8000000000000080,
    0x000000000000800A,
    0x800000008000000A,
    0x8000000080008081,
    0x8000000000008080,
    0x0000000080000001,
    0x8000000080008008,
];
const ROTR: [usize; 25] = [ //(5*y)+x
    0,
    1,
    62,
    28,
    27,
    36,
    44,
    6,
    55,
    20,
    3,
    10,
    43,
    25,
    39,
    41,
    45,
    15,
    21,
    8,
    18,
    2,
    61,
    56,
    14,
];

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

//Process
fn keccak_f_1600(input: Vec<bool>) -> Vec<bool> {
    let mut A = input;

    for i in 0..24 {
        A = Round_1600(&A, ROUND_CONSTANTS[i]);
    }

    return A;
}

fn Round_1600(A: &Vec<bool>, RC: u64) -> Vec<bool> {
    assert_eq!(A.len(), 1600);//64*25

    // # θ step
    // C[x] = A[x,0] xor A[x,1] xor A[x,2] xor A[x,3] xor A[x,4],   for x in 0…4
    let mut C = vec![false; 320];
    for x in 0..5 {
        for bit in 0..64 {
            C[(x * 64usize) + bit] = A[(x * 64usize) + bit + (0usize * 64usize)] ^ A[(x * 64usize) + bit + (1usize * 64usize)] ^ A[(x * 64usize) + bit + (2usize * 64usize)] ^ A[(x * 64usize) + bit + (3usize * 64usize)] ^ A[(x * 64usize) + bit + (4usize * 64usize)];
        }
    }
    // D[x] = C[x-1] xor rot(C[x+1],1),                             for x in 0…4
    let mut D = vec![false; 320];
    for x in 0..5 {
        for bit in 0..64 {
            //x-1 == (x+4)%5
            D[(x * 64usize) + bit] = C[(((x + 4usize) % 5usize) * 64usize) + bit] ^ C[(((x + 1usize) % 5usize) * 64usize) + ((bit - 1usize) % 64)];
        }
    }
    // A[x,y] = A[x,y] xor D[x],                           for (x,y) in (0…4,0…4)
    let mut A_new = vec![false; 1600];
    for x in 0..5 {
        for y in 0..5 {
            for bit in 0..64 {
                A_new[(y * 320usize) + (x * 64usize) + bit] = A[(y * 320usize) + (x * 64usize) + bit] ^ D[(x * 64usize) + bit];
            }
        }
    }

    // # ρ and π steps
    // B[y,2*x+3*y] = rot(A[x,y], r[x,y]),                 for (x,y) in (0…4,0…4)
    let mut B = vec![false; 1600];
    for x in 0..5 {
        for y in 0..5 {
            for bit in 0..64 {
                B[((((2usize * x) + (3usize * y)) % 5) * 320usize) + (y * 64usize) + bit] = A_new[(y * 320usize) + (x * 64usize) + ((ROTR[(y * 5usize) + x] + bit) % 64usize)];
            }
        }
    }

    // # χ step
    // A[x,y] = B[x,y] xor ((not B[x+1,y]) and B[x+2,y]),  for (x,y) in (0…4,0…4)
    let mut A_new2 = vec![false; 1600];
    for x in 0..5 {
        for y in 0..5 {
            for bit in 0..64 {
                A_new2[(y * 320usize) + (x * 64usize) + bit] = B[(y * 320usize) + (x * 64usize) + bit] ^ (!B[(y * 320usize) + (((x + 1usize) % 5usize) * 64usize) + bit] & B[(y * 320usize) + (((x + 2usize) % 5usize) * 64usize) + bit]);
            }
        }
    }

    // # ι step
    let mut RC_bits = vec![false; 64];
    for bit in 0..64 {
        let val = 1u64 << bit;
        if RC & val != 0u64 {
            RC_bits[bit] = true;
        }
    }

    // A[0,0] = A[0,0] xor RC
    for bit in 0..64 {
        A_new2[bit] = A_new2[bit] ^ RC_bits[bit];
    }

    return A_new2;
}


//Circuit & gadget
impl<E: Engine> Circuit<E> for Sha3_256Gadget {
    fn synthesize<CS: ConstraintSystem<E>>(self, mut cs: &mut CS) -> Result<(), SynthesisError> {
        //TODO: Implement
        panic!("Not implemented");
    }
}

//Test
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
