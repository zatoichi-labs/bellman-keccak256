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
    1u64,
    0x8082u64,
    0x800000000000808au64,
    0x8000000080008000u64,
    0x808bu64,
    0x80000001u64,
    0x8000000080008081u64,
    0x8000000000008009u64,
    0x8au64,
    0x88u64,
    0x80008009u64,
    0x8000000au64,
    0x8000808bu64,
    0x800000000000008bu64,
    0x8000000000008089u64,
    0x8000000000008003u64,
    0x8000000000008002u64,
    0x8000000000000080u64,
    0x800au64,
    0x800000008000000au64,
    0x8000000080008081u64,
    0x8000000000008080u64,
    0x80000001u64,
    0x8000000080008008u64,
];
const PI: [usize; 24] = [
    10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4, 15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1,
];
// const ROTR: [usize; 25] = [ //(5*y)+x
//     0,
//     1,
//     62,
//     28,
//     27,
//     36,
//     44,
//     6,
//     55,
//     20,
//     3,
//     10,
//     43,
//     25,
//     39,
//     41,
//     45,
//     15,
//     21,
//     8,
//     18,
//     2,
//     61,
//     56,
//     14,
// ];
const RHO: [usize; 24] = [
    1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14, 27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44,
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
fn keccak_f_1600(input: Vec<bool>, a: &mut [u64; 25]) -> Vec<bool> {
    let mut A = input;

    for i in 0..24 {
        A = Round_1600(&A, a, ROUND_CONSTANTS[i]);
    }

    return A;
}

fn Round_1600(A: &Vec<bool>, a: &mut [u64; 25], RC: u64) -> Vec<bool> {
    assert_eq!(A.len(), 1600);//64*25

    let mut array: [u64; 5] = [0; 5];

    // # θ step
    // C[x] = A[x,0] xor A[x,1] xor A[x,2] xor A[x,3] xor A[x,4],   for x in 0…4
    let mut C = vec![false; 320];
    for x in 0..5 {
        for bit in 0..64 {
            C[(x * 64usize) + bit] = A[(x * 64usize) + bit + (0usize * 320usize)] ^ A[(x * 64usize) + bit + (1usize * 320usize)] ^ A[(x * 64usize) + bit + (2usize * 320usize)] ^ A[(x * 64usize) + bit + (3usize * 320usize)] ^ A[(x * 64usize) + bit + (4usize * 320usize)];
        }
    }
    // D[x] = C[x-1] xor rot(C[x+1],1),                             for x in 0…4
    let mut D = vec![false; 320];
    for x in 0..5 {
        for bit in 0..64 {
            //x-1 == (x+4)%5
            //bit-1 == (bit+63)%64
            D[(x * 64usize) + bit] = C[(((x + 4usize) % 5usize) * 64usize) + bit] ^ C[(((x + 1usize) % 5usize) * 64usize) + ((bit + 1usize) % 64)];
        }
    }
    // A[x,y] = A[x,y] xor D[x],                           for (x,y) in (0…4,0…4)
    let mut A_new1 = vec![false; 1600];
    for x in 0..5 {
        for y in 0..5 {
            for bit in 0..64 {
                A_new1[(y * 320usize) + (x * 64usize) + bit] = A[(y * 320usize) + (x * 64usize) + bit] ^ D[(x * 64usize) + bit];
            }
        }
    }

    // Theta
    for x in 0..5 {
        for y_count in 0..5 {
            let y = y_count * 5;
            array[x] ^= a[x + y];
        }
    }
    for x in 0..5 {
        for y_count in 0..5 {
            let y = y_count * 5;
            a[y + x] ^= array[(x + 4) % 5] ^ array[(x + 1) % 5].rotate_left(1);
        }
    }
    //Compare
    for i in 0..25 {
        for bit in 0..64 {
            let val = 1u64 << (63usize - bit);
            let a_set = a[i] & val != 0u64;
            assert_eq!(A_new1[(i * 64usize) + bit], a_set);
        }
    }

    // # ρ and π steps
    // B[y,2*x+3*y] = rot(A[x,y], r[x,y]),                 for (x,y) in (0…4,0…4)
    // let mut B = vec![false; 1600];
    // for x in 0..5 {
    //     for y in 0..5 {
    //         for bit in 0..64 {
    //             B[((((2usize * x) + (3usize * y)) % 5) * 320usize) + (y * 64usize) + bit] = A_new1[(y * 320usize) + (x * 64usize) + ((ROTR[(y * 5usize) + x] + bit) % 64usize)];
    //         }
    //     }
    // }
    let mut B = vec![false; 1600];
    for bit in 0..64 {//Since PI[] doesn't contain 0
        B[bit] = A_new1[bit];
    }
    let mut last = 1usize;
    for i in 0..24 {
        for bit in 0..64 {
            B[(PI[i] * 64usize) + bit] = A_new1[(last * 64usize) + ((bit + RHO[i]) % 64usize)];
        }
        last = PI[i];
    }

    // Rho and pi
    let mut last = a[1];
    for x in 0..24 {
        array[0] = a[PI[x]];
        a[PI[x]] = last.rotate_left(RHO[x] as u32);
        last = array[0];
    }
    //Compare
    for i in 0..25 {
        for bit in 0..64 {
            let val = 1u64 << (63usize - bit);
            let a_set = a[i] & val != 0u64;
            assert_eq!(B[(i * 64usize) + bit], a_set);
        }
    }

    // # χ step
    // A[x,y] = B[x,y] xor ((not B[x+1,y]) and B[x+2,y]),  for (x,y) in (0…4,0…4)
    let mut A_new2 = vec![false; 1600];
    for x in 0..5 {
        for y in 0..5 {
            for bit in 0..64 {
                A_new2[(y * 320usize) + (x * 64usize) + bit] = B[(y * 320usize) + (x * 64usize) + bit] ^ ((!B[(y * 320usize) + (((x + 1usize) % 5usize) * 64usize) + bit]) & B[(y * 320usize) + (((x + 2usize) % 5usize) * 64usize) + bit]);
            }
        }
    }

    // Chi
    for y_step in 0..5 {
        let y = y_step * 5;
        for x in 0..5 {
            array[x] = a[y + x];
        }
        for x in 0..5 {
            a[y + x] = array[x] ^ ((!array[(x + 1) % 5]) & (array[(x + 2) % 5]));
        }
    }
    //Compare
    for i in 0..25 {
        for bit in 0..64 {
            let val = 1u64 << (63usize - bit);
            let a_set = a[i] & val != 0u64;
            assert_eq!(A_new2[(i * 64usize) + bit], a_set);
        }
    }

    // # ι step
    let mut RC_bits = vec![false; 64];
    for bit in 0..64 {
        let val = 1u64 << (63usize - bit);
        // let val = 1u64 << bit;
        if RC & val != 0u64 {
            RC_bits[bit] = true;
        }
    }
    // A[0,0] = A[0,0] xor RC
    for bit in 0..64 {
        A_new2[bit] = A_new2[bit] ^ RC_bits[bit];
    }

    // Iota
    a[0] ^= RC;
    //Compare
    for i in 0..25 {
        for bit in 0..64 {
            let val = 1u64 << (63usize - bit);
            let a_set = a[i] & val != 0u64;
            assert_eq!(A_new2[(i * 64usize) + bit], a_set);
        }
    }

    return A_new2;
}

// fn Keccak_256_512(Mbytes: &Vec<bool>) -> Vec<bool> {
//     assert_eq!(Mbytes.len(), 512);

//     // # Padding
//     // d = 2^|Mbits| + sum for i=0..|Mbits|-1 of 2^i*Mbits[i]
//     // P = Mbytes || d || 0x00 || … || 0x00
//     // P = P xor (0x00 || … || 0x00 || 0x80)
//     let mut P_append = vec![false; 1600];
//     //0x0600 ... 0080
//     P_append[5] = true;
//     P_append[6] = true;
//     P_append[1592] = true;

//     // # Initialization
//     // S[x,y] = 0,                               for (x,y) in (0…4,0…4)
//     let mut S = vec![false; 1600];

//     // # Absorbing phase
//     // for each block Pi in P
//     //   S[x,y] = S[x,y] xor Pi[x+5*y],          for (x,y) such that x+5*y < r/w
//     //   S = Keccak-f[r+c](S)
//     for x in 0..5 {
//         for y in 0..5 {
//             for bit in 0..64 {
//                 S[(y * 320usize) + (x * 64usize) + bit] = Mbytes[(y * 320usize) + (x * 64usize) + bit];
//             }
//         }
//     }
//     S = keccak_f_1600(S);
//     for x in 0..5 {
//         for y in 0..5 {
//             for bit in 0..64 {
//                 S[(y * 320usize) + (x * 64usize) + bit] = S[(y * 320usize) + (x * 64usize) + bit] ^ P_append[(y * 320usize) + (x * 64usize) + bit];
//             }
//         }
//     }
//     S = keccak_f_1600(S);

//     // # Squeezing phase
//     // Z = empty string
//     let mut Z = vec![false; 256];

//     // while output is requested
//     //   Z = Z || S[x,y],                        for (x,y) such that x+5*y < r/w
//     //   S = Keccak-f[r+c](S)
//     for bit in 0..256 {
//         Z[bit] = S[bit];
//     }

//     return Z;
// }

fn Keccak_256_0() -> (Vec<bool>,Vec<u64>) {
    // # Padding
    // d = 2^|Mbits| + sum for i=0..|Mbits|-1 of 2^i*Mbits[i]
    // P = Mbytes || d || 0x00 || … || 0x00
    // P = P xor (0x00 || … || 0x00 || 0x80)
    let mut P_append = vec![false; 1600];
    //0x0600 ... 0080
    P_append[5] = true;
    P_append[6] = true;
    P_append[1080] = true;

    // # Initialization
    // S[x,y] = 0,                               for (x,y) in (0…4,0…4)
    let mut S = vec![false; 1600];

    let mut a = [0u64; 25];
    a[0] = 0x0600000000000000u64;
    a[16] = 0x80u64;

    // # Absorbing phase
    // for each block Pi in P
    //   S[x,y] = S[x,y] xor Pi[x+5*y],          for (x,y) such that x+5*y < r/w
    //   S = Keccak-f[r+c](S)
    // for x in 0..5 {
    //     for y in 0..5 {
    //         for bit in 0..64 {
    //             S[(y * 320usize) + (x * 64usize) + bit] = Mbytes[(y * 320usize) + (x * 64usize) + bit];
    //         }
    //     }
    // }
    // S = keccak_f_1600(S);
    for x in 0..5 {
        for y in 0..5 {
            for bit in 0..64 {
                S[(y * 320usize) + (x * 64usize) + bit] = S[(y * 320usize) + (x * 64usize) + bit] ^ P_append[(y * 320usize) + (x * 64usize) + bit];
            }
        }
    }
    S = keccak_f_1600(S, &mut a);

    // # Squeezing phase
    // Z = empty string
    let mut Z = vec![false; 256];

    // while output is requested
    //   Z = Z || S[x,y],                        for (x,y) such that x+5*y < r/w
    //   S = Keccak-f[r+c](S)
    for bit in 0..256 {
        Z[bit] = S[bit];
    }

    return (Z, a.to_vec());
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
    use rand::{thread_rng, Rng}; //thread_rng

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
    use tiny_keccak::Keccak;
    use tiny_keccak::Sha3;
    use tiny_keccak::Hasher;

    #[test]
    fn test_Keccak_256_0() {
        let mut hash_sha3 = [0u8; 32];

        let sha3 = Sha3::v256();

        sha3.finalize(&mut hash_sha3);

        //0xa7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a
        assert_eq!(BigUint::from_bytes_be(&hash_sha3), BigUint::from_str("75988164966894747974200307809782762084705920897667750218208675113520516842314").unwrap());

        let (hash_vector, a) = super::Keccak_256_0();

        let mut hash = [0u8; 32];
        for bit in 0..256 {
            if hash_vector[bit] {
                let byte = bit / 8;
                let byte_bit = 7 - (bit % 8);
                hash[byte] = hash[byte] | (1u8 << byte_bit);
            }
        }

        panic!("hash: {:?}    a: {:?}", hash, a);
    }

    #[ignore]
    #[test]
    fn test_Keccak_256_512() {
        let mut rng = rand::thread_rng();
        for _ in 0..1 {
            let rand_value_left = rng.gen::<[u8; 32]>(); //256 bits
            let rand_value_right = rng.gen::<[u8; 32]>(); //256 bits

            let mut hash = [0u8; 32];

            let mut keccak = Keccak::v256();

            keccak.update(&rand_value_left);
            keccak.update(&rand_value_right);
            keccak.finalize(&mut hash);

            panic!("hash: {:?}", hash);
            // assert_eq!(hash, CARP);
        }
    }
}
