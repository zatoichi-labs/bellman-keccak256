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
            C[(x * 64usize) + bit] = A[(x * 64usize) + bit + (0usize * 320usize)] ^ A[(x * 64usize) + bit + (1usize * 320usize)] ^ A[(x * 64usize) + bit + (2usize * 320usize)] ^ A[(x * 64usize) + bit + (3usize * 320usize)] ^ A[(x * 64usize) + bit + (4usize * 320usize)];
        }
    }
    // // D[x] = C[x-1] xor rot(C[x+1],1),                             for x in 0…4
    // let mut D = vec![false; 320];
    // for x in 0..5 {
    //     for bit in 0..64 {
    //         //x-1 == (x+4)%5
    //         //bit-1 == (bit+63)%64
    //         D[(x * 64usize) + bit] = C[(((x + 4usize) % 5usize) * 64usize) + bit] ^ C[(((x + 1usize) % 5usize) * 64usize) + ((bit + 1usize) % 64)];
    //     }
    // }
    // A[x,y] = A[x,y] xor D[x],                           for (x,y) in (0…4,0…4)
    let mut A_new1 = vec![false; 1600];
    for x in 0..5 {
        for y in 0..5 {
            for bit in 0..64 {
                // A_new1[(y * 320usize) + (x * 64usize) + bit] = A[(y * 320usize) + (x * 64usize) + bit] ^ D[(x * 64usize) + bit];
                A_new1[(y * 320usize) + (x * 64usize) + bit] = A[(y * 320usize) + (x * 64usize) + bit] ^ (C[(((x + 4usize) % 5usize) * 64usize) + bit] ^ C[(((x + 1usize) % 5usize) * 64usize) + ((bit + 1usize) % 64)]);
            }
        }
    }

    // # ρ and π steps
    // B[y,2*x+3*y] = rot(A[x,y], r[x,y]),                 for (x,y) in (0…4,0…4)
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

    return A_new2;
}

fn Keccak_256_512(Mbytes: &Vec<bool>) -> Vec<bool> {
    assert_eq!(Mbytes.len(), 512);

    // # Padding
    // d = 2^|Mbits| + sum for i=0..|Mbits|-1 of 2^i*Mbits[i]
    // P = Mbytes || d || 0x00 || … || 0x00
    // P = P xor (0x00 || … || 0x00 || 0x80)
    //0x0100 ... 0080
    let mut P_append = vec![false; 1088];//1600-512
    P_append[63] = true;
    P_append[1024 - 512] = true;

    // # Initialization
    // S[x,y] = 0,                               for (x,y) in (0…4,0…4)
    let mut S = Mbytes.clone();
    S.append(&mut P_append);

    // # Absorbing phase
    // for each block Pi in P
    //   S[x,y] = S[x,y] xor Pi[x+5*y],          for (x,y) such that x+5*y < r/w
    //   S = Keccak-f[r+c](S)

    S = keccak_f_1600(S);

    // # Squeezing phase
    // Z = empty string
    let mut Z = vec![false; 256];

    // while output is requested
    //   Z = Z || S[x,y],                        for (x,y) such that x+5*y < r/w
    //   S = Keccak-f[r+c](S)
    for bit in 0..256 {
        Z[bit] = S[bit];
    }

    return Z;
}

// fn Keccak_256_0() -> Vec<bool> {
//     // # Padding
//     // d = 2^|Mbits| + sum for i=0..|Mbits|-1 of 2^i*Mbits[i]
//     // P = Mbytes || d || 0x00 || … || 0x00
//     // P = P xor (0x00 || … || 0x00 || 0x80)
//     let mut P_append = vec![false; 1600];
//     //0x0600 ... 0080
//     // P_append[5] = true;
//     // P_append[6] = true;
//     // P_append[1080] = true;
//     P_append[61] = true;
//     P_append[62] = true;
//     P_append[1024] = true;


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
    // use tiny_keccak::Sha3;
    use tiny_keccak::Hasher;
    use secp256k1::{PublicKey, SecretKey, Secp256k1};

    // #[test]
    // fn test_Keccak_256_0() {
    //     let mut hash_sha3 = [0u8; 32];

    //     let sha3 = Sha3::v256();

    //     sha3.finalize(&mut hash_sha3);

    //     //0xa7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a
    //     assert_eq!(BigUint::from_bytes_be(&hash_sha3), BigUint::from_str("75988164966894747974200307809782762084705920897667750218208675113520516842314").unwrap());

    //     let hash_vector = super::Keccak_256_0();

    //     //Convert from little-endian
    //     let mut hash = [0u8; 32];
    //     for bit in 0..256 {
    //         if hash_vector[bit] {
    //             let byte_be = bit / 8;
    //             let word = bit / 64;
    //             let word_byte_le = 7 - (byte_be % 8);
    //             let byte_le = (word * 8) + word_byte_le;
    //             let byte_bit = 7 - (bit % 8);
    //             hash[byte_le] = hash[byte_le] | (1u8 << byte_bit);
    //         }
    //     }

    //     assert_eq!(BigUint::from_bytes_be(&hash), BigUint::from_str("75988164966894747974200307809782762084705920897667750218208675113520516842314").unwrap());
    // }

    #[test]
    fn test_Keccak_256_512() {
        let mut rng = rand::thread_rng();
        for _ in 0..16 {
            let mut keccak = Keccak::v256();

            let mut rand_value = [0u8; 64];
            rng.fill(&mut rand_value);                    // array fill

            keccak.update(&rand_value);

            let mut hash_source = [0u8; 32];
            keccak.finalize(&mut hash_source);

            //Prepare with be-to-le
            let mut preimage = vec![false; 512];
            for byte in 0usize..64usize {
                let byte_input = byte;
                let word_output = byte / 8usize;
                let word_byte_output = 7usize - byte % 8usize;
                let byte_output = (word_output * 8usize) + word_byte_output;

                for bit in 0usize..8usize {
                    let byte_bit = 7usize - (bit % 8usize);
                    preimage[(byte_output * 8usize) + byte_bit] = (rand_value[byte_input] & (1u8 << bit)) != 0u8;
                }
            }

            //Call
            let hash_vector = super::Keccak_256_512(&preimage);

            //Convert from little-endian
            let mut hash = [0u8; 32];
            for bit in 0..256 {
                if hash_vector[bit] {
                    let byte_be = bit / 8usize;
                    let word = bit / 64usize;
                    let word_byte_le = 7usize - (byte_be % 8usize);
                    let byte_le = (word * 8usize) + word_byte_le;
                    let byte_bit = 7usize - (bit % 8usize);
                    hash[byte_le] |= 1u8 << byte_bit;
                }
            }

            assert_eq!(hash, hash_source);
        }
    }

    #[test]
    fn test_ethereum_addresses() {
        // mnemonic:	"into trim cross then helmet popular suit hammer cart shrug oval student"
        // seed:		ca5a4407934514911183f0c4ffd71674ab28028c060c15d270977ba57c390771967ab84ed473702fef5eb36add05ea590d99ddff14c730e93ad14b418a2788b8
        // private key:	d6840b79c2eb1f5ff97a41590df3e04d7d4b0965073ff2a9fbb7ff003799dc71
        // address:	0x604a95C9165Bc95aE016a5299dd7d400dDDBEa9A
        // mnemonic:	"finish oppose decorate face calm tragic certain desk hour urge dinosaur mango"
        // seed:		7d34eb533ad9fea340cd93d82b8baead0c00a81380caa682aca06631fe851a63093db5cb5c81b3009a0281b2c34959750bbb5dfaab219d17f04f1a1b37b93400
        // private key:	d3cc16948a02a91b9fcf83735653bf3dfd82c86543fdd1e9a828bd25e8a7b68d
        // address:	0x1c96099350f13D558464eC79B9bE4445AA0eF579

        let secp = Secp256k1::new();
        {
            let s = SecretKey::from_str("0000000000000000000000000000000000000000000000000000000000000001").unwrap();
            let public_key: PublicKey = PublicKey::from_secret_key(&secp, &s);

            let public_key_serial = public_key.serialize_uncompressed();

            let public_key_serial_type = &public_key_serial[0..1];
            // let public_key_serial_x = &public_key_serial[1..33];
            // let public_key_serial_y = &public_key_serial[33..65];

            assert_eq!(public_key_serial_type[0], 4u8); //Long, y is signed

            let preimage = (&public_key_serial[1..]).clone();
            assert_eq!(preimage.len(), 64);

            {
                let mut keccak = Keccak::v256();

                keccak.update(&preimage);

                let mut hash = [0u8; 32];
                keccak.finalize(&mut hash);

                let address = (&hash[12..32]).clone();

                let address_hex = hex::encode(address);
                assert_eq!(address_hex, "7e5f4552091a69125d5dfcb7b8c2659029395bdf");
            }

            //Prepare with be-to-le
            let mut preimage_bits = vec![false; 512];
            for byte in 0usize..64usize {
                let byte_input = byte;
                let word_output = byte / 8usize;
                let word_byte_output = 7usize - byte % 8usize;
                let byte_output = (word_output * 8usize) + word_byte_output;

                for bit in 0usize..8usize {
                    let byte_bit = 7usize - (bit % 8usize);
                    preimage_bits[(byte_output * 8usize) + byte_bit] = (preimage[byte_input] & (1u8 << bit)) != 0u8;
                }
            }

            //Call
            let hash_vector = super::Keccak_256_512(&preimage_bits);

            //Convert from little-endian
            let mut hash = [0u8; 32];
            for bit in 0..256 {
                if hash_vector[bit] {
                    let byte_be = bit / 8usize;
                    let word = bit / 64usize;
                    let word_byte_le = 7usize - (byte_be % 8usize);
                    let byte_le = (word * 8usize) + word_byte_le;
                    let byte_bit = 7usize - (bit % 8usize);
                    hash[byte_le] |= 1u8 << byte_bit;
                }
            }

            let address = (&hash[12..32]).clone();

            let address_hex = hex::encode(address);
            assert_eq!(address_hex, "7e5f4552091a69125d5dfcb7b8c2659029395bdf");
        }

        {
            let s = SecretKey::from_str("d6840b79c2eb1f5ff97a41590df3e04d7d4b0965073ff2a9fbb7ff003799dc71").unwrap();
            let public_key: PublicKey = PublicKey::from_secret_key(&secp, &s);

            let public_key_serial = public_key.serialize_uncompressed();

            let public_key_serial_type = &public_key_serial[0..1];
            // let public_key_serial_x = &public_key_serial[1..33];
            // let public_key_serial_y = &public_key_serial[33..65];

            assert_eq!(public_key_serial_type[0], 4u8); //Long, y is signed

            let preimage = (&public_key_serial[1..]).clone();
            assert_eq!(preimage.len(), 64);

            {
                let mut keccak = Keccak::v256();

                keccak.update(&preimage);

                let mut hash = [0u8; 32];
                keccak.finalize(&mut hash);

                let address = (&hash[12..32]).clone();

                let address_hex = hex::encode(address);

                let address_check = hex::decode("604a95C9165Bc95aE016a5299dd7d400dDDBEa9A").unwrap();
                let address_check_hex = hex::encode(address_check);

                assert_eq!(address_hex, address_check_hex);
            }

            //Prepare with be-to-le
            let mut preimage_bits = vec![false; 512];
            for byte in 0usize..64usize {
                let byte_input = byte;
                let word_output = byte / 8usize;
                let word_byte_output = 7usize - byte % 8usize;
                let byte_output = (word_output * 8usize) + word_byte_output;

                for bit in 0usize..8usize {
                    let byte_bit = 7usize - (bit % 8usize);
                    preimage_bits[(byte_output * 8usize) + byte_bit] = (preimage[byte_input] & (1u8 << bit)) != 0u8;
                }
            }

            //Call
            let hash_vector = super::Keccak_256_512(&preimage_bits);

            //Convert from little-endian
            let mut hash = [0u8; 32];
            for bit in 0..256 {
                if hash_vector[bit] {
                    let byte_be = bit / 8usize;
                    let word = bit / 64usize;
                    let word_byte_le = 7usize - (byte_be % 8usize);
                    let byte_le = (word * 8usize) + word_byte_le;
                    let byte_bit = 7usize - (bit % 8usize);
                    hash[byte_le] |= 1u8 << byte_bit;
                }
            }

            let address = (&hash[12..32]).clone();

            let address_hex = hex::encode(address);

            let address_check = hex::decode("604a95C9165Bc95aE016a5299dd7d400dDDBEa9A").unwrap();
            let address_check_hex = hex::encode(address_check);

            assert_eq!(address_hex, address_check_hex);
        }

        {
            let s = SecretKey::from_str("d3cc16948a02a91b9fcf83735653bf3dfd82c86543fdd1e9a828bd25e8a7b68d").unwrap();
            let public_key: PublicKey = PublicKey::from_secret_key(&secp, &s);

            let public_key_serial = public_key.serialize_uncompressed();

            let public_key_serial_type = &public_key_serial[0..1];
            // let public_key_serial_x = &public_key_serial[1..33];
            // let public_key_serial_y = &public_key_serial[33..65];

            assert_eq!(public_key_serial_type[0], 4u8); //Long, y is signed

            let preimage = (&public_key_serial[1..]).clone();
            assert_eq!(preimage.len(), 64);

            {
                let mut keccak = Keccak::v256();

                keccak.update(&preimage);

                let mut hash = [0u8; 32];
                keccak.finalize(&mut hash);

                let address = (&hash[12..32]).clone();

                let address_hex = hex::encode(address);

                let address_check = hex::decode("1c96099350f13D558464eC79B9bE4445AA0eF579").unwrap();
                let address_check_hex = hex::encode(address_check);

                assert_eq!(address_hex, address_check_hex);
            }

            //Prepare with be-to-le
            let mut preimage_bits = vec![false; 512];
            for byte in 0usize..64usize {
                let byte_input = byte;
                let word_output = byte / 8usize;
                let word_byte_output = 7usize - byte % 8usize;
                let byte_output = (word_output * 8usize) + word_byte_output;

                for bit in 0usize..8usize {
                    let byte_bit = 7usize - (bit % 8usize);
                    preimage_bits[(byte_output * 8usize) + byte_bit] = (preimage[byte_input] & (1u8 << bit)) != 0u8;
                }
            }

            //Call
            let hash_vector = super::Keccak_256_512(&preimage_bits);

            //Convert from little-endian
            let mut hash = [0u8; 32];
            for bit in 0..256 {
                if hash_vector[bit] {
                    let byte_be = bit / 8usize;
                    let word = bit / 64usize;
                    let word_byte_le = 7usize - (byte_be % 8usize);
                    let byte_le = (word * 8usize) + word_byte_le;
                    let byte_bit = 7usize - (bit % 8usize);
                    hash[byte_le] |= 1u8 << byte_bit;
                }
            }

            let address = (&hash[12..32]).clone();

            let address_hex = hex::encode(address);

            let address_check = hex::decode("1c96099350f13D558464eC79B9bE4445AA0eF579").unwrap();
            let address_check_hex = hex::encode(address_check);

            assert_eq!(address_hex, address_check_hex);
        }
    }
}