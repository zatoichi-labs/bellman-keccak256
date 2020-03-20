use core::convert::{TryFrom, TryInto};

use bellman::gadgets::boolean::{AllocatedBit, Boolean};
use bellman::gadgets::multipack;
use bellman::groth16::generate_random_parameters;
use bellman::groth16::Parameters;
use bellman::groth16::Proof as Groth16Proof;
use bellman::groth16::{create_random_proof, prepare_verifying_key, verify_proof};
use bellman::SynthesisError;
use bellman::{Circuit, ConstraintSystem};

use ff::ScalarEngine;
use pairing::bls12_381::Bls12;
use pairing::Engine;
use rand_core::OsRng;

use crate::types::{Error, H256, H512};
use crate::uint64::UInt64;

#[allow(clippy::unreadable_literal)]
pub const ROUND_CONSTANTS: [u64; 24] = [
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
const ROTR: [usize; 25] = [
    0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14,
];

#[derive(Deserialize, Serialize, Clone, Copy, Debug)]
pub struct PublicInput {
    pub hash: H256, // Hash
}

impl PublicInput {
    pub fn new(hash: H256) -> Self {
        Self { hash: hash }
    }
}

#[derive(Deserialize, Serialize, Clone, Debug)]
pub struct PrivateInput {
    pub preimage: H512,
}

impl PrivateInput {
    pub fn new(preimage: H512) -> Self {
        Self { preimage: preimage }
    }
}

#[derive(Clone)]
struct Keccak256gadgetInput {
    /// Hash
    hash: H256,
    /// Preimage
    preimage: H512,
}

#[derive(Default)]
pub struct Keccak256gadget {
    input: Option<Keccak256gadgetInput>,
}

impl Keccak256gadget {
    /// Used when generating setup parameters
    #[cfg(feature = "std")]
    pub fn default() -> Self {
        Self { input: None }
    }

    /// Used when generating a proof
    pub fn new(hash: H256, preimage: H512) -> Self {
        let input = Keccak256gadgetInput { hash, preimage };
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

fn xor_2<E, CS>(mut cs: CS, a: &UInt64, b: &UInt64) -> Result<UInt64, SynthesisError>
where
    E: ScalarEngine,
    CS: ConstraintSystem<E>,
{
    // a ^ b
    a.xor(cs.namespace(|| "xor_2"), b)
}

fn xor_5<E, CS>(
    mut cs: CS,
    a: &UInt64,
    b: &UInt64,
    c: &UInt64,
    d: &UInt64,
    e: &UInt64,
) -> Result<UInt64, SynthesisError>
where
    E: ScalarEngine,
    CS: ConstraintSystem<E>,
{
    // a ^ b ^ c ^ d ^ e
    let ab = a.xor(cs.namespace(|| "xor_5 first"), b)?;
    let abc = ab.xor(cs.namespace(|| "xor_5 second"), c)?;
    let abcd = abc.xor(cs.namespace(|| "xor_5 third"), d)?;
    abcd.xor(cs.namespace(|| "xor_5 fourth"), e)
}

fn xor_not_and<E, CS>(
    mut cs: CS,
    a: &UInt64,
    b: &UInt64,
    c: &UInt64,
) -> Result<UInt64, SynthesisError>
where
    E: ScalarEngine,
    CS: ConstraintSystem<E>,
{
    // a ^ ((!b) & c)
    let nb = b.not();
    let nbc = nb.and(cs.namespace(|| "xor_not_and second"), c)?;
    a.xor(cs.namespace(|| "xor_not_and third"), &nbc)
}

fn round_1600<E, CS>(mut cs: CS, a: Vec<UInt64>, rc: u64) -> Result<Vec<UInt64>, SynthesisError>
where
    E: ScalarEngine,
    CS: ConstraintSystem<E>,
{
    assert_eq!(a.len(), 25);

    // panic!("a: {:?}", a);

    // # θ step
    // C[x] = A[x,0] xor A[x,1] xor A[x,2] xor A[x,3] xor A[x,4],   for x in 0…4
    let mut c = Vec::new();
    for x in 0..5 {
        let cs = &mut cs.namespace(|| format!("omega c {}", x));

        c.push(xor_5(
            cs,
            &a[x + 0usize],
            &a[x + 5usize],
            &a[x + 10usize],
            &a[x + 15usize],
            &a[x + 20usize],
        )?);
    }

    // panic!("c: {:?}", c);

    // D[x] = C[x-1] xor rot(C[x+1],1),                             for x in 0…4
    let mut d = Vec::new();
    for x in 0..5 {
        let cs = &mut cs.namespace(|| format!("omega d {}", x));

        d.push(xor_2(
            cs,
            &c[(x + 4usize) % 5usize],
            &c[(x + 1usize) % 5usize].rotl(1),
        )?);
    }

    // panic!("d: {:?}", d);

    // A[x,y] = A[x,y] xor D[x],                           for (x,y) in (0…4,0…4)
    let mut a_new1 = Vec::new();
    for y in 0..5 {
        for x in 0..5 {
            let cs = &mut cs.namespace(|| format!("omega {},{}", x, y));

            a_new1.push(xor_2(cs, &a[x + (y * 5usize)], &d[x])?);
        }
    }

    // panic!("a_new1: {:?}", a_new1);

    // # ρ and π steps
    // B[y,2*x+3*y] = rot(A[x,y], r[x,y]),                 for (x,y) in (0…4,0…4)
    let mut b = a_new1.clone();
    for y in 0..5 {
        for x in 0..5 {
            b[y + ((((2 * x) + (3 * y)) % 5) * 5usize)] =
                a_new1[x + (y * 5usize)].rotl(ROTR[x + (y * 5usize)]);
        }
    }

    // panic!("b: {:?}", b);

    let mut a_new2 = Vec::new();

    // # χ step
    // A[x,y] = B[x,y] xor ((not B[x+1,y]) and B[x+2,y]),  for (x,y) in (0…4,0…4)
    for y in 0..5 {
        for x in 0..5 {
            let cs = &mut cs.namespace(|| format!("chi {},{}", x, y));

            a_new2.push(xor_not_and(
                cs,
                &b[x + (y * 5usize)],
                &b[((x + 1usize) % 5usize) + (y * 5usize)],
                &b[((x + 2usize) % 5usize) + (y * 5usize)],
            )?);
        }
    }

    // panic!("a_new2: {:?}", a_new2);

    // // # ι step
    // // A[0,0] = A[0,0] xor RC
    let rc = UInt64::constant(rc);
    a_new2[0] = a_new2[0].xor(cs.namespace(|| "xor RC"), &rc)?;

    // panic!("a_new2: {:?}", a_new2);

    Ok(a_new2)
}

fn keccak_f_1600<E, CS>(mut cs: CS, input: Vec<Boolean>) -> Result<Vec<Boolean>, SynthesisError>
where
    E: ScalarEngine,
    CS: ConstraintSystem<E>,
{
    assert_eq!(input.len(), 1600);

    let mut a = input
        .chunks(64)
        .map(|e| UInt64::from_bits(e))
        .collect::<Vec<_>>();

    for i in 0..24 {
        let cs = &mut cs.namespace(|| format!("keccack round {}", i));

        a = round_1600(cs, a, ROUND_CONSTANTS[i])?;
    }

    let a_new = a.into_iter().flat_map(|e| e.into_bits()).collect();

    return Ok(a_new);
}

// TODO Make this private!
pub fn keccak_256_512<E, CS>(cs: CS, input: Vec<Boolean>) -> Result<Vec<Boolean>, SynthesisError>
where
    E: ScalarEngine,
    CS: ConstraintSystem<E>,
{
    assert_eq!(input.len(), 512);

    let mut m = Vec::new();
    for i in 0..1600 {
        if i < 512 {
            m.push(input[i].clone());
        } else {
            m.push(Boolean::Constant(false));
        }
    }

    // # Padding
    // d = 2^|Mbits| + sum for i=0..|Mbits|-1 of 2^i*Mbits[i]
    // P = Mbytes || d || 0x00 || … || 0x00
    // P = P xor (0x00 || … || 0x00 || 0x80)
    //0x0100 ... 0080
    m[512] = Boolean::Constant(true);
    m[1087] = Boolean::Constant(true);

    // # Initialization
    // S[x,y] = 0,                               for (x,y) in (0…4,0…4)

    // # Absorbing phase
    // for each block Pi in P
    //   S[x,y] = S[x,y] xor Pi[x+5*y],          for (x,y) such that x+5*y < r/w
    //   S = Keccak-f[r+c](S)

    let m = keccak_f_1600(cs, m)?;

    // # Squeezing phase
    // Z = empty string
    let mut z = Vec::new();

    // while output is requested
    //   Z = Z || S[x,y],                        for (x,y) such that x+5*y < r/w
    //   S = Keccak-f[r+c](S)
    for i in 0..256 {
        z.push(m[i].clone());
    }

    return Ok(z);
}

//Circuit & gadget
impl<E: Engine> Circuit<E> for Keccak256gadget {
    fn synthesize<CS: ConstraintSystem<E>>(self, mut cs: &mut CS) -> Result<(), SynthesisError> {
        let preimage;
        if let Some(input_parameters) = self.input.clone() {
            preimage = (0..512)
                .map(|i| {
                    let byte_input = i / 8usize;
                    let bit = i % 8usize;
                    let flag =
                        (input_parameters.preimage.to_vec()[byte_input] & (1u8 << bit)) != 0u8;
                    if flag {
                        AllocatedBit::alloc(
                            cs.namespace(|| format!("preimage bit {}", i)),
                            Some(true),
                        )
                        .unwrap()
                        .into()
                    } else {
                        AllocatedBit::alloc(
                            cs.namespace(|| format!("preimage bit {}", i)),
                            Some(false),
                        )
                        .unwrap()
                        .into()
                    }
                })
                .collect();
        } else {
            preimage = (0..512)
                .map(|i| {
                    AllocatedBit::alloc(cs.namespace(|| format!("preimage bit {}", i)), None)
                        .unwrap()
                        .into()
                })
                .collect();
        }

        //Call
        let hash_vector = keccak_256_512(&mut cs, preimage)?;

        //Convert & confirm
        // if let Some(input_parameters) = self.input {
        //     let mut hash = [0u8; 32];
        //     for bit in 0..256 {
        //         if hash_vector[bit].get_value().unwrap() {
        //             let byte_bit = bit % 8usize;
        //             let byte_be = bit / 8usize;
        //             hash[byte_be] |= 1u8 << byte_bit;
        //         }
        //     }

        //     assert_eq!(input_parameters.hash.to_vec(), hash.to_vec());
        // }
        if let Some(input_parameters) = self.input {
            let commitment_map: Vec<bool> = input_parameters
                .hash
                .iter()
                .map(|byte| {
                    (0..8).map(move |i| {
                        if (byte >> i) & 1u8 == 1u8 {
                            true
                        } else {
                            false
                        }
                    })
                })
                .flatten()
                .collect();

            let hash_clone = hash_vector.clone();
            for (i, b) in hash_clone.into_iter().enumerate() {
                assert_eq!(commitment_map[i], b.get_value().unwrap());
            }
        } else {
            //Do nothing
        }

        // Expose the vector of 32 boolean variables as compact public inputs.
        multipack::pack_into_inputs(cs.namespace(|| "pack hash"), &hash_vector)
    }
}

pub fn generate() -> Result<SetupParams, Error> {
    generate_random_parameters::<Bls12, _, _>(Keccak256gadget::default(), &mut OsRng)
        .map_err(|e| Error::Synthesis(e))
}

pub fn prove(params: &SetupParams, x: PublicInput, w: PrivateInput) -> Result<Proof, Error> {
    let gadget = Keccak256gadget::new(x.hash, w.preimage);

    let proof = create_random_proof(gadget, params, &mut OsRng).map_err(|e| Error::Synthesis(e))?;

    Ok(proof.try_into()?)
}

pub fn verify(params: &SetupParams, x: PublicInput, proof: Proof) -> bool {
    // Prepare the verification key (for proof verification).
    let pvk = prepare_verifying_key(&params.vk);

    let hash = x.hash; //login_hash(x.global_salt, x.password_hash);

    // Pack the hash as inputs for proof verification.
    let hash_bits = multipack::bytes_to_bits_le(hash.as_ref());
    let inputs = multipack::compute_multipacking::<Bls12>(&hash_bits);

    // Check the proof!
    let proof = proof.try_into();
    if proof.is_err() {
        return false;
    }

    // Won't panic now
    let result = verify_proof(&pvk, &proof.unwrap(), &inputs);
    result.is_ok() && result.unwrap() // True if result is Ok() and is set
}
