use core::convert::TryInto;

use bellman::gadgets::multipack;
#[cfg(feature = "std")]
use bellman::groth16::generate_random_parameters;
use bellman::groth16::{create_random_proof, prepare_verifying_key, verify_proof};

use pairing::bls12_381::Bls12;

// use tiny_keccak::Keccak;

#[cfg(feature = "std")]
use rand_core::OsRng; //RngCore
#[cfg(not(feature = "std"))]
use rand_core::{RngCore, SeedableRng};
#[cfg(not(feature = "std"))]
use rand_xorshift::XorShiftRng;

use crate::gadget::{Proof, SetupParams, Sha3_256Gadget};
use crate::types::{Credentials, Error, Login}; //, H256, H512

#[cfg(feature = "std")]
pub fn generate() -> Result<SetupParams, Error> {
    generate_random_parameters::<Bls12, _, _>(Sha3_256Gadget::default(), &mut OsRng)
        .map_err(|e| Error::Synthesis(e))
}

type PublicInputs = Login;
type PrivateInputs = Credentials;

pub fn prove(
    params: &SetupParams,
    x: PublicInputs, // NOTE: x.committed_public_key is not populated, initially
    w: PrivateInputs,
    #[cfg(not(feature = "std"))] seed: Seed, // NOTE: no_std builds need to provide their own rng seed
) -> Result<Proof, Error> {
    let gadget = Sha3_256Gadget::new(x.hash, w.preimage);

    #[cfg(not(feature = "std"))]
    let mut rng = XorShiftRng::from_seed(seed);

    #[cfg(not(feature = "std"))]
    let proof = create_random_proof(gadget, params, &mut rng).map_err(|e| Error::Synthesis(e))?;

    #[cfg(feature = "std")]
    let proof = create_random_proof(gadget, params, &mut OsRng).map_err(|e| Error::Synthesis(e))?;

    Ok(proof.try_into()?)
}

pub fn verify(params: &SetupParams, x: PublicInputs, proof: Proof) -> bool {
    // Prepare the verification key (for proof verification).
    let pvk = prepare_verifying_key(&params.vk);

    let login_hash = x.as_vec(); //login_hash(x.global_salt, x.password_hash);

    // Pack the hash as inputs for proof verification.
    let hash_bits = multipack::bytes_to_bits_le(login_hash.as_ref());
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

#[cfg(all(test, not(feature = "std")))]
mod no_std_test {}

#[cfg(all(test, feature = "std"))]
mod std_test {}
