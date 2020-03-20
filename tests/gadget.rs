use rand::Rng;

use bellman::gadgets::boolean::Boolean;
use bellman::gadgets::test::*;
use pairing::bls12_381::Bls12;
use std::str::FromStr;
use tiny_keccak::Keccak;
use secp256k1::{PublicKey, Secp256k1, SecretKey};
use std::{fs::OpenOptions, io::prelude::*};
use tiny_keccak::Hasher;

use keccak_gadget;

const PI: [usize; 24] = [
    10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4, 15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1,
];

const RHO: [usize; 24] = [
    1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14, 27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44,
];

fn keccak_f_1600_primitive(input: Vec<bool>) -> Vec<bool> {
    let mut A = input;

    for i in 0..24 {
        A = round_1600_primitive(&A, keccak_gadget::ROUND_CONSTANTS[i]);
    }

    return A;
}

fn xor_2_primitive(a: &bool, b: &bool) -> bool {
    a ^ b
}

fn xor_3_primitive(a: &bool, b: &bool, c: &bool) -> bool {
    a ^ b ^ c
}

fn xor_5_primitive(a: &bool, b: &bool, c: &bool, d: &bool, e: &bool) -> bool {
    a ^ b ^ c ^ d ^ e
}

fn xor_not_and_primitive(a: &bool, b: &bool, c: &bool) -> bool {
    a ^ ((!b) & c)
}

fn round_1600_primitive(A: &Vec<bool>, RC: u64) -> Vec<bool> {
    assert_eq!(A.len(), 1600); //64*25

    // # θ step
    // C[x] = A[x,0] xor A[x,1] xor A[x,2] xor A[x,3] xor A[x,4],   for x in 0…4
    let mut C = vec![false; 320];
    for x in 0..5 {
        for bit in 0..64 {
            C[(x * 64usize) + bit] = xor_5_primitive(
                &A[(x * 64usize) + bit + (0usize * 320usize)],
                &A[(x * 64usize) + bit + (1usize * 320usize)],
                &A[(x * 64usize) + bit + (2usize * 320usize)],
                &A[(x * 64usize) + bit + (3usize * 320usize)],
                &A[(x * 64usize) + bit + (4usize * 320usize)],
            );
        }
    }
    // D[x] = C[x-1] xor rot(C[x+1],1),                             for x in 0…4
    // A[x,y] = A[x,y] xor D[x],                           for (x,y) in (0…4,0…4)
    let mut A_new1 = vec![false; 1600];
    for x in 0..5 {
        for y in 0..5 {
            for bit in 0..64 {
                // A_new1[(y * 320usize) + (x * 64usize) + bit] = A[(y * 320usize) + (x * 64usize) + bit] ^ D[(x * 64usize) + bit];
                A_new1[(y * 320usize) + (x * 64usize) + bit] = xor_3_primitive(
                    &A[(y * 320usize) + (x * 64usize) + bit],
                    &C[(((x + 4usize) % 5usize) * 64usize) + bit],
                    &C[(((x + 1usize) % 5usize) * 64usize) + ((bit + 1usize) % 64)],
                );
            }
        }
    }

    // # ρ and π steps
    // B[y,2*x+3*y] = rot(A[x,y], r[x,y]),                 for (x,y) in (0…4,0…4)
    let mut B = vec![false; 1600];
    for bit in 0..64 {
        //Since PI[] doesn't contain 0
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
                A_new2[(y * 320usize) + (x * 64usize) + bit] = xor_not_and_primitive(
                    &B[(y * 320usize) + (x * 64usize) + bit],
                    &B[(y * 320usize) + (((x + 1usize) % 5usize) * 64usize) + bit],
                    &B[(y * 320usize) + (((x + 2usize) % 5usize) * 64usize) + bit],
                );
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
        A_new2[bit] = xor_2_primitive(&A_new2[bit], &RC_bits[bit]);
    }

    return A_new2;
}

fn keccak_256_512_primitive(mbytes: &Vec<bool>) -> Vec<bool> {
    assert_eq!(mbytes.len(), 512);

    // # Padding
    // d = 2^|Mbits| + sum for i=0..|Mbits|-1 of 2^i*Mbits[i]
    // P = Mbytes || d || 0x00 || … || 0x00
    // P = P xor (0x00 || … || 0x00 || 0x80)
    //0x0100 ... 0080
    let mut p_append = vec![false; 1088]; //1600-512
    p_append[63] = true;
    p_append[1024 - 512] = true;

    // # Initialization
    // S[x,y] = 0,                               for (x,y) in (0…4,0…4)
    let mut s = mbytes.clone();
    s.append(&mut p_append);

    // # Absorbing phase
    // for each block Pi in P
    //   S[x,y] = S[x,y] xor Pi[x+5*y],          for (x,y) such that x+5*y < r/w
    //   S = Keccak-f[r+c](S)

    s = keccak_f_1600_primitive(s);

    // # Squeezing phase
    // Z = empty string
    let mut z = vec![false; 256];

    // while output is requested
    //   Z = Z || S[x,y],                        for (x,y) such that x+5*y < r/w
    //   S = Keccak-f[r+c](S)
    for bit in 0..256 {
        z[bit] = s[bit];
    }

    return z;
}

#[ignore]
#[test]
fn test_Keccak_256_512_primitive() {
    let mut rng = rand::thread_rng();
    for _ in 0..1 {
        let mut keccak = Keccak::v256();

        let mut rand_value = [0u8; 64];
        rng.fill(&mut rand_value); // array fill

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
                preimage[(byte_output * 8usize) + byte_bit] =
                    (rand_value[byte_input] & (1u8 << bit)) != 0u8;
            }
        }

        //Call
        let hash_vector = keccak_256_512_primitive(&preimage);

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

#[ignore]
#[test]
fn test_ethereum_addresses_primitive() {
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
        let s = SecretKey::from_str(
            "0000000000000000000000000000000000000000000000000000000000000001",
        )
        .unwrap();
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
                preimage_bits[(byte_output * 8usize) + byte_bit] =
                    (preimage[byte_input] & (1u8 << bit)) != 0u8;
            }
        }

        //Call
        let hash_vector = keccak_256_512_primitive(&preimage_bits);

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
        let s = SecretKey::from_str(
            "d6840b79c2eb1f5ff97a41590df3e04d7d4b0965073ff2a9fbb7ff003799dc71",
        )
        .unwrap();
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

            let address_check =
                hex::decode("604a95C9165Bc95aE016a5299dd7d400dDDBEa9A").unwrap();
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
                preimage_bits[(byte_output * 8usize) + byte_bit] =
                    (preimage[byte_input] & (1u8 << bit)) != 0u8;
            }
        }

        //Call
        let hash_vector = keccak_256_512_primitive(&preimage_bits);

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
        let s = SecretKey::from_str(
            "d3cc16948a02a91b9fcf83735653bf3dfd82c86543fdd1e9a828bd25e8a7b68d",
        )
        .unwrap();
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

            let address_check =
                hex::decode("1c96099350f13D558464eC79B9bE4445AA0eF579").unwrap();
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
                preimage_bits[(byte_output * 8usize) + byte_bit] =
                    (preimage[byte_input] & (1u8 << bit)) != 0u8;
            }
        }

        //Call
        let hash_vector = keccak_256_512_primitive(&preimage_bits);

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

#[test]
fn test_Keccak_256_512() {
    let mut rng = rand::thread_rng();
    for _ in 0..1 {
        let mut keccak = Keccak::v256();

        let mut rand_value = [0u8; 64];
        rng.fill(&mut rand_value); // array fill
                                   // rand_value[0] = 1;

        keccak.update(&rand_value);

        let mut hash_source = [0u8; 32];
        keccak.finalize(&mut hash_source);

        //Prepare preimage
        let mut preimage = Vec::new();
        for _ in 0..512 {
            preimage.push(Boolean::Constant(false));
        }
        for byte in 0usize..64usize {
            let byte_input = byte;
            let byte_output = byte;

            for bit in 0usize..8usize {
                let byte_bit = bit;
                let flag = (rand_value[byte_input] & (1u8 << bit)) != 0u8;
                if flag {
                    preimage[(byte_output * 8usize) + byte_bit] = Boolean::Constant(true);
                }
            }
        }

        let mut cs = TestConstraintSystem::<Bls12>::new();

        //Call
        let hash_vector = keccak_gadget::keccak_256_512(&mut cs, preimage).unwrap();

        //Convert
        let mut hash = [0u8; 32];
        for bit in 0..256 {
            if hash_vector[bit].get_value().unwrap() {
                let byte_bit = bit % 8usize;
                let byte_be = bit / 8usize;
                hash[byte_be] |= 1u8 << byte_bit;
            }
        }

        assert_eq!(hash, hash_source);
    }
}

#[ignore]
#[test]
fn test_keccak_generate_and_save() {
    let params_file = "params.keys";

    let mut params_file = OpenOptions::new()
        .write(true) // Write only
        .create(true) // Create file if it doesn't exist
        .truncate(true) // Delete previous key
        .open(params_file)
        .unwrap();

    let params = keccak_gadget::generate().unwrap();

    let mut v = vec![];
    params.write(&mut v).unwrap();
    params_file.write_all(&v).unwrap();
}

#[test]
fn test_keccak_proof() {
    let params_file = "params.keys";

    let mut params_file = OpenOptions::new().read(true).open(params_file).unwrap();
    let params = keccak_gadget::SetupParams::read(&mut params_file, false)
        .expect("couldn't deserialize keccak parameters file");

    let mut keccak = Keccak::v256();

    let mut rand_value = [0u8; 64];
    let mut rng = rand::thread_rng();
    rng.fill(&mut rand_value); // array fill

    keccak.update(&rand_value);

    let mut hash_source = [0u8; 32];
    keccak.finalize(&mut hash_source);

    let w = keccak_gadget::PrivateInput::new(rand_value.into());
    let x = keccak_gadget::PublicInput::new(hash_source.into());

    let proof = keccak_gadget::prove(&params, x, w).unwrap();
    assert!(keccak_gadget::verify(&params, x, proof));
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

    let params_file = "params.keys";

    let mut params_file = OpenOptions::new().read(true).open(params_file).unwrap();
    let params = keccak_gadget::SetupParams::read(&mut params_file, false)
        .expect("couldn't deserialize keccak parameters file");

    let secp = Secp256k1::new();
    {
        let s = SecretKey::from_str(
            "0000000000000000000000000000000000000000000000000000000000000001",
        )
        .unwrap();
        let public_key: PublicKey = PublicKey::from_secret_key(&secp, &s);

        let public_key_serial = public_key.serialize_uncompressed();

        let public_key_serial_type = &public_key_serial[0..1];
        // let public_key_serial_x = &public_key_serial[1..33];
        // let public_key_serial_y = &public_key_serial[33..65];

        assert_eq!(public_key_serial_type[0], 4u8); //Long, y is signed

        let preimage = (&public_key_serial[1..]).clone();
        assert_eq!(preimage.len(), 64);

        let mut hash = [0u8; 32];
        {
            let mut keccak = Keccak::v256();

            keccak.update(&preimage);

            keccak.finalize(&mut hash);

            let address = (&hash[12..32]).clone();

            let address_hex = hex::encode(address);
            assert_eq!(address_hex, "7e5f4552091a69125d5dfcb7b8c2659029395bdf");
        }

        let w = keccak_gadget::PrivateInput::new(preimage.into());
        let x = keccak_gadget::PublicInput::new(hash.into());

        let proof = keccak_gadget::prove(&params, x, w).unwrap();
        assert!(keccak_gadget::verify(&params, x, proof));

        let address = (&hash[12..32]).clone();

        let address_hex = hex::encode(address);
        assert_eq!(address_hex, "7e5f4552091a69125d5dfcb7b8c2659029395bdf");
    }

    {
        let s = SecretKey::from_str(
            "d6840b79c2eb1f5ff97a41590df3e04d7d4b0965073ff2a9fbb7ff003799dc71",
        )
        .unwrap();
        let public_key: PublicKey = PublicKey::from_secret_key(&secp, &s);

        let public_key_serial = public_key.serialize_uncompressed();

        let public_key_serial_type = &public_key_serial[0..1];
        // let public_key_serial_x = &public_key_serial[1..33];
        // let public_key_serial_y = &public_key_serial[33..65];

        assert_eq!(public_key_serial_type[0], 4u8); //Long, y is signed

        let preimage = (&public_key_serial[1..]).clone();
        assert_eq!(preimage.len(), 64);

        let mut hash = [0u8; 32];
        {
            let mut keccak = Keccak::v256();

            keccak.update(&preimage);

            keccak.finalize(&mut hash);

            let address = (&hash[12..32]).clone();

            let address_hex = hex::encode(address);

            let address_check =
                hex::decode("604a95C9165Bc95aE016a5299dd7d400dDDBEa9A").unwrap();
            let address_check_hex = hex::encode(address_check);

            assert_eq!(address_hex, address_check_hex);
        }

        let w = keccak_gadget::PrivateInput::new(preimage.into());
        let x = keccak_gadget::PublicInput::new(hash.into());

        let proof = keccak_gadget::prove(&params, x, w).unwrap();
        assert!(keccak_gadget::verify(&params, x, proof));

        let address = (&hash[12..32]).clone();

        let address_hex = hex::encode(address);

        let address_check = hex::decode("604a95C9165Bc95aE016a5299dd7d400dDDBEa9A").unwrap();
        let address_check_hex = hex::encode(address_check);

        assert_eq!(address_hex, address_check_hex);
    }

    {
        let s = SecretKey::from_str(
            "d3cc16948a02a91b9fcf83735653bf3dfd82c86543fdd1e9a828bd25e8a7b68d",
        )
        .unwrap();
        let public_key: PublicKey = PublicKey::from_secret_key(&secp, &s);

        let public_key_serial = public_key.serialize_uncompressed();

        let public_key_serial_type = &public_key_serial[0..1];
        // let public_key_serial_x = &public_key_serial[1..33];
        // let public_key_serial_y = &public_key_serial[33..65];

        assert_eq!(public_key_serial_type[0], 4u8); //Long, y is signed

        let preimage = (&public_key_serial[1..]).clone();
        assert_eq!(preimage.len(), 64);

        let mut hash = [0u8; 32];
        {
            let mut keccak = Keccak::v256();

            keccak.update(&preimage);

            keccak.finalize(&mut hash);

            let address = (&hash[12..32]).clone();

            let address_hex = hex::encode(address);

            let address_check =
                hex::decode("1c96099350f13D558464eC79B9bE4445AA0eF579").unwrap();
            let address_check_hex = hex::encode(address_check);

            assert_eq!(address_hex, address_check_hex);
        }

        let w = keccak_gadget::PrivateInput::new(preimage.into());
        let x = keccak_gadget::PublicInput::new(hash.into());

        let proof = keccak_gadget::prove(&params, x, w).unwrap();
        assert!(keccak_gadget::verify(&params, x, proof));

        let address = (&hash[12..32]).clone();

        let address_hex = hex::encode(address);

        let address_check = hex::decode("1c96099350f13D558464eC79B9bE4445AA0eF579").unwrap();
        let address_check_hex = hex::encode(address_check);

        assert_eq!(address_hex, address_check_hex);
    }
}
