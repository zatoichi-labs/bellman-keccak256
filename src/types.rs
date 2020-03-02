use core::convert::TryFrom;
use core::slice::Iter;

use bellman::SynthesisError;
use std::io::Error as IoError;
use tiny_keccak::Hasher;
use tiny_keccak::Keccak;

#[derive(Debug)]
pub enum Error {
    Synthesis(SynthesisError),
    Io(IoError),
    /// Expected size, Actual size
    Size((usize, usize)),
}

#[derive(Deserialize, Serialize, Clone, Copy, Debug)]
pub struct H128([u8; 16]);
#[derive(Deserialize, Serialize, Clone, Copy, Debug)]
pub struct H256([u8; 32]);
#[derive(Deserialize, Serialize, Clone, Debug)]
pub struct H512(Vec<u8>);

impl H128 {
    pub fn from(array: [u8; 16]) -> Self {
        Self(array)
    }

    pub fn iter(&self) -> Iter<u8> {
        self.0.iter()
    }

    pub fn to_vec(&self) -> Vec<u8> {
        self.0.to_vec()
    }

    pub fn from_slice(bytes: &[u8]) -> Result<Self, Error> {
        let mut array = [0u8; 16];
        if array.len() != bytes.len() {
            return Err(Error::Size((array.len(), bytes.len())));
        }
        array.copy_from_slice(bytes);
        Ok(Self(array))
    }
}

impl Into<Vec<u8>> for H128 {
    fn into(self) -> Vec<u8> {
        self.to_vec()
    }
}

impl TryFrom<Vec<u8>> for H128 {
    type Error = Error;

    fn try_from(v: Vec<u8>) -> Result<Self, Error> {
        Self::from_slice(&v)
    }
}

impl AsRef<[u8]> for H128 {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl H256 {
    pub fn zero() -> Self {
        Self([0u8; 32])
    }
    pub fn from(array: [u8; 32]) -> Self {
        Self(array)
    }

    #[cfg(not(feature = "python"))]
    pub fn iter(&self) -> Iter<u8> {
        self.0.iter()
    }

    pub fn to_vec(&self) -> Vec<u8> {
        self.0.to_vec()
    }

    pub fn from_slice(bytes: &[u8]) -> Result<Self, Error> {
        let mut array = [0u8; 32];
        if array.len() != bytes.len() {
            return Err(Error::Size((array.len(), bytes.len())));
        }
        array.copy_from_slice(bytes);
        Ok(Self(array))
    }
}

impl Into<Vec<u8>> for H256 {
    fn into(self) -> Vec<u8> {
        self.to_vec()
    }
}

impl TryFrom<Vec<u8>> for H256 {
    type Error = Error;

    fn try_from(v: Vec<u8>) -> Result<Self, Error> {
        Self::from_slice(&v)
    }
}

impl AsRef<[u8]> for H256 {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl From<[u8; 32]> for H256 {
    fn from(array: [u8; 32]) -> Self {
        Self::from(array)
    }
}

impl H512 {
    pub fn zero() -> Self {
        Self([0u8; 64].to_vec())
    }
    pub fn from(array: [u8; 64]) -> Self {
        Self(array.to_vec())
    }

    #[cfg(not(feature = "python"))]
    pub fn iter(&self) -> Iter<u8> {
        self.0.iter()
    }

    pub fn to_vec(&self) -> Vec<u8> {
        self.0.to_vec()
    }

    pub fn from_slice(bytes: &[u8]) -> Result<Self, Error> {
        let mut array = [0u8; 64];
        if array.len() != bytes.len() {
            return Err(Error::Size((array.len(), bytes.len())));
        }
        array.copy_from_slice(bytes);
        Ok(Self(array.to_vec()))
    }
}

impl Into<Vec<u8>> for H512 {
    fn into(self) -> Vec<u8> {
        self.to_vec()
    }
}

impl TryFrom<Vec<u8>> for H512 {
    type Error = Error;

    fn try_from(v: Vec<u8>) -> Result<Self, Error> {
        Self::from_slice(&v)
    }
}

impl AsRef<[u8]> for H512 {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl From<[u8; 64]> for H512 {
    fn from(array: [u8; 64]) -> Self {
        Self::from(array)
    }
}

#[derive(Deserialize, Serialize, Clone, Copy, Debug)]
pub struct Login {
    pub hash: H256,
}

impl Login {
    pub fn new(hash: H256) -> Self {
        Self { hash }
    }
    pub fn new_hash(preimage_left: H256, preimage_right: H256) -> Self {
        let mut keccak = Keccak::v256();
        let mut hash = [0u8; 32];

        keccak.update(&preimage_left.0);
        keccak.update(&preimage_right.0);
        keccak.finalize(&mut hash);

        Self {
            hash: H256::from(hash),
        }
    }

    pub fn as_vec(&self) -> Vec<u8> {
        self.hash.to_vec()
    }
}

#[derive(Deserialize, Serialize, Clone, Debug)]
pub struct Credentials {
    pub preimage: H512,
}

impl Credentials {
    pub fn new(preimage: &[u8; 64]) -> Result<Self, Error> {
        Ok(Self {
            preimage: H512::from(*preimage),
        })
    }
    pub fn new_raw(preimage: H512) -> Self {
        Self { preimage: preimage }
    }

    pub fn as_vec(&self) -> Vec<u8> {
        let serialized_data = self.preimage.to_vec();
        serialized_data
    }
}
