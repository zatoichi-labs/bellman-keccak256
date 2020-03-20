#[macro_use]
extern crate serde_derive;

mod gadget;
pub use gadget::{
    ROUND_CONSTANTS,
    SetupParams, PublicInput, PrivateInput,
    generate, prove, verify,
    keccak_256_512,
};

mod types;
pub use types::{Error, Login, H128, H256};

mod uint64;
