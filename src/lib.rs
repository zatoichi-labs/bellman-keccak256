#[macro_use]
extern crate serde_derive;

mod gadget;
mod uint64;
pub use gadget::{Proof, SetupParams};

mod types;
pub use types::{Error, Login, H128, H256};
