#[macro_use]
extern crate serde_derive;

mod api;
#[cfg(all(feature = "std", not(feature = "python")))]
pub use api::generate;
#[cfg(all(not(feature = "std"), not(feature = "python")))]
pub use api::Seed;
#[cfg(not(feature = "python"))]
pub use api::{prove, verify};

mod gadget;
mod uint64;
#[cfg(not(feature = "python"))]
pub use gadget::{Proof, SetupParams};

mod types;
#[cfg(not(feature = "python"))]
pub use types::{Error, Login, H128, H256};

#[cfg(feature = "python")]
mod python;
#[cfg(feature = "python")]
pub use python::keccak;
