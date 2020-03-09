#[macro_use]
extern crate serde_derive;

mod api;
#[cfg(not(feature = "std"))]
pub use api::generate;
#[cfg(not(feature = "std"))]
pub use api::Seed;
pub use api::{prove, verify};

mod gadget;
mod uint64;
pub use gadget::{Proof, SetupParams};

mod types;
pub use types::{Error, Login, H128, H256};
