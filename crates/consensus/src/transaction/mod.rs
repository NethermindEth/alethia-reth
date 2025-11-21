//! Transaction types for Taiko.

mod tx_type;

mod envelope;
pub use envelope::{TaikoTxEnvelope, TaikoTxType};

#[cfg(all(feature = "serde", feature = "serde-bincode-compat"))]
pub use envelope::serde_bincode_compat as envelope_serde_bincode_compat;

mod typed;
pub use typed::TaikoTypedTransaction;

mod pooled;
pub use pooled::TaikoPooledTransaction;

#[cfg(feature = "reth-codec")]
mod compress;

/// Bincode-compatible serde implementations for transaction types.
#[cfg(all(feature = "serde", feature = "serde-bincode-compat"))]
pub mod serde_bincode_compat {
    pub use super::envelope::serde_bincode_compat::*;
}
