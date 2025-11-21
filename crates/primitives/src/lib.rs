use alethia_reth_consensus::transaction::TaikoTxEnvelope;
use reth_ethereum::Receipt;

pub mod engine;
pub mod payload;

/// Taiko-specific block type.
pub type TaikoBlock = alloy_consensus::Block<TaikoTxEnvelope>;

/// Taiko-specific block body type.
pub type TaikoBlockBody = <TaikoBlock as reth_primitives_traits::Block>::Body;

/// Primitive types for Taiko Node.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TaikoPrimitives;

impl reth_primitives_traits::NodePrimitives for TaikoPrimitives {
    type Block = TaikoBlock;
    type BlockHeader = alloy_consensus::Header;
    type BlockBody = TaikoBlockBody;
    type SignedTx = TaikoTxEnvelope;
    type Receipt = Receipt;
}
/// Bincode-compatible serde implementations.
#[cfg(feature = "serde-bincode-compat")]
pub mod serde_bincode_compat {
    pub use alethia_reth_consensus::transaction::serde_bincode_compat::*;
}
