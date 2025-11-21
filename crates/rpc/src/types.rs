//! Taiko RPC types configuration

use crate::transaction::TaikoTransactionRequest;
use alloy_rpc_types_eth::{Header, Transaction, TransactionReceipt};
use reth_ethereum_primitives::Receipt;
use reth_rpc_convert::RpcTypes;

/// Taiko RPC types configuration.
///
/// This defines the RPC type mappings used throughout the Taiko RPC layer,
/// following the same pattern as Optimism with custom transaction request types.
#[derive(Debug, Clone, Copy, Default)]
#[non_exhaustive]
//! Taiko RPC types configuration

use crate::transaction::TaikoTransactionRequest;
use alloy_rpc_types_eth::{Header, Transaction, TransactionReceipt};
use reth_ethereum_primitives::Receipt;
use reth_rpc_convert::RpcTypes;

/// Taiko RPC types configuration.
///
/// This defines the RPC type mappings used throughout the Taiko RPC layer,
/// following the same pattern as Optimism with custom transaction request types.
#[derive(Debug, Clone, Copy, Default)]
#[non_exhaustive]
pub struct TaikoRpcTypes;

impl RpcTypes for TaikoRpcTypes {
    type Header = Header;
    type Receipt = TransactionReceipt<Receipt>;
    type TransactionRequest = TaikoTransactionRequest;
    type TransactionResponse = Transaction;
}


impl RpcTypes for TaikoRpcTypes {
    type Header = Header;
    type Receipt = TransactionReceipt<Receipt>;
    type TransactionRequest = TaikoTransactionRequest;
    type TransactionResponse = Transaction;
}
