/// Shared anchor / l1-max-anchor context for the L1 precompiles.
pub mod context;
/// L1SLOAD precompile implementation (RIP-7728).
pub mod l1sload;
/// L1STATICCALL precompile implementation.
pub mod l1staticcall;

use reth_evm::precompiles::{DynPrecompile, PrecompilesMap};
use reth_revm::precompile::{PrecompileSpecId, Precompiles, u64_to_address};

/// Builds a [`PrecompilesMap`] that includes the standard Ethereum precompiles
/// plus the Taiko L1SLOAD precompile at address `0x10001` and L1STATICCALL at `0x10002`.
pub fn taiko_precompiles_map(spec_id: PrecompileSpecId) -> PrecompilesMap {
    let mut map = PrecompilesMap::from_static(Precompiles::new(spec_id));
    let l1sload_addr = u64_to_address(0x10001);
    let l1sload_dyn: DynPrecompile = (l1sload::l1sload_run as fn(&[u8], u64) -> _).into();
    let l1staticcall_addr = u64_to_address(0x10002);
    let l1staticcall_dyn: DynPrecompile =
        (l1staticcall::l1staticcall_run as fn(&[u8], u64) -> _).into();
    map.extend_precompiles([(l1sload_addr, l1sload_dyn), (l1staticcall_addr, l1staticcall_dyn)]);
    map
}

/// One-shot reset of every L1 precompile global: caches, anchor context, RPC fetchers,
/// and the served-call lists, for both L1SLOAD and L1STATICCALL.
///
/// Use this at the top of every new block / batch iteration. The historical
/// [`l1sload::clear_l1_storage`] only sweeps the L1SLOAD half — callers that relied on
/// it alone would silently inherit stale L1STATICCALL cache entries from the previous
/// block. This wrapper is the safe default.
pub fn clear_all_precompile_state() {
    l1sload::clear_l1_storage();
    l1staticcall::clear_l1_staticcall_cache();
    l1staticcall::clear_l1_staticcall_rpc_fetcher();
    l1staticcall::clear_l1_staticcall_rpc_served_calls();
}
