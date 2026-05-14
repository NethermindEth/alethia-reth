/// Shared anchor / l1-max-anchor context for the L1 precompiles.
pub mod context;
/// L1SLOAD precompile implementation (RIP-7728).
pub mod l1sload;
/// L1STATICCALL precompile implementation.
pub mod l1staticcall;

use reth_evm::precompiles::{DynPrecompile, PrecompilesMap};
use reth_revm::precompile::{PrecompileSpecId, Precompiles, u64_to_address};

use crate::spec::TaikoSpecId;

/// Address of the L1SLOAD precompile (RIP-7728).
pub const L1SLOAD_PRECOMPILE_ADDRESS: u64 = 0x10001;
/// Address of the L1STATICCALL precompile.
pub const L1STATICCALL_PRECOMPILE_ADDRESS: u64 = 0x10002;

/// Builds a [`PrecompilesMap`] that includes the standard Ethereum precompiles plus, where the
/// active Taiko hardfork enables them, the L1SLOAD precompile at `0x10001` and the L1STATICCALL
/// precompile at `0x10002`.
///
/// **Hardfork gating.** L1SLOAD (RIP-7728) registers from [`TaikoSpecId::SHASTA`] onward.
/// L1STATICCALL registers from [`TaikoSpecId::REALTIME`] onward. On chains where these forks are
/// `ForkCondition::Never` (e.g. Taiko Mainnet at the time of writing — see
/// `crates/chainspec/src/hardfork.rs::TAIKO_MAINNET_HARDFORKS`), the addresses are left
/// unregistered, so a call to `0x10001` or `0x10002` lands on the standard EVM "no code at
/// address" path instead of returning an internal "L1SLOAD/L1STATICCALL context unset"
/// precompile error.
pub fn taiko_precompiles_map(spec_id: PrecompileSpecId, taiko_spec: TaikoSpecId) -> PrecompilesMap {
    let mut map = PrecompilesMap::from_static(Precompiles::new(spec_id));
    if taiko_spec.is_enabled_in(TaikoSpecId::SHASTA) {
        let l1sload_addr = u64_to_address(L1SLOAD_PRECOMPILE_ADDRESS);
        let l1sload_dyn: DynPrecompile = (l1sload::l1sload_run as fn(&[u8], u64) -> _).into();
        map.extend_precompiles([(l1sload_addr, l1sload_dyn)]);
    }
    if taiko_spec.is_enabled_in(TaikoSpecId::REALTIME) {
        let l1staticcall_addr = u64_to_address(L1STATICCALL_PRECOMPILE_ADDRESS);
        let l1staticcall_dyn: DynPrecompile =
            (l1staticcall::l1staticcall_run as fn(&[u8], u64) -> _).into();
        map.extend_precompiles([(l1staticcall_addr, l1staticcall_dyn)]);
    }
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

#[cfg(test)]
mod tests {
    use super::*;
    use alloy_primitives::Address;

    fn precompile_spec_id() -> PrecompileSpecId {
        PrecompileSpecId::from_spec_id(TaikoSpecId::SHASTA.into())
    }

    fn map_contains(map: &PrecompilesMap, addr_u64: u64) -> bool {
        let needle = u64_to_address(addr_u64);
        map.addresses().any(|a: &Address| *a == needle)
    }

    #[test]
    fn pacaya_does_not_register_l1_precompiles() {
        let map = taiko_precompiles_map(precompile_spec_id(), TaikoSpecId::PACAYA);
        assert!(
            !map_contains(&map, L1SLOAD_PRECOMPILE_ADDRESS),
            "L1SLOAD must not be registered before Shasta"
        );
        assert!(
            !map_contains(&map, L1STATICCALL_PRECOMPILE_ADDRESS),
            "L1STATICCALL must not be registered before RealTime"
        );
    }

    #[test]
    fn shasta_registers_l1sload_only() {
        let map = taiko_precompiles_map(precompile_spec_id(), TaikoSpecId::SHASTA);
        assert!(
            map_contains(&map, L1SLOAD_PRECOMPILE_ADDRESS),
            "L1SLOAD must be registered from Shasta onward"
        );
        assert!(
            !map_contains(&map, L1STATICCALL_PRECOMPILE_ADDRESS),
            "L1STATICCALL must not be registered until RealTime"
        );
    }

    #[test]
    fn realtime_registers_both_l1_precompiles() {
        let map = taiko_precompiles_map(precompile_spec_id(), TaikoSpecId::REALTIME);
        assert!(
            map_contains(&map, L1SLOAD_PRECOMPILE_ADDRESS),
            "L1SLOAD must be registered from Shasta onward"
        );
        assert!(
            map_contains(&map, L1STATICCALL_PRECOMPILE_ADDRESS),
            "L1STATICCALL must be registered from RealTime onward"
        );
    }

    #[test]
    fn pre_shasta_specs_skip_both_precompiles() {
        for spec in [TaikoSpecId::GENESIS, TaikoSpecId::ONTAKE, TaikoSpecId::PACAYA] {
            let map = taiko_precompiles_map(precompile_spec_id(), spec);
            assert!(
                !map_contains(&map, L1SLOAD_PRECOMPILE_ADDRESS),
                "L1SLOAD must not be registered at {spec:?}"
            );
            assert!(
                !map_contains(&map, L1STATICCALL_PRECOMPILE_ADDRESS),
                "L1STATICCALL must not be registered at {spec:?}"
            );
        }
    }
}
