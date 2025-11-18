//! Taiko precompiles implementation

use alloy_primitives::Address;
use reth_evm::precompiles::PrecompilesMap;
use reth_revm::{
    context::Cfg,
    context_interface::ContextTr,
    handler::{EthPrecompiles, PrecompileProvider},
    interpreter::{InputsImpl, InterpreterResult},
    precompile::Precompiles,
    primitives::hardfork::SpecId,
};
use std::{boxed::Box, sync::OnceLock};

use crate::spec::TaikoSpecId;

pub mod l1sload;

/// Taiko precompile provider
#[derive(Debug, Clone)]
pub struct TaikoPrecompiles {
    /// Inner precompile provider is same as Ethereum's.
    inner: EthPrecompiles,
    /// Spec id of the precompile provider.
    spec: TaikoSpecId,
}

impl TaikoPrecompiles {
    /// Create a new precompile provider with the given TaikoSpecId.
    #[inline]
    pub fn new_with_spec(spec: TaikoSpecId) -> Self {
        let precompiles = match spec {
            TaikoSpecId::GENESIS => Precompiles::new(spec.into_eth_spec().into()),
            TaikoSpecId::ONTAKE => ontake(),
            TaikoSpecId::PACAYA => pacaya(),
            TaikoSpecId::SHASTA => shasta(),
        };

        Self { inner: EthPrecompiles { precompiles, spec: SpecId::default() }, spec }
    }

    /// Precompiles getter.
    #[inline]
    pub fn precompiles(&self) -> &'static Precompiles {
        self.inner.precompiles
    }
}

/// Returns precompiles for Ontake spec.
pub fn ontake() -> &'static Precompiles {
    static INSTANCE: OnceLock<Precompiles> = OnceLock::new();
    INSTANCE.get_or_init(|| {
        let precompiles = Precompiles::berlin().clone();
        precompiles
    })
}

/// Returns precompiles for Pacaya spec.
pub fn pacaya() -> &'static Precompiles {
    static INSTANCE: OnceLock<Precompiles> = OnceLock::new();
    INSTANCE.get_or_init(|| {
        let mut precompiles = ontake().clone();
        precompiles.extend([l1sload::L1SLOAD]);
        precompiles
    })
}

/// Returns precompiles for Shasta spec.
pub fn shasta() -> &'static Precompiles {
    static INSTANCE: OnceLock<Precompiles> = OnceLock::new();
    INSTANCE.get_or_init(|| {
        let precompiles = pacaya().clone();
        precompiles
    })
}

impl<CTX> PrecompileProvider<CTX> for TaikoPrecompiles
where
    CTX: ContextTr<Cfg: Cfg<Spec = TaikoSpecId>>,
{
    type Output = InterpreterResult;

    #[inline]
    fn set_spec(&mut self, spec: <CTX::Cfg as Cfg>::Spec) -> bool {
        if spec == self.spec {
            return false;
        }
        *self = Self::new_with_spec(spec);
        true
    }

    #[inline]
    fn run(
        &mut self,
        context: &mut CTX,
        address: &Address,
        inputs: &InputsImpl,
        is_static: bool,
        gas_limit: u64,
    ) -> Result<Option<Self::Output>, String> {
        self.inner.run(context, address, inputs, is_static, gas_limit)
    }

    #[inline]
    fn warm_addresses(&self) -> Box<impl Iterator<Item = Address>> {
        self.inner.warm_addresses()
    }

    #[inline]
    fn contains(&self, address: &Address) -> bool {
        self.inner.contains(address)
    }
}

impl Default for TaikoPrecompiles {
    fn default() -> Self {
        Self::new_with_spec(TaikoSpecId::default())
    }
}

impl Into<PrecompilesMap> for TaikoPrecompiles {
    fn into(self) -> PrecompilesMap {
        PrecompilesMap::from_static(&self.inner.precompiles)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloy_primitives::address;

    #[test]
    fn test_taiko_precompiles_creation() {
        // Test creation for all TaikoSpecId variants
        let specs = vec![
            TaikoSpecId::GENESIS,
            TaikoSpecId::ONTAKE,
            TaikoSpecId::PACAYA,
            TaikoSpecId::SHASTA,
        ];

        for spec in specs {
            let precompiles = TaikoPrecompiles::new_with_spec(spec);
            assert_eq!(precompiles.spec, spec);

            // Verify that precompiles are not empty
            let addresses: Vec<_> = precompiles.precompiles().addresses().collect();
            assert!(!addresses.is_empty(), "Precompiles should not be empty for spec {:?}", spec);

            // Verify basic Ethereum precompiles are present
            let ecrecover_addr = address!("0000000000000000000000000000000000000001");
            assert!(
                addresses.contains(&&ecrecover_addr),
                "ECRECOVER should be present for spec {:?}",
                spec
            );
        }
    }

    #[test]
    fn test_spec_specific_precompiles() {
        let genesis = TaikoPrecompiles::new_with_spec(TaikoSpecId::GENESIS);
        let ontake = TaikoPrecompiles::new_with_spec(TaikoSpecId::ONTAKE);
        let pacaya = TaikoPrecompiles::new_with_spec(TaikoSpecId::PACAYA);
        let shasta = TaikoPrecompiles::new_with_spec(TaikoSpecId::SHASTA);

        // All should have basic Ethereum precompiles
        let basic_precompiles = [
            address!("0000000000000000000000000000000000000001"), // ECRECOVER
            address!("0000000000000000000000000000000000000002"), // SHA256
            address!("0000000000000000000000000000000000000003"), // RIPEMD160
            address!("0000000000000000000000000000000000000004"), // DATACOPY
        ];

        for addr in basic_precompiles {
            let genesis_addrs: Vec<_> = genesis.precompiles().addresses().collect();
            let ontake_addrs: Vec<_> = ontake.precompiles().addresses().collect();
            let pacaya_addrs: Vec<_> = pacaya.precompiles().addresses().collect();
            let shasta_addrs: Vec<_> = shasta.precompiles().addresses().collect();

            assert!(
                genesis_addrs.contains(&&addr),
                "Genesis should contain basic precompile at {:?}",
                addr
            );
            assert!(
                ontake_addrs.contains(&&addr),
                "Ontake should contain basic precompile at {:?}",
                addr
            );
            assert!(
                pacaya_addrs.contains(&&addr),
                "Pacaya should contain basic precompile at {:?}",
                addr
            );
            assert!(
                shasta_addrs.contains(&&addr),
                "Shasta should contain basic precompile at {:?}",
                addr
            );
        }

        // Test that specs are properly hierarchical
        let genesis_count = genesis.precompiles().addresses().count();
        let ontake_count = ontake.precompiles().addresses().count();
        let pacaya_count = pacaya.precompiles().addresses().count();
        let shasta_count = shasta.precompiles().addresses().count();

        // Pacaya should have one more precompile than Ontake (L1SLOAD)
        assert_eq!(
            pacaya_count,
            ontake_count + 1,
            "Pacaya should have L1SLOAD precompile added to Ontake"
        );
        // Shasta should have the same as Pacaya (inherits from Pacaya)
        assert_eq!(shasta_count, pacaya_count, "Shasta inherits from Pacaya");

        // Genesis might be different if it uses a different base spec
        println!(
            "Precompile counts - Genesis: {}, Ontake: {}, Pacaya: {}, Shasta: {}",
            genesis_count, ontake_count, pacaya_count, shasta_count
        );

        // Test that Pacaya and Shasta contain the L1SLOAD precompile
        let l1sload_addr = alloy_primitives::address!("0000000000000000000000000000000000010001");
        let pacaya_addrs: Vec<_> = pacaya.precompiles().addresses().collect();
        let shasta_addrs: Vec<_> = shasta.precompiles().addresses().collect();
        let ontake_addrs: Vec<_> = ontake.precompiles().addresses().collect();

        assert!(pacaya_addrs.contains(&&l1sload_addr), "Pacaya should contain L1SLOAD precompile");
        assert!(shasta_addrs.contains(&&l1sload_addr), "Shasta should contain L1SLOAD precompile");
        assert!(
            !ontake_addrs.contains(&&l1sload_addr),
            "Ontake should NOT contain L1SLOAD precompile"
        );
    }

    #[test]
    fn test_default_implementation() {
        let default_precompiles = TaikoPrecompiles::default();
        let expected_spec = TaikoSpecId::default();

        assert_eq!(default_precompiles.spec, expected_spec);
        assert!(!default_precompiles.precompiles().addresses().collect::<Vec<_>>().is_empty());
    }

    #[test]
    fn test_precompiles_map_conversion() {
        let specs = vec![
            TaikoSpecId::GENESIS,
            TaikoSpecId::ONTAKE,
            TaikoSpecId::PACAYA,
            TaikoSpecId::SHASTA,
        ];

        for spec in specs {
            let taiko_precompiles = TaikoPrecompiles::new_with_spec(spec);
            let original_addresses: Vec<_> = taiko_precompiles.precompiles().addresses().collect();

            // Convert to PrecompilesMap
            let precompiles_map: PrecompilesMap = taiko_precompiles.into();
            let converted_addresses: Vec<_> = precompiles_map.addresses().collect();

            // Should have the same addresses
            assert_eq!(
                original_addresses.len(),
                converted_addresses.len(),
                "Address count should match after conversion for spec {:?}",
                spec
            );

            for addr in original_addresses {
                assert!(
                    converted_addresses.contains(&addr),
                    "Address {:?} should be present after conversion for spec {:?}",
                    addr,
                    spec
                );
            }
        }
    }

    #[test]
    fn test_lazy_static_initialization() {
        // Test that multiple calls to the same spec function return the same reference
        let ontake1 = ontake();
        let ontake2 = ontake();
        assert!(
            std::ptr::eq(ontake1, ontake2),
            "Ontake precompiles should be the same static reference"
        );

        let pacaya1 = pacaya();
        let pacaya2 = pacaya();
        assert!(
            std::ptr::eq(pacaya1, pacaya2),
            "Pacaya precompiles should be the same static reference"
        );

        let shasta1 = shasta();
        let shasta2 = shasta();
        assert!(
            std::ptr::eq(shasta1, shasta2),
            "Shasta precompiles should be the same static reference"
        );
    }

    #[test]
    fn test_precompiles_addresses() {
        let precompiles = TaikoPrecompiles::new_with_spec(TaikoSpecId::PACAYA);
        let addresses: Vec<_> = precompiles.precompiles().addresses().collect();

        // Should not be empty
        assert!(!addresses.is_empty(), "Precompiles addresses should not be empty");

        // Should contain basic Ethereum precompiles
        let expected_addresses = [
            address!("0000000000000000000000000000000000000001"), // ECRECOVER
            address!("0000000000000000000000000000000000000002"), // SHA256
            address!("0000000000000000000000000000000000000003"), // RIPEMD160
            address!("0000000000000000000000000000000000000004"), // DATACOPY
        ];

        for expected_addr in expected_addresses {
            assert!(
                addresses.contains(&&expected_addr),
                "Precompiles should contain address {:?}",
                expected_addr
            );
        }
    }

    #[test]
    fn test_clone_implementation() {
        let original = TaikoPrecompiles::new_with_spec(TaikoSpecId::PACAYA);
        let cloned = original.clone();

        assert_eq!(original.spec, cloned.spec);
        // Both should point to the same static precompiles reference
        assert!(std::ptr::eq(original.precompiles(), cloned.precompiles()));
    }

    #[test]
    fn test_debug_implementation() {
        let precompiles = TaikoPrecompiles::new_with_spec(TaikoSpecId::PACAYA);
        let debug_string = format!("{:?}", precompiles);

        // Should contain the struct name and spec
        assert!(debug_string.contains("TaikoPrecompiles"));
        assert!(debug_string.contains("PACAYA"));
    }

    #[test]
    fn test_spec_hierarchy() {
        // Test that the spec functions work correctly
        let ontake_precompiles = ontake();
        let pacaya_precompiles = pacaya();
        let shasta_precompiles = shasta();

        // Verify they return different instances but with proper inheritance
        assert!(!std::ptr::eq(ontake_precompiles, pacaya_precompiles));
        assert!(!std::ptr::eq(pacaya_precompiles, shasta_precompiles));

        // All should have at least the basic Ethereum precompiles
        let ontake_count = ontake_precompiles.addresses().count();
        let pacaya_count = pacaya_precompiles.addresses().count();
        let shasta_count = shasta_precompiles.addresses().count();

        assert!(ontake_count > 0, "Ontake should have precompiles");
        assert!(pacaya_count > 0, "Pacaya should have precompiles");
        assert!(shasta_count > 0, "Shasta should have precompiles");

        // Pacaya should have more precompiles than Ontake (adds L1SLOAD)
        assert_eq!(
            pacaya_count,
            ontake_count + 1,
            "Pacaya should have L1SLOAD added to Ontake precompiles"
        );
        // Shasta inherits from Pacaya, so should have the same count
        assert_eq!(shasta_count, pacaya_count, "Shasta inherits from Pacaya");

        // Test that L1SLOAD is present in Pacaya and Shasta but not Ontake
        let l1sload_addr = alloy_primitives::address!("0000000000000000000000000000000000010001");
        let ontake_addrs: Vec<_> = ontake_precompiles.addresses().collect();
        let pacaya_addrs: Vec<_> = pacaya_precompiles.addresses().collect();
        let shasta_addrs: Vec<_> = shasta_precompiles.addresses().collect();

        assert!(!ontake_addrs.contains(&&l1sload_addr), "Ontake should not have L1SLOAD");
        assert!(pacaya_addrs.contains(&&l1sload_addr), "Pacaya should have L1SLOAD");
        assert!(shasta_addrs.contains(&&l1sload_addr), "Shasta should have L1SLOAD");
    }

    #[test]
    fn test_factory_integration() {
        // Test that TaikoPrecompiles works with the factory pattern
        let specs =
            [TaikoSpecId::GENESIS, TaikoSpecId::ONTAKE, TaikoSpecId::PACAYA, TaikoSpecId::SHASTA];

        for spec in specs {
            let taiko_precompiles = TaikoPrecompiles::new_with_spec(spec);

            // Test conversion to PrecompilesMap (used in factory)
            let precompiles_map: PrecompilesMap = taiko_precompiles.into();

            // Verify the conversion maintains the precompiles
            let addresses: Vec<_> = precompiles_map.addresses().collect();
            assert!(
                !addresses.is_empty(),
                "Converted PrecompilesMap should not be empty for spec {:?}",
                spec
            );

            // Should contain basic precompiles
            let ecrecover = address!("0000000000000000000000000000000000000001");
            assert!(
                addresses.contains(&&ecrecover),
                "Should contain ECRECOVER after conversion for spec {:?}",
                spec
            );
        }
    }

    #[test]
    fn test_l1sload_precompile_integration() {
        // Test that L1SLOAD is properly integrated in Pacaya and Shasta specs
        let l1sload_addr = alloy_primitives::address!("0000000000000000000000000000000000010001");

        // Test with TaikoPrecompiles instances
        let ontake_precompiles = TaikoPrecompiles::new_with_spec(TaikoSpecId::ONTAKE);
        let pacaya_precompiles = TaikoPrecompiles::new_with_spec(TaikoSpecId::PACAYA);
        let shasta_precompiles = TaikoPrecompiles::new_with_spec(TaikoSpecId::SHASTA);

        let ontake_addrs: Vec<_> = ontake_precompiles.precompiles().addresses().collect();
        let pacaya_addrs: Vec<_> = pacaya_precompiles.precompiles().addresses().collect();
        let shasta_addrs: Vec<_> = shasta_precompiles.precompiles().addresses().collect();

        // L1SLOAD should only be in Pacaya and Shasta
        assert!(!ontake_addrs.contains(&&l1sload_addr), "Ontake should not contain L1SLOAD");
        assert!(pacaya_addrs.contains(&&l1sload_addr), "Pacaya should contain L1SLOAD");
        assert!(shasta_addrs.contains(&&l1sload_addr), "Shasta should contain L1SLOAD");

        // Verify counts are correct
        assert_eq!(
            pacaya_addrs.len(),
            ontake_addrs.len() + 1,
            "Pacaya should have one more precompile than Ontake"
        );
        assert_eq!(
            shasta_addrs.len(),
            pacaya_addrs.len(),
            "Shasta should have same number as Pacaya"
        );

        // Test that the L1SLOAD precompile from l1sload module is accessible
        assert_eq!(
            crate::precompiles::l1sload::L1SLOAD.address(),
            &l1sload_addr,
            "L1SLOAD constant should have correct address"
        );
    }
}
