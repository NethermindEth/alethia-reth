use std::{
    collections::HashMap,
    sync::{LazyLock, Mutex},
};

use alloy_primitives::{Address, B256, Bytes};
use reth_revm::precompile::{
    Precompile, PrecompileError, PrecompileId, PrecompileOutput, PrecompileResult, u64_to_address,
};

pub const L1SLOAD: Precompile = Precompile::new(
    PrecompileId::Custom(std::borrow::Cow::Borrowed("L1SLOAD")),
    u64_to_address(0x10001),
    l1sload_run,
);

/// Gas constants for L1SLOAD precompile
pub const L1SLOAD_FIXED_GAS: u64 = 2000;
pub const L1SLOAD_PER_LOAD_GAS: u64 = 2000;

/// Expected input length: 20 bytes (address) + 32 bytes (storage key) = 52 bytes
/// Note: Block number is no longer part of input; it's obtained from the anchor block context
pub const EXPECTED_INPUT_LENGTH: usize = 52;

/// In-memory cache for L1 storage values
/// Key: (contract_address, storage_key) -> Value: storage_value
/// The anchor block context is managed separately via CURRENT_ANCHOR_BLOCK_ID
static L1_STORAGE_CACHE: LazyLock<Mutex<HashMap<(Address, B256), B256>>> =
    LazyLock::new(|| Mutex::new(HashMap::new()));

/// Current anchor block ID context for L1SLOAD operations
/// This is set before block execution and used by the precompile to determine which L1 block
/// to query
static CURRENT_ANCHOR_BLOCK_ID: LazyLock<Mutex<Option<B256>>> = LazyLock::new(|| Mutex::new(None));

/// Set the current anchor block ID context
/// This must be called before executing any block that uses L1SLOAD
pub fn set_anchor_block_id(anchor_block_id: B256) {
    if let Ok(mut ctx) = CURRENT_ANCHOR_BLOCK_ID.lock() {
        *ctx = Some(anchor_block_id);
    }
}

/// Clear the anchor block ID context
pub fn clear_anchor_block_id() {
    if let Ok(mut ctx) = CURRENT_ANCHOR_BLOCK_ID.lock() {
        *ctx = None;
    }
}

/// Get the current anchor block ID
fn get_anchor_block_id() -> Option<B256> {
    if let Ok(ctx) = CURRENT_ANCHOR_BLOCK_ID.lock() { *ctx } else { None }
}

/// Set a value in the L1 storage cache
pub fn set_l1_storage_value(contract_address: Address, storage_key: B256, value: B256) {
    if let Ok(mut cache) = L1_STORAGE_CACHE.lock() {
        cache.insert((contract_address, storage_key), value);
    }
}

/// Clear L1 storage cache and anchor block ID context
pub fn clear_l1_storage() {
    if let Ok(mut cache) = L1_STORAGE_CACHE.lock() {
        cache.clear();
    }
    clear_anchor_block_id();
}

/// Get a value from the L1 storage cache
/// Uses the current anchor block ID context
fn get_l1_storage_value(contract_address: Address, storage_key: B256) -> Option<B256> {
    if let Ok(cache) = L1_STORAGE_CACHE.lock() {
        cache.get(&(contract_address, storage_key)).copied()
    } else {
        None
    }
}

/// L1SLOAD precompile - read storage values from L1 contracts (RIP-7728).
///
/// The input to the L1SLOAD precompile consists of:
/// - [0: 19] (20 bytes)  - address: The L1 contract address
/// - [20: 51] (32 bytes) - storageKey: The storage key to read
///
/// Output: Storage value (32 bytes)
///
/// Note: The L1 block number is implicitly determined by the current block's anchor block ID,
/// which must be set via set_anchor_block_id() before block execution.
pub fn l1sload_run(input: &[u8], gas_limit: u64) -> PrecompileResult {
    // Check gas limit
    let gas_used = L1SLOAD_FIXED_GAS + L1SLOAD_PER_LOAD_GAS;
    if gas_used > gas_limit {
        return Err(PrecompileError::OutOfGas);
    }

    // Validate input length
    if input.len() != EXPECTED_INPUT_LENGTH {
        return Err(PrecompileError::Other("Invalid input length".into()));
    }

    // Parse input parameters
    let contract_address = Address::from_slice(&input[0..20]);
    let storage_key = B256::from_slice(&input[20..52]);

    // Verify anchor block ID is set
    get_anchor_block_id()
        .ok_or_else(|| PrecompileError::Other("Anchor block ID not set".into()))?;

    // Get cached L1 storage value
    let storage_value = get_l1_storage_value(contract_address, storage_key);

    match storage_value {
        Some(value) => {
            // Convert storage value to output bytes (32 bytes)
            let mut output = [0u8; 32];
            output.copy_from_slice(value.as_slice());
            Ok(PrecompileOutput::new(gas_used, Bytes::from(output)))
        }
        None => {
            // Return error if no cached data found
            Err(PrecompileError::Other("L1 storage value not found in cache".into()))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serial_test::serial;

    const TEST_ADDRESS: [u8; 20] = [1u8; 20];
    const TEST_STORAGE_KEY: [u8; 32] = [2u8; 32];
    const TEST_BLOCK_NUMBER: [u8; 32] = [3u8; 32];
    const TEST_STORAGE_VALUE: [u8; 32] = [5u8; 32];
    const SUFFICIENT_GAS: u64 = L1SLOAD_FIXED_GAS + L1SLOAD_PER_LOAD_GAS;
    const INSUFFICIENT_GAS: u64 = SUFFICIENT_GAS - 1;

    /// Helper function to create test input with predefined test data
    fn create_test_input() -> Vec<u8> {
        let mut input = vec![0u8; EXPECTED_INPUT_LENGTH];
        input[0..20].copy_from_slice(&TEST_ADDRESS);
        input[20..52].copy_from_slice(&TEST_STORAGE_KEY);
        input
    }

    /// Helper function to setup storage cache with test data
    fn setup_test_storage() -> (Address, B256, B256, B256) {
        let address = Address::from(TEST_ADDRESS);
        let key = B256::from(TEST_STORAGE_KEY);
        let block = B256::from(TEST_BLOCK_NUMBER);
        let value = B256::from(TEST_STORAGE_VALUE);

        // Set anchor block ID context
        set_anchor_block_id(block);
        // Set cache value
        set_l1_storage_value(address, key, value);
        (address, key, block, value)
    }

    #[test]
    #[serial]
    fn test_l1sload_rejects_invalid_input_lengths() {
        clear_l1_storage();
        set_anchor_block_id(B256::from(TEST_BLOCK_NUMBER));

        // Test input too short
        let short_input = Bytes::from(vec![0u8; 40]);
        let result = l1sload_run(&short_input, SUFFICIENT_GAS);
        assert!(result.is_err(), "Should reject too short input");

        // Test input too long
        let long_input = Bytes::from(vec![0u8; 84]);
        let result = l1sload_run(&long_input, SUFFICIENT_GAS);
        assert!(result.is_err(), "Should reject too long input");
    }

    #[test]
    #[serial]
    fn test_l1sload_fails_without_anchor_block_id() {
        clear_l1_storage();

        let input = create_test_input();
        let result = l1sload_run(&Bytes::from(input), SUFFICIENT_GAS);

        assert!(result.is_err(), "Should fail when anchor block ID is not set");
    }

    #[test]
    #[serial]
    fn test_l1sload_fails_without_cached_storage() {
        clear_l1_storage();
        set_anchor_block_id(B256::from(TEST_BLOCK_NUMBER));

        let input = create_test_input();
        let result = l1sload_run(&Bytes::from(input), SUFFICIENT_GAS);

        assert!(result.is_err(), "Should fail when storage value is not cached");
    }

    #[test]
    #[serial]
    fn test_l1sload_succeeds_with_cached_storage() {
        clear_l1_storage();

        // Setup test data and cache
        let (_, _, _, expected_value) = setup_test_storage();
        let input = create_test_input();

        let result = l1sload_run(&Bytes::from(input), SUFFICIENT_GAS);
        assert!(
            result.is_ok(),
            "Should succeed when storage value is cached. Error: {:?}",
            result.err()
        );

        let output = result.unwrap();

        // Verify gas usage
        let expected_gas = L1SLOAD_FIXED_GAS + L1SLOAD_PER_LOAD_GAS;
        assert_eq!(output.gas_used, expected_gas, "Gas usage should be fixed cost + per-load cost");

        // Verify output length
        assert_eq!(output.bytes.len(), 32, "Output should be exactly 32 bytes");

        // Verify output content matches stored value
        assert_eq!(
            output.bytes.as_ref(),
            &expected_value.0,
            "Output should match the cached storage value"
        );
    }

    #[test]
    #[serial]
    fn test_l1sload_fails_with_insufficient_gas() {
        clear_l1_storage();
        set_anchor_block_id(B256::from(TEST_BLOCK_NUMBER));

        let input = Bytes::from(vec![0u8; EXPECTED_INPUT_LENGTH]);
        let result = l1sload_run(&input, INSUFFICIENT_GAS);

        assert!(result.is_err(), "Should fail when gas limit is insufficient");
    }

    #[test]
    #[serial]
    fn test_storage_cache_operations() {
        clear_l1_storage();

        let address = Address::from(TEST_ADDRESS);
        let key = B256::from(TEST_STORAGE_KEY);
        let value = B256::from(TEST_STORAGE_VALUE);

        // Verify cache is initially empty
        assert!(get_l1_storage_value(address, key).is_none(), "Cache should be empty initially");

        set_l1_storage_value(address, key, value);
        assert_eq!(
            get_l1_storage_value(address, key),
            Some(value),
            "Should retrieve the cached value"
        );
    }

    #[test]
    #[serial]
    fn test_anchor_block_id_context() {
        clear_anchor_block_id();

        // Verify context is initially empty
        assert!(get_anchor_block_id().is_none(), "Context should be empty initially");

        let block = B256::from(TEST_BLOCK_NUMBER);
        set_anchor_block_id(block);
        assert_eq!(get_anchor_block_id(), Some(block), "Should retrieve the set anchor block ID");

        clear_anchor_block_id();
        assert!(get_anchor_block_id().is_none(), "Context should be cleared");
    }

    #[test]
    #[serial]
    fn test_cache_key_uniqueness() {
        clear_l1_storage();

        let address1 = Address::from([1u8; 20]);
        let address2 = Address::from([2u8; 20]);
        let key1 = B256::from([1u8; 32]);
        let key2 = B256::from([2u8; 32]);
        let value1 = B256::from([10u8; 32]);
        let value2 = B256::from([20u8; 32]);

        // Set different values for different cache keys (address, key)
        set_l1_storage_value(address1, key1, value1);
        set_l1_storage_value(address2, key2, value2);

        // Verify each key returns its correct value
        assert_eq!(get_l1_storage_value(address1, key1), Some(value1));
        assert_eq!(get_l1_storage_value(address2, key2), Some(value2));

        // Verify non-existent combinations return None
        assert!(get_l1_storage_value(address1, key2).is_none());
        assert!(get_l1_storage_value(address2, key1).is_none());
    }
}
