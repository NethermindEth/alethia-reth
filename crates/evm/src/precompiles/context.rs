//! Shared L1 precompile context — `(anchor_block_id, l1_max_anchor_block_id)`.
//!
//! Both [`super::l1sload`] and [`super::l1staticcall`] consume the same two globals to
//! decide whether a given `requested_block` is in the trusted `[l1_max_anchor − 256,
//! l1_max_anchor]` lookback window. Owning the context here (rather than in `l1sload`
//! as it lived historically) makes the shared dependency explicit and avoids the
//! awkward cross-precompile import of `l1sload::get_*` from `l1staticcall.rs`.
//!
//! **Threading invariant.** The same single-threaded contract that applies to the per-
//! precompile caches applies here: the host (raiko / sequencer) must drive these
//! getters/setters with one `(anchor, l1_max_anchor)` value at a time. The module-level
//! docs on `l1sload.rs` and `l1staticcall.rs` spell out the broader pattern.

use std::sync::{LazyLock, Mutex};

/// Current anchor block ID — sourced from the L2 anchor tx's `Checkpoint.blockNumber`
/// (`anchorV4` in Shasta / `anchorV4WithSignalSlots` in RealTime). Identical semantics
/// in both forks.
static CURRENT_ANCHOR_BLOCK_ID: LazyLock<Mutex<Option<u64>>> = LazyLock::new(|| Mutex::new(None));

/// Current L1 max-anchor block ID — the upper bound of the `[N − 256, N]` lookback
/// window. In Shasta this is the proposal's `originBlockNumber`; in RealTime it's the
/// proposal's `maxAnchorBlockNumber`. Both fields play the same structural role: an
/// on-chain-verified L1 block number that anchors the prover's trust window.
static CURRENT_L1_MAX_ANCHOR_BLOCK_ID: LazyLock<Mutex<Option<u64>>> =
    LazyLock::new(|| Mutex::new(None));

/// Set the current anchor block ID.
pub fn set_anchor_block_id(anchor_block_id: u64) {
    let mut ctx = CURRENT_ANCHOR_BLOCK_ID.lock().expect("CURRENT_ANCHOR_BLOCK_ID mutex poisoned");
    *ctx = Some(anchor_block_id);
}

/// Read the current anchor block ID.
pub fn get_anchor_block_id() -> Option<u64> {
    *CURRENT_ANCHOR_BLOCK_ID.lock().expect("CURRENT_ANCHOR_BLOCK_ID mutex poisoned")
}

/// Set the L1 max-anchor block ID.
pub fn set_l1_max_anchor_block_id(l1_max_anchor_block_id: u64) {
    let mut ctx = CURRENT_L1_MAX_ANCHOR_BLOCK_ID
        .lock()
        .expect("CURRENT_L1_MAX_ANCHOR_BLOCK_ID mutex poisoned");
    *ctx = Some(l1_max_anchor_block_id);
}

/// Read the current L1 max-anchor block ID.
pub fn get_l1_max_anchor_block_id() -> Option<u64> {
    *CURRENT_L1_MAX_ANCHOR_BLOCK_ID.lock().expect("CURRENT_L1_MAX_ANCHOR_BLOCK_ID mutex poisoned")
}

/// Clear both anchor context globals — used by `clear_l1_storage` / `clear_all_precompile_state`.
///
/// **Non-atomic by design.** The two globals are reset in sequence, releasing the first
/// mutex before acquiring the second. Under the documented single-threaded invariant
/// (host driver + raiko's `acquire_l1_precompile_lock`), no concurrent reader can observe
/// the intermediate `(None, Some(_))` state — the lock that protects the entire
/// `prepare → execute → finalize` cycle is held by the same caller that invokes this
/// reset. Combining both fields into a single `Mutex<(Option<u64>, Option<u64>)>` would
/// also require lock-stepping every setter and reader (`set_anchor_block_id`,
/// `set_l1_max_anchor_block_id`, `get_*`), so the same atomicity concern would apply at
/// every call site, not just the clear. If the single-threaded contract is ever relaxed,
/// revisit this as part of the same refactor.
pub fn clear_anchor_context() {
    *CURRENT_ANCHOR_BLOCK_ID.lock().expect("CURRENT_ANCHOR_BLOCK_ID mutex poisoned") = None;
    *CURRENT_L1_MAX_ANCHOR_BLOCK_ID
        .lock()
        .expect("CURRENT_L1_MAX_ANCHOR_BLOCK_ID mutex poisoned") = None;
}
