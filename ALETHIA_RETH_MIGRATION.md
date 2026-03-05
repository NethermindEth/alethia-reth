# Alethia-Reth: RealTime Fork Migration Guide

> Step-by-step specification of every change required in alethia-reth to support the RealTime
> fork alongside the existing Shasta fork. All RealTime code is **additive**; no existing Shasta
> code is removed or modified.
>
> Companion documents:
> - [PROTOCOL_MIGRATION_REAL_TIME_FORK.md](PROTOCOL_MIGRATION_REAL_TIME_FORK.md) — on-chain contract changes
> - [PROVING_MIGRATION.md](PROVING_MIGRATION.md) — proving pipeline changes

---

## Table of Contents

1. [Overview of Execution-Layer Impact](#1-overview-of-execution-layer-impact)
2. [Step 1 — Hardfork Registration (`crates/chainspec`)](#step-1--hardfork-registration-crateschainspec)
3. [Step 2 — TaikoSpecId Extension (`crates/evm`)](#step-2--taikospecid-extension-cratesevm)
4. [Step 3 — Fork Detection in Block Config (`crates/block`)](#step-3--fork-detection-in-block-config-cratesblock)
5. [Step 4 — New Anchor Function (`crates/consensus`)](#step-4--new-anchor-function-cratesconsensus)
6. [Step 5 — Anchor Validation Logic (`crates/consensus`)](#step-5--anchor-validation-logic-cratesconsensus)
7. [Step 6 — Signal Slot Relay in EVM Handler (`crates/evm`)](#step-6--signal-slot-relay-in-evm-handler-cratesevm)
8. [Step 7 — Extra Data Format (`crates/primitives`)](#step-7--extra-data-format-cratesprimtives)
9. [Step 8 — Payload Attributes Extension (`crates/primitives`)](#step-8--payload-attributes-extension-cratesprimitives)
10. [Step 9 — Payload Builder Updates (`crates/payload`)](#step-9--payload-builder-updates-cratespayload)
11. [Step 10 — Block Executor Updates (`crates/block`)](#step-10--block-executor-updates-cratesblock)
12. [Step 11 — Database Model Updates (`crates/db`)](#step-11--database-model-updates-cratesdb)
13. [Step 12 — Network Hardfork Schedules](#step-12--network-hardfork-schedules)
14. [Step 13 — Tests](#step-13--tests)
15. [Cross-Cutting Concerns](#cross-cutting-concerns)
16. [What Does NOT Change](#what-does-not-change)

---

## 1. Overview of Execution-Layer Impact

The RealTime fork changes the L1 inbox from a two-phase (propose + prove) model to an
atomic single-phase model. For the **execution layer** (alethia-reth), the visible differences
are:

| Concern | Shasta | RealTime |
|---------|--------|----------|
| Anchor function | `anchorV4(Checkpoint)` | `anchorV4WithSignalSlots(Checkpoint, bytes32[])` |
| Anchor gas limit | 1,000,000 | 1,000,000 (unchanged) |
| Signal slot relay | No | Yes — L2 `Anchor.sol` calls `setSignalsReceived()` internally |
| Anchor linkage validation | **Prover-only** | **Prover-only** (unchanged) |
| Extra data byte 0 | `basefeeSharingPctg` | `basefeeSharingPctg` (unchanged) |
| Extra data bytes 1–6 | Proposal ID (sequential) | No longer meaningful; can be zero |
| Forced inclusions | Possible (`is_forced_inclusion=true`) | Never (`is_forced_inclusion` always false) |
| Fee sharing logic | EVM handler splits base fee | Unchanged |
| Base fee formula | EIP-4396 | Unchanged |

The execution layer does **not** handle proof verification, commitment hash construction,
anchor linkage cross-referencing, signal slot hash verification, or the `ProposedAndProved`
event — those are prover-layer concerns. Reth's anchor validation for every fork (including
Shasta today) is limited to: **selector, value=0, gas limit, tip=0, sender=GOLDEN_TOUCH**.
RealTime follows the same pattern — only the selector constant changes.

---

## Step 1 — Hardfork Registration (`crates/chainspec`)

### 1.1 Add `RealTime` to `TaikoHardfork` enum

**File:** [crates/chainspec/src/hardfork.rs](crates/chainspec/src/hardfork.rs)

Add `RealTime` as the next Taiko hardfork after `Shasta`:

```rust
hardfork!(
    TaikoHardfork {
        Ontake,
        Pacaya,
        Shasta,
        RealTime,   // NEW
    }
);
```

### 1.2 Add helper method to `TaikoHardforks` trait

In the same file, extend the trait with a `is_realtime_active()` method:

```rust
pub trait TaikoHardforks: EthereumHardforks {
    // ... existing methods unchanged ...

    /// Checks if the `RealTime` hardfork is active at the given timestamp.
    ///
    /// Like Shasta, RealTime is timestamp-gated only (London is active from genesis).
    fn is_realtime_active(&self, timestamp: u64) -> bool {
        self.taiko_fork_activation(TaikoHardfork::RealTime).active_at_timestamp(timestamp)
    }
}
```

### 1.3 Add `TaikoExecutorSpec::is_realtime_active()`

**File:** [crates/chainspec/src/spec.rs](crates/chainspec/src/spec.rs)

Extend `TaikoExecutorSpec` with the RealTime activation check:

```rust
pub trait TaikoExecutorSpec: EthExecutorSpec {
    // ... existing methods unchanged ...

    /// Checks if the `RealTime` hardfork is active at the given timestamp.
    fn is_realtime_active(&self, timestamp: u64) -> bool {
        self.taiko_fork_activation(TaikoHardfork::RealTime).active_at_timestamp(timestamp)
    }
}
```

The blanket impl on `TaikoChainSpec` already satisfies this via `taiko_fork_activation()`.

### 1.4 Network activation schedules (placeholder)

For each network static `ChainHardforks`, add the `RealTime` entry. Use
`ForkCondition::Never` until the actual timestamp is determined:

```rust
// TAIKO_MAINNET_HARDFORKS — add:
(TaikoHardfork::RealTime.boxed(), ForkCondition::Never),

// TAIKO_HOODI_HARDFORKS — add (concrete timestamp TBD):
(TaikoHardfork::RealTime.boxed(), ForkCondition::Never),

// TAIKO_DEVNET_HARDFORKS — add (activates immediately for testing):
(TaikoHardfork::RealTime.boxed(), ForkCondition::Timestamp(0)),

// TAIKO_MASAYA_HARDFORKS — add:
(TaikoHardfork::RealTime.boxed(), ForkCondition::Timestamp(0)),
```

See [Step 12](#step-12--network-hardfork-schedules) for how to wire actual timestamps
once they are known.

---

## Step 2 — TaikoSpecId Extension (`crates/evm`)

**File:** [crates/evm/src/spec.rs](crates/evm/src/spec.rs)

### 2.1 Add `REALTIME` variant

```rust
#[repr(u8)]
pub enum TaikoSpecId {
    GENESIS = 0,
    ONTAKE  = 1,
    PACAYA  = 2,
    SHASTA  = 3,
    REALTIME = 4,  // NEW — supersedes Shasta
}
```

Because `TaikoSpecId` uses `repr(u8)` ordering, `is_enabled_in()` automatically returns `true`
when `REALTIME` code runs under a `SHASTA` or older check — no change needed to that method.

### 2.2 Update `into_eth_spec()`

```rust
pub const fn into_eth_spec(self) -> SpecId {
    match self {
        Self::GENESIS | Self::ONTAKE | Self::PACAYA | Self::SHASTA | Self::REALTIME => {
            SpecId::SHANGHAI
        }
    }
}
```

### 2.3 Update `FromStr` and `From<TaikoSpecId> for &'static str`

```rust
// In FromStr:
name::REALTIME => Ok(TaikoSpecId::REALTIME),

// In From impl:
TaikoSpecId::REALTIME => name::REALTIME,

// In name module:
pub const REALTIME: &str = "RealTime";
```

### 2.4 Update tests

Add `REALTIME` to the existing ordering test:

```rust
(TaikoSpecId::SHASTA, false),
(TaikoSpecId::REALTIME, false),   // NEW — PACAYA is not enabled in REALTIME ordering
```

Add a new test case for `REALTIME`:

```rust
(TaikoSpecId::REALTIME, vec![
    (TaikoSpecId::GENESIS, true),
    (TaikoSpecId::ONTAKE,  true),
    (TaikoSpecId::PACAYA,  true),
    (TaikoSpecId::SHASTA,  true),
    (TaikoSpecId::REALTIME, true),
]),
```

---

## Step 3 — Fork Detection in Block Config (`crates/block`)

**File:** [crates/block/src/config.rs](crates/block/src/config.rs)

### 3.1 Update `taiko_spec_by_timestamp_and_block_number()`

RealTime supersedes Shasta, so it must be checked first:

```rust
pub fn taiko_spec_by_timestamp_and_block_number<C>(
    chain_spec: &C,
    timestamp: u64,
    block_number: u64,
) -> TaikoSpecId
where
    C: EthereumHardforks + EthChainSpec + Hardforks,
{
    if chain_spec.fork(TaikoHardfork::RealTime).active_at_timestamp(timestamp) {
        // NEW — check RealTime before Shasta
        TaikoSpecId::REALTIME
    } else if chain_spec.fork(TaikoHardfork::Shasta).active_at_timestamp(timestamp) {
        TaikoSpecId::SHASTA
    } else if chain_spec
        .fork(TaikoHardfork::Pacaya)
        .active_at_timestamp_or_number(timestamp, block_number)
    {
        TaikoSpecId::PACAYA
    } else if chain_spec
        .fork(TaikoHardfork::Ontake)
        .active_at_timestamp_or_number(timestamp, block_number)
    {
        TaikoSpecId::ONTAKE
    } else {
        TaikoSpecId::GENESIS
    }
}
```

This function is called from `taiko_revm_spec()`, `next_evm_env()`, and
`evm_env_for_payload()` — all three automatically pick up the new fork without further changes.

---

## Step 4 — New Anchor Function (`crates/consensus`)

**File:** [crates/consensus/src/validation.rs](crates/consensus/src/validation.rs)

### 4.1 Declare `anchorV4WithSignalSlots` in the `sol!` block

```rust
sol! {
    function anchor(bytes32, bytes32, uint64, uint32) external;
    function anchorV2(uint64, bytes32, uint32, (uint8, uint8, uint32, uint64, uint32)) external;
    function anchorV3(uint64, bytes32, uint32, (uint8, uint8, uint32, uint64, uint32), bytes32[]) external;
    function anchorV4((uint48, bytes32, bytes32)) external;
    // NEW — RealTime anchor that also relays signal slots
    function anchorV4WithSignalSlots((uint48, bytes32, bytes32), bytes32[]) external;
}
```

### 4.2 Add the selector constant

```rust
/// Selector for the RealTime-era `anchorV4WithSignalSlots` transaction.
pub const ANCHOR_V4_WITH_SIGNAL_SLOTS_SELECTOR: &[u8; 4] =
    &anchorV4WithSignalSlotsCall::SELECTOR;
```

The gas limit constant `ANCHOR_V3_V4_GAS_LIMIT` (1,000,000) is **reused unchanged** for
RealTime anchor transactions.

---

## Step 5 — Anchor Validation Logic (`crates/consensus`)

**File:** [crates/consensus/src/validation.rs](crates/consensus/src/validation.rs)

### 5.1 Update `validate_anchor_transaction()`

The selector check must accept `anchorV4WithSignalSlots` when RealTime is active. Both the
first block (with signal slots) and subsequent blocks (with empty signal slots array) use the
same selector.

```rust
pub fn validate_anchor_transaction(
    anchor_transaction: &impl SignedTransaction,
    chain_spec: &TaikoChainSpec,
    ctx: AnchorValidationContext,
) -> Result<(), ConsensusError> {
    // Ensure the input data starts with the correct anchor selector for this fork.
    if chain_spec.is_realtime_active(ctx.timestamp) {
        // NEW — RealTime uses anchorV4WithSignalSlots for all blocks (empty slots for non-first)
        validate_input_selector(
            anchor_transaction.input(),
            ANCHOR_V4_WITH_SIGNAL_SLOTS_SELECTOR,
        )?;
    } else if chain_spec.is_shasta_active(ctx.timestamp) {
        validate_input_selector(anchor_transaction.input(), ANCHOR_V4_SELECTOR)?;
    } else if chain_spec.is_pacaya_active_at_block(ctx.block_number) {
        validate_input_selector(anchor_transaction.input(), ANCHOR_V3_SELECTOR)?;
    } else if chain_spec.is_ontake_active_at_block(ctx.block_number) {
        validate_input_selector(anchor_transaction.input(), ANCHOR_V2_SELECTOR)?;
    } else {
        validate_input_selector(anchor_transaction.input(), ANCHOR_V1_SELECTOR)?;
    }

    // Value, gas limit, tip, and sender checks are unchanged.
    // The gas limit branch needs no change: `is_pacaya_active_at_block()` returns true
    // for RealTime blocks (RealTime activates after Pacaya), so ANCHOR_V3_V4_GAS_LIMIT
    // is selected automatically.
    // ...
}
```

---

## Step 6 — Signal Slot Relay in EVM Handler (`crates/evm`)

**File:** [crates/evm/src/handler/mod.rs](crates/evm/src/handler/mod.rs)

### 6.1 Context: how signal relay works

From [PROTOCOL_MIGRATION § 7](PROTOCOL_MIGRATION_REAL_TIME_FORK.md):

```
anchor tx (first block): anchorV4WithSignalSlots(checkpoint, signalSlots)
  → calls SignalService.setSignalsReceived(signalSlots) on L2
```

The `SignalService` is an L2 system contract. In the execution layer, this call is made
*inside* the anchor transaction's EVM execution — it happens automatically when the anchor
contract runs `setSignalsReceived()`.

The execution layer does **not** need custom handler logic for signal relay; it is handled
by the L2 `Anchor.sol` contract itself during normal transaction execution. The executor
simply executes the anchor transaction, which in turn calls `SignalService`.

**No changes are needed in `crates/evm/src/handler/mod.rs`** for signal relay — the existing
`reward_beneficiary`, `validate_against_state_and_deduct_caller`, and `reimburse_caller`
handlers continue to work without modification.

The only requirement is that the executor correctly identifies `anchorV4WithSignalSlots` as
an anchor transaction (same sender + nonce + treasury recipient pattern — unchanged).

### 6.2 Anchor detection is selector-agnostic

The anchor detection in the EVM handler identifies anchors by:
- `tx.caller() == TAIKO_GOLDEN_TOUCH_ADDRESS`
- `tx.nonce() == anchor_caller_nonce` (set via system call pre-execution)
- `tx.kind().to() == Some(&get_treasury_address(chain_id))`

This is **not** selector-based — it works for both `anchorV4` and `anchorV4WithSignalSlots`
without modification.

---

## Step 7 — Extra Data Format (`crates/primitives`)

**File:** [crates/primitives/src/extra_data.rs](crates/primitives/src/extra_data.rs)

### 7.1 RealTime extra data layout

RealTime blocks use the **same** extra data layout as Shasta:

```
extra_data[0]     = basefeeSharingPctg  (u8, 0–100)
extra_data[1..7]  = (no longer a proposal ID — proposals have no sequential IDs)
```

The existing `decode_shasta_basefee_sharing_pctg()` function is reused as-is. No proposal ID
needs to be decoded for RealTime blocks (proposals are identified by hash, not sequential ID).

Add a doc comment to clarify this dual use:

```rust
/// Returns the base fee sharing percentage encoded in Shasta/RealTime extra data (byte 0).
///
/// Both Shasta and RealTime use identical encoding for this field.
pub fn decode_shasta_basefee_sharing_pctg(extra: &[u8]) -> u8 {
    extra.first().copied().unwrap_or_default()
}
```

`decode_shasta_proposal_id()` is **Shasta-only**. Do not call it for RealTime blocks (it
will return bytes 1–6 which are no longer a proposal ID and may be zeroed).

---

## Step 8 — Payload Attributes Extension (`crates/primitives`)

**File:** [crates/primitives/src/payload/attributes.rs](crates/primitives/src/payload/attributes.rs)

### 8.1 Add RealTime fields to `TaikoPayloadAttributes`

The payload attributes carry the CL → EL data needed to build a block. For RealTime, two
new optional fields are required:

```rust
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TaikoPayloadAttributes {
    #[cfg_attr(feature = "serde", serde(flatten))]
    pub payload_attributes: EthPayloadAttributes,
    pub base_fee_per_gas: U256,
    pub block_metadata: TaikoBlockMetadata,
    pub l1_origin: RpcL1Origin,
    pub anchor_transaction: Option<AlloyBytes>,

    // NEW — RealTime fork fields (both absent for Shasta and earlier)
    /// Signal slots to relay via the anchor transaction's first block.
    /// `None` or empty = Shasta/pre-RealTime block; non-empty = RealTime first block.
    #[cfg_attr(
        feature = "serde",
        serde(skip_serializing_if = "Option::is_none", default)
    )]
    pub signal_slots: Option<Vec<B256>>,

    /// The highest L1 block number the L2 derivation may reference (`maxAnchorBlockNumber`).
    /// Required when `signal_slots` is present; ignored for pre-RealTime blocks.
    #[cfg_attr(
        feature = "serde",
        serde(skip_serializing_if = "Option::is_none", default)
    )]
    pub max_anchor_block_number: Option<u64>,
}
```

### 8.2 `RpcL1Origin` field semantics for RealTime

The existing `RpcL1Origin` fields map to RealTime concepts as follows:

| `RpcL1Origin` field | Shasta meaning | RealTime meaning |
|---------------------|---------------|-----------------|
| `l1_block_height` | L1 block where proposal was included | `maxAnchorBlockNumber` — highest L1 anchor block |
| `l1_block_hash` | Hash of that L1 block | `maxAnchorBlockHash` |
| `is_forced_inclusion` | `true` if forced | Always `false` |
| `block_id` | Sequential proposal ID | Not meaningful; can be `0` or hash truncated |

No structural changes are needed to `RpcL1Origin`. The CL is responsible for populating
`l1_block_height` with `maxAnchorBlockNumber` and `l1_block_hash` with `maxAnchorBlockHash`.

### 8.3 Update `LocalPayloadAttributesBuilder` default

Update the local builder used in tests and devnet:

```rust
TaikoPayloadAttributes {
    // ... existing fields ...
    signal_slots: None,         // NEW default
    max_anchor_block_number: None,  // NEW default
}
```

---

## Step 9 — Payload Builder Updates (`crates/payload`)

**File:** [crates/payload/src/builder.rs](crates/payload/src/builder.rs)

### 9.1 Pass signal slots to anchor transaction

The `anchor_transaction` field in `TaikoPayloadAttributes` carries a pre-built, RLP-encoded
signed anchor transaction. For RealTime blocks, the CL node (driver) constructs this
transaction and encodes it as `anchorV4WithSignalSlots(checkpoint, signalSlots)` for the
first block, and `anchorV4WithSignalSlots(checkpoint, [])` for subsequent blocks.

The payload builder already injects `anchor_transaction` verbatim — no selector inspection is
required. The builder does need to validate the anchor transaction's selector to be
`ANCHOR_V4_WITH_SIGNAL_SLOTS_SELECTOR` when RealTime is active.

### 9.2 Update `execute_anchor_and_pool_transactions()`

The existing `validate_anchor_transaction()` call is what performs selector validation.
Since that function already dispatches on fork (Step 5.1), **no additional changes** are
needed in the payload builder for selector validation.

However, the gas reservation for anchor overhead must remain correct:

```rust
// Existing line — still correct for RealTime (same gas limit):
gas_limit: attributes.gas_limit.saturating_sub(ANCHOR_V3_V4_GAS_LIMIT),
```

### 9.3 No forced-inclusion logic for RealTime

The existing payload builder does not contain forced-inclusion–specific transaction selection
logic (that was the raiko/prover side). No changes needed.

---

## Step 10 — Block Executor Updates (`crates/block`)

**File:** [crates/block/src/executor.rs](crates/block/src/executor.rs)

### 10.1 Extra data decoding in `apply_pre_execution_changes()`

The existing code already handles Shasta correctly, and RealTime uses the same extra data
byte 0 for `basefeeSharingPctg`. Add a branch that also accepts RealTime:

```rust
let base_fee_share_pgtg =
    if self.spec.is_realtime_active(self.evm.block().timestamp().to()) ||
       self.spec.is_shasta_active(self.evm.block().timestamp().to())
    {
        // Both Shasta and RealTime encode basefeeSharingPctg in byte 0
        decode_shasta_basefee_sharing_pctg(self.ctx.extra_data.as_ref()) as u64
    } else if self.spec.is_ontake_active_at_block(self.evm.block().number().to()) {
        decode_post_ontake_extra_data(self.ctx.extra_data.clone())
    } else {
        0
    };
```

Because `TaikoSpecId::REALTIME > TaikoSpecId::SHASTA` in the `is_enabled_in()` ordering,
checking `is_realtime_active()` first prevents the Shasta branch from also firing.
Alternatively, since both branches execute the same code, a combined condition is equivalent.

### 10.2 No forced-inclusion skipping

The `#[cfg(feature = "prover")]` `execute_block()` override skips invalid transactions and
handles forced-inclusion anchor transactions. For RealTime, `isForcedInclusion` is always
`false` and no special case is needed — the existing logic works correctly.

---

## Step 11 — Database Model Updates (`crates/db`)

**File:** [crates/db/src/model.rs](crates/db/src/model.rs)

### 11.1 `StoredL1Origin` — no structural changes

The `StoredL1Origin` struct stores `is_forced_inclusion: bool`. For RealTime blocks this
field is always `false`. No schema migration is required.

### 11.2 `BatchToLastBlock` table — no changes

This table maps batch/proposal IDs to their last L2 block. In RealTime, proposals have no
sequential IDs; the table can continue to be used by the prover/driver with a different
keying scheme if needed, but the execution layer does not query it during block validation.

### 11.3 Signal slots storage (optional)

If the RPC layer needs to expose signal slots for historical queries, consider adding a new
table:

```rust
tables! {
    // NEW — optional, for RealTime signal slot historical queries
    table RealTimeSignalSlotsTable {
        type Key = BlockNumber;   // L2 block number of the first block in the batch
        type Value = Vec<B256>;   // Signal slots relayed in that block's anchor tx
    }
}
```

This table is **not required** for block execution or validation; it is only needed if an
RPC endpoint exposing signal slots is planned.

---

## Step 12 — Network Hardfork Schedules

**File:** [crates/chainspec/src/hardfork.rs](crates/chainspec/src/hardfork.rs)

### 12.1 Network activation pattern

Follow the same pattern as Shasta. Replace `ForkCondition::Never` placeholders from Step 1.4
with the real timestamps once they are published:

```rust
pub static TAIKO_HOODI_HARDFORKS: LazyLock<ChainHardforks> = LazyLock::new(|| {
    ChainHardforks::new(extend_with_shared_hardforks(vec![
        (TaikoHardfork::Ontake.boxed(), ForkCondition::Block(0)),
        (TaikoHardfork::Pacaya.boxed(), ForkCondition::Block(0)),
        (TaikoHardfork::Shasta.boxed(), ForkCondition::Timestamp(1_770_296_400)),
        (TaikoHardfork::RealTime.boxed(), ForkCondition::Timestamp(REALTIME_HOODI_TS)), // TBD
    ]))
});
```

### 12.2 `clone_with_devnet_realtime_timestamp()`

Add a devnet override helper similar to the Shasta one in `spec.rs`, to allow integration
tests to set arbitrary RealTime activation timestamps:

```rust
/// Returns a cloned [`TaikoChainSpec`] with the RealTime hardfork activation timestamp
/// updated when the chainspec targets the Taiko devnet. Returns `None` for other networks.
pub fn clone_with_devnet_realtime_timestamp(&self, timestamp: u64) -> Option<Self> {
    if self.genesis_hash() != TAIKO_DEVNET_GENESIS_HASH {
        return None;
    }
    let mut cloned = self.clone();
    cloned
        .inner
        .hardforks
        .insert(TaikoHardfork::RealTime, ForkCondition::Timestamp(timestamp));
    Some(cloned)
}
```

---

## Step 13 — Tests

### 13.1 Hardfork tests (`crates/chainspec/src/hardfork.rs`)

Add tests mirroring existing Shasta tests:

```rust
#[test]
fn test_devnet_realtime_uses_timestamp_activation() {
    let realtime = TAIKO_DEVNET_HARDFORKS.fork(TaikoHardfork::RealTime);
    assert!(realtime.is_timestamp(), "realtime activation should be timestamp-based");
    assert_eq!(realtime, ForkCondition::Timestamp(0));
}

#[test]
fn test_realtime_supersedes_shasta() {
    // On devnet both activate at 0; RealTime should be detected first.
    // taiko_spec_by_timestamp_and_block_number returns REALTIME, not SHASTA.
    use alethia_reth_block::config::taiko_spec_by_timestamp_and_block_number;
    use alethia_reth_evm::spec::TaikoSpecId;
    let spec = taiko_spec_by_timestamp_and_block_number(&*TAIKO_DEVNET, 1, 1);
    assert_eq!(spec, TaikoSpecId::REALTIME);
}
```

### 13.2 Anchor selector test (`crates/consensus/src/validation.rs`)

```rust
#[test]
fn test_anchor_v4_with_signal_slots_selector_matches_protocol() {
    // Selector is keccak256("anchorV4WithSignalSlots((uint48,bytes32,bytes32),bytes32[])")[:4]
    // Verify it does NOT equal the anchorV4 selector.
    assert_ne!(
        ANCHOR_V4_WITH_SIGNAL_SLOTS_SELECTOR,
        ANCHOR_V4_SELECTOR,
        "selectors must differ"
    );
}

#[test]
fn test_validate_anchor_uses_v4_with_signal_slots_for_realtime() {
    // Build a mock anchor transaction with ANCHOR_V4_WITH_SIGNAL_SLOTS_SELECTOR prefix.
    // Verify validate_anchor_transaction() passes for a REALTIME-active chainspec.
    // ...
}
```

### 13.3 TaikoSpecId ordering test

```rust
#[test]
fn test_realtime_is_enabled_in_shasta() {
    // REALTIME code should run under SHASTA or newer checks.
    assert!(TaikoSpecId::REALTIME.is_enabled_in(TaikoSpecId::SHASTA));
    assert!(TaikoSpecId::REALTIME.is_enabled_in(TaikoSpecId::REALTIME));
    assert!(!TaikoSpecId::SHASTA.is_enabled_in(TaikoSpecId::REALTIME));
}
```

---

## Cross-Cutting Concerns

### Base fee validation

The `validate_header_against_parent()` function in
[crates/consensus/src/validation.rs](crates/consensus/src/validation.rs) uses
`is_shasta_active()` to gate EIP-4396 base fee validation. RealTime is a superset of Shasta
and must also use EIP-4396. Update the condition:

```rust
if self.chain_spec.is_realtime_active(header.timestamp()) ||
   self.chain_spec.is_shasta_active(header.timestamp())
{
    // EIP-4396 base fee validation (unchanged logic)
    // Strict timestamp ordering (unchanged)
    // ...
}
```

Since the RealTime hardfork is always at a higher timestamp than Shasta for any given network,
and `is_shasta_active()` returns `true` for any timestamp ≥ Shasta activation, the simpler
approach is to keep the `is_shasta_active()` guard and ensure the Shasta timestamp ≤ RealTime
timestamp during network configuration. Verify this invariant in the hardfork activation tests.

### No blob transactions

The `TaikoTxEnvelope` enum does not include EIP-4844 blob transactions. This is unchanged in
RealTime.

### Osaka size checks

The `validate_block_pre_execution()` and `taiko_payload()` builder already check Osaka RLP
size limits. These checks are fork-agnostic and work for RealTime blocks without change.

### Engine API

`TaikoExecutionData` and the engine validator do not need changes — they operate on the same
payload format. The fork is transparent to the engine API layer.

---

## What Does NOT Change

The following components require **no modifications** for the RealTime fork:

| Component | Reason |
|-----------|--------|
| `crates/evm/src/handler/mod.rs` | Anchor detection is address/nonce-based, not selector-based; fee sharing logic unchanged |
| `crates/evm/src/evm.rs` | EVM core unchanged |
| `crates/evm/src/factory.rs` | EVM factory unchanged |
| `crates/consensus/src/eip4396.rs` | EIP-4396 base fee formula is reused as-is |
| `crates/consensus/src/transaction/` | Transaction types (Legacy, EIP1559, etc.) unchanged |
| `crates/block/src/assembler.rs` | Block assembler is fork-agnostic |
| `crates/block/src/tx_selection.rs` | Transaction selection for mempool is unchanged |
| `crates/block/src/receipt_builder.rs` | Receipt construction is unchanged |
| `crates/rpc/` | RPC API surface unchanged; taiko_l1OriginByID still works |
| `crates/node/` | Node composition and AddOns unchanged |
| `crates/network/` | P2P network builder unchanged |
| `crates/cli/` | CLI interface unchanged |
| `bin/alethia-reth/` | Binary entry point unchanged |

---

## Implementation Order

The following order minimises compilation failures between steps:

```
1. crates/chainspec — add TaikoHardfork::RealTime, helper methods, network schedules
2. crates/evm       — add TaikoSpecId::REALTIME, update FromStr/Display
3. crates/block     — update taiko_spec_by_timestamp_and_block_number()
4. crates/consensus — add anchorV4WithSignalSlots sol!, selector, validate_anchor_transaction()
5. crates/primitives — update TaikoPayloadAttributes (signal_slots, max_anchor_block_number)
6. crates/payload   — validate signal slots field in anchor injection path
7. crates/block     — update apply_pre_execution_changes() for RealTime extra_data
8. crates/db        — add RealTimeSignalSlotsTable if signal slot RPC is needed
9. tests across all crates
```
