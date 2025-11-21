use alethia_reth_block::config::TaikoEvmConfig;
use alethia_reth_chainspec::spec::TaikoChainSpec;
use alethia_reth_primitives::{TaikoPrimitives, engine::TaikoEngineTypes};
use alethia_reth_rpc::{converter::TaikoRpcConverter, eth::types::TaikoEthApi};
use reth_node_api::{FullNodeComponents, NodeTypes};
use reth_node_builder::rpc::{EthApiBuilder, EthApiCtx};

/// Builds [`TaikoEthApi`] for the Taiko node.
#[derive(Debug, Default, Clone)]
pub struct TaikoEthApiBuilder;

impl TaikoEthApiBuilder {
    /// Creates a new instance of `TaikoEthApiBuilder`.
    pub const fn new() -> Self {
        Self
    }
}

impl<N> EthApiBuilder<N> for TaikoEthApiBuilder
where
    N: FullNodeComponents<Evm = TaikoEvmConfig>,
    N::Types: NodeTypes<
            Primitives = TaikoPrimitives,
            ChainSpec = TaikoChainSpec,
            Payload = TaikoEngineTypes,
        >,
{
    /// The Ethapi implementation this builder will build.
    type EthApi = TaikoEthApi<N, TaikoRpcConverter<TaikoEvmConfig>>;

    /// Builds the [`TaikoEthApi`] from the given context.
    async fn build_eth_api(self, ctx: EthApiCtx<'_, N>) -> eyre::Result<Self::EthApi> {
        // Build the Eth API
        let api = ctx.eth_api_builder().build();

        Ok(TaikoEthApi(api))
    }
}
