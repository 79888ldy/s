use crate::{
    context::RpcContext,
    v02::types::{reply::FeeEstimate, request::BroadcastedTransaction},
};
use pathfinder_common::BlockId;

use super::common::prepare_handle_and_block;

#[derive(serde::Deserialize, Debug, PartialEq, Eq)]
pub struct EstimateFeeInput {
    request: Vec<BroadcastedTransaction>,
    block_id: BlockId,
}

crate::error::generate_rpc_error_subset!(
    EstimateFeeError: BlockNotFound,
    ContractNotFound,
    ContractError,
    InvalidMessageSelector,
    InvalidCallData
);

impl From<crate::cairo::ext_py::CallFailure> for EstimateFeeError {
    fn from(c: crate::cairo::ext_py::CallFailure) -> Self {
        use crate::cairo::ext_py::CallFailure::*;
        match c {
            NoSuchBlock => Self::BlockNotFound,
            NoSuchContract => Self::ContractNotFound,
            InvalidEntryPoint => Self::InvalidMessageSelector,
            ExecutionFailed(e) => Self::Internal(anyhow::anyhow!("Internal error: {e}")),
            // Intentionally hide the message under Internal
            Internal(_) | Shutdown => Self::Internal(anyhow::anyhow!("Internal error")),
        }
    }
}

pub async fn estimate_fee(
    context: RpcContext,
    input: EstimateFeeInput,
) -> Result<Vec<FeeEstimate>, EstimateFeeError> {
    unimplemented!()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::v02::types::request::BroadcastedInvokeTransaction;
    use pathfinder_common::{
        felt, CallParam, ContractAddress, Fee, StarknetBlockHash, TransactionNonce,
        TransactionSignatureElem, TransactionVersion,
    };

    mod parsing {
        use super::*;

        fn test_invoke_txn() -> BroadcastedTransaction {
            BroadcastedTransaction::Invoke(BroadcastedInvokeTransaction::V1(
                crate::v02::types::request::BroadcastedInvokeTransactionV1 {
                    version: TransactionVersion::ONE_WITH_QUERY_VERSION,
                    max_fee: Fee(felt!("0x6")),
                    signature: vec![TransactionSignatureElem(felt!("0x7"))],
                    nonce: TransactionNonce(felt!("0x8")),
                    sender_address: ContractAddress::new_or_panic(felt!("0xaaa")),
                    calldata: vec![CallParam(felt!("0xff"))],
                },
            ))
        }

        #[test]
        fn positional_args() {
            use jsonrpsee::types::Params;

            let positional = r#"[
                [
                    {
                        "type": "INVOKE",
                        "version": "0x100000000000000000000000000000001",
                        "max_fee": "0x6",
                        "signature": [
                            "0x7"
                        ],
                        "nonce": "0x8",
                        "sender_address": "0xaaa",
                        "calldata": [
                            "0xff"
                        ]
                    }
                ],
                { "block_hash": "0xabcde" }
            ]"#;
            let positional = Params::new(Some(positional));

            let input = positional.parse::<EstimateFeeInput>().unwrap();
            let expected = EstimateFeeInput {
                request: vec![test_invoke_txn()],
                block_id: BlockId::Hash(StarknetBlockHash(felt!("0xabcde"))),
            };
            assert_eq!(input, expected);
        }

        #[test]
        fn named_args() {
            use jsonrpsee::types::Params;

            let named_args = r#"{
                "request": [
                    {
                        "type": "INVOKE",
                        "version": "0x100000000000000000000000000000001",
                        "max_fee": "0x6",
                        "signature": [
                            "0x7"
                        ],
                        "nonce": "0x8",
                        "sender_address": "0xaaa",
                        "calldata": [
                            "0xff"
                        ]
                    }
                ],
                "block_id": { "block_hash": "0xabcde" }
            }"#;
            let named_args = Params::new(Some(named_args));

            let input = named_args.parse::<EstimateFeeInput>().unwrap();
            let expected = EstimateFeeInput {
                request: vec![test_invoke_txn()],
                block_id: BlockId::Hash(StarknetBlockHash(felt!("0xabcde"))),
            };
            assert_eq!(input, expected);
        }
    }

    // These tests require a Python environment properly set up _and_ a mainnet database with the first six blocks.
    mod ext_py {
        use super::*;
        use crate::v02::method::estimate_fee::tests::ext_py::{
            test_context, valid_invoke_v1, BLOCK_5,
        };
        use crate::v02::types::request::{
            BroadcastedDeclareTransaction, BroadcastedDeclareTransactionV1,
            BroadcastedDeclareTransactionV2, BroadcastedInvokeTransactionV1,
        };
        use crate::v02::types::{ContractClass, SierraContractClass};
        use pathfinder_common::{felt_bytes, CasmHash};

        #[tokio::test]
        async fn no_such_block() {
            let (_db_dir, context, account_address, _) = test_context().await;

            let input = EstimateFeeInput {
                request: vec![valid_invoke_v1(account_address)],
                block_id: BlockId::Hash(StarknetBlockHash(felt_bytes!(b"nonexistent"))),
            };
            let error = estimate_fee(context, input).await;
            assert_matches::assert_matches!(error, Err(EstimateFeeError::BlockNotFound));
        }

        #[tokio::test]
        async fn no_such_contract() {
            let (_db_dir, context, account_address, _) = test_context().await;

            let mainnet_invoke = valid_invoke_v1(account_address)
                .into_invoke()
                .unwrap()
                .into_v1()
                .unwrap();
            let input = EstimateFeeInput {
                request: vec![BroadcastedTransaction::Invoke(
                    BroadcastedInvokeTransaction::V1(BroadcastedInvokeTransactionV1 {
                        sender_address: ContractAddress::new_or_panic(felt!("0xdeadbeef")),
                        ..mainnet_invoke
                    }),
                )],
                block_id: BLOCK_5,
            };
            let error = estimate_fee(context, input).await;
            assert_matches::assert_matches!(error, Err(EstimateFeeError::ContractNotFound));
        }

        #[tokio::test]
        async fn successful_invoke_v1() {
            let (_db_dir, context, account_address, latest_block_hash) = test_context().await;

            let transaction0 = valid_invoke_v1(account_address);
            let transaction1 = BroadcastedTransaction::Invoke(BroadcastedInvokeTransaction::V1(
                BroadcastedInvokeTransactionV1 {
                    nonce: TransactionNonce(felt!("0x1")),
                    ..transaction0
                        .clone()
                        .into_invoke()
                        .unwrap()
                        .into_v1()
                        .unwrap()
                },
            ));
            let input = EstimateFeeInput {
                request: vec![transaction0, transaction1],
                block_id: BlockId::Hash(latest_block_hash),
            };
            let result = estimate_fee(context, input).await.unwrap();
            assert_eq!(result, vec![FeeEstimate::default(), FeeEstimate::default()]);
        }

        #[test_log::test(tokio::test)]
        async fn successful_declare_v1() {
            let (_db_dir, context, account_address, latest_block_hash) = test_context().await;

            let contract_class = {
                let compressed_json =
                    starknet_gateway_test_fixtures::zstd_compressed_contracts::CONTRACT_DEFINITION;
                let json = zstd::decode_all(compressed_json).unwrap();
                ContractClass::from_definition_bytes(&json)
                    .unwrap()
                    .as_cairo()
                    .unwrap()
            };

            let declare_transaction = BroadcastedTransaction::Declare(
                BroadcastedDeclareTransaction::V1(BroadcastedDeclareTransactionV1 {
                    version: TransactionVersion::ONE_WITH_QUERY_VERSION,
                    max_fee: Fee(Default::default()),
                    signature: vec![],
                    nonce: TransactionNonce(Default::default()),
                    contract_class,
                    sender_address: account_address,
                }),
            );

            let input = EstimateFeeInput {
                request: vec![declare_transaction],
                block_id: BlockId::Hash(latest_block_hash),
            };
            let result = estimate_fee(context, input).await.unwrap();
            assert_eq!(result, vec![FeeEstimate::default()]);
        }

        #[test_log::test(tokio::test)]
        async fn successful_declare_v2() {
            let (_db_dir, context, account_address, latest_block_hash) = test_context().await;

            let contract_class: SierraContractClass = {
                let definition = starknet_gateway_test_fixtures::zstd_compressed_contracts::CAIRO_1_0_0_ALPHA6_SIERRA;
                let definition = zstd::decode_all(definition).unwrap();
                ContractClass::from_definition_bytes(&definition)
                    .unwrap()
                    .as_sierra()
                    .unwrap()
            };

            let declare_transaction = BroadcastedTransaction::Declare(
                BroadcastedDeclareTransaction::V2(BroadcastedDeclareTransactionV2 {
                    version: TransactionVersion::TWO_WITH_QUERY_VERSION,
                    max_fee: Fee(Default::default()),
                    signature: vec![],
                    nonce: TransactionNonce(Default::default()),
                    contract_class,
                    sender_address: account_address,
                    // Taken from
                    // https://external.integration.starknet.io/feeder_gateway/get_state_update?blockNumber=284544
                    compiled_class_hash: CasmHash::new_or_panic(felt!(
                        "0x5bcd45099caf3dca6c0c0f6697698c90eebf02851acbbaf911186b173472fcc"
                    )),
                }),
            );

            let input = EstimateFeeInput {
                request: vec![declare_transaction],
                block_id: BlockId::Hash(latest_block_hash),
            };
            let result = estimate_fee(context, input).await.unwrap();
            assert_eq!(result, vec![FeeEstimate::default()]);
        }
    }
}
