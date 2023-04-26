use crate::context::RpcContext;
use crate::felt::RpcFelt;
use anyhow::{anyhow, Context};
use pathfinder_common::{BlockId, ContractAddress, StorageAddress, StorageValue};
use pathfinder_storage::StarknetBlocksBlockId;
use serde::Deserialize;

#[derive(Deserialize, Debug, PartialEq, Eq)]
pub struct GetStorageAtInput {
    pub contract_address: ContractAddress,
    pub key: StorageAddress,
    pub block_id: BlockId,
}

#[serde_with::serde_as]
#[derive(serde::Serialize)]
pub struct GetStorageOutput(#[serde_as(as = "RpcFelt")] StorageValue);

crate::error::generate_rpc_error_subset!(GetStorageAtError: ContractNotFound, BlockNotFound);

/// Get the value of the storage at the given address and key.
pub async fn get_storage_at(
    context: RpcContext,
    input: GetStorageAtInput,
) -> Result<GetStorageOutput, GetStorageAtError> {
    let block_id = match input.block_id {
        BlockId::Hash(hash) => hash.into(),
        BlockId::Number(number) => number.into(),
        BlockId::Latest => StarknetBlocksBlockId::Latest,
        BlockId::Pending => {
            match context
                .pending_data
                .ok_or_else(|| anyhow!("Pending data not supported in this configuration"))?
                .state_update()
                .await
            {
                Some(update) => {
                    let pending_value = update
                        .state_diff
                        .storage_diffs
                        .get(&input.contract_address)
                        .and_then(|storage| {
                            storage.iter().find_map(|update| {
                                (update.key == input.key).then_some(update.value)
                            })
                        });

                    match pending_value {
                        Some(value) => return Ok(GetStorageOutput(value)),
                        None => StarknetBlocksBlockId::Latest,
                    }
                }
                None => StarknetBlocksBlockId::Latest,
            }
        }
    };

    let storage = context.storage.clone();
    let span = tracing::Span::current();

    let jh = tokio::task::spawn_blocking(move || {
        let _g = span.enter();
        let mut db = storage
            .connection()
            .context("Opening database connection")?;

        let tx = db.transaction().context("Creating database transaction")?;

        // Check for block existence.
        if !crate::utils::block_exists(&tx, block_id)? {
            return Err(GetStorageAtError::BlockNotFound);
        }

        let value = match block_id {
            StarknetBlocksBlockId::Number(number) => {
                database::storage_at_block_number(&tx, input.contract_address, input.key, number)
            }
            StarknetBlocksBlockId::Hash(hash) => {
                database::storage_at_block_hash(&tx, input.contract_address, input.key, hash)
            }
            StarknetBlocksBlockId::Latest => {
                database::storage_at_latest(&tx, input.contract_address, input.key)
            }
        }?;

        match value {
            Some(value) => Ok(GetStorageOutput(value)),
            None => {
                if database::contract_exists(&tx, input.contract_address, block_id)? {
                    Ok(GetStorageOutput(StorageValue::ZERO))
                } else {
                    Err(GetStorageAtError::ContractNotFound)
                }
            }
        }
    });

    jh.await.context("Database read panic or shutting down")?
}

mod database {
    use pathfinder_common::{StarknetBlockHash, StarknetBlockNumber};
    use rusqlite::{params, OptionalExtension, Transaction};

    use super::*;

    pub fn storage_at_latest(
        tx: &Transaction<'_>,
        contract_address: ContractAddress,
        key: StorageAddress,
    ) -> anyhow::Result<Option<StorageValue>> {
        tx.query_row(
            r"SELECT storage_value FROM storage_updates 
                WHERE contract_address = ? AND storage_address = ?
                ORDER BY block_number DESC LIMIT 1",
            params![contract_address, key],
            |row| row.get(0),
        )
        .optional()
        .context("Reading latest storage value")
    }

    pub fn storage_at_block_hash(
        tx: &Transaction<'_>,
        contract_address: ContractAddress,
        key: StorageAddress,
        block: StarknetBlockHash,
    ) -> anyhow::Result<Option<StorageValue>> {
        tx.query_row(
            r"SELECT storage_value FROM storage_updates 
                WHERE contract_address = ? AND storage_address = ? AND block_number <= (
                    SELECT number FROM canonical_blocks WHERE hash = ?
                )
                ORDER BY block_number DESC LIMIT 1",
            params![contract_address, key, block],
            |row| row.get(0),
        )
        .optional()
        .context("Reading storage value at block hash")
    }

    pub fn storage_at_block_number(
        tx: &Transaction<'_>,
        contract_address: ContractAddress,
        key: StorageAddress,
        block: StarknetBlockNumber,
    ) -> anyhow::Result<Option<StorageValue>> {
        tx.query_row(
            r"SELECT storage_value FROM storage_updates 
                WHERE contract_address = ? AND storage_address = ? AND block_number <= ?
                ORDER BY block_number DESC LIMIT 1",
            params![contract_address, key, block],
            |row| row.get(0),
        )
        .optional()
        .context("Reading storage value at block number")
    }

    pub fn contract_exists(
        tx: &Transaction<'_>,
        contract_address: ContractAddress,
        block_id: StarknetBlocksBlockId,
    ) -> anyhow::Result<bool> {
        match block_id {
            StarknetBlocksBlockId::Number(number) => tx.query_row(
                "SELECT EXISTS(SELECT 1 FROM contract_updates WHERE contract_address = ? AND block_number <= ?)",
                params![contract_address, number],
                |row| row.get(0),
            ),
            StarknetBlocksBlockId::Hash(hash) => tx.query_row(
                r"SELECT EXISTS(
                    SELECT 1 FROM contract_updates WHERE contract_address = ? AND block_number <= (
                        SELECT number FROM canonical_blocks WHERE hash = ?
                    )
                )",
                params![contract_address, hash],
                |row| row.get(0),
            ),
            StarknetBlocksBlockId::Latest => tx.query_row(
                "SELECT EXISTS(SELECT 1 FROM contract_updates WHERE contract_address = ?)",
                [contract_address],
                |row| row.get(0),
            ),
        }
        .context("Querying that contract exists")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use assert_matches::assert_matches;
    use jsonrpsee::types::Params;
    use pathfinder_common::{felt, felt_bytes, ContractAddress, StarknetBlockHash, StorageAddress};

    /// # Important
    ///
    /// `BlockId` parsing is tested in [`get_block`][crate::rpc::v02::method::get_block::tests::parsing]
    /// and is not repeated here.
    #[test]
    fn parsing() {
        let expected = GetStorageAtInput {
            contract_address: ContractAddress::new_or_panic(felt!("0x1")),
            key: StorageAddress::new_or_panic(felt!("0x2")),
            block_id: BlockId::Latest,
        };

        [
            r#"["1", "2", "latest"]"#,
            r#"{"contract_address": "0x1", "key": "0x2", "block_id": "latest"}"#,
        ]
        .into_iter()
        .enumerate()
        .for_each(|(i, input)| {
            let actual = Params::new(Some(input))
                .parse::<GetStorageAtInput>()
                .unwrap_or_else(|error| panic!("test case {i}: {input}, {error}"));
            assert_eq!(actual, expected, "test case {i}: {input}");
        });
    }

    type TestCaseHandler = Box<dyn Fn(usize, &Result<StorageValue, GetStorageAtError>)>;

    /// Execute a single test case and check its outcome for `get_storage_at`
    async fn check(
        test_case_idx: usize,
        test_case: &(
            RpcContext,
            ContractAddress,
            StorageAddress,
            BlockId,
            TestCaseHandler,
        ),
    ) {
        let (context, contract_address, key, block_id, f) = test_case;
        let result = get_storage_at(
            context.clone(),
            GetStorageAtInput {
                contract_address: *contract_address,
                key: *key,
                block_id: *block_id,
            },
        )
        .await
        .map(|x| x.0);
        f(test_case_idx, &result);
    }

    /// Common assertion type for most of the happy paths
    fn assert_value(expected: &'static [u8]) -> TestCaseHandler {
        Box::new(|i: usize, result| {
            assert_matches!(result, Ok(value) => assert_eq!(
                *value,
                StorageValue(pathfinder_common::felt_bytes!(expected)),
                "test case {i}"
            ), "test case {i}");
        })
    }

    impl PartialEq for GetStorageAtError {
        fn eq(&self, other: &Self) -> bool {
            match (self, other) {
                (Self::Internal(l), Self::Internal(r)) => l.to_string() == r.to_string(),
                _ => core::mem::discriminant(self) == core::mem::discriminant(other),
            }
        }
    }

    /// Common assertion type for most of the error paths
    fn assert_error(expected: GetStorageAtError) -> TestCaseHandler {
        Box::new(move |i: usize, result| {
            assert_matches!(result, Err(error) => assert_eq!(*error, expected, "test case {i}"), "test case {i}");
        })
    }

    #[tokio::test]
    async fn happy_paths_and_major_errors() {
        let ctx = RpcContext::for_tests_with_pending().await;
        let ctx_with_pending_empty = RpcContext::for_tests()
            .with_pending_data(starknet_gateway_types::pending::PendingData::default());
        let ctx_with_pending_disabled = RpcContext::for_tests();

        let pending_contract0 =
            ContractAddress::new_or_panic(felt_bytes!(b"pending contract 1 address"));
        let pending_key0 = StorageAddress::new_or_panic(felt_bytes!(b"pending storage key 0"));
        let contract1 = ContractAddress::new_or_panic(felt_bytes!(b"contract 1"));
        let key0 = StorageAddress::new_or_panic(felt_bytes!(b"storage addr 0"));
        let deployment_block = BlockId::Hash(StarknetBlockHash(felt_bytes!(b"block 1")));
        let non_existent_key = StorageAddress::new_or_panic(felt_bytes!(b"non-existent"));

        let non_existent_contract = ContractAddress::new_or_panic(felt_bytes!(b"non-existent"));
        let pre_deploy_block = BlockId::Hash(StarknetBlockHash(felt_bytes!(b"genesis")));
        let non_existent_block = BlockId::Hash(StarknetBlockHash(felt_bytes!(b"non-existent")));

        let cases: &[(
            RpcContext,
            ContractAddress,
            StorageAddress,
            BlockId,
            TestCaseHandler,
        )] = &[
            // Pending - happy paths
            (
                ctx.clone(),
                pending_contract0,
                pending_key0,
                BlockId::Pending,
                assert_value(b"pending storage value 0"),
            ),
            (
                ctx_with_pending_empty,
                contract1,
                key0,
                BlockId::Pending,
                // Pending data is absent, fallback to the latest block
                assert_value(b"storage value 2"),
            ),
            // Other block ids - happy paths
            (
                ctx.clone(),
                contract1,
                key0,
                deployment_block,
                assert_value(b"storage value 1"),
            ),
            (
                ctx.clone(),
                contract1,
                key0,
                BlockId::Latest,
                assert_value(b"storage value 2"),
            ),
            (
                ctx.clone(),
                contract1,
                non_existent_key,
                BlockId::Latest,
                assert_value(&[0]),
            ),
            // Errors
            (
                ctx.clone(),
                non_existent_contract,
                key0,
                BlockId::Latest,
                assert_error(GetStorageAtError::ContractNotFound),
            ),
            (
                ctx.clone(),
                contract1,
                key0,
                non_existent_block,
                assert_error(GetStorageAtError::BlockNotFound),
            ),
            (
                ctx.clone(),
                contract1,
                key0,
                pre_deploy_block,
                assert_error(GetStorageAtError::ContractNotFound),
            ),
            (
                ctx_with_pending_disabled,
                pending_contract0,
                pending_key0,
                BlockId::Pending,
                assert_error(GetStorageAtError::Internal(anyhow!(
                    "Pending data not supported in this configuration"
                ))),
            ),
        ];

        for (i, test_case) in cases.iter().enumerate() {
            check(i, test_case).await;
        }
    }
}
