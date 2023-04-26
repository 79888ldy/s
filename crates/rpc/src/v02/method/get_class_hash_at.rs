use crate::context::RpcContext;
use crate::felt::RpcFelt;
use anyhow::Context;
use pathfinder_common::{BlockId, ClassHash, ContractAddress};
use pathfinder_storage::StarknetBlocksBlockId;
use starknet_gateway_types::pending::PendingData;

crate::error::generate_rpc_error_subset!(GetClassHashAtError: BlockNotFound, ContractNotFound);

#[derive(serde::Deserialize, Debug, PartialEq, Eq)]
pub struct GetClassHashAtInput {
    block_id: BlockId,
    contract_address: ContractAddress,
}

#[serde_with::serde_as]
#[derive(serde::Serialize, Debug)]
pub struct GetClassHashOutput(#[serde_as(as = "RpcFelt")] ClassHash);

pub async fn get_class_hash_at(
    context: RpcContext,
    input: GetClassHashAtInput,
) -> Result<GetClassHashOutput, GetClassHashAtError> {
    let block_id = match input.block_id {
        BlockId::Hash(hash) => hash.into(),
        BlockId::Number(number) => number.into(),
        BlockId::Latest => StarknetBlocksBlockId::Latest,
        BlockId::Pending => {
            match get_pending_class_hash(context.pending_data, input.contract_address).await {
                Some(class_hash) => return Ok(GetClassHashOutput(class_hash)),
                None => StarknetBlocksBlockId::Latest,
            }
        }
    };

    let span = tracing::Span::current();
    let jh = tokio::task::spawn_blocking(move || {
        let _g = span.enter();
        let mut db = context
            .storage
            .connection()
            .context("Opening database connection")?;

        let tx = db.transaction().context("Creating database transaction")?;

        // Check for block existence.
        let block_exists = match block_id {
            StarknetBlocksBlockId::Number(number) => database::block_number_exists(&tx, number),
            StarknetBlocksBlockId::Hash(hash) => database::block_hash_exists(&tx, hash),
            StarknetBlocksBlockId::Latest => Ok(true),
        }?;
        if !block_exists {
            return Err(GetClassHashAtError::BlockNotFound);
        }

        match block_id {
            StarknetBlocksBlockId::Number(number) => {
                database::class_hash_at_block_number(&tx, input.contract_address, number)
            }
            StarknetBlocksBlockId::Hash(hash) => {
                database::class_hash_at_block_hash(&tx, input.contract_address, hash)
            }
            StarknetBlocksBlockId::Latest => {
                database::class_hash_at_latest_block(&tx, input.contract_address)
            }
        }?
        .ok_or(GetClassHashAtError::ContractNotFound)
        .map(GetClassHashOutput)
    });

    jh.await.context("Database read panic or shutting down")?
}

/// Returns the [ClassHash] of the given [ContractAddress] if any is defined in the pending data.
async fn get_pending_class_hash(
    pending: Option<PendingData>,
    address: ContractAddress,
) -> Option<ClassHash> {
    pending?.state_update().await.and_then(|state_update| {
        state_update
            .state_diff
            .deployed_contracts
            .iter()
            .find_map(|contract| (contract.address == address).then_some(contract.class_hash))
            .or(state_update
                .state_diff
                .replaced_classes
                .iter()
                .find_map(|contract| (contract.address == address).then_some(contract.class_hash)))
    })
}

mod database {
    use pathfinder_common::{StarknetBlockHash, StarknetBlockNumber};
    use rusqlite::{OptionalExtension, Transaction};

    use super::*;

    pub fn class_hash_at_latest_block(
        tx: &Transaction<'_>,
        contract: ContractAddress,
    ) -> anyhow::Result<Option<ClassHash>> {
        tx.query_row(
            r"SELECT class_hash FROM contract_updates WHERE contract_address = ?
                ORDER BY block_number DESC LIMIT 1",
            [contract],
            |row| row.get(0),
        )
        .optional()
        .context("Querying database for class hash at latest block")
    }

    pub fn class_hash_at_block_number(
        tx: &Transaction<'_>,
        contract: ContractAddress,
        block_number: StarknetBlockNumber,
    ) -> anyhow::Result<Option<ClassHash>> {
        tx.query_row(
            r"SELECT class_hash FROM contract_updates WHERE contract_address = ? AND
                block_number <= ? ORDER BY block_number DESC LIMIT 1",
            rusqlite::params![contract, block_number],
            |row| row.get(0),
        )
        .optional()
        .context("Querying database for class hash at block number")
    }

    pub fn class_hash_at_block_hash(
        tx: &Transaction<'_>,
        contract: ContractAddress,
        block_hash: StarknetBlockHash,
    ) -> anyhow::Result<Option<ClassHash>> {
        tx.query_row(
            r"SELECT class_hash FROM contract_updates JOIN canonical_blocks ON (contract_updates.block_number = canonical_blocks.number)
                WHERE contract_address = ? AND
                block_number <= (SELECT number FROM canonical_blocks WHERE hash = ?)
                ORDER BY block_number DESC LIMIT 1",
            rusqlite::params![contract, block_hash],
            |row| row.get(0),
        )
        .optional()
        .context("Querying database for class hash at block hash")
    }

    pub fn block_hash_exists(
        tx: &Transaction<'_>,
        block_hash: StarknetBlockHash,
    ) -> anyhow::Result<bool> {
        tx.query_row(
            "SELECT EXISTS(SELECT 1  from canonical_blocks WHERE hash = ?)",
            [block_hash],
            |row| row.get(0),
        )
        .context("Querying for existence of block hash")
    }

    pub fn block_number_exists(
        tx: &Transaction<'_>,
        block_number: StarknetBlockNumber,
    ) -> anyhow::Result<bool> {
        tx.query_row(
            "SELECT EXISTS (SELECT 1 from canonical_blocks WHERE number = ?)",
            [block_number],
            |row| row.get(0),
        )
        .context("Querying for existence of block number")
    }
}

// 047C3637B57C2B079B93C61539950C17E868A28F46CDEF28F88521067F21E943
// 0037150BA6F2CCB3A19A45EBE2DE28E85B21DBDCAF77436F4E0CDF686A109989

// block:       047C3637B57C2B079B93C61539950C17E868A28F46CDEF28F88521067F21E943
// class:       010455C752B86932CE552F2B0FE81A880746649B9AEE7E0D842BF3F52378F9F8
// contract:    031C9CDB9B00CB35CF31C05855C0EC3ECF6F7952A1CE6E3C53C3455FCD75A280

#[cfg(test)]
mod tests {
    use super::*;
    use assert_matches::assert_matches;
    use pathfinder_common::{felt, felt_bytes};

    mod parsing {
        use super::*;
        use jsonrpsee::types::Params;
        use pathfinder_common::StarknetBlockHash;

        #[test]
        fn positional_args() {
            let positional = r#"[
                { "block_hash": "0xabcde" },
                "0x12345"
            ]"#;
            let positional = Params::new(Some(positional));

            let input = positional.parse::<GetClassHashAtInput>().unwrap();
            let expected = GetClassHashAtInput {
                block_id: StarknetBlockHash(felt!("0xabcde")).into(),
                contract_address: ContractAddress::new_or_panic(felt!("0x12345")),
            };
            assert_eq!(input, expected);
        }

        #[test]
        fn named_args() {
            let named = r#"{
                "block_id": { "block_hash": "0xabcde" },
                "contract_address": "0x12345"
            }"#;
            let named = Params::new(Some(named));

            let input = named.parse::<GetClassHashAtInput>().unwrap();
            let expected = GetClassHashAtInput {
                block_id: StarknetBlockHash(felt!("0xabcde")).into(),
                contract_address: ContractAddress::new_or_panic(felt!("0x12345")),
            };
            assert_eq!(input, expected);
        }
    }

    mod errors {
        use super::*;

        #[tokio::test]
        async fn contract_not_found() {
            let context = RpcContext::for_tests();

            let input = GetClassHashAtInput {
                block_id: BlockId::Latest,
                contract_address: ContractAddress::new_or_panic(felt_bytes!(b"invalid")),
            };
            let result = get_class_hash_at(context, input).await;
            assert_matches!(result, Err(GetClassHashAtError::ContractNotFound));
        }

        #[tokio::test]
        async fn block_not_found() {
            use pathfinder_common::StarknetBlockHash;

            let context = RpcContext::for_tests();

            let input = GetClassHashAtInput {
                block_id: BlockId::Hash(StarknetBlockHash(felt_bytes!(b"invalid"))),
                // This contract does exist and is added in block 0.
                contract_address: ContractAddress::new_or_panic(felt_bytes!(b"contract 0")),
            };
            let result = get_class_hash_at(context, input).await;
            assert_matches!(result, Err(GetClassHashAtError::BlockNotFound));
        }
    }

    #[tokio::test]
    async fn latest() {
        let context = RpcContext::for_tests();
        let expected = ClassHash(felt_bytes!(b"class 0 hash"));

        let input = GetClassHashAtInput {
            block_id: BlockId::Latest,
            contract_address: ContractAddress::new_or_panic(felt_bytes!(b"contract 0")),
        };
        let result = get_class_hash_at(context, input).await.unwrap();
        assert_eq!(result.0, expected);
    }

    #[tokio::test]
    async fn at_block() {
        use pathfinder_common::StarknetBlockNumber;
        let context = RpcContext::for_tests();

        // This contract is deployed in block 1.
        let address = ContractAddress::new_or_panic(felt_bytes!(b"contract 1"));

        let input = GetClassHashAtInput {
            block_id: StarknetBlockNumber::new_or_panic(0).into(),
            contract_address: address,
        };
        let result = get_class_hash_at(context.clone(), input).await;
        assert_matches!(result, Err(GetClassHashAtError::ContractNotFound));

        let expected = ClassHash(felt_bytes!(b"class 1 hash"));
        let input = GetClassHashAtInput {
            block_id: StarknetBlockNumber::new_or_panic(1).into(),
            contract_address: address,
        };
        let result = get_class_hash_at(context.clone(), input).await.unwrap();
        assert_eq!(result.0, expected);

        let input = GetClassHashAtInput {
            block_id: StarknetBlockNumber::new_or_panic(2).into(),
            contract_address: address,
        };
        let result = get_class_hash_at(context, input).await.unwrap();
        assert_eq!(result.0, expected);
    }

    #[tokio::test]
    async fn pending_defaults_to_latest() {
        let context = RpcContext::for_tests();
        let expected = ClassHash(felt_bytes!(b"class 0 hash"));

        let input = GetClassHashAtInput {
            block_id: BlockId::Pending,
            contract_address: ContractAddress::new_or_panic(felt_bytes!(b"contract 0")),
        };
        let result = get_class_hash_at(context, input).await.unwrap();
        assert_eq!(result.0, expected);
    }

    #[tokio::test]
    async fn pending() {
        let context = RpcContext::for_tests_with_pending().await;

        // This should still work even though it was deployed in an actual block.
        let expected = ClassHash(felt_bytes!(b"class 0 hash"));
        let input = GetClassHashAtInput {
            block_id: BlockId::Pending,
            contract_address: ContractAddress::new_or_panic(felt_bytes!(b"contract 0")),
        };
        let result = get_class_hash_at(context.clone(), input).await.unwrap();
        assert_eq!(result.0, expected);

        // This is an actual pending deployed contract.
        let expected = ClassHash(felt_bytes!(b"pending class 0 hash"));
        let input = GetClassHashAtInput {
            block_id: BlockId::Pending,
            contract_address: ContractAddress::new_or_panic(felt_bytes!(
                b"pending contract 0 address"
            )),
        };
        let result = get_class_hash_at(context.clone(), input).await.unwrap();
        assert_eq!(result.0, expected);

        // Replaced class in pending should also work.
        let expected = ClassHash(felt_bytes!(b"pending class 2 hash (replaced)"));
        let input = GetClassHashAtInput {
            block_id: BlockId::Pending,
            contract_address: ContractAddress::new_or_panic(felt_bytes!(
                b"pending contract 2 (replaced)"
            )),
        };
        let result = get_class_hash_at(context.clone(), input).await.unwrap();
        assert_eq!(result.0, expected);

        // This one remains missing.
        let input = GetClassHashAtInput {
            block_id: BlockId::Latest,
            contract_address: ContractAddress::new_or_panic(felt_bytes!(b"invalid")),
        };
        let result = get_class_hash_at(context, input).await;
        assert_matches!(result, Err(GetClassHashAtError::ContractNotFound));
    }
}
