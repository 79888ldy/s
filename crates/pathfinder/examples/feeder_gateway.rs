use std::collections::HashMap;

use anyhow::Context;
use pathfinder_common::{
    Chain, ClassHash, ContractAddress, ContractNonce, StarknetBlockHash, StarknetBlockNumber,
};
use pathfinder_ethereum::contract::ContractAddresses;
use pathfinder_storage::{
    StarknetBlocksBlockId, StarknetBlocksTable, StarknetStateUpdatesTable,
    StarknetTransactionsTable,
};
use serde::Deserialize;
use stark_hash::Felt;
use starknet_gateway_types::reply::{
    state_update::{DeclaredSierraClass, DeployedContract, ReplacedClass, StorageDiff},
    Status,
};
use tracing_subscriber::{fmt, prelude::*, EnvFilter};
use warp::Filter;

/// Serve feeder gateway REST endpoints required for pathfinder to sync.
///
/// Usage:
/// `cargo run --release -p pathfinder --example feeder_gateway ./testnet2.sqlite`
///
/// Then pathfinder can be run with the following arguments to use this tool as a sync source:
///
/// ```text
/// cargo run --release -p pathfinder -- \
///     --network custom --chain-id SN_GOERLI2 \
///     --gateway-url http://localhost:8080/gateway \
///     --feeder-gateway-url http://localhost:8080/feeder_gateway \
///     --data-directory /tmp
/// ```
#[tokio::main]
async fn main() -> anyhow::Result<()> {
    tracing_subscriber::registry()
        .with(fmt::layer())
        .with(EnvFilter::from_default_env())
        .init();
    serve().await
}

async fn serve() -> anyhow::Result<()> {
    let database_path = std::env::args().nth(1).unwrap();
    let storage = pathfinder_storage::Storage::migrate(
        database_path.into(),
        pathfinder_storage::JournalMode::WAL,
    )?;

    let chain = {
        let mut connection = storage.connection()?;
        let tx = connection.transaction()?;
        get_chain(&tx)?
    };

    let get_contract_addresses = warp::path("get_contract_addresses").map(move || {
        let addresses = contract_addresses(chain).unwrap();
        let reply =
            serde_json::json!({"GpsStatementVerifier": addresses.gps, "Starknet": addresses.core});
        warp::reply::json(&reply)
    });

    #[derive(Debug, Deserialize)]
    struct BlockIdParam {
        #[serde(default, rename = "blockNumber")]
        block_number: Option<String>,
        #[serde(default, rename = "blockHash")]
        block_hash: Option<StarknetBlockHash>,
    }

    impl TryInto<StarknetBlocksBlockId> for BlockIdParam {
        type Error = ();

        fn try_into(self) -> Result<StarknetBlocksBlockId, Self::Error> {
            if let Some(n) = self.block_number {
                if n == "latest" {
                    return Ok(StarknetBlocksBlockId::Latest);
                } else {
                    let n: u64 = n.parse().map_err(|_| ())?;
                    return Ok(StarknetBlocksBlockId::Number(
                        StarknetBlockNumber::new_or_panic(n),
                    ));
                }
            }

            if let Some(h) = self.block_hash {
                return Ok(StarknetBlocksBlockId::Hash(h));
            }
            Err(())
        }
    }

    let get_block = warp::path("get_block")
        .and(warp::query::<BlockIdParam>())
        .and_then({
            let storage = storage.clone();
            move |block_id: BlockIdParam| {
                let storage = storage.clone();
                async move {
                    match block_id.try_into() {
                        Ok(block_id) => {
                            let block = tokio::task::spawn_blocking(move || {
                                let mut connection = storage.connection().unwrap();
                                let tx = connection.transaction().unwrap();

                                resolve_block(&tx, block_id)
                            }).await.unwrap();

                            match block {
                                Ok(block) => {
                                    Ok(warp::reply::json(&block))
                                },
                                Err(_) => {
                                    let error = serde_json::json!({"code": "StarknetErrorCode.BLOCK_NOT_FOUND", "message": "Block number not found"});
                                    Ok(warp::reply::json(&error))
                                }
                            }
                        },
                        Err(_) => Err(warp::reject::reject()),
                    }
                }
            }
        });

    let get_state_update = warp::path("get_state_update")
        .and(warp::query::<BlockIdParam>())
        .and_then({
            let storage = storage.clone();
            move |block_id: BlockIdParam| {
                let storage = storage.clone();
                async move {
                    match block_id.try_into() {
                        Ok(block_id) => {
                            let state_update = tokio::task::spawn_blocking(move || {
                                let mut connection = storage.connection().unwrap();
                                let tx = connection.transaction().unwrap();

                                resolve_state_update(&tx, block_id)
                            }).await.unwrap();

                            match state_update {
                                Ok(state_update) => {
                                    Ok(warp::reply::json(&state_update))
                                },
                                Err(_) => {
                                    let error = serde_json::json!({"code": "StarknetErrorCode.BLOCK_NOT_FOUND", "message": "Block number not found"});
                                    Ok(warp::reply::json(&error))
                                }
                            }
                        },
                        Err(_) => Err(warp::reject::reject()),
                    }
                }
            }
        });

    #[derive(Debug, Deserialize)]
    struct ClassHashParam {
        #[serde(rename = "classHash")]
        class_hash: ClassHash,
    }

    let get_class_by_hash = warp::path("get_class_by_hash")
        .and(warp::query::<ClassHashParam>())
        .then({
            let storage = storage.clone();
            move |class_hash: ClassHashParam| {
                let storage = storage.clone();
                async move {
                    let class = tokio::task::spawn_blocking(move || {
                        let mut connection = storage.connection().unwrap();
                        let tx = connection.transaction().unwrap();

                        resolve_class(&tx, class_hash.class_hash)
                    }).await.unwrap();

                    match class {
                        Ok(class) => {
                            let response = warp::http::Response::builder().header("content-type", "application/json").body(class).unwrap();
                            Ok(response)
                        },
                        Err(_) => {
                            let error = r#"{"code": "StarknetErrorCode.UNDECLARED_CLASS", "message": "Class not found"}"#;
                            let response = warp::http::Response::builder().status(500).body(error.as_bytes().to_owned()).unwrap();
                            Ok(response)
                        }
                    }
                }
            }
        });

    let handler = warp::get()
        .and(warp::path("feeder_gateway"))
        .and(
            get_block
                .or(get_state_update)
                .or(get_contract_addresses)
                .or(get_class_by_hash),
        )
        .with(warp::filters::trace::request());

    warp::serve(handler).run(([127, 0, 0, 1], 8080)).await;

    Ok(())
}

fn get_chain(tx: &rusqlite::Transaction<'_>) -> anyhow::Result<Chain> {
    use pathfinder_common::consts::{
        INTEGRATION_GENESIS_HASH, MAINNET_GENESIS_HASH, TESTNET2_GENESIS_HASH, TESTNET_GENESIS_HASH,
    };

    let genesis_hash = StarknetBlocksTable::get_hash(tx, StarknetBlockNumber::GENESIS.into())
        .unwrap()
        .context("Getting genesis hash")?;

    let chain = match genesis_hash {
        MAINNET_GENESIS_HASH => Chain::Mainnet,
        TESTNET_GENESIS_HASH => Chain::Testnet,
        TESTNET2_GENESIS_HASH => Chain::Testnet2,
        INTEGRATION_GENESIS_HASH => Chain::Integration,
        _other => Chain::Custom,
    };

    Ok(chain)
}

fn contract_addresses(chain: Chain) -> anyhow::Result<ContractAddresses> {
    use pathfinder_ethereum::contract::{
        INTEGRATION_ADDRESSES, MAINNET_ADDRESSES, TESTNET2_ADDRESSES, TESTNET_ADDRESSES,
    };
    let addresses = match chain {
        Chain::Mainnet => MAINNET_ADDRESSES,
        Chain::Testnet => TESTNET_ADDRESSES,
        Chain::Integration => INTEGRATION_ADDRESSES,
        Chain::Testnet2 => TESTNET2_ADDRESSES,
        Chain::Custom => anyhow::bail!("Unexpected chain"),
    };

    Ok(addresses)
}

fn resolve_block(
    tx: &rusqlite::Transaction<'_>,
    block_id: StarknetBlocksBlockId,
) -> anyhow::Result<starknet_gateway_types::reply::Block> {
    let block =
        pathfinder_storage::StarknetBlocksTable::get(tx, block_id)?.context("Fetching block")?;

    let parent_hash = match block.number {
        StarknetBlockNumber::GENESIS => StarknetBlockHash(Felt::ZERO),
        other => {
            let parent_block = StarknetBlocksTable::get(tx, (other - 1).into())
                .context("Read parent block from database")?
                .context("Parent block missing")?;

            parent_block.hash
        }
    };

    let transactions_receipts =
        StarknetTransactionsTable::get_transaction_data_for_block(tx, block.number.into())
            .context("Reading transactions from database")?;

    let (transactions, transaction_receipts): (Vec<_>, Vec<_>) =
        transactions_receipts.into_iter().unzip();

    let block_status = get_block_status(tx, block.number)?;
    let block_version = StarknetBlocksTable::get_version(tx, block_id)?;

    Ok(starknet_gateway_types::reply::Block {
        block_hash: block.hash,
        block_number: block.number,
        gas_price: Some(block.gas_price),
        parent_block_hash: parent_hash,
        sequencer_address: Some(block.sequencer_address),
        state_commitment: block.state_commmitment,
        status: block_status,
        timestamp: block.timestamp,
        transaction_receipts,
        transactions,
        starknet_version: block_version,
    })
}

fn get_block_status(
    tx: &rusqlite::Transaction<'_>,
    block_number: StarknetBlockNumber,
) -> anyhow::Result<Status> {
    // All our data is L2 accepted, check our L1-L2 head to see if this block has been accepted on L1.
    let l1_l2_head = pathfinder_storage::RefsTable::get_l1_l2_head(tx)
        .context("Read latest L1 head from database")?;
    let block_status = match l1_l2_head {
        Some(number) if number >= block_number => Status::AcceptedOnL1,
        _ => Status::AcceptedOnL2,
    };

    Ok(block_status)
}

fn resolve_state_update(
    tx: &rusqlite::Transaction<'_>,
    block_id: StarknetBlocksBlockId,
) -> anyhow::Result<starknet_gateway_types::reply::StateUpdate> {
    let block_hash = match block_id {
        StarknetBlocksBlockId::Hash(h) => h,
        StarknetBlocksBlockId::Number(_) | StarknetBlocksBlockId::Latest => {
            StarknetBlocksTable::get_hash(tx, block_id.try_into().expect("block_id is not a hash"))?
                .context("Read block hash from database")?
        }
    };

    let state_update = StarknetStateUpdatesTable::get(tx, block_hash)?
        .context("Read state update from database")?;

    let mut storage_diffs: HashMap<ContractAddress, Vec<StorageDiff>> = HashMap::new();
    for d in state_update.state_diff.storage_diffs {
        storage_diffs
            .entry(d.address)
            .or_default()
            .push(StorageDiff {
                key: d.key,
                value: d.value,
            });
    }

    let nonces: HashMap<ContractAddress, ContractNonce> = state_update
        .state_diff
        .nonces
        .into_iter()
        .map(|n| (n.contract_address, n.nonce))
        .collect();

    Ok(starknet_gateway_types::reply::StateUpdate {
        block_hash,
        new_root: state_update.new_root,
        old_root: state_update.old_root,
        state_diff: starknet_gateway_types::reply::state_update::StateDiff {
            storage_diffs,
            deployed_contracts: state_update
                .state_diff
                .deployed_contracts
                .into_iter()
                .map(|d| DeployedContract {
                    address: d.address,
                    class_hash: d.class_hash,
                })
                .collect(),
            old_declared_contracts: state_update
                .state_diff
                .declared_contracts
                .into_iter()
                .map(|c| c.class_hash)
                .collect(),
            declared_classes: state_update
                .state_diff
                .declared_sierra_classes
                .into_iter()
                .map(|c| DeclaredSierraClass {
                    class_hash: c.class_hash,
                    compiled_class_hash: c.compiled_class_hash,
                })
                .collect(),
            nonces,
            replaced_classes: state_update
                .state_diff
                .replaced_classes
                .into_iter()
                .map(|r| ReplacedClass {
                    address: r.address,
                    class_hash: r.class_hash,
                })
                .collect(),
        },
    })
}

fn resolve_class(tx: &rusqlite::Transaction<'_>, class_hash: ClassHash) -> anyhow::Result<Vec<u8>> {
    use rusqlite::OptionalExtension;

    tracing::info!(%class_hash, "Resolving class hash");

    let definition = tx
        .query_row(
            r"SELECT definition FROM class_definitions WHERE hash = ?",
            [class_hash],
            |row| {
                let def = row.get_ref_unwrap(0).as_blob()?.to_owned();
                Ok(def)
            },
        )
        .optional()
        .context("Reading class definition from database")?
        .ok_or_else(|| anyhow::anyhow!("No such class found"))?;

    let definition = zstd::decode_all(&*definition).context("Decompressing class definition")?;

    Ok(definition)
}
