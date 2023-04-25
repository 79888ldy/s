use anyhow::Context;
use pathfinder_common::{ChainId, StarknetBlockNumber};
use pathfinder_storage::{
    JournalMode, StarknetBlocksBlockId, StarknetBlocksTable, StarknetTransactionsTable, Storage,
};

/// Verify block hashes in a pathfinder database.
///
/// Iterates over all blocks in the database and verifies if the computed block hash matches
/// values we store for the block.
///
/// Usage:
/// `cargo run --release -p pathfinder --example verify_block_hashes mainnet ./mainnet.sqlite`
/// Either mainnet or goerli is accepted as the chain name.
fn main() -> anyhow::Result<()> {
    let chain_name = std::env::args().nth(1).unwrap();
    let chain_id = match chain_name.as_str() {
        "mainnet" => ChainId::MAINNET,
        "testnet" => ChainId::TESTNET,
        "testnet2" => ChainId::TESTNET2,
        "integration" => ChainId::INTEGRATION,
        _ => panic!("Expected chain name: mainnet/goerli/integration"),
    };

    let database_path = std::env::args().nth(2).unwrap();
    let storage = Storage::migrate(database_path.into(), JournalMode::WAL)?;
    let mut db = storage
        .connection()
        .context("Opening database connection")?;

    let latest_block_number = {
        let tx = db.transaction().unwrap();
        StarknetBlocksTable::get_latest_number(&tx)?.unwrap()
    };

    for block_number in 0..latest_block_number.get() {
        let tx = db.transaction().unwrap();
        let block_id =
            StarknetBlocksBlockId::Number(StarknetBlockNumber::new_or_panic(block_number));
        let block = StarknetBlocksTable::get(&tx, block_id)?.unwrap();
        let transactions_and_receipts =
            StarknetTransactionsTable::get_transaction_data_for_block(&tx, block_id)?;
        drop(tx);

        let (transactions, _): (Vec<_>, Vec<_>) = transactions_and_receipts.into_iter().unzip();

        let result = pathfinder_rpc::cairo::starknet_rs::estimate_fee_for_gateway_transactions(
            storage.clone(),
            block.storage_commitment,
            transactions,
            chain_id,
            block.gas_price.0.into(),
        )?;
    }

    Ok(())
}
