use std::sync::Arc;
use std::time::Duration;

use pathfinder_ethereum::{EthereumClientApi, StarknetEthereumClient};
use primitive_types::H256;

/// Caching of `eth_gasPrice` with single request at a time refreshing.
///
/// The `gasPrice` is used for `estimate_fee` when user
/// requests for [`pathfinder_common::BlockId::Latest`] or  [`pathfinder_common::BlockId::Pending`].
#[derive(Clone)]
pub struct Cached {
    inner: Arc<std::sync::Mutex<Inner>>,
    eth: Arc<StarknetEthereumClient>,
    stale_limit: Duration,
}

impl Cached {
    pub fn new(eth: Arc<StarknetEthereumClient>) -> Self {
        Cached {
            inner: Default::default(),
            eth,
            stale_limit: Duration::from_secs(10),
        }
    }

    /// Returns either a fast fresh value, slower a periodically polled value or fails because
    /// polling has stopped.
    pub async fn get(&self) -> Option<H256> {
        let mut rx = {
            let mut g = self.inner.lock().unwrap_or_else(|e| e.into_inner());

            if let Some((fetched_at, gas_price)) = g.latest.as_ref() {
                if fetched_at.elapsed() < self.stale_limit {
                    // fresh
                    let accepted = *gas_price;
                    return Some(accepted);
                }
            }

            // clear stale since it's not going to be useful for anyone
            g.latest = None;

            // this is an adaptation of https://fasterthanli.me/articles/request-coalescing-in-async-rust

            if let Some(tx) = g.next.upgrade() {
                // there's already an existing request being fulfilled
                tx.subscribe()
            } else {
                let (tx, rx) = tokio::sync::broadcast::channel(1);

                // the use of Weak works here, because the only strong reference is being sent to
                // the async task, which upon completion holds the lock again while sending
                // everyone listening the response, and clears the weak.
                let tx = Arc::new(tx);

                let inner = self.inner.clone();
                let eth = self.eth.clone();

                g.next = Arc::downgrade(&tx);

                // in general, asking eth_gasPrice seems to be fast enough especially as we already
                // have a connection open because the EthereumTransport impl is being used for sync
                // as well.
                //
                // it being fast enough, allows us to just coalesce the requests, but also not poll
                // for fun while no one is using the gas estimation.
                tokio::spawn(async move {
                    let price = match eth.gas_price().await {
                        Ok(price) => price,
                        Err(_e) => {
                            let _ = tx.send(None);
                            return;
                        }
                    };

                    let now = std::time::Instant::now();

                    let mut out = [0u8; 32];
                    price.to_big_endian(&mut out[..]);
                    let gas_price = H256::from(out);

                    let mut g = inner.lock().unwrap_or_else(|e| e.into_inner());
                    g.latest.replace((now, gas_price));

                    let _ = tx.send(Some(gas_price));
                    drop(tx);
                    // when g is dropped and the mutex unlocked, no one will be able to upgrade
                    // the weak, because the only strong has been dropped.
                });

                rx
            }
        };

        rx.recv().await.ok().flatten()
    }
}

#[derive(Default)]
struct Inner {
    latest: Option<(std::time::Instant, H256)>,
    next: std::sync::Weak<tokio::sync::broadcast::Sender<Option<H256>>>,
}
