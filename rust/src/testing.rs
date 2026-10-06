// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Deterministic scaffolding for testing code that uses the async client
//! (feature `async`).
//!
//! [`TurnExecutor`] stands in for the [`AsyncClient`]'s worker thread: it hosts
//! a sync [`Client`] the test built, and runs each call queued on it on the
//! test's own thread, one per turn, in the order the calls were queued. A call
//! whose future is dropped before its turn never reaches the client, as a
//! queued job the worker skips; once its turn comes it runs to completion, as a
//! job the worker has started does. Every run therefore takes the same path,
//! and no test needs a thread, a timer or a runtime. It lives in the crate
//! proper, beside the client it serves, so consumers testing their own async
//! usage have it too.
//!
//! ```no_run
//! use aletheia::testing::TurnExecutor;
//! use aletheia::Client;
//!
//! let turns = TurnExecutor::new();
//! let client = turns.adopt(Client::new()?);
//! let pong = turns.block_on(client.process(r#"{"command":"ping"}"#.to_string()))?;
//! # Ok::<(), aletheia::Error>(())
//! ```

use std::cell::RefCell;
use std::future::Future;
use std::pin::pin;
use std::sync::mpsc::{self, Receiver, TryRecvError};
use std::task::{Context, Poll, Waker};

use crate::async_client::Job;
use crate::{AsyncClient, Client};

/// One hosted client and the queue of calls made on its async handle.
struct Hosted {
    client: Client,
    jobs: Receiver<Job>,
}

/// Runs the calls of the async clients it hosts on the calling thread, one per
/// turn; see the module docs.
#[derive(Default)]
pub struct TurnExecutor {
    hosted: RefCell<Vec<Hosted>>,
}

impl TurnExecutor {
    /// An executor hosting no client.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Host `client` and return the async handle whose calls this executor runs.
    #[must_use]
    pub fn adopt(&self, client: Client) -> AsyncClient {
        let (jobs, queue) = mpsc::channel();
        self.hosted.borrow_mut().push(Hosted {
            client,
            jobs: queue,
        });
        AsyncClient::hosted(jobs)
    }

    /// Run one turn: the oldest queued call of the first hosted client, in
    /// the order they were adopted, that has one. Answers whether a call ran.
    ///
    /// A client whose handle has been dropped and whose queue is empty is
    /// closed here, as the worker closes it once its channel closes.
    pub fn run_turn(&self) -> bool {
        let mut hosted = self.hosted.borrow_mut();
        let mut index = 0;
        while index < hosted.len() {
            match hosted[index].jobs.try_recv() {
                Ok(job) => {
                    job(&hosted[index].client);
                    return true;
                }
                Err(TryRecvError::Empty) => index += 1,
                Err(TryRecvError::Disconnected) => drop(hosted.remove(index)),
            }
        }
        false
    }

    /// Drive `future` to its output, running one turn each time it waits.
    ///
    /// # Panics
    /// When `future` waits while no hosted client has a call queued: nothing
    /// this executor runs can wake it, so the test would otherwise hang.
    pub fn block_on<F: Future>(&self, future: F) -> F::Output {
        let mut future = pin!(future);
        let mut cx = Context::from_waker(Waker::noop());
        loop {
            if let Poll::Ready(output) = future.as_mut().poll(&mut cx) {
                return output;
            }
            assert!(
                self.run_turn(),
                "the future waits, and no client this executor hosts has a call queued"
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use std::cell::Cell;
    use std::rc::Rc;

    use super::TurnExecutor;
    use crate::{Client, MockBackend};

    const PING: &str = r#"{"command":"ping"}"#;
    const ACK: &str = r#"{"status":"ack"}"#;

    fn mock_client(mock: &MockBackend) -> Client {
        Client::builder().build_with_backend(Box::new(mock.clone()))
    }

    #[test]
    #[should_panic(expected = "no client this executor hosts has a call queued")]
    fn a_future_waiting_on_nothing_queued_fails_rather_than_hangs() {
        let turns = TurnExecutor::new();
        turns.block_on(std::future::pending::<()>());
    }

    #[test]
    fn calls_run_in_the_order_they_were_queued_across_clients() {
        let turns = TurnExecutor::new();
        let first = MockBackend::new();
        let second = MockBackend::new();
        first.respond_json(ACK);
        second.respond_json(ACK);
        let a = turns.adopt(mock_client(&first));
        let b = turns.adopt(mock_client(&second));
        let order = Rc::new(Cell::new(0u8));
        let (seen_a, seen_b) = turns.block_on(async {
            let one = async {
                let _ = a.process(PING.to_string()).await;
                order.set(order.get() * 10 + 1);
            };
            let two = async {
                let _ = b.process(PING.to_string()).await;
                order.set(order.get() * 10 + 2);
            };
            futures_util::future::join(one, two).await;
            (first.captured(), second.captured())
        });
        assert_eq!(seen_a, vec![PING.to_string()]);
        assert_eq!(seen_b, vec![PING.to_string()]);
        assert_eq!(
            order.get(),
            12,
            "a's call was queued first, so it ran first"
        );
    }

    #[test]
    fn a_dropped_handle_s_client_is_closed_at_the_next_turn() {
        let turns = TurnExecutor::new();
        let kept = turns.adopt(mock_client(&MockBackend::new()));
        let dropped = turns.adopt(mock_client(&MockBackend::new()));
        drop(dropped);
        assert_eq!(
            turns.hosted.borrow().len(),
            2,
            "nothing runs between a drop and the next turn"
        );
        assert!(!turns.run_turn(), "neither queue holds a call");
        assert_eq!(
            turns.hosted.borrow().len(),
            1,
            "the turn closed the dropped handle's client"
        );
        drop(kept);
    }
}
