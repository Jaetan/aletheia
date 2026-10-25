// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! The core count a start or a client asks is held to one through the CPUs the
//! process may use, as the runtime of the library counts them, and the answer
//! names the bound. The recording kernel counts four CPUs whatever the machine
//! and its runtime entry is a no-op, so the runtime reads as started on the
//! count asked. Its own test binary (= its own process) because a library
//! stays loaded for the process lifetime and this one must be the first the
//! process loads, and one test because the steps share that one start.

mod stand_in;

use aletheia::{Client, Error};

fn refusal(cores: u32) -> String {
    format!("core count {cores} is outside 1 to 4, the CPUs this process may use")
}

#[test]
fn counts_are_held_to_the_cpus_the_runtime_counts_and_a_count_less_client_asks_the_running_one() {
    std::env::set_var("ALETHEIA_LIB", stand_in::stand_in("recording_kernel"));
    for cores in [0, 5] {
        let started = aletheia::start_runtime(cores, None).expect_err("outside the bound");
        assert!(
            matches!(&started, Error::Validation { message, .. } if *message == refusal(cores)),
            "got: {started:?}"
        );
        let built = Client::builder()
            .rts_cores(cores)
            .build()
            .err()
            .expect("outside the bound");
        assert!(
            matches!(&built, Error::Validation { message, .. } if *message == refusal(cores)),
            "got: {built:?}"
        );
    }
    assert_eq!(aletheia::allocated_bytes(), None);

    aletheia::start_runtime(2, None).expect("start the stand-in's runtime on two");
    let captured = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
    let sink = std::sync::Arc::clone(&captured);
    let logger = move |rec: &aletheia::LogRecord| {
        sink.lock().expect("lock").push(rec.event.to_string());
    };
    let _count_less = Client::builder()
        .logger(logger.clone())
        .build()
        .expect("a client naming no count");
    assert!(captured.lock().expect("lock").is_empty());
    let _one = Client::builder()
        .rts_cores(1)
        .logger(logger)
        .build()
        .expect("a client asking one of a runtime on two");
    assert_eq!(
        *captured.lock().expect("lock"),
        vec![aletheia::log::events::RTS_CORES_MISMATCH.to_string()]
    );
}
