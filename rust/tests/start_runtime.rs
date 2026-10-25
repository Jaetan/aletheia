// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! `aletheia::start_runtime` starts the kernel's runtime before any client: a
//! program starts it, loads checks holding decimals and hands them to the
//! builder's default checks; a client naming no core count asks for the count
//! running. Its own test binary (= its own process) because the claims are
//! about a process whose runtime nothing has started, and one test because the
//! steps share that one start.

use std::sync::{Arc, Mutex};

use aletheia::log::events;
use aletheia::{
    load_checks_from_yaml, CanId, Client, Dlc, Error, FrameResponse, LogRecord, Logger, Rational,
    Timestamp, Verdict,
};

// EngineSpeed's factor 0.25 decodes raw 800 to 200 rpm, past the 199.5 limit.
const DBC: &str = "VERSION \"\"\n\nNS_ :\n\nBS_:\n\nBU_: ECU\n\nBO_ 256 EngineStatus: 8 ECU\n SG_ EngineSpeed : 0|16@1+ (0.25,0) [0|8000] \"rpm\" ECU\n";
const CHECKS: &str = "checks:\n  - name: Speed limit\n    signal: EngineSpeed\n    condition: never_exceeds\n    value: 199.5\n    severity: critical\n";

/// A logger keeping each record as one line: the event, then `key=value` per field.
#[derive(Clone, Default)]
struct Captured(Arc<Mutex<Vec<String>>>);

impl Logger for Captured {
    fn log(&self, rec: &LogRecord) {
        let fields: Vec<String> = rec
            .fields
            .iter()
            .map(|f| format!("{}={:?}", f.key, f.value))
            .collect();
        self.0
            .lock()
            .expect("lock")
            .push(format!("{} {}", rec.event, fields.join(" ")));
    }
}

impl Captured {
    fn mismatches(&self) -> Vec<String> {
        self.0
            .lock()
            .expect("lock")
            .iter()
            .filter(|line| line.starts_with(events::RTS_CORES_MISMATCH))
            .cloned()
            .collect()
    }
}

#[test]
fn default_checks_holding_a_decimal_load_after_a_start_and_a_count_less_client_runs_silent() {
    // Before any start a number read is refused, naming the remedy, and the
    // allocation count answers none.
    assert_eq!(aletheia::allocated_bytes(), None);
    let refused = Rational::from_decimal("1.5").expect_err("no runtime runs yet");
    assert!(
        matches!(refused, Error::RtsNotInitialized),
        "got: {refused:?}"
    );
    assert_eq!(
        refused.to_string(),
        "GHC runtime not initialized: call aletheia::start_runtime or build a Client before \
         rendering or parsing a number"
    );
    // Zero is outside the bound on every machine; the bound's own figure is the
    // machine's, which the stand-in test holds whole on its four CPUs.
    let zero = aletheia::start_runtime(0, None).expect_err("zero cores");
    assert!(
        matches!(&zero, Error::Validation { message, .. }
            if message.starts_with("core count 0 is outside 1 to ")
                && message.ends_with(", the CPUs this process may use")),
        "got: {zero:?}"
    );
    assert_eq!(aletheia::allocated_bytes(), None);

    aletheia::start_runtime(1, None).expect("start the runtime on one core");
    assert!(aletheia::allocated_bytes().is_some());
    assert_eq!(
        Rational::from_decimal("1.5").expect("a decimal"),
        Rational::new(3, 2).expect("3/2")
    );

    let checks = load_checks_from_yaml(CHECKS).expect("checks holding 199.5");
    let log = Captured::default();
    let client = Client::builder()
        .default_checks(checks)
        .logger(log.clone())
        .build()
        .expect("a client naming no count");
    client.parse_dbc_text(DBC).expect("parse DBC text");
    client.add_checks(&[]).expect("add the default checks");
    client.start_stream().expect("start stream");
    let id = CanId::standard(256).expect("id");
    let dlc = Dlc::new(8).expect("dlc");
    let resp = client
        .send_frame(
            Timestamp(1_000),
            id,
            dlc,
            &[0x20, 0x03, 0, 0, 0, 0, 0, 0],
            None,
            None,
        )
        .expect("send frame");
    match resp {
        FrameResponse::Verdicts(results) => assert!(
            results
                .iter()
                .any(|r| r.verdict == Verdict::Fails && r.property_index == 0),
            "the default check holding 199.5 did not fail on 200 rpm: {results:?}"
        ),
        FrameResponse::Ack => panic!("the default check holding 199.5 did not fail on 200 rpm"),
    }
    assert_eq!(log.mismatches(), Vec::<String>::new());

    // Another count asked of the runtime on one is warned, from a start and a
    // client alike; the count running asked again is not.
    aletheia::start_runtime(1, Some(&log)).expect("the running count again");
    aletheia::start_runtime(2, Some(&log)).expect("another count");
    let _two = Client::builder()
        .rts_cores(2)
        .logger(log.clone())
        .build()
        .expect("a client asking two");
    let warned = format!(
        "{} active_cores=U64(1) requested_cores=U64(2)",
        events::RTS_CORES_MISMATCH
    );
    assert_eq!(log.mismatches(), vec![warned.clone(), warned]);
}
