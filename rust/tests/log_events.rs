// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Cross-binding log-event vocabulary parity (Slice R4a). Mirrors
//! `go/aletheia/log_events_test.go`, `python/tests/test_log_events_parity.py`,
//! and `cpp/tests/test_log_events_parity.cpp`: every event the Rust client emits
//! must be a member of the canonical vocabulary in `docs/LOG_EVENTS.yaml`, with
//! the same level. Catches a rogue / mistyped event name or a level drift.

use std::collections::HashMap;
use std::fs;
use std::path::Path;

use aletheia::log::events;
use aletheia::LogLevel;
use yaml_rust2::YamlLoader;

/// `name -> level` for every event in the canonical vocabulary.
fn yaml_vocabulary() -> HashMap<String, String> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../docs/LOG_EVENTS.yaml");
    let text = fs::read_to_string(&path).expect("read docs/LOG_EVENTS.yaml");
    let docs = YamlLoader::load_from_str(&text).expect("parse LOG_EVENTS.yaml");
    docs[0]["events"]
        .as_vec()
        .expect("events sequence")
        .iter()
        .map(|e| {
            (
                e["name"].as_str().expect("event name").to_string(),
                e["level"].as_str().expect("event level").to_string(),
            )
        })
        .collect()
}

/// The events the Rust client emits, paired with the level it emits them at.
/// Keep in lockstep with the emit sites in `lib.rs`.
fn rust_emitted() -> Vec<(&'static str, LogLevel)> {
    vec![
        (events::DBC_PARSED, LogLevel::Info),
        (events::PROPERTIES_SET, LogLevel::Info),
        (events::STREAM_STARTED, LogLevel::Info),
        (events::STREAM_ENDED, LogLevel::Info),
        (events::RTS_CORES_MISMATCH, LogLevel::Warn),
        (events::FRAME_PROCESSED, LogLevel::Debug),
        (events::ERROR_EVENT_SENT, LogLevel::Debug),
        (events::REMOTE_EVENT_SENT, LogLevel::Debug),
        (events::ENDSTREAM_UNCACHED_ATOM, LogLevel::Warn),
    ]
}

#[test]
fn vocabulary_is_the_canonical_sixteen() {
    assert_eq!(
        yaml_vocabulary().len(),
        16,
        "docs/LOG_EVENTS.yaml is the cross-binding canonical 16-event vocabulary"
    );
}

#[test]
fn every_rust_event_is_in_the_vocabulary_with_the_same_level() {
    let vocab = yaml_vocabulary();
    for (name, level) in rust_emitted() {
        let yaml_level = vocab
            .get(name)
            .unwrap_or_else(|| panic!("emitted event {name:?} is not in docs/LOG_EVENTS.yaml"));
        assert_eq!(
            yaml_level,
            &level.to_string(),
            "level mismatch for {name}: Rust emits {level}, YAML says {yaml_level}"
        );
    }
}
