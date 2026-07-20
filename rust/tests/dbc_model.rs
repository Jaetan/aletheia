// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Typed DBC document tests against the real `libaletheia-ffi.so`.
//!
//! Exercises the read side of the typed DBC API: `parse_dbc_text` returning the
//! typed [`Dbc`], the `format_dbc` export round-trip, and the mux-query / lookup
//! helpers. Set `ALETHEIA_LIB` to the built shared library (run_ci / CI does).

use aletheia::{CanId, Client, Presence};

/// The shared corpus `multiplexing.dbc` — two messages, single-multiplexor each.
const DBC: &str = include_str!("../../python/tests/fixtures/dbc_corpus/multiplexing.dbc");

fn client() -> Client {
    Client::new().expect("init client — is ALETHEIA_LIB set to a built libaletheia-ffi.so?")
}

#[test]
fn parse_dbc_text_returns_typed_document() {
    let c = client();
    let dbc = c.parse_dbc_text(DBC).expect("parse DBC text").dbc;

    let m = dbc
        .message_by_id(CanId::standard(100).expect("valid id"))
        .expect("message 100 present");
    assert!(m.is_multiplexed());
    assert_eq!(m.multiplexor_names(), vec!["Mode"]);

    let payload_a = m.signal_by_name("PayloadA").expect("PayloadA present");
    match &payload_a.presence {
        Presence::Multiplexed {
            multiplexor,
            values,
        } => {
            assert_eq!(multiplexor, "Mode");
            assert_eq!(values, &[0]);
        }
        Presence::Always => panic!("PayloadA should be multiplexed"),
    }

    // Lookup helpers resolve.
    assert!(dbc.message_by_name(&m.name).is_some());
}

#[test]
fn format_dbc_round_trips_the_loaded_document() {
    let c = client();
    let parsed = c.parse_dbc_text(DBC).expect("parse DBC text").dbc;
    let exported = c.format_dbc().expect("format_dbc export");
    assert_eq!(
        parsed, exported,
        "parse_dbc_text then format_dbc must yield the same typed document"
    );
}

/// The attribute-bearing corpus fixture, so the round-trip is exercised against
/// the full typed `BA_*` vocabulary.
const ATTRS_DBC: &str = include_str!("../../python/tests/fixtures/dbc_corpus/attributes.dbc");

#[test]
fn format_dbc_round_trips_typed_attributes() {
    let c = client();
    let parsed = c
        .parse_dbc_text(ATTRS_DBC)
        .expect("parse attributes DBC")
        .dbc;
    assert!(
        !parsed.attributes.is_empty(),
        "attributes.dbc must carry attributes to exercise the typed model"
    );
    let exported = c.format_dbc().expect("format_dbc export");
    assert_eq!(
        parsed.attributes, exported.attributes,
        "the typed attribute vocabulary must survive parse → format_dbc"
    );
}

/// The comprehensive corpus fixture — messages, multiplexing, value tables,
/// env vars, signal groups, comments, and the full attribute vocabulary — so
/// the serialize round-trips exercise every part of `Dbc::to_value`.
const KITCHEN: &str = include_str!("../../python/tests/fixtures/dbc_corpus/kitchen_sink.dbc");

#[test]
fn parse_dbc_round_trips_the_serialized_document() {
    let c = client();
    let from_text = c.parse_dbc_text(KITCHEN).expect("parse DBC text").dbc;
    // parse_dbc serializes the typed document and feeds it back through the core
    // (the JSON path); a correct serialize re-parses to the same document.
    let from_json = c.parse_dbc(&from_text).expect("parse_dbc (JSON path)").dbc;
    assert_eq!(
        from_text, from_json,
        "parse_dbc_text → parse_dbc must round-trip the typed document"
    );
}

#[test]
fn format_dbc_text_round_trips_through_the_formatter() {
    let c = client();
    let from_text = c.parse_dbc_text(KITCHEN).expect("parse DBC text").dbc;
    // serialize → core .dbc formatter → re-parse must be the identity.
    let text = c.format_dbc_text(&from_text).expect("format_dbc_text").text;
    let reparsed = c
        .parse_dbc_text(&text)
        .expect("re-parse formatted text")
        .dbc;
    assert_eq!(
        from_text, reparsed,
        "format_dbc_text output must re-parse to the same typed document"
    );
}

#[test]
fn validate_dbc_reports_no_errors_for_the_valid_corpus() {
    let c = client();
    let dbc = c.parse_dbc_text(KITCHEN).expect("parse DBC text").dbc;
    let result = c.validate_dbc(&dbc).expect("validate_dbc");
    assert!(
        !result.has_errors,
        "kitchen_sink is a valid DBC — validation found errors: {:?}",
        result.issues
    );
}

#[test]
fn validate_dbc_flags_an_invalid_document() {
    let c = client();
    let mut dbc = c.parse_dbc_text(KITCHEN).expect("parse DBC text").dbc;
    // Give two messages the same CAN ID: a structural error the validator
    // must report (pins the has_errors == true branch the valid-corpus test
    // never reaches).  Geometry violations no longer serve here — shrinking
    // a DLC under its signals is refused by the shared entry gate with a
    // typed parse error before the validator runs.
    let first_id = dbc.messages.first().expect("a message").id;
    let second = dbc.messages.get_mut(1).expect("a second message");
    second.id = first_id;
    let result = c.validate_dbc(&dbc).expect("validate_dbc");
    assert!(result.has_errors, "a duplicate CAN ID must be an error");
    assert!(!result.issues.is_empty(), "errors must carry issues");
}

#[test]
fn validate_dbc_refuses_out_of_frame_geometry_at_the_gate() {
    let c = client();
    let mut dbc = c.parse_dbc_text(KITCHEN).expect("parse DBC text").dbc;
    // Shrink a populated message to 0 bytes: every signal's geometry is now
    // outside the frame capacity, and the shared entry gate refuses the
    // document with a typed parse error naming the submitted values —
    // before any validation issue list is produced.
    let msg = dbc
        .messages
        .iter_mut()
        .find(|m| !m.signals.is_empty())
        .expect("a message with signals");
    msg.dlc = 0;
    let err = c
        .validate_dbc(&dbc)
        .expect_err("gate must refuse dlc=0 with signals");
    let aletheia::Error::Core { code, .. } = err else {
        panic!("expected a typed core refusal, got {err:?}");
    };
    assert!(
        code.starts_with("parse_signal_"),
        "expected a parse_signal_* geometry refusal, got {code}"
    );
}

/// A signal spanning the whole 64-byte CAN-FD frame is kernel-legal (the
/// entry gate checks per-frame fit), so the binding's response decoder must
/// accept the echo rather than re-rejecting it with a stale classic-CAN
/// bit-length cap — the decode guard is only the type-level ceiling.
const FULL_FRAME_FD: &str = "VERSION \"\"\n\nNS_ :\n\nBS_:\n\nBU_: Engine\n\nBO_ 100 Wide: 64 Engine\n SG_ Blob : 0|512@1+ (1,0) [0|0] \"\" Engine\n";

/// The textbook Motorola layout — MSB at bit 7, descending through the whole
/// DLC-2 frame — loads on the text route and the SAME document is accepted
/// back by the JSON route (kernel closure under its own emission).
const MOTOROLA_FULL_FRAME: &str = "VERSION \"\"\n\nNS_ :\n\nBS_:\n\nBU_: Engine\n\nBO_ 100 Msg: 2 Engine\n SG_ Sig : 7|16@0+ (1,0) [0|0] \"\" Engine\n";

#[test]
fn motorola_full_frame_signal_closes_over_both_routes() {
    let c = client();
    let loaded = c
        .parse_dbc_text(MOTOROLA_FULL_FRAME)
        .expect("text route")
        .dbc;
    let sig = &loaded.messages[0].signals[0];
    assert_eq!((sig.start_bit, sig.length), (7, 16));

    let echoed = c.parse_dbc(&loaded).expect("JSON route echo").dbc;
    let sig = &echoed.messages[0].signals[0];
    assert_eq!((sig.start_bit, sig.length), (7, 16));
}

#[test]
fn full_frame_fd_signal_decodes_through_both_routes() {
    let c = client();
    let loaded = c.parse_dbc_text(FULL_FRAME_FD).expect("text route").dbc;
    let sig = &loaded.messages[0].signals[0];
    assert_eq!((sig.start_bit, sig.length), (0, 512));

    let echoed = c.parse_dbc(&loaded).expect("JSON route echo").dbc;
    let sig = &echoed.messages[0].signals[0];
    assert_eq!((sig.start_bit, sig.length), (0, 512));
}

// ── warning-class validator mirrors of the round-trip mux diagnostics ───────
//
// CHECK 24 (multi_value_mux_selector) and CHECK 25 (mux_master_incoherent)
// mirror the text-round-trip checker warning-class: both shapes load and
// stream fine but cannot round-trip to `.dbc` text (`format_dbc_text` refuses
// them with the same codes). The text route only ever yields
// singleton-selector, single-master assignments, so each shape is built by
// mutating the typed document and submitting it over the JSON route.

use aletheia::{IssueCode, IssueSeverity, ValidationIssue};

fn has_warning(issues: &[ValidationIssue], code: &IssueCode) -> bool {
    issues
        .iter()
        .any(|i| i.severity == IssueSeverity::Warning && &i.code == code)
}

#[test]
fn validate_dbc_warns_on_a_multi_value_mux_selector() {
    let c = client();
    let mut dbc = c.parse_dbc_text(DBC).expect("parse DBC text").dbc;
    // Widen PayloadA's selector to {0, 3}: still disjoint from PayloadB (1)
    // and PayloadC (2), so no error-class overlap co-presence arises — the
    // mirror warning is the only diagnostic the shape earns.
    let sig = dbc.messages[0]
        .signals
        .iter_mut()
        .find(|s| s.name == "PayloadA")
        .expect("PayloadA present");
    match &mut sig.presence {
        Presence::Multiplexed { values, .. } => *values = vec![0, 3],
        Presence::Always => panic!("PayloadA should be multiplexed"),
    }

    let result = c.validate_dbc(&dbc).expect("validate_dbc");
    assert!(
        !result.has_errors,
        "the mirror is warning-class — has_errors must stay false: {:?}",
        result.issues
    );
    assert!(
        has_warning(&result.issues, &IssueCode::MultiValueMuxSelector),
        "expected a multi_value_mux_selector warning, got {:?}",
        result.issues
    );

    // The load route surfaces the same warning without blocking.
    let parsed = c.parse_dbc(&dbc).expect("a warning-only shape must load");
    assert!(
        has_warning(&parsed.warnings, &IssueCode::MultiValueMuxSelector),
        "expected the warning on the load, got {:?}",
        parsed.warnings
    );
}

#[test]
fn validate_dbc_warns_on_a_split_mux_master() {
    let c = client();
    let mut dbc = c.parse_dbc_text(DBC).expect("parse DBC text").dbc;
    // Re-point one slave at the Always signal CommonCounter: both named
    // masters exist and there is no cycle (no error-class check trips), but
    // the slaves now sit under two masters — the split-master shape.
    let sig = dbc.messages[0]
        .signals
        .iter_mut()
        .find(|s| s.name == "PayloadB")
        .expect("PayloadB present");
    match &mut sig.presence {
        Presence::Multiplexed { multiplexor, .. } => {
            *multiplexor = "CommonCounter".to_owned();
        }
        Presence::Always => panic!("PayloadB should be multiplexed"),
    }
    // Signals under different masters may now be co-present, so give
    // PayloadB its own bit range — the mux-aware overlap check would
    // otherwise report an error-class signal_overlap.
    sig.start_bit = 32;

    let result = c.validate_dbc(&dbc).expect("validate_dbc");
    assert!(
        !result.has_errors,
        "the mirror is warning-class — has_errors must stay false: {:?}",
        result.issues
    );
    assert!(
        has_warning(&result.issues, &IssueCode::MuxMasterIncoherent),
        "expected a mux_master_incoherent warning, got {:?}",
        result.issues
    );

    // The load route surfaces the same warning without blocking.
    let parsed = c.parse_dbc(&dbc).expect("a warning-only shape must load");
    assert!(
        has_warning(&parsed.warnings, &IssueCode::MuxMasterIncoherent),
        "expected the warning on the load, got {:?}",
        parsed.warnings
    );
}

#[test]
fn validate_dbc_reports_no_mirror_warnings_for_the_coherent_corpus() {
    let c = client();
    let dbc = c.parse_dbc_text(DBC).expect("parse DBC text").dbc;
    let result = c.validate_dbc(&dbc).expect("validate_dbc");
    assert!(
        !has_warning(&result.issues, &IssueCode::MultiValueMuxSelector)
            && !has_warning(&result.issues, &IssueCode::MuxMasterIncoherent),
        "the singleton-selector, single-master corpus drew a mirror warning: {:?}",
        result.issues
    );
}
