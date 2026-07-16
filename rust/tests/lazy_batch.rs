// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Lazy batch send (`Client::send_frames_iter`) contract, exercised through the
//! `MockBackend` DI seam — no `libaletheia-ffi.so` needed. The real-FFI
//! eager-vs-lazy equivalence lives in `frame_ops.rs`; the async `Stream` mirror
//! in `async_client.rs`.

use aletheia::{CanId, Client, Dlc, Error, Frame, FrameResponse, MockBackend, Timestamp};

/// A minimal valid frame (payload length matches DLC). The id/data are
/// irrelevant here: the mock records a fixed sentinel and replays the queued
/// responses regardless of input.
fn frame(ts: u64) -> Frame {
    Frame {
        timestamp: Timestamp(ts),
        id: CanId::standard(256).expect("id"),
        dlc: Dlc::new(8).expect("dlc"),
        data: vec![0u8; 8],
        brs: None,
        esi: None,
    }
}

#[test]
fn yields_one_ok_per_frame_in_order() {
    let m = MockBackend::new();
    m.respond_json(r#"{"status":"ack"}"#)
        .respond_json(r#"{"status":"ack"}"#)
        .respond_json(r#"{"status":"ack"}"#);
    let c = Client::with_backend(Box::new(m.clone()));

    let out: Vec<_> = c
        .send_frames_iter(vec![frame(0), frame(1), frame(2)])
        .collect();

    assert_eq!(out.len(), 3);
    assert!(out.iter().all(|r| matches!(r, Ok(FrameResponse::Ack))));
    assert_eq!(
        m.captured(),
        vec!["<binary:sendFrame>"; 3],
        "one FFI send per frame, in order"
    );
}

#[test]
fn stops_after_first_error_and_sends_no_more() {
    let m = MockBackend::new();
    m.respond_json(r#"{"status":"ack"}"#)
        .respond_err(Error::Protocol("boom".to_string()))
        .respond_json(r#"{"status":"ack"}"#); // must never be consumed
    let c = Client::with_backend(Box::new(m.clone()));

    let out: Vec<_> = c
        .send_frames_iter(vec![frame(0), frame(1), frame(2)])
        .collect();

    assert_eq!(out.len(), 2, "Ok prefix then the terminal Err, then fused");
    assert!(matches!(out[0], Ok(FrameResponse::Ack)));
    // The error is tagged with the failing frame's 0-based index (frame 1).
    assert!(
        matches!(out[1], Err(Error::Frame { index: 1, .. })),
        "expected Error::Frame {{ index: 1, .. }}, got {:?}",
        out[1]
    );
    assert_eq!(
        m.captured(),
        vec!["<binary:sendFrame>"; 2],
        "the frame after the failing frame is never sent"
    );
}

#[test]
fn lazy_and_eager_tag_the_same_failing_frame_index() {
    // Error-path equivalence: both forms must report the SAME failing frame via
    // Error::Frame { index } — the happy-path equivalence test does not cover this.
    let mk = || {
        let m = MockBackend::new();
        m.respond_json(r#"{"status":"ack"}"#)
            .respond_err(Error::Protocol("boom".to_string()));
        m
    };

    let ce = Client::with_backend(Box::new(mk()));
    let (_ok, eager_err) = ce.send_frames(&[frame(0), frame(1)]);

    let cl = Client::with_backend(Box::new(mk()));
    let lazy: Vec<_> = cl.send_frames_iter(vec![frame(0), frame(1)]).collect();

    assert!(
        matches!(eager_err, Some(Error::Frame { index: 1, .. })),
        "eager error: {eager_err:?}"
    );
    assert!(
        matches!(lazy.last(), Some(Err(Error::Frame { index: 1, .. }))),
        "lazy last item: {:?}",
        lazy.last()
    );
}

#[test]
fn empty_input_yields_nothing_and_sends_nothing() {
    let m = MockBackend::new();
    let c = Client::with_backend(Box::new(m.clone()));

    let out: Vec<_> = c.send_frames_iter(Vec::<Frame>::new()).collect();

    assert!(out.is_empty());
    assert!(m.captured().is_empty());
}

#[test]
fn cancelling_early_commits_only_the_consumed_prefix() {
    // Stop pulling after 2 of 5 frames (drop the iterator): the remaining 3 are
    // never sent — the commit-prefix contract, observed deterministically via the
    // recorded call count (no sleeps; never wait on physical time).
    let m = MockBackend::new();
    for _ in 0..5 {
        m.respond_json(r#"{"status":"ack"}"#);
    }
    let c = Client::with_backend(Box::new(m.clone()));

    let prefix: Vec<_> = c
        .send_frames_iter(vec![frame(0), frame(1), frame(2), frame(3), frame(4)])
        .take(2)
        .collect();

    assert_eq!(prefix.len(), 2);
    assert_eq!(
        m.captured(),
        vec!["<binary:sendFrame>"; 2],
        "frames after the consumed prefix are never sent"
    );
}

#[test]
fn lazy_matches_eager_responses_and_call_sequence() {
    // Equivalence: the same frames through send_frames (eager) and
    // send_frames_iter (lazy) must produce identical responses AND drive the
    // backend with the identical call sequence (the mock's observable state) —
    // the structural guarantee that the two loop wrappers cannot drift.
    let responses = [
        r#"{"status":"ack"}"#,
        r#"{"status":"ack"}"#,
        r#"{"status":"ack"}"#,
    ];

    let me = MockBackend::new();
    for r in responses {
        me.respond_json(r);
    }
    let ce = Client::with_backend(Box::new(me.clone()));
    let (eager, eager_err) = ce.send_frames(&[frame(0), frame(1), frame(2)]);

    let ml = MockBackend::new();
    for r in responses {
        ml.respond_json(r);
    }
    let cl = Client::with_backend(Box::new(ml.clone()));
    let lazy_ok: Vec<FrameResponse> = cl
        .send_frames_iter(vec![frame(0), frame(1), frame(2)])
        .map(|r| r.expect("all ok"))
        .collect();

    assert!(eager_err.is_none());
    assert_eq!(eager, lazy_ok, "identical per-frame responses");
    assert_eq!(
        me.captured(),
        ml.captured(),
        "identical backend call sequence"
    );
}
