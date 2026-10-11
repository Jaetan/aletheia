// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! The pure halves of the binary path, driven without the core: the codecs
//! the FFI arguments and results pass through, at their boundaries.

use std::cell::Cell;

use super::{
    buffer_refusal, check_buffer_status, encode_opt_bool, frame_len, symbols,
    take_extraction_buffer, Backend, MAX_EXTRACT_BUF,
};
use crate::error::Error;
use crate::mock::MockBackend;
use crate::types::{CanId, Dlc};

#[test]
fn opt_bool_encodes_presence_then_value() {
    assert_eq!(encode_opt_bool(None), (0, 0));
    assert_eq!(encode_opt_bool(Some(false)), (1, 0));
    assert_eq!(encode_opt_bool(Some(true)), (1, 1));
}

/// `frame_len` over `data` with the DLC whose code is `code`.
fn len_for(code: u8, data: &[u8]) -> Result<u8, Error> {
    frame_len(Dlc::new(code).expect("dlc"), data)
}

#[test]
fn frame_len_admits_exactly_the_dlc_byte_count() {
    assert_eq!(len_for(0, &[]).expect("DLC 0, no payload"), 0);
    assert_eq!(len_for(8, &[0u8; 8]).expect("DLC 8, 8 bytes"), 8);
    assert_eq!(len_for(9, &[0u8; 12]).expect("DLC 9, 12 bytes"), 12);
    assert_eq!(len_for(15, &[0u8; 64]).expect("DLC 15, 64 bytes"), 64);
}

#[test]
fn frame_len_refuses_any_other_length_within_the_largest_frame() {
    // Each length is at most 64 bytes, the largest a DLC names, and still
    // not the byte count of the DLC it travels with.
    for (code, len) in [(8, 20), (8, 7), (8, 9), (0, 1), (9, 8), (15, 48), (15, 63)] {
        let result = len_for(code, &vec![0u8; len]);
        assert!(
            matches!(&result, Err(Error::Validation(m)) if m.contains("does not match DLC")),
            "DLC {code} with {len} bytes: {result:?}"
        );
    }
}

#[test]
fn frame_len_refuses_a_length_past_the_largest_frame() {
    // 65 is one past any DLC's byte count; 256 is the first length the
    // frame's u8 cannot carry, which wrapped would read as 0.
    assert!(matches!(len_for(15, &[0u8; 65]), Err(Error::Validation(_))));
    assert!(matches!(len_for(0, &[0u8; 256]), Err(Error::Validation(_))));
}

#[test]
fn buffer_status_zero_is_success_and_nonzero_without_a_message_is_a_protocol_fault() {
    let syms = symbols().expect("load libaletheia-ffi.so for test (is ALETHEIA_LIB set?)");
    assert!(check_buffer_status(0, std::ptr::null_mut(), syms, "op").is_ok());
    let err = check_buffer_status(1, std::ptr::null_mut(), syms, "op").unwrap_err();
    assert!(
        matches!(&err, Error::Protocol(m) if m.contains("null error message")),
        "got: {err}"
    );
}

#[test]
fn a_buffer_refusal_surfaces_the_envelope_code_and_message() {
    let err = buffer_refusal(
        "build_frame",
        r#"{"status":"error","code":"handler_no_dbc","message":"no DBC loaded"}"#,
    );
    assert!(
        matches!(&err, Error::Core { code, message }
            if code == "handler_no_dbc" && message == "no DBC loaded"),
        "got: {err:?}"
    );
    // The shim's own refusals carry their code the same way.
    let err = buffer_refusal(
        "update_frame",
        r#"{"status":"error","code":"ffi_validation_error","message":"aletheia_update_frame_bin: null out buffer"}"#,
    );
    assert!(
        matches!(&err, Error::Core { code, message }
            if code == "ffi_validation_error"
                && message == "aletheia_update_frame_bin: null out buffer"),
        "got: {err:?}"
    );
}

#[test]
fn a_buffer_refusal_lifts_a_structured_envelope_as_the_json_path_does() {
    let err = buffer_refusal(
        "extract_signals_bin",
        r#"{"status":"error","code":"input_bound_exceeded","message":"m","bound_kind":"nesting_depth","observed":65,"limit":64}"#,
    );
    assert!(
        matches!(&err, Error::InputBoundExceeded { bound_kind, observed: 65, limit: 64, .. }
            if bound_kind == "nesting_depth"),
        "got: {err:?}"
    );
}

#[test]
fn a_buffer_error_that_is_not_an_error_envelope_is_a_wire_fault() {
    let err = buffer_refusal("build_frame", "no DBC loaded");
    assert!(
        matches!(&err, Error::Protocol(m)
            if m.starts_with("build_frame: malformed error envelope")),
        "got: {err:?}"
    );
    let err = buffer_refusal("build_frame", r#"{"status":"ack"}"#);
    assert!(
        matches!(&err, Error::Protocol(m)
            if m.starts_with("build_frame: error is not an error envelope")),
        "got: {err:?}"
    );
}

/// Run `take_extraction_buffer` over `ptr` reported as `size` long, counting
/// the frees.
///
/// # Safety
/// `ptr` is null or points to at least `size` readable bytes.
unsafe fn take(ptr: *mut u8, size: u32) -> (Result<Vec<u8>, Error>, usize) {
    let frees = Cell::new(0);
    // SAFETY: the caller's contract, and the free only counts.
    let result = unsafe { take_extraction_buffer(ptr, size, |_| frees.set(frees.get() + 1)) };
    (result, frees.get())
}

/// `take` over the test's own buffer, which must cover the reported size.
fn take_from(bytes: &mut [u8], size: u32) -> (Result<Vec<u8>, Error>, usize) {
    assert!(
        bytes.len() >= size as usize,
        "the test's own buffer must cover the size"
    );
    // SAFETY: `bytes` holds at least `size` bytes.
    unsafe { take(bytes.as_mut_ptr(), size) }
}

#[test]
fn a_null_buffer_is_empty_at_size_zero_and_a_fault_otherwise() {
    // SAFETY: a null pointer is never read.
    let (result, frees) = unsafe { take(std::ptr::null_mut(), 0) };
    assert_eq!(result.expect("empty"), Vec::<u8>::new());
    assert_eq!(frees, 0);
    // SAFETY: a null pointer is never read.
    let (result, frees) = unsafe { take(std::ptr::null_mut(), 3) };
    assert!(matches!(result, Err(Error::Protocol(_))));
    assert_eq!(frees, 0);
}

#[test]
fn a_buffer_is_copied_out_and_freed_once() {
    let (result, frees) = take_from(&mut [1, 2, 3, 4, 5], 5);
    assert_eq!(result.expect("copied"), vec![1, 2, 3, 4, 5]);
    assert_eq!(frees, 1);
}

#[test]
fn the_size_cap_is_inclusive_and_a_refused_buffer_is_still_freed() {
    // The cap is the wire's plausible maximum, a number the constants
    // above derive: the header, three u16-counted sections at their
    // strides, the offsets table and 512 bytes of reason per error.
    assert_eq!(MAX_EXTRACT_BUF, 35_323_379);
    let cap = u32::try_from(MAX_EXTRACT_BUF).expect("fits u32");
    let mut at_cap = vec![7u8; MAX_EXTRACT_BUF];
    let (result, frees) = take_from(&mut at_cap, cap);
    assert_eq!(
        result.expect("the cap itself is admitted").len(),
        MAX_EXTRACT_BUF
    );
    assert_eq!(frees, 1);
    let mut past_cap = vec![7u8; MAX_EXTRACT_BUF + 1];
    let (result, frees) = take_from(&mut past_cap, cap + 1);
    assert!(
        matches!(&result, Err(Error::Protocol(m)) if m.contains("exceeds wire maximum")),
        "got: {result:?}"
    );
    assert_eq!(frees, 1);
}

#[test]
fn the_binary_extraction_default_reports_the_path_unsupported() {
    // A backend that does not override the binary path answers with the
    // variant the client falls back to the JSON path on.
    let mock = MockBackend::new();
    let result = mock.extract_signals_bin(
        CanId::standard(1).expect("id"),
        Dlc::new(8).expect("dlc"),
        &[0u8; 8],
    );
    assert!(
        matches!(result, Err(Error::BinaryPathUnsupported)),
        "got: {result:?}"
    );
    assert!(mock.captured().is_empty(), "the default records nothing");
}
