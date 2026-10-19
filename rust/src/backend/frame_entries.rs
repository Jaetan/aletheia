// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! The payload guard and the refusal envelope at the real entries: a
//! payload of any length but the DLC's byte count never reaches the core,
//! and one of exactly that length does, the core then refusing it for want
//! of a DBC with its own code.

use super::{Backend, FfiBackend, SignalInjection};
use crate::error::Error;
use crate::log::LogLevel;
use crate::types::{CanId, Dlc, Timestamp};

const NO_SIGNALS: SignalInjection<'static> = SignalInjection {
    indices: &[],
    nums: &[],
    dens: &[],
};

fn backend() -> FfiBackend {
    FfiBackend::new(None, None, LogLevel::Warn)
        .expect("load libaletheia-ffi.so for test (is ALETHEIA_LIB set?)")
}

fn id() -> CanId {
    CanId::standard(256).expect("id")
}

fn dlc8() -> Dlc {
    Dlc::new(8).expect("dlc")
}

/// A refusal by the guard, which names the mismatch.
fn assert_guarded<T: std::fmt::Debug>(entry: &str, result: Result<T, Error>) {
    assert!(
        matches!(
            &result,
            Err(Error::Validation { message: m, .. }) if m.contains("does not match DLC")
        ),
        "{entry}: {result:?}"
    );
}

/// The core's refusal for want of a DBC, carried from the envelope.
fn assert_no_dbc<T: std::fmt::Debug>(entry: &str, result: Result<T, Error>) {
    assert!(
        matches!(&result, Err(Error::Core { code, message })
            if code == "handler_no_dbc" && message == "DBC not loaded"),
        "{entry}: {result:?}"
    );
}

#[test]
fn every_payload_entry_refuses_a_length_other_than_the_dlc_byte_count() {
    // 20 bytes is within the largest frame and is not the 8 a DLC of 8
    // names.
    let b = backend();
    let data = [0u8; 20];
    assert_guarded(
        "send_frame_binary",
        b.send_frame_binary(Timestamp(0), id(), dlc8(), &data, None, None),
    );
    assert_guarded(
        "extract_signals_binary",
        b.extract_signals_binary(id(), dlc8(), &data),
    );
    assert_guarded(
        "extract_signals_bin",
        b.extract_signals_bin(id(), dlc8(), &data),
    );
    assert_guarded(
        "update_frame_bin",
        b.update_frame_bin(256, false, dlc8(), &data, NO_SIGNALS),
    );
}

#[test]
fn the_binary_output_entries_carry_the_core_code_of_a_refusal() {
    // The exact length passes the guard, and with no DBC loaded each entry
    // answers the core's own refusal.
    let b = backend();
    let data = [0u8; 8];
    assert_no_dbc(
        "extract_signals_bin",
        b.extract_signals_bin(id(), dlc8(), &data),
    );
    assert_no_dbc(
        "build_frame_bin",
        b.build_frame_bin(256, false, dlc8(), NO_SIGNALS),
    );
    assert_no_dbc(
        "update_frame_bin",
        b.update_frame_bin(256, false, dlc8(), &data, NO_SIGNALS),
    );
}
