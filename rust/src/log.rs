// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Structured logging — opt-in, zero-cost when no logger is configured.
//!
//! A [`Logger`] is a callback sink the [`Client`](crate::Client) invokes with a
//! typed [`LogRecord`] (level + event name + fields). It mirrors the C++
//! `aletheia::Logger` and Go's `slog` injection: the binding emits a fixed
//! vocabulary of event names (the cross-binding [`events`] set, authoritative in
//! `docs/LOG_EVENTS.yaml`) and the caller bridges them to whatever logging
//! backend they use.
//!
//! ```no_run
//! use aletheia::{Client, LogLevel};
//! let client = Client::builder()
//!     .logger(|rec: &aletheia::LogRecord| eprintln!("{}: {}", rec.level, rec.event))
//!     .min_level(LogLevel::Info)
//!     .build()?;
//! # Ok::<(), aletheia::Error>(())
//! ```
//!
//! A bare closure works as a [`Logger`] via a blanket impl, so the common
//! single-sink case needs no boilerplate.

use std::fmt;

/// Severity of a log record. Ordered so a configured minimum level filters
/// lower-severity records (`Debug < Info < Warn < Error`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum LogLevel {
    /// Verbose per-frame / cache detail.
    Debug,
    /// Lifecycle milestones.
    Info,
    /// Recoverable anomalies (the stream continues).
    Warn,
    /// Errors.
    Error,
}

impl fmt::Display for LogLevel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            LogLevel::Debug => "debug",
            LogLevel::Info => "info",
            LogLevel::Warn => "warn",
            LogLevel::Error => "error",
        };
        f.write_str(s)
    }
}

/// A typed structured-field value (the Rust analogue of the C++ `LogValue`
/// variant). Borrows for the duration of the [`Logger::log`] call.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum LogValue<'a> {
    /// A string value.
    Str(&'a str),
    /// A signed integer value.
    I64(i64),
    /// An unsigned integer value.
    U64(u64),
    /// A floating-point value.
    F64(f64),
    /// A boolean value.
    Bool(bool),
}

/// One `key = value` field on a [`LogRecord`].
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct LogField<'a> {
    /// The field name.
    pub key: &'a str,
    /// The field value.
    pub value: LogValue<'a>,
}

impl<'a> LogField<'a> {
    /// Construct a field.
    #[must_use]
    pub fn new(key: &'a str, value: LogValue<'a>) -> Self {
        LogField { key, value }
    }
}

/// One structured log record. Valid only for the duration of the
/// [`Logger::log`] call — the borrowed `event` / `fields` may reference
/// temporaries, so a sink must not store the record beyond the callback.
#[derive(Debug, Clone, Copy)]
pub struct LogRecord<'a> {
    /// Severity.
    pub level: LogLevel,
    /// The event name — one of the [`events`] vocabulary.
    pub event: &'a str,
    /// Structured fields attached to the event.
    pub fields: &'a [LogField<'a>],
}

/// A structured-log sink. Implemented for any `Fn(&LogRecord) + Send + Sync`, so
/// a closure is a `Logger`; implement the trait directly for a stateful sink.
///
/// `Send + Sync` is required so the logger can be shared with a future async
/// client's worker thread; it does not make the synchronous [`Client`](crate::Client) itself
/// `Send`.
pub trait Logger: Send + Sync {
    /// Handle one record. The minimum-level filter is applied by the caller
    /// before this is invoked.
    fn log(&self, record: &LogRecord);
}

impl<F: Fn(&LogRecord) + Send + Sync> Logger for F {
    fn log(&self, record: &LogRecord) {
        self(record);
    }
}

/// The cross-binding structured-log event vocabulary — the full canonical set,
/// authoritative in `docs/LOG_EVENTS.yaml` and shared with the Python / Go / C++
/// bindings (Python's `LogEvent` enum is the analogue). All 16 names are defined
/// here, so downstream code can refer to any vocabulary event uniformly across
/// bindings even where this client does not yet emit it; [`ALL`](events::ALL) lists them and
/// the `log_events` parity test pins the set to the YAML. The subset this client
/// emits today is noted per-constant.
pub mod events {
    // --- Emitted by this client ---

    /// A DBC definition was loaded. *(emitted)*
    pub const DBC_PARSED: &str = "dbc.parsed";
    /// Properties were registered with the client. *(emitted)*
    pub const PROPERTIES_SET: &str = "properties.set";
    /// A streaming session was opened. *(emitted)*
    pub const STREAM_STARTED: &str = "stream.started";
    /// A streaming session was closed. *(emitted)*
    pub const STREAM_ENDED: &str = "stream.ended";
    /// RTS init requested with an `N` disagreeing with the earlier process-wide init. *(emitted)*
    pub const RTS_CORES_MISMATCH: &str = "rts.cores_mismatch";
    /// A CAN frame was processed during streaming. *(emitted)*
    pub const FRAME_PROCESSED: &str = "frame.processed";
    /// An error event was forwarded to the streaming session. *(emitted)*
    pub const ERROR_EVENT_SENT: &str = "error_event.sent";
    /// A remote event was forwarded to the streaming session. *(emitted)*
    pub const REMOTE_EVENT_SENT: &str = "remote_event.sent";
    /// An end-of-stream warning: an atom referenced a signal the cache never observed. *(emitted)*
    pub const ENDSTREAM_UNCACHED_ATOM: &str = "endstream.uncached_atom";

    /// A violation referenced a property index outside the registered set. *(emitted)*
    pub const ENRICHMENT_PROPERTY_INDEX_OOB: &str = "enrichment.property_index_oob";
    /// Signal extraction for violation enrichment returned no result. *(emitted)*
    pub const ENRICHMENT_EXTRACTION_FAILED: &str = "enrichment.extraction_failed";
    /// An extraction request failed at the FFI process boundary. *(emitted)*
    pub const EXTRACTION_PROCESS_FAILED: &str = "extraction.process_failed";
    /// An extraction response could not be parsed. *(emitted)*
    pub const EXTRACTION_PARSE_FAILED: &str = "extraction.parse_failed";

    // --- Vocabulary completeness (defined but not emitted by this client) ---
    // The cache.* events instrument an extraction-result memoization cache this
    // binding does not implement (see docs/FEATURE_MATRIX.yaml
    // `violation_enrichment`: the extraction-cache layer is a perf optimization,
    // not part of the cross-binding contract). Defined here so downstream code can
    // refer to the full vocabulary uniformly across bindings.

    /// Signal extraction served a cached payload.
    pub const CACHE_HIT: &str = "cache.hit";
    /// Signal extraction missed the cache and called through to the core.
    pub const CACHE_MISS: &str = "cache.miss";
    /// The extraction cache reached its capacity bound.
    pub const CACHE_FULL: &str = "cache.full";

    /// Every event in the canonical vocabulary, in `docs/LOG_EVENTS.yaml` order.
    pub const ALL: [&str; 16] = [
        DBC_PARSED,
        PROPERTIES_SET,
        STREAM_STARTED,
        STREAM_ENDED,
        RTS_CORES_MISMATCH,
        FRAME_PROCESSED,
        ERROR_EVENT_SENT,
        REMOTE_EVENT_SENT,
        ENRICHMENT_PROPERTY_INDEX_OOB,
        ENRICHMENT_EXTRACTION_FAILED,
        CACHE_HIT,
        CACHE_MISS,
        CACHE_FULL,
        EXTRACTION_PROCESS_FAILED,
        EXTRACTION_PARSE_FAILED,
        ENDSTREAM_UNCACHED_ATOM,
    ];
}
