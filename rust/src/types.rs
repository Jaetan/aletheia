// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Validated value types shared across the binding.
//!
//! Each type validates on construction (returning [`Error::Validation`]) so an
//! out-of-range CAN ID, an invalid DLC, or a non-positive rational denominator
//! cannot be represented — the parity discipline of the Go and C++ bindings,
//! expressed with Rust's `Result` instead of `(T, error)` / `expected`.

use serde_json::{json, Value};

use crate::error::Error;

/// Largest 11-bit standard CAN identifier (0..=2047).
pub const MAX_STANDARD_ID: u16 = (1 << 11) - 1;
/// Largest 29-bit extended CAN identifier (0..=536_870_911).
pub const MAX_EXTENDED_ID: u32 = (1 << 29) - 1;

/// A CAN bus identifier — standard (11-bit) or extended (29-bit).
///
/// A native Rust enum is naturally sealed and matchable, so this replaces the
/// Go binding's `CANID` sealed interface + `StandardID`/`ExtendedID` pair.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CanId {
    /// 11-bit identifier (0..=[`MAX_STANDARD_ID`]).
    Standard(u16),
    /// 29-bit identifier (0..=[`MAX_EXTENDED_ID`]).
    Extended(u32),
}

impl CanId {
    /// Construct an 11-bit standard identifier.
    ///
    /// # Errors
    /// [`Error::Validation`] if `value` exceeds [`MAX_STANDARD_ID`].
    pub fn standard(value: u16) -> Result<Self, Error> {
        if value > MAX_STANDARD_ID {
            return Err(Error::Validation(format!(
                "standard CAN ID {value} exceeds 11-bit range (0-{MAX_STANDARD_ID})"
            )));
        }
        Ok(CanId::Standard(value))
    }

    /// Construct a 29-bit extended identifier.
    ///
    /// # Errors
    /// [`Error::Validation`] if `value` exceeds [`MAX_EXTENDED_ID`].
    pub fn extended(value: u32) -> Result<Self, Error> {
        if value > MAX_EXTENDED_ID {
            return Err(Error::Validation(format!(
                "extended CAN ID {value} exceeds 29-bit range (0-{MAX_EXTENDED_ID})"
            )));
        }
        Ok(CanId::Extended(value))
    }

    /// The raw identifier value.
    #[must_use]
    pub fn value(self) -> u32 {
        match self {
            CanId::Standard(v) => u32::from(v),
            CanId::Extended(v) => v,
        }
    }

    /// Whether this is a 29-bit extended identifier.
    #[must_use]
    pub fn is_extended(self) -> bool {
        matches!(self, CanId::Extended(_))
    }
}

/// Data Length Code (0..=15). Maps non-linearly to a byte count for CAN-FD.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Dlc(u8);

const DLC_TABLE: [usize; 16] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 12, 16, 20, 24, 32, 48, 64];

impl Dlc {
    /// Construct a DLC.
    ///
    /// # Errors
    /// [`Error::Validation`] if `code` is outside `0..=15`.
    pub fn new(code: u8) -> Result<Self, Error> {
        if code > 15 {
            return Err(Error::Validation(format!(
                "DLC {code} out of range [0, 15]"
            )));
        }
        Ok(Dlc(code))
    }

    /// The raw 0..=15 code.
    #[must_use]
    pub fn value(self) -> u8 {
        self.0
    }

    /// The payload byte count this code encodes (CAN-FD: 9..=15 → 12,16,…,64).
    #[must_use]
    pub fn to_bytes(self) -> usize {
        DLC_TABLE[self.0 as usize]
    }

    /// Construct a DLC from a payload byte count — the inverse of
    /// [`Dlc::to_bytes`]. Accepts only the valid CAN/CAN-FD byte counts
    /// (`0..=8`, then `12, 16, 20, 24, 32, 48, 64`); the wire-symmetric mirror
    /// of the Go binding's `BytesToDLC` and the C++ binding's `bytes_to_dlc`.
    ///
    /// # Errors
    /// [`Error::Validation`] if `bytes` is not a valid CAN/CAN-FD byte count.
    pub fn from_bytes(bytes: usize) -> Result<Self, Error> {
        DLC_TABLE
            .iter()
            .position(|&b| b == bytes)
            .map(|code| Dlc(code as u8))
            .ok_or_else(|| {
                Error::Validation(format!("{bytes} is not a valid CAN/CAN-FD DLC byte count"))
            })
    }
}

/// An exact rational value — the precision currency of LTL predicates
/// (wire-symmetric with the Go binding's `Rational` and Python's `Fraction`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Rational {
    numerator: i64,
    denominator: i64,
}

impl Rational {
    /// Construct a rational `numerator / denominator`.
    ///
    /// # Errors
    /// [`Error::Validation`] if `denominator` is zero or negative (the core and
    /// the other bindings reject non-positive denominators at the wire rather
    /// than silently rewriting them).
    pub fn new(numerator: i64, denominator: i64) -> Result<Self, Error> {
        if denominator == 0 {
            return Err(Error::Validation(
                "rational denominator is zero".to_string(),
            ));
        }
        if denominator < 0 {
            return Err(Error::Validation(format!(
                "rational denominator must be positive, got {denominator}"
            )));
        }
        Ok(Rational {
            numerator,
            denominator,
        })
    }

    /// Value comparison `self <= other`. Denominators are positive by
    /// construction, so cross-multiplication preserves the inequality; `i128`
    /// avoids `i64` overflow on the product.
    ///
    /// Deliberately NOT `PartialOrd`/`Ord`: `new` does not reduce to lowest
    /// terms, so the derived `Eq` is structural (`1/2 != 2/4`) and a
    /// value-based `Ord` would violate the `Ord`/`Eq` consistency contract
    /// (silently corrupting `BTreeMap`/`sort` users). Crate-private on
    /// purpose — a public comparison would be new Rust-only API surface.
    pub(crate) fn le(self, other: Rational) -> bool {
        i128::from(self.numerator) * i128::from(other.denominator)
            <= i128::from(other.numerator) * i128::from(self.denominator)
    }

    /// An exact integer rational (`n / 1`).
    #[must_use]
    pub fn integer(n: i64) -> Self {
        Rational {
            numerator: n,
            denominator: 1,
        }
    }

    /// Parse a decimal string into an exact [`Rational`] via the verified Agda
    /// kernel — the cross-binding single source of truth for decimal→rational
    /// (the float principle: a decimal is an exact rational, never a float).
    /// `"0.1" → 1/10`, `"3.14" → 157/50`, `"42" → 42/1`. The accepted grammar is
    /// the kernel's: `-?digits` or `-?digits.digits+` — no `+` sign, no
    /// leading/trailing `.`, no exponent (so `"1e3"`, `".5"`, `"1."`, `"+2"` are
    /// rejected). Requires a live backend: like rational *display*, decimal
    /// parsing is RTS-gated (it runs the kernel's `toℚ` + the `i64` bound check),
    /// and an `FfiBackend` (via a [`Client`](crate::Client)) is the sole RTS
    /// initialiser.
    ///
    /// # Errors
    /// [`Error::Validation`] if the string is not a valid decimal literal or its
    /// rational overflows `i64`; [`Error::RtsNotInitialized`] if no backend has
    /// been created; [`Error::LibraryLoad`] / [`Error::SymbolMissing`] if the
    /// `.so` or the export is unavailable.
    pub fn from_decimal(s: &str) -> Result<Self, Error> {
        crate::backend::parse_decimal(s)
    }

    /// The numerator.
    #[must_use]
    pub fn numerator(self) -> i64 {
        self.numerator
    }

    /// The denominator (always positive).
    #[must_use]
    pub fn denominator(self) -> i64 {
        self.denominator
    }

    /// Encode for the wire: a plain integer when the denominator is 1, else a
    /// `{"numerator","denominator"}` object — matching every other binding so
    /// exact precision survives the round-trip.
    pub(crate) fn to_value(self) -> Value {
        if self.denominator == 1 {
            json!(self.numerator)
        } else {
            json!({ "numerator": self.numerator, "denominator": self.denominator })
        }
    }
}

/// An integer is always a valid rational (`n / 1`) — the ergonomic input for the
/// check DSL (`signal("x").never_exceeds(1000)`). Fractions go through the
/// fallible [`Rational::new`], so there is no panicking `From` for them.
impl From<i64> for Rational {
    fn from(n: i64) -> Self {
        Rational::integer(n)
    }
}

/// A trace timestamp in microseconds since the start of the stream.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Timestamp(pub u64);

impl Timestamp {
    /// Microseconds since trace start.
    #[must_use]
    pub fn micros(self) -> u64 {
        self.0
    }
}

/// A metric (time-bounded) window in microseconds, for the metric LTL operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TimeBound(pub u64);

impl TimeBound {
    /// The window in microseconds.
    #[must_use]
    pub fn micros(self) -> u64 {
        self.0
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn dlc_from_bytes_round_trips_and_rejects_invalid() {
        use super::Dlc;
        // `from_bytes` is the exact inverse of `to_bytes` over every valid code.
        for code in 0..=15u8 {
            let dlc = Dlc::new(code).expect("0..=15 is valid");
            let back = Dlc::from_bytes(dlc.to_bytes()).expect("a real byte count round-trips");
            assert_eq!(back, dlc, "round-trip failed for code {code}");
        }
        // 9 bytes is not a valid length (the table jumps 8 -> 12); 65 exceeds CAN-FD's 64.
        assert!(Dlc::from_bytes(9).is_err());
        assert!(Dlc::from_bytes(65).is_err());
    }
}
