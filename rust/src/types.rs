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

    /// An exact integer rational (`n / 1`).
    #[must_use]
    pub fn integer(n: i64) -> Self {
        Rational {
            numerator: n,
            denominator: 1,
        }
    }

    /// Convert a `f64` to a [`Rational`] via the cross-binding `round(v × 10⁹), 10⁹`
    /// convention, then reduce to lowest terms (so `0.1 → 1/10`, `100.5 → 201/2`).
    ///
    /// This is the **shared** float→rational convention of every binding — Python
    /// `float_to_rational`, Go `FloatToRational`, C++ `Rational::from_double` — so a
    /// decimal value written in a check file produces the same rational everywhere.
    /// The conversion is necessarily binding-side: the FFI takes an integer pair and
    /// `0.1` is not a rational in IEEE-754, so there is no proven-core form to defer
    /// to (the core still normalises whatever pair it receives).
    ///
    /// Integer-valued floats take the exact `n/1` path.
    ///
    /// # Errors
    /// [`Error::Validation`] if `v` is NaN, infinite, or overflows `i64` when scaled
    /// — matching the Python and C++ loaders (and the Go check builders), which fail
    /// on such input rather than silently clamping.
    pub fn from_f64(v: f64) -> Result<Self, Error> {
        if v.is_nan() || v.is_infinite() {
            return Err(Error::Validation(format!("cannot convert {v} to rational")));
        }
        // Integer fast path (exact for whole-number thresholds like 220.0).
        // Strict upper bound: `i64::MAX as f64` rounds UP to 2^63 (one past
        // i64::MAX), so `<=` would let exactly 2^63 through to a *saturating*
        // `as i64` (→ i64::MAX, silently wrong). `<` rejects 2^63 instead; the
        // largest valid integer double, 2^63-2048, is still strictly below it.
        if v.fract() == 0.0 && v >= i64::MIN as f64 && v < i64::MAX as f64 {
            return Ok(Rational::integer(v as i64));
        }
        // Fixed-point 10⁹ scaling, with the same overflow guard as the peers.
        const SCALE: i64 = 1_000_000_000;
        let limit = (i64::MAX / SCALE - 1) as f64;
        if v > limit || v < -limit {
            return Err(Error::Validation(format!(
                "value {v} overflows i64 when scaled to rational"
            )));
        }
        let num = (v * SCALE as f64).round() as i64;
        let g = gcd(num.unsigned_abs(), SCALE as u64);
        // g ≥ 1 (SCALE ≠ 0), and both operands are within i64, so the divisions
        // are exact and in range — no further validation needed.
        Ok(Rational {
            numerator: num / g as i64,
            denominator: SCALE / g as i64,
        })
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

/// Euclid's GCD, for reducing a `round(v × 10⁹), 10⁹` rational to lowest terms.
/// With a nonzero second argument the result is ≥ 1.
fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
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
    use super::Rational;

    #[test]
    fn from_f64_rejects_2_pow_63_instead_of_saturating() {
        // `i64::MAX as f64` rounds up to 2^63 (one past i64::MAX); the integer
        // fast path must reject exactly +2^63, not saturate it to i64::MAX.
        let two_pow_63 = 9_223_372_036_854_775_808.0_f64; // 2^63
        assert!(Rational::from_f64(two_pow_63).is_err());
        // -2^63 IS i64::MIN — exactly representable as f64 and a valid i64, so it
        // is accepted (only the upper bound was off-by-one; the lower is exact).
        let min = Rational::from_f64(-two_pow_63).expect("-2^63 == i64::MIN is in range");
        assert_eq!(min.numerator(), i64::MIN);
        assert_eq!(min.denominator(), 1);
    }

    #[test]
    fn from_f64_accepts_largest_in_range_integer_double() {
        // The largest integer-valued double strictly below 2^63 is 2^63 - 2048;
        // it fits i64 exactly and must round-trip through the integer fast path.
        let max_int_double = 9_223_372_036_854_773_760.0_f64; // 2^63 - 2048
        let r = Rational::from_f64(max_int_double).expect("in-range integer double");
        assert_eq!(r.numerator(), 9_223_372_036_854_773_760);
        assert_eq!(r.denominator(), 1);
    }
}
