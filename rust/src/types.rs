// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Validated value types shared across the binding.
//!
//! Each type validates on construction (returning [`Error::Validation`]) so an
//! out-of-range CAN ID, an invalid DLC, or a non-positive rational denominator
//! cannot be represented — the parity discipline of the Go and C++ bindings,
//! expressed with Rust's `Result` instead of `(T, error)` / `expected`.

use std::fmt;
use std::num::TryFromIntError;
use std::str::FromStr;

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
            return Err(Error::validation(format!(
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
            return Err(Error::validation(format!(
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
            return Err(Error::validation(format!(
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
                Error::validation(format!("{bytes} is not a valid CAN/CAN-FD DLC byte count"))
            })
    }
}

/// An exact rational value, the precision currency of LTL predicates
/// (wire-symmetric with the Go binding's `Rational` and Python's `Fraction`):
/// a sign, a numerator magnitude and a positive denominator, each magnitude up
/// to 2^128-1.
///
/// Every constructor stores the value in lowest terms, a zero as `0/1` with no
/// sign, so the derived equality and hash are value equality (`1/2 == 2/4`).
/// There is no ordering: the kernel decides every comparison a property holds.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Rational {
    negative: bool,
    numerator: u128,
    denominator: u128,
}

/// The greatest common divisor of `a` and `b`, `a` when `b` is zero.
///
/// Euclid's remainders fall at least as fast as the Fibonacci numbers, so
/// two `u128`s reach a zero remainder within 184 steps, the count the two
/// largest Fibonacci numbers below 2^128 take; the bound keeps every run of
/// the loop finite.
fn gcd(mut a: u128, mut b: u128) -> u128 {
    for _ in 0..u128::BITS * 2 {
        if b == 0 {
            break;
        }
        (a, b) = (b, a % b);
    }
    a
}

impl Rational {
    /// Construct a rational `numerator / denominator`, in lowest terms.
    ///
    /// # Errors
    /// [`Error::Validation`] if `denominator` is zero or negative (the core and
    /// the other bindings reject non-positive denominators at the wire rather
    /// than silently rewriting them).
    pub fn new(numerator: i64, denominator: i64) -> Result<Self, Error> {
        if denominator == 0 {
            return Err(Error::validation("rational denominator is zero"));
        }
        if denominator < 0 {
            return Err(Error::validation(format!(
                "rational denominator must be positive, got {denominator}"
            )));
        }
        Ok(Rational::reduced(
            numerator < 0,
            u128::from(numerator.unsigned_abs()),
            u128::from(denominator.unsigned_abs()),
        ))
    }

    /// Construct the rational of `numerator / denominator`, negated when
    /// `negative`, in lowest terms: the constructor reaching every magnitude
    /// up to 2^128-1.
    ///
    /// # Errors
    /// [`Error::Validation`] if `denominator` is zero.
    pub fn from_parts(negative: bool, numerator: u128, denominator: u128) -> Result<Self, Error> {
        if denominator == 0 {
            return Err(Error::validation("rational denominator is zero"));
        }
        Ok(Rational::reduced(negative, numerator, denominator))
    }

    /// The value over a non-zero `denominator`, divided by the two
    /// magnitudes' greatest common divisor, a zero unsigned.
    fn reduced(negative: bool, numerator: u128, denominator: u128) -> Self {
        let divisor = gcd(numerator, denominator);
        Rational::from_kernel(negative, numerator / divisor, denominator / divisor)
    }

    /// The rational stored as given, a zero unsigned whatever its sign: what
    /// every constructor stores once its value is in lowest terms, and what a
    /// reader stores the kernel's rationals through. The kernel's rationals
    /// are its standard library's, reduced by their type over a denominator
    /// its proofs hold positive, so a reader stores one with no check and no
    /// reduction.
    pub(crate) fn from_kernel(negative: bool, numerator: u128, denominator: u128) -> Self {
        Rational {
            negative: negative && numerator != 0,
            numerator,
            denominator,
        }
    }

    /// An exact integer rational (`n / 1`).
    #[must_use]
    pub fn integer(n: i128) -> Self {
        Rational {
            negative: n < 0,
            numerator: n.unsigned_abs(),
            denominator: 1,
        }
    }

    /// Parse a decimal string into an exact [`Rational`] via the verified Agda
    /// kernel, the cross-binding single source of truth for decimal to
    /// rational (the float principle: a decimal is an exact rational, never a
    /// float). `"0.1"` is 1/10, `"3.14"` is 157/50, `"42"` is 42/1. The
    /// accepted grammar is the kernel's: `-?digits` or `-?digits.digits+`, no
    /// `+` sign, no leading or trailing `.`, no exponent (so `"1e3"`, `".5"`,
    /// `"1."`, `"+2"` are refused). Like rational *display*, decimal parsing
    /// needs the GHC runtime up (the kernel parses the literal and holds each
    /// rational component to its magnitude bound):
    /// [`start_runtime`](crate::start_runtime) or a [`Client`](crate::Client)
    /// starts it, and this never does.
    ///
    /// # Errors
    /// [`Error::Validation`] with `code` `Some("text_parse_failure")` (not a
    /// decimal literal) or `Some("text_trailing_input")` (a literal followed by
    /// more text), the kernel's line and column in its message, or
    /// `Some("ffi_validation_error")` when the shim refused the bytes (a NUL
    /// byte in `s`); [`Error::InputBoundExceeded`] with `field` `"decimal"`
    /// when the numerator or the denominator crosses the rational component
    /// magnitude bound, 2^128-1; [`Error::Protocol`] when the entry reports a
    /// refusal without an error envelope or the envelope is malformed;
    /// [`Error::RtsNotInitialized`] if the runtime has not started.
    pub fn from_decimal(s: &str) -> Result<Self, Error> {
        crate::backend::parse_decimal(s)
    }

    /// Whether the value is below zero; a zero is never negative.
    #[must_use]
    pub fn is_negative(self) -> bool {
        self.negative
    }

    /// The numerator's magnitude, in lowest terms.
    #[must_use]
    pub fn numerator(self) -> u128 {
        self.numerator
    }

    /// The denominator, positive and in lowest terms.
    #[must_use]
    pub fn denominator(self) -> u128 {
        self.denominator
    }
}

/// An integer is always a valid rational (`n / 1`), the ergonomic input for
/// the check DSL (`signal("x").never_exceeds(1000)`, whose unsuffixed literal
/// is an `i32`). Fractions go through the fallible [`Rational::new`] or
/// [`Rational::from_parts`], so there is no panicking `From` for them.
macro_rules! rational_from_integer {
    ($($signed:ty),*; $($unsigned:ty),*) => {
        $(impl From<$signed> for Rational {
            fn from(n: $signed) -> Self {
                Rational::integer(i128::from(n))
            }
        })*
        $(impl From<$unsigned> for Rational {
            fn from(n: $unsigned) -> Self {
                Rational::from_kernel(false, u128::from(n), 1)
            }
        })*
    };
}

rational_from_integer!(i8, i16, i32, i64, i128; u8, u16, u32, u64, u128);

/// A whole number as a sign and a magnitude up to 2^128-1: the key of a value
/// description, which a DBC writes in either sign.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SignMagnitude {
    /// Whether the number is below zero.
    pub negative: bool,
    /// The number's magnitude.
    pub magnitude: u128,
}

/// The number's decimal digits, after a `-` when it is negative; a zero is
/// printed unsigned whatever its sign.
impl fmt::Display for SignMagnitude {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.negative && self.magnitude != 0 {
            write!(f, "-{}", self.magnitude)
        } else {
            write!(f, "{}", self.magnitude)
        }
    }
}

/// The number as an `i64`, refused when it lies outside the `i64` range.
impl TryFrom<SignMagnitude> for i64 {
    type Error = TryFromIntError;

    fn try_from(value: SignMagnitude) -> Result<Self, Self::Error> {
        let magnitude = i128::try_from(value.magnitude)?;
        i64::try_from(if value.negative {
            -magnitude
        } else {
            magnitude
        })
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

    /// Read a time bound, a whole number of microseconds, from `text` through
    /// the kernel's time-bound entry, which is what every binding's loader
    /// reads a check's window with. Like [`Rational::from_decimal`] it needs
    /// the GHC runtime up and never starts it.
    ///
    /// # Errors
    /// The kernel's refusal, typed as [`Rational::from_decimal`] types one:
    /// [`Error::Validation`] carrying the kernel's code and reason for a
    /// negative or fractional number (`handler_property_refused`) or for text
    /// that is no decimal (the decimal parser's codes);
    /// [`Error::InputBoundExceeded`] with `field` `"time bound"` for a value
    /// past 2^64-1; [`Error::Protocol`] when the entry reports a refusal
    /// without an error envelope or the envelope is malformed;
    /// [`Error::RtsNotInitialized`] if the runtime has not started.
    pub fn parse(text: &str) -> Result<Self, Error> {
        crate::backend::parse_time_bound(text)
    }
}

/// `"1500".parse::<TimeBound>()`, the standard spelling of [`TimeBound::parse`].
impl FromStr for TimeBound {
    type Err = Error;

    fn from_str(text: &str) -> Result<Self, Self::Err> {
        TimeBound::parse(text)
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

    #[test]
    fn can_id_ranges_are_inclusive_at_the_top() {
        use super::{CanId, MAX_EXTENDED_ID, MAX_STANDARD_ID};
        // The maximum of each width is a valid identifier; one past it is not.
        assert_eq!(
            CanId::standard(MAX_STANDARD_ID)
                .expect("the 11-bit maximum")
                .value(),
            u32::from(MAX_STANDARD_ID)
        );
        assert!(CanId::standard(MAX_STANDARD_ID + 1).is_err());
        assert_eq!(
            CanId::extended(MAX_EXTENDED_ID)
                .expect("the 29-bit maximum")
                .value(),
            MAX_EXTENDED_ID
        );
        assert!(CanId::extended(MAX_EXTENDED_ID + 1).is_err());
    }

    #[test]
    fn a_ratio_taking_euclids_longest_run_below_2_128_stays_in_lowest_terms() {
        use super::Rational;
        // The two largest Fibonacci numbers below 2^128, coprime, and the pair
        // Euclid takes the most steps over; a common factor of 6 is removed.
        let (larger, smaller) = (
            332_825_110_087_067_562_321_196_029_789_634_457_848_u128,
            205_697_230_343_233_228_174_223_751_303_346_572_685_u128,
        );
        let ratio = Rational::from_parts(false, larger, smaller).expect("a positive denominator");
        assert_eq!((ratio.numerator(), ratio.denominator()), (larger, smaller));
        let scaled = Rational::from_parts(true, 6 * 7, 6 * 11).expect("a positive denominator");
        assert_eq!(
            (
                scaled.is_negative(),
                scaled.numerator(),
                scaled.denominator()
            ),
            (true, 7, 11)
        );
    }

    #[test]
    fn a_sign_magnitude_prints_a_minus_only_before_a_negative_non_zero_magnitude() {
        use super::SignMagnitude;
        let shown = |negative, magnitude| {
            SignMagnitude {
                negative,
                magnitude,
            }
            .to_string()
        };
        assert_eq!(shown(false, 5), "5");
        assert_eq!(shown(true, 0), "0");
        assert_eq!(shown(true, 5), "-5");
    }

    #[test]
    fn a_sign_magnitude_converts_to_i64_within_its_range_and_is_refused_past_it() {
        use super::SignMagnitude;
        let to_i64 = |negative, magnitude| {
            i64::try_from(SignMagnitude {
                negative,
                magnitude,
            })
        };
        assert_eq!(to_i64(false, 5), Ok(5));
        assert_eq!(to_i64(true, 5), Ok(-5));
        assert_eq!(to_i64(true, 1 << 63), Ok(i64::MIN));
        assert!(to_i64(false, 1 << 63).is_err());
        assert!(to_i64(true, u128::MAX).is_err());
    }

    #[test]
    fn timestamp_and_time_bound_read_back_their_micros() {
        use super::{TimeBound, Timestamp};
        assert_eq!(Timestamp(1_234_567).micros(), 1_234_567);
        assert_eq!(TimeBound(89).micros(), 89);
    }
}
