// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! LTL predicates and formulas.
//!
//! `Predicate` and `Formula` are plain Rust enums, naturally sealed and
//! exhaustively matchable, replacing the Go binding's `predicate()` /
//! `formula()` sealed-interface marker methods with no ceremony. The kernel's
//! JSON for each (`{"operator":…}` for formulas, `{"predicate":…}` for atoms)
//! is written by the crate-private `Serialize` impls below, which decide
//! nothing: the kernel's property parse decides every field, at a builder's
//! end or at `set_properties`.
//!
//! Each builder hands what it made to the kernel's property parse
//! (`aletheia_check_property`), which refuses it with the reason
//! `set_properties` would give, so a predicate or a formula is refused where
//! it is built. The parse needs the GHC runtime up
//! ([`start_runtime`](crate::start_runtime) or a client) and never starts it:
//! while the runtime is down each builder answers [`Error::RtsNotInitialized`].
//! A predicate or a formula written as a literal skips this and is refused at
//! `set_properties` instead.

use serde::ser::{Serialize, SerializeMap, Serializer};

use crate::backend::check_property;
use crate::error::Error;
use crate::types::{Rational, TimeBound};
use crate::wire_json::{json_object, to_text, Number, Wire};

/// Client-side recursion guard on formula nesting depth (mirrors Go's 100-deep
/// stack guard), applied before serialization to fail fast rather than recurse
/// unboundedly. This is **distinct from** the kernel's JSON nesting cap of 64
/// (`Aletheia.Limits.max-nesting-depth`), which is the true wire limit: a formula
/// deeper than 64 is rejected by the core as a `nesting_depth` bound even though
/// it passes this guard.
pub const MAX_FORMULA_DEPTH: usize = 100;

/// A signal predicate, an atomic proposition over one signal's value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Predicate {
    /// `signal == value`.
    Equals { signal: String, value: Rational },
    /// `signal < value`.
    LessThan { signal: String, value: Rational },
    /// `signal > value`.
    GreaterThan { signal: String, value: Rational },
    /// `signal <= value`.
    LessThanOrEqual { signal: String, value: Rational },
    /// `signal >= value`.
    GreaterThanOrEqual { signal: String, value: Rational },
    /// `min <= signal <= max` (requires `min <= max`).
    Between {
        signal: String,
        min: Rational,
        max: Rational,
    },
    /// The signal changed by at least `delta` (sign selects direction).
    ChangedBy { signal: String, delta: Rational },
    /// The signal stayed within `tolerance` of its previous value (`tolerance >= 0`).
    StableWithin { signal: String, tolerance: Rational },
}

impl Predicate {
    /// `signal == value` (Agda `ValuePredicate.Equals`).
    ///
    /// # Errors
    /// The kernel's refusal of the predicate, typed as
    /// [`Rational::from_decimal`] types one ([`Error::Validation`] carrying the
    /// kernel's code, [`Error::InputBoundExceeded`] for a bound), or
    /// [`Error::RtsNotInitialized`] while the runtime is down.
    pub fn equals(
        signal: impl Into<String>,
        value: impl Into<Rational>,
    ) -> Result<Predicate, Error> {
        checked_predicate(Predicate::Equals {
            signal: signal.into(),
            value: value.into(),
        })
    }

    /// `signal < value` (Agda `ValuePredicate.LessThan`).
    ///
    /// # Errors
    /// As [`Predicate::equals`].
    pub fn less_than(
        signal: impl Into<String>,
        value: impl Into<Rational>,
    ) -> Result<Predicate, Error> {
        checked_predicate(Predicate::LessThan {
            signal: signal.into(),
            value: value.into(),
        })
    }

    /// `signal > value` (Agda `ValuePredicate.GreaterThan`).
    ///
    /// # Errors
    /// As [`Predicate::equals`].
    pub fn greater_than(
        signal: impl Into<String>,
        value: impl Into<Rational>,
    ) -> Result<Predicate, Error> {
        checked_predicate(Predicate::GreaterThan {
            signal: signal.into(),
            value: value.into(),
        })
    }

    /// `signal <= value` (Agda `ValuePredicate.LessThanOrEqual`).
    ///
    /// # Errors
    /// As [`Predicate::equals`].
    pub fn less_than_or_equal(
        signal: impl Into<String>,
        value: impl Into<Rational>,
    ) -> Result<Predicate, Error> {
        checked_predicate(Predicate::LessThanOrEqual {
            signal: signal.into(),
            value: value.into(),
        })
    }

    /// `signal >= value` (Agda `ValuePredicate.GreaterThanOrEqual`).
    ///
    /// # Errors
    /// As [`Predicate::equals`].
    pub fn greater_than_or_equal(
        signal: impl Into<String>,
        value: impl Into<Rational>,
    ) -> Result<Predicate, Error> {
        checked_predicate(Predicate::GreaterThanOrEqual {
            signal: signal.into(),
            value: value.into(),
        })
    }

    /// `min <= signal <= max` (Agda `ValuePredicate.Between`).
    ///
    /// # Errors
    /// As [`Predicate::equals`]; the kernel refuses a range whose minimum is
    /// above its maximum.
    pub fn between(
        signal: impl Into<String>,
        min: impl Into<Rational>,
        max: impl Into<Rational>,
    ) -> Result<Predicate, Error> {
        checked_predicate(Predicate::Between {
            signal: signal.into(),
            min: min.into(),
            max: max.into(),
        })
    }

    /// The signal moved by at least `delta` since the previous frame, a positive
    /// delta asking for a rise and a negative one for a fall
    /// (Agda `DeltaPredicate.ChangedBy`).
    ///
    /// # Errors
    /// As [`Predicate::equals`].
    pub fn changed_by(
        signal: impl Into<String>,
        delta: impl Into<Rational>,
    ) -> Result<Predicate, Error> {
        checked_predicate(Predicate::ChangedBy {
            signal: signal.into(),
            delta: delta.into(),
        })
    }

    /// The signal stayed within `tolerance` of its previous value
    /// (Agda `DeltaPredicate.StableWithin`).
    ///
    /// # Errors
    /// As [`Predicate::equals`]; the kernel refuses a negative tolerance.
    pub fn stable_within(
        signal: impl Into<String>,
        tolerance: impl Into<Rational>,
    ) -> Result<Predicate, Error> {
        checked_predicate(Predicate::StableWithin {
            signal: signal.into(),
            tolerance: tolerance.into(),
        })
    }
}

/// An LTL formula over signal predicates.
///
/// Recursive variants box their children. Construct directly, or via the
/// convenience constructors ([`Formula::never`], [`Formula::implies`], …).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Formula {
    /// A predicate leaf.
    Atomic(Predicate),
    /// Logical negation.
    Not(Box<Formula>),
    /// Conjunction.
    And(Box<Formula>, Box<Formula>),
    /// Disjunction.
    Or(Box<Formula>, Box<Formula>),
    /// Holds at the next step.
    Next(Box<Formula>),
    /// Holds at the next step, or vacuously at end-of-trace.
    WeakNext(Box<Formula>),
    /// Holds at every future step (G).
    Always(Box<Formula>),
    /// Holds at some future step (F).
    Eventually(Box<Formula>),
    /// `left` holds until `right` becomes true.
    Until(Box<Formula>, Box<Formula>),
    /// `right` holds up to and including when `left` becomes true.
    Release(Box<Formula>, Box<Formula>),
    /// `inner` holds at every step within `bound`.
    MetricAlways {
        bound: TimeBound,
        inner: Box<Formula>,
    },
    /// `inner` holds at some step within `bound`.
    MetricEventually {
        bound: TimeBound,
        inner: Box<Formula>,
    },
    /// Time-bounded until within `bound`.
    MetricUntil {
        bound: TimeBound,
        left: Box<Formula>,
        right: Box<Formula>,
    },
    /// Time-bounded release within `bound`.
    MetricRelease {
        bound: TimeBound,
        left: Box<Formula>,
        right: Box<Formula>,
    },
}

impl Formula {
    /// `G(¬p)`: the predicate never holds.
    #[must_use]
    pub fn never(p: Predicate) -> Formula {
        Formula::Always(Box::new(Formula::Not(Box::new(Formula::Atomic(p)))))
    }

    /// `¬antecedent ∨ consequent`, the standard LTL encoding of implication.
    #[must_use]
    pub fn implies(antecedent: Formula, consequent: Formula) -> Formula {
        Formula::Or(
            Box::new(Formula::Not(Box::new(antecedent))),
            Box::new(consequent),
        )
    }

    /// `G[0,bound] inner`, read by the kernel's property parse, the bound
    /// included, as the predicate builders' are.
    ///
    /// # Errors
    /// [`Error::Validation`] if `inner` nests past [`MAX_FORMULA_DEPTH`]; the
    /// kernel's refusal of the formula, typed as [`Predicate::equals`] types
    /// one; or [`Error::RtsNotInitialized`] while the runtime is down.
    pub fn always_within(bound: TimeBound, inner: Formula) -> Result<Formula, Error> {
        checked_formula(Formula::MetricAlways {
            bound,
            inner: Box::new(inner),
        })
    }

    /// `F[0,bound] inner`, read by the kernel's property parse as
    /// [`Formula::always_within`]'s is.
    ///
    /// # Errors
    /// As [`Formula::always_within`].
    pub fn eventually_within(bound: TimeBound, inner: Formula) -> Result<Formula, Error> {
        checked_formula(Formula::MetricEventually {
            bound,
            inner: Box::new(inner),
        })
    }

    /// Refuse the formula when it nests past [`MAX_FORMULA_DEPTH`], the
    /// writer's guard on its own recursion, which every route to the wire
    /// passes before the formula is written.
    ///
    /// # Errors
    /// [`Error::Validation`] naming the depth.
    pub(crate) fn within_depth(&self) -> Result<(), Error> {
        self.within_depth_from(0)
    }

    fn within_depth_from(&self, depth: usize) -> Result<(), Error> {
        if depth > MAX_FORMULA_DEPTH {
            return Err(Error::validation(format!(
                "formula nesting depth exceeds {MAX_FORMULA_DEPTH}"
            )));
        }
        match self {
            Formula::Atomic(_) => Ok(()),
            Formula::Not(inner)
            | Formula::Next(inner)
            | Formula::WeakNext(inner)
            | Formula::Always(inner)
            | Formula::Eventually(inner)
            | Formula::MetricAlways { inner, .. }
            | Formula::MetricEventually { inner, .. } => inner.within_depth_from(depth + 1),
            Formula::And(left, right)
            | Formula::Or(left, right)
            | Formula::Until(left, right)
            | Formula::Release(left, right)
            | Formula::MetricUntil { left, right, .. }
            | Formula::MetricRelease { left, right, .. } => {
                left.within_depth_from(depth + 1)?;
                right.within_depth_from(depth + 1)
            }
        }
    }
}

/// Refuse `f` as the kernel's property parse refuses it, reading the formula
/// exactly as `set_properties` writes one property: every field, ordering,
/// denominator and time bound is decided, and each signal name as an
/// identifier, whether a DBC carries the signal being left to
/// `set_properties`.
///
/// # Errors
/// [`Error::Validation`] if `f` nests past [`MAX_FORMULA_DEPTH`]; the kernel's
/// refusal, typed as [`Rational::from_decimal`] types one ([`Error::Validation`]
/// carrying the kernel's code, [`Error::InputBoundExceeded`] for a bound);
/// [`Error::RtsNotInitialized`] while the runtime is down.
pub(crate) fn check_formula(f: &Formula) -> Result<(), Error> {
    f.within_depth()?;
    check_property(&to_text(&Wire(f))?)
}

/// `f`, once the kernel's property parse reads it ([`check_formula`]).
fn checked_formula(f: Formula) -> Result<Formula, Error> {
    check_formula(&f)?;
    Ok(f)
}

/// `p`, once the kernel's property parse reads the atomic formula wrapping it
/// ([`check_formula`]).
fn checked_predicate(p: Predicate) -> Result<Predicate, Error> {
    check_property(&to_text(&Atom(&p))?)?;
    Ok(p)
}

// ── The kernel's JSON ───────────────────────────────────────────────────────
//
// Each object's keys are written in byte order (see `wire_json::json_object`).

/// A predicate as the atomic formula wrapping it.
struct Atom<'a>(&'a Predicate);

impl Serialize for Atom<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        json_object!(serializer, {
            "operator" => "atomic",
            "predicate" => &Wire(self.0),
        })
    }
}

/// A predicate carrying one rational under a key after `signal`.
fn comparison<S: Serializer>(
    serializer: S,
    tag: &str,
    signal: &str,
    key: &'static str,
    value: Rational,
) -> Result<S::Ok, S::Error> {
    let mut map = serializer.serialize_map(Some(3))?;
    map.serialize_entry("predicate", tag)?;
    map.serialize_entry("signal", signal)?;
    map.serialize_entry(key, &Wire(&value))?;
    map.end()
}

impl Serialize for Wire<'_, Predicate> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self.0 {
            Predicate::Equals { signal, value } => {
                comparison(serializer, "equals", signal, "value", *value)
            }
            Predicate::LessThan { signal, value } => {
                comparison(serializer, "lessThan", signal, "value", *value)
            }
            Predicate::GreaterThan { signal, value } => {
                comparison(serializer, "greaterThan", signal, "value", *value)
            }
            Predicate::LessThanOrEqual { signal, value } => {
                comparison(serializer, "lessThanOrEqual", signal, "value", *value)
            }
            Predicate::GreaterThanOrEqual { signal, value } => {
                comparison(serializer, "greaterThanOrEqual", signal, "value", *value)
            }
            Predicate::StableWithin { signal, tolerance } => {
                comparison(serializer, "stableWithin", signal, "tolerance", *tolerance)
            }
            Predicate::ChangedBy { signal, delta } => json_object!(serializer, {
                "delta" => &Wire(delta),
                "predicate" => "changedBy",
                "signal" => signal,
            }),
            Predicate::Between { signal, min, max } => json_object!(serializer, {
                "max" => &Wire(max),
                "min" => &Wire(min),
                "predicate" => "between",
                "signal" => signal,
            }),
        }
    }
}

/// An operator over one formula.
fn unary<S: Serializer>(serializer: S, op: &str, inner: &Formula) -> Result<S::Ok, S::Error> {
    json_object!(serializer, {
        "formula" => &Wire(inner),
        "operator" => op,
    })
}

/// An operator over two formulas.
fn binary<S: Serializer>(
    serializer: S,
    op: &str,
    left: &Formula,
    right: &Formula,
) -> Result<S::Ok, S::Error> {
    json_object!(serializer, {
        "left" => &Wire(left),
        "operator" => op,
        "right" => &Wire(right),
    })
}

/// A metric operator over one formula, with its time bound.
fn unary_within<S: Serializer>(
    serializer: S,
    op: &str,
    bound: TimeBound,
    inner: &Formula,
) -> Result<S::Ok, S::Error> {
    json_object!(serializer, {
        "formula" => &Wire(inner),
        "operator" => op,
        "timebound" => &Number::natural(bound.micros()),
    })
}

/// A metric operator over two formulas, with its time bound.
fn binary_within<S: Serializer>(
    serializer: S,
    op: &str,
    bound: TimeBound,
    left: &Formula,
    right: &Formula,
) -> Result<S::Ok, S::Error> {
    json_object!(serializer, {
        "left" => &Wire(left),
        "operator" => op,
        "right" => &Wire(right),
        "timebound" => &Number::natural(bound.micros()),
    })
}

/// A formula as `set_properties` writes one property. The recursion is
/// bounded by [`Formula::within_depth`], which every writer of a formula
/// passes first.
impl Serialize for Wire<'_, Formula> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self.0 {
            Formula::Atomic(p) => Atom(p).serialize(serializer),
            Formula::Not(f) => unary(serializer, "not", f),
            Formula::And(l, r) => binary(serializer, "and", l, r),
            Formula::Or(l, r) => binary(serializer, "or", l, r),
            Formula::Next(f) => unary(serializer, "next", f),
            Formula::WeakNext(f) => unary(serializer, "weakNext", f),
            Formula::Always(f) => unary(serializer, "always", f),
            Formula::Eventually(f) => unary(serializer, "eventually", f),
            Formula::Until(l, r) => binary(serializer, "until", l, r),
            Formula::Release(l, r) => binary(serializer, "release", l, r),
            Formula::MetricAlways { bound, inner } => {
                unary_within(serializer, "metricAlways", *bound, inner)
            }
            Formula::MetricEventually { bound, inner } => {
                unary_within(serializer, "metricEventually", *bound, inner)
            }
            Formula::MetricUntil { bound, left, right } => {
                binary_within(serializer, "metricUntil", *bound, left, right)
            }
            Formula::MetricRelease { bound, left, right } => {
                binary_within(serializer, "metricRelease", *bound, left, right)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Predicate;
    use crate::backend::ensure_rts_for_test;
    use crate::error::Error;
    use crate::types::Rational;

    #[test]
    fn a_predicate_the_kernel_refuses_is_refused_where_it_is_built() {
        ensure_rts_for_test(); // each builder hands its predicate to the kernel
        let err = Predicate::between("Voltage", 14, 11).expect_err("an inverted range");
        assert!(
            matches!(&err, Error::Validation { code: Some(code), located: None, .. }
                if code == "handler_property_refused"),
            "got: {err:?}"
        );
        assert_eq!(err.to_string(), "between: min 14 exceeds max 11");
    }

    #[test]
    fn equals_constructor_builds_equals_variant() {
        ensure_rts_for_test(); // each builder hands its predicate to the kernel
        assert_eq!(
            Predicate::equals("Speed", 220).expect("the kernel reads the predicate"),
            Predicate::Equals {
                signal: "Speed".to_string(),
                value: Rational::integer(220),
            }
        );
    }

    #[test]
    fn between_constructor_builds_between_variant() {
        ensure_rts_for_test(); // each builder hands its predicate to the kernel
        assert_eq!(
            Predicate::between("Voltage", 11, 14).expect("the kernel reads the predicate"),
            Predicate::Between {
                signal: "Voltage".to_string(),
                min: Rational::integer(11),
                max: Rational::integer(14),
            }
        );
    }

    #[test]
    fn changed_by_constructor_builds_changed_by_variant() {
        ensure_rts_for_test(); // each builder hands its predicate to the kernel
        assert_eq!(
            Predicate::changed_by("Speed", -10).expect("the kernel reads the predicate"),
            Predicate::ChangedBy {
                signal: "Speed".to_string(),
                delta: Rational::integer(-10),
            }
        );
    }

    #[test]
    fn stable_within_constructor_builds_stable_within_variant() {
        ensure_rts_for_test(); // each builder hands its predicate to the kernel
        assert_eq!(
            Predicate::stable_within("Temp", 2).expect("the kernel reads the predicate"),
            Predicate::StableWithin {
                signal: "Temp".to_string(),
                tolerance: Rational::integer(2),
            }
        );
    }

    #[test]
    fn less_than_constructor_builds_less_than_variant() {
        ensure_rts_for_test(); // each builder hands its predicate to the kernel
        assert_eq!(
            Predicate::less_than("Speed", 220).expect("the kernel reads the predicate"),
            Predicate::LessThan {
                signal: "Speed".to_string(),
                value: Rational::integer(220),
            }
        );
    }

    #[test]
    fn greater_than_constructor_builds_greater_than_variant() {
        ensure_rts_for_test(); // each builder hands its predicate to the kernel
        assert_eq!(
            Predicate::greater_than("Speed", 220).expect("the kernel reads the predicate"),
            Predicate::GreaterThan {
                signal: "Speed".to_string(),
                value: Rational::integer(220),
            }
        );
    }

    #[test]
    fn less_than_or_equal_constructor_builds_lte_variant() {
        ensure_rts_for_test(); // each builder hands its predicate to the kernel
        assert_eq!(
            Predicate::less_than_or_equal("Speed", 220).expect("the kernel reads the predicate"),
            Predicate::LessThanOrEqual {
                signal: "Speed".to_string(),
                value: Rational::integer(220),
            }
        );
    }

    #[test]
    fn greater_than_or_equal_constructor_builds_gte_variant() {
        ensure_rts_for_test(); // each builder hands its predicate to the kernel
        assert_eq!(
            Predicate::greater_than_or_equal("Speed", 220).expect("the kernel reads the predicate"),
            Predicate::GreaterThanOrEqual {
                signal: "Speed".to_string(),
                value: Rational::integer(220),
            }
        );
    }

    #[test]
    fn fractional_value_via_rational() {
        ensure_rts_for_test(); // each builder hands its predicate to the kernel
                               // A fractional threshold is passed as an explicit Rational (no From<f64>).
        let half = Rational::new(1, 2).expect("1/2 is a valid rational");
        assert_eq!(
            Predicate::less_than("Throttle", half).expect("the kernel reads the predicate"),
            Predicate::LessThan {
                signal: "Throttle".to_string(),
                value: half,
            }
        );
    }
}
