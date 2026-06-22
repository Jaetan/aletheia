// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! LTL predicates and formulas.
//!
//! `Predicate` and `Formula` are plain Rust enums — naturally sealed and
//! exhaustively matchable, replacing the Go binding's `predicate()` / `formula()`
//! sealed-interface marker methods with no ceremony. `to_value` emits the exact
//! JSON wire shape the Agda core accepts (`{"operator":…}` for formulas,
//! `{"predicate":…}` for atoms), enforcing the same validity rules the other
//! bindings apply at serialization time.

use serde_json::{json, Value};

use crate::error::Error;
use crate::types::{Rational, TimeBound};

/// Client-side recursion guard on formula nesting depth (mirrors Go's 100-deep
/// stack guard), applied before serialization to fail fast rather than recurse
/// unboundedly. This is **distinct from** the kernel's JSON nesting cap of 64
/// (`Aletheia.Limits.max-nesting-depth`), which is the true wire limit: a formula
/// deeper than 64 is rejected by the core as a `nesting_depth` bound even though
/// it passes this guard.
pub const MAX_FORMULA_DEPTH: usize = 100;

/// A signal predicate — an atomic proposition over one signal's value.
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

/// Compare two rationals with positive denominators: `a <= b`.
fn rational_le(a: Rational, b: Rational) -> bool {
    // Denominators are guaranteed positive by `Rational::new`, so the direction
    // of the inequality is preserved by cross-multiplication. i128 avoids i64
    // overflow on the product.
    i128::from(a.numerator()) * i128::from(b.denominator())
        <= i128::from(b.numerator()) * i128::from(a.denominator())
}

impl Predicate {
    /// `signal == value` (Agda `ValuePredicate.Equals`).
    #[must_use]
    pub fn equals(signal: impl Into<String>, value: impl Into<Rational>) -> Predicate {
        Predicate::Equals {
            signal: signal.into(),
            value: value.into(),
        }
    }

    /// `signal < value` (Agda `ValuePredicate.LessThan`).
    #[must_use]
    pub fn less_than(signal: impl Into<String>, value: impl Into<Rational>) -> Predicate {
        Predicate::LessThan {
            signal: signal.into(),
            value: value.into(),
        }
    }

    /// `signal > value` (Agda `ValuePredicate.GreaterThan`).
    #[must_use]
    pub fn greater_than(signal: impl Into<String>, value: impl Into<Rational>) -> Predicate {
        Predicate::GreaterThan {
            signal: signal.into(),
            value: value.into(),
        }
    }

    /// `signal <= value` (Agda `ValuePredicate.LessThanOrEqual`).
    #[must_use]
    pub fn less_than_or_equal(signal: impl Into<String>, value: impl Into<Rational>) -> Predicate {
        Predicate::LessThanOrEqual {
            signal: signal.into(),
            value: value.into(),
        }
    }

    /// `signal >= value` (Agda `ValuePredicate.GreaterThanOrEqual`).
    #[must_use]
    pub fn greater_than_or_equal(
        signal: impl Into<String>,
        value: impl Into<Rational>,
    ) -> Predicate {
        Predicate::GreaterThanOrEqual {
            signal: signal.into(),
            value: value.into(),
        }
    }

    /// Encode the predicate as its `{"predicate":…}` wire object.
    ///
    /// # Errors
    /// [`Error::Validation`] if `Between.min > max` or `StableWithin.tolerance < 0`.
    pub(crate) fn to_value(&self) -> Result<Value, Error> {
        let v = match self {
            Predicate::Equals { signal, value } => {
                json!({ "predicate": "equals", "signal": signal, "value": value.to_value() })
            }
            Predicate::LessThan { signal, value } => {
                json!({ "predicate": "lessThan", "signal": signal, "value": value.to_value() })
            }
            Predicate::GreaterThan { signal, value } => {
                json!({ "predicate": "greaterThan", "signal": signal, "value": value.to_value() })
            }
            Predicate::LessThanOrEqual { signal, value } => {
                json!({ "predicate": "lessThanOrEqual", "signal": signal, "value": value.to_value() })
            }
            Predicate::GreaterThanOrEqual { signal, value } => {
                json!({ "predicate": "greaterThanOrEqual", "signal": signal, "value": value.to_value() })
            }
            Predicate::Between { signal, min, max } => {
                if !rational_le(*min, *max) {
                    return Err(Error::Validation(format!(
                        "between: min ({}/{}) exceeds max ({}/{})",
                        min.numerator(),
                        min.denominator(),
                        max.numerator(),
                        max.denominator()
                    )));
                }
                json!({ "predicate": "between", "signal": signal,
                        "min": min.to_value(), "max": max.to_value() })
            }
            Predicate::ChangedBy { signal, delta } => {
                json!({ "predicate": "changedBy", "signal": signal, "delta": delta.to_value() })
            }
            Predicate::StableWithin { signal, tolerance } => {
                if tolerance.numerator() < 0 {
                    return Err(Error::Validation(format!(
                        "stableWithin: negative tolerance {}/{}",
                        tolerance.numerator(),
                        tolerance.denominator()
                    )));
                }
                json!({ "predicate": "stableWithin", "signal": signal,
                        "tolerance": tolerance.to_value() })
            }
        };
        Ok(v)
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
    /// `G(¬p)` — the predicate never holds.
    #[must_use]
    pub fn never(p: Predicate) -> Formula {
        Formula::Always(Box::new(Formula::Not(Box::new(Formula::Atomic(p)))))
    }

    /// `¬antecedent ∨ consequent` — the standard LTL encoding of implication.
    #[must_use]
    pub fn implies(antecedent: Formula, consequent: Formula) -> Formula {
        Formula::Or(
            Box::new(Formula::Not(Box::new(antecedent))),
            Box::new(consequent),
        )
    }

    /// `G[0,bound] inner`.
    #[must_use]
    pub fn always_within(bound: TimeBound, inner: Formula) -> Formula {
        Formula::MetricAlways {
            bound,
            inner: Box::new(inner),
        }
    }

    /// `F[0,bound] inner`.
    #[must_use]
    pub fn eventually_within(bound: TimeBound, inner: Formula) -> Formula {
        Formula::MetricEventually {
            bound,
            inner: Box::new(inner),
        }
    }

    /// Encode the formula as its `{"operator":…}` wire object.
    ///
    /// # Errors
    /// [`Error::Validation`] if nesting exceeds [`MAX_FORMULA_DEPTH`] or a
    /// contained predicate is invalid.
    pub(crate) fn to_value(&self) -> Result<Value, Error> {
        self.to_value_depth(0)
    }

    fn to_value_depth(&self, depth: usize) -> Result<Value, Error> {
        if depth > MAX_FORMULA_DEPTH {
            return Err(Error::Validation(format!(
                "formula nesting depth exceeds {MAX_FORMULA_DEPTH}"
            )));
        }
        let unary = |op: &str, inner: &Formula| -> Result<Value, Error> {
            Ok(json!({ "operator": op, "formula": inner.to_value_depth(depth + 1)? }))
        };
        let binary = |op: &str, l: &Formula, r: &Formula| -> Result<Value, Error> {
            Ok(json!({ "operator": op,
                       "left": l.to_value_depth(depth + 1)?,
                       "right": r.to_value_depth(depth + 1)? }))
        };
        let metric_unary = |op: &str, b: TimeBound, inner: &Formula| -> Result<Value, Error> {
            Ok(json!({ "operator": op, "timebound": b.micros(),
                       "formula": inner.to_value_depth(depth + 1)? }))
        };
        let metric_binary =
            |op: &str, b: TimeBound, l: &Formula, r: &Formula| -> Result<Value, Error> {
                Ok(json!({ "operator": op, "timebound": b.micros(),
                           "left": l.to_value_depth(depth + 1)?,
                           "right": r.to_value_depth(depth + 1)? }))
            };
        match self {
            Formula::Atomic(p) => Ok(json!({ "operator": "atomic", "predicate": p.to_value()? })),
            Formula::Not(f) => unary("not", f),
            Formula::And(l, r) => binary("and", l, r),
            Formula::Or(l, r) => binary("or", l, r),
            Formula::Next(f) => unary("next", f),
            Formula::WeakNext(f) => unary("weakNext", f),
            Formula::Always(f) => unary("always", f),
            Formula::Eventually(f) => unary("eventually", f),
            Formula::Until(l, r) => binary("until", l, r),
            Formula::Release(l, r) => binary("release", l, r),
            Formula::MetricAlways { bound, inner } => metric_unary("metricAlways", *bound, inner),
            Formula::MetricEventually { bound, inner } => {
                metric_unary("metricEventually", *bound, inner)
            }
            Formula::MetricUntil { bound, left, right } => {
                metric_binary("metricUntil", *bound, left, right)
            }
            Formula::MetricRelease { bound, left, right } => {
                metric_binary("metricRelease", *bound, left, right)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Predicate;
    use crate::types::Rational;

    #[test]
    fn equals_constructor_builds_equals_variant() {
        assert_eq!(
            Predicate::equals("Speed", 220),
            Predicate::Equals {
                signal: "Speed".to_string(),
                value: Rational::integer(220),
            }
        );
    }

    #[test]
    fn less_than_constructor_builds_less_than_variant() {
        assert_eq!(
            Predicate::less_than("Speed", 220),
            Predicate::LessThan {
                signal: "Speed".to_string(),
                value: Rational::integer(220),
            }
        );
    }

    #[test]
    fn greater_than_constructor_builds_greater_than_variant() {
        assert_eq!(
            Predicate::greater_than("Speed", 220),
            Predicate::GreaterThan {
                signal: "Speed".to_string(),
                value: Rational::integer(220),
            }
        );
    }

    #[test]
    fn less_than_or_equal_constructor_builds_lte_variant() {
        assert_eq!(
            Predicate::less_than_or_equal("Speed", 220),
            Predicate::LessThanOrEqual {
                signal: "Speed".to_string(),
                value: Rational::integer(220),
            }
        );
    }

    #[test]
    fn greater_than_or_equal_constructor_builds_gte_variant() {
        assert_eq!(
            Predicate::greater_than_or_equal("Speed", 220),
            Predicate::GreaterThanOrEqual {
                signal: "Speed".to_string(),
                value: Rational::integer(220),
            }
        );
    }

    #[test]
    fn fractional_value_via_rational() {
        // A fractional threshold is passed as an explicit Rational (no From<f64>).
        let half = Rational::new(1, 2).expect("1/2 is a valid rational");
        assert_eq!(
            Predicate::less_than("Throttle", half),
            Predicate::LessThan {
                signal: "Throttle".to_string(),
                value: half,
            }
        );
    }
}
