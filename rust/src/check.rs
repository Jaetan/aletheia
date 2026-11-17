// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Fluent check DSL: domain-friendly builders that compile to LTL [`Formula`]s
//! plus display metadata. The "engineers / CI" tier above the raw enums.
//!
//! Two entry points mirror the other bindings' check builders:
//! - [`signal`], single-signal invariants:
//!   `check::signal("Speed").never_exceeds(120)?`.
//! - [`when`], causal when/then:
//!   `check::when("Brake").exceeds(50).then("Light").equals(1).within(TimeBound(100_000))?`.
//!
//! Numeric values take `impl Into<Rational>`, so an integer literal works
//! directly (`never_exceeds(120)`); fractions use `Rational::new(1, 4)?`. A
//! window is a [`TimeBound`] in microseconds. Each chain's finishing call
//! hands the formula it made to the kernel's property parse, which refuses a
//! zero denominator, a range whose minimum is above its maximum, a time bound
//! past its limit and a signal name that is no identifier with the reason
//! `set_properties` would give, so a check is refused where it is built. The
//! parse needs the GHC runtime up ([`start_runtime`](crate::start_runtime) or a
//! client) and never starts it: while the runtime is down each finishing call
//! answers [`Error::RtsNotInitialized`]. The raw LTL combinators (until /
//! release / metric / and / or) stay on [`Formula`] for power users; this
//! module covers the common check vocabulary the peers expose.

use crate::backend::format_rational;
use crate::error::Error;
use crate::ltl::{check_formula, Formula, Predicate};
use crate::types::{Rational, TimeBound};

/// One piece of a check's deferred condition description. Literal text is fixed
/// when the check is built; a [`Rational`] is rendered lazily at
/// [`Check::condition_desc`] read-time via the kernel `formatℚ` (the SSOT
/// renderer), so building a check renders nothing.
#[derive(Debug, Clone, PartialEq, Eq)]
enum DescPart {
    /// Fixed text: an operator, a separator, or the `within {n}µs` suffix.
    Lit(String),
    /// A threshold rendered via the kernel at read-time.
    Rat(Rational),
}

/// An operator prefix followed by a single rational, e.g. `"<= "` + `v`.
fn op_desc(op: &str, v: Rational) -> Vec<DescPart> {
    vec![DescPart::Lit(op.to_string()), DescPart::Rat(v)]
}

/// `between {lo} and {hi}`.
fn between_desc(lo: Rational, hi: Rational) -> Vec<DescPart> {
    vec![
        DescPart::Lit("between ".to_string()),
        DescPart::Rat(lo),
        DescPart::Lit(" and ".to_string()),
        DescPart::Rat(hi),
    ]
}

/// `parts` followed by ` within {bound}µs`, the window in microseconds.
fn within_desc(mut parts: Vec<DescPart>, bound: TimeBound) -> Vec<DescPart> {
    parts.push(DescPart::Lit(format!(" within {}µs", bound.micros())));
    parts
}

/// Render a deferred description, delegating every threshold to the kernel
/// `formatℚ` so the output is byte-identical to the other bindings (no local
/// fallback).
fn render_desc(parts: &[DescPart]) -> Result<String, Error> {
    let mut out = String::new();
    for part in parts {
        match part {
            DescPart::Lit(s) => out.push_str(s),
            DescPart::Rat(r) => out.push_str(&format_rational(*r)?),
        }
    }
    Ok(out)
}

/// `G(predicate)`: the predicate holds at every step.
fn always_pred(p: Predicate) -> Formula {
    Formula::Always(Box::new(Formula::Atomic(p)))
}

/// The check over `formula`, once the kernel's property parse reads it.
fn checked(
    formula: Formula,
    signal_name: String,
    condition_desc: Vec<DescPart>,
) -> Result<Check, Error> {
    check_formula(&formula)?;
    Ok(Check {
        formula,
        name: String::new(),
        severity: String::new(),
        signal_name,
        condition_desc,
    })
}

/// A built check: an LTL [`Formula`] plus display/reporting metadata.
///
/// The metadata (`name`, `severity`, condition description) is **not** sent to
/// the core: [`Client::add_checks`](crate::Client::add_checks) binds only the
/// formula. It is for the caller's reporting (and violation enrichment).
/// Immutable; [`Check::named`] / [`Check::with_severity`] return a new value.
///
/// Every chain's finishing call answers `Result<Check, Error>`: the kernel's
/// refusal of the formula, typed as [`Rational::from_decimal`] types one
/// ([`Error::Validation`] carrying the kernel's code,
/// [`Error::InputBoundExceeded`] for a bound), or
/// [`Error::RtsNotInitialized`] while the runtime is down.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Check {
    formula: Formula,
    name: String,
    severity: String,
    signal_name: String,
    condition_desc: Vec<DescPart>,
}

impl Check {
    /// The LTL formula this check compiles to (what `add_checks` binds).
    #[must_use]
    pub fn formula(&self) -> &Formula {
        &self.formula
    }
    /// Human-readable name (empty if unset).
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }
    /// Severity label (empty if unset), free-form, matching the other bindings.
    #[must_use]
    pub fn severity(&self) -> &str {
        &self.severity
    }
    /// Primary signal the check concerns.
    #[must_use]
    pub fn signal_name(&self) -> &str {
        &self.signal_name
    }
    /// Human-readable description of the condition, with thresholds rendered via
    /// the kernel `formatℚ` (the SSOT renderer; byte-identical to the other
    /// bindings) and a window as ` within {n}µs`.
    ///
    /// # Errors
    /// [`Error::RtsNotInitialized`] if the GHC runtime is down: the renderer
    /// never starts it.
    pub fn condition_desc(&self) -> Result<String, Error> {
        render_desc(&self.condition_desc)
    }

    /// Return a copy with the human-readable name set.
    #[must_use]
    pub fn named(mut self, name: impl Into<String>) -> Check {
        self.name = name.into();
        self
    }
    /// Return a copy with the severity level set.
    #[must_use]
    pub fn with_severity(mut self, level: impl Into<String>) -> Check {
        self.severity = level.into();
        self
    }
}

// ── Single-signal checks ─────────────────────────────────────────────────────

/// Begin a single-signal check: `check::signal("Speed").never_exceeds(120)?`.
#[must_use]
pub fn signal(name: impl Into<String>) -> Signal {
    Signal { name: name.into() }
}

/// Builder for single-signal checks (from [`signal`]).
#[derive(Debug, Clone)]
pub struct Signal {
    name: String,
}

impl Signal {
    /// `G(signal <= value)`: the signal never goes above `value`; `value`
    /// itself is allowed (inclusive, matching the Agda core's
    /// `LessThanOrEqual` and the dual [`never_below`](Self::never_below) `>=`;
    /// "never exceeds 220" lets 220 pass).
    ///
    /// # Errors
    /// The kernel's refusal of the check (see [`Check`]).
    pub fn never_exceeds(self, value: impl Into<Rational>) -> Result<Check, Error> {
        let v = value.into();
        let f = always_pred(Predicate::LessThanOrEqual {
            signal: self.name.clone(),
            value: v,
        });
        checked(f, self.name, op_desc("<= ", v))
    }

    /// `G(signal >= value)`: the signal never drops below `value`.
    ///
    /// # Errors
    /// The kernel's refusal of the check (see [`Check`]).
    pub fn never_below(self, value: impl Into<Rational>) -> Result<Check, Error> {
        let v = value.into();
        let f = always_pred(Predicate::GreaterThanOrEqual {
            signal: self.name.clone(),
            value: v,
        });
        checked(f, self.name, op_desc(">= ", v))
    }

    /// `G(lo <= signal <= hi)`.
    ///
    /// # Errors
    /// The kernel's refusal of the check (see [`Check`]), a range whose `lo` is
    /// above its `hi` among them.
    pub fn stays_between(
        self,
        lo: impl Into<Rational>,
        hi: impl Into<Rational>,
    ) -> Result<Check, Error> {
        let (lo, hi) = (lo.into(), hi.into());
        let f = always_pred(Predicate::Between {
            signal: self.name.clone(),
            min: lo,
            max: hi,
        });
        checked(f, self.name, between_desc(lo, hi))
    }

    /// `G(¬(signal == value))`: the signal never equals `value`.
    ///
    /// # Errors
    /// The kernel's refusal of the check (see [`Check`]).
    pub fn never_equals(self, value: impl Into<Rational>) -> Result<Check, Error> {
        let v = value.into();
        let f = Formula::never(Predicate::Equals {
            signal: self.name.clone(),
            value: v,
        });
        checked(f, self.name, op_desc("!= ", v))
    }

    /// Begin an `equals(value).always()` chain, which
    /// [`SignalEquals::always`] checks.
    #[must_use]
    pub fn equals(self, value: impl Into<Rational>) -> SignalEquals {
        SignalEquals {
            name: self.name,
            value: value.into(),
        }
    }

    /// Begin a `settles_between(lo, hi).within(bound)` chain, which
    /// [`Settles::within`] checks, so the chain never breaks.
    #[must_use]
    pub fn settles_between(self, lo: impl Into<Rational>, hi: impl Into<Rational>) -> Settles {
        Settles {
            name: self.name,
            lo: lo.into(),
            hi: hi.into(),
        }
    }
}

/// Intermediate from [`Signal::equals`]; finish with [`SignalEquals::always`].
#[derive(Debug, Clone)]
pub struct SignalEquals {
    name: String,
    value: Rational,
}

impl SignalEquals {
    /// `G(signal == value)`: the signal equals `value` at every step.
    ///
    /// # Errors
    /// The kernel's refusal of the check (see [`Check`]).
    pub fn always(self) -> Result<Check, Error> {
        let f = always_pred(Predicate::Equals {
            signal: self.name.clone(),
            value: self.value,
        });
        checked(f, self.name, op_desc("= ", self.value))
    }
}

/// Intermediate from [`Signal::settles_between`]; finish with [`Settles::within`].
#[derive(Debug, Clone)]
pub struct Settles {
    name: String,
    lo: Rational,
    hi: Rational,
}

impl Settles {
    /// `G≤bound(lo <= signal <= hi)`: the signal stays within `[lo, hi]` over
    /// the first `bound` microseconds.
    ///
    /// # Errors
    /// The kernel's refusal of the check (see [`Check`]), a range whose `lo` is
    /// above its `hi` among them.
    pub fn within(self, bound: TimeBound) -> Result<Check, Error> {
        let f = Formula::MetricAlways {
            bound,
            inner: Box::new(Formula::Atomic(Predicate::Between {
                signal: self.name.clone(),
                min: self.lo,
                max: self.hi,
            })),
        };
        let desc = within_desc(between_desc(self.lo, self.hi), bound);
        checked(f, self.name, desc)
    }
}

// ── Causal when/then checks ──────────────────────────────────────────────────

/// Begin a causal when/then check:
/// `check::when("Brake").exceeds(50).then("Light").equals(1).within(TimeBound(100_000))?`.
#[must_use]
pub fn when(name: impl Into<String>) -> When {
    When { name: name.into() }
}

/// Trigger-side builder (from [`when`]).
#[derive(Debug, Clone)]
pub struct When {
    name: String,
}

impl When {
    /// Trigger when `signal > value`.
    #[must_use]
    pub fn exceeds(self, value: impl Into<Rational>) -> WhenCondition {
        WhenCondition {
            trigger: Predicate::GreaterThan {
                signal: self.name,
                value: value.into(),
            },
        }
    }
    /// Trigger when `signal == value`.
    #[must_use]
    pub fn equals(self, value: impl Into<Rational>) -> WhenCondition {
        WhenCondition {
            trigger: Predicate::Equals {
                signal: self.name,
                value: value.into(),
            },
        }
    }
    /// Trigger when `signal < value`.
    #[must_use]
    pub fn drops_below(self, value: impl Into<Rational>) -> WhenCondition {
        WhenCondition {
            trigger: Predicate::LessThan {
                signal: self.name,
                value: value.into(),
            },
        }
    }
}

/// Holds the trigger predicate; continue with [`WhenCondition::then`].
#[derive(Debug, Clone)]
pub struct WhenCondition {
    trigger: Predicate,
}

impl WhenCondition {
    /// Name the signal that must respond to the trigger.
    #[must_use]
    pub fn then(self, signal: impl Into<String>) -> ThenSignal {
        ThenSignal {
            trigger: self.trigger,
            name: signal.into(),
        }
    }
}

/// Response-side builder (from [`WhenCondition::then`]).
#[derive(Debug, Clone)]
pub struct ThenSignal {
    trigger: Predicate,
    name: String,
}

impl ThenSignal {
    /// Response: the then-signal equals `value`.
    #[must_use]
    pub fn equals(self, value: impl Into<Rational>) -> ThenCondition {
        let v = value.into();
        let response = Predicate::Equals {
            signal: self.name.clone(),
            value: v,
        };
        self.respond(response, op_desc("= ", v))
    }
    /// Response: the then-signal exceeds `value`.
    #[must_use]
    pub fn exceeds(self, value: impl Into<Rational>) -> ThenCondition {
        let v = value.into();
        let response = Predicate::GreaterThan {
            signal: self.name.clone(),
            value: v,
        };
        self.respond(response, op_desc("> ", v))
    }
    /// Response: the then-signal stays between `lo` and `hi`, which
    /// [`ThenCondition::within`] checks, so the chain never breaks.
    #[must_use]
    pub fn stays_between(self, lo: impl Into<Rational>, hi: impl Into<Rational>) -> ThenCondition {
        let (lo, hi) = (lo.into(), hi.into());
        let response = Predicate::Between {
            signal: self.name.clone(),
            min: lo,
            max: hi,
        };
        self.respond(response, between_desc(lo, hi))
    }

    fn respond(self, response: Predicate, desc: Vec<DescPart>) -> ThenCondition {
        ThenCondition {
            trigger: self.trigger,
            response,
            then_signal: self.name,
            then_desc: desc,
        }
    }
}

/// Holds trigger + response; finish with [`ThenCondition::within`].
#[derive(Debug, Clone)]
pub struct ThenCondition {
    trigger: Predicate,
    response: Predicate,
    then_signal: String,
    then_desc: Vec<DescPart>,
}

impl ThenCondition {
    /// `G(trigger → F≤bound(response))`: whenever the trigger holds, the
    /// response must follow within `bound` microseconds. The kernel checks the
    /// whole formula, trigger included.
    ///
    /// # Errors
    /// The kernel's refusal of the check (see [`Check`]), a `stays_between`
    /// response whose `lo` is above its `hi` among them.
    pub fn within(self, bound: TimeBound) -> Result<Check, Error> {
        let f = Formula::Always(Box::new(Formula::implies(
            Formula::Atomic(self.trigger),
            Formula::MetricEventually {
                bound,
                inner: Box::new(Formula::Atomic(self.response)),
            },
        )));
        let desc = within_desc(self.then_desc, bound);
        checked(f, self.then_signal, desc)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::backend::ensure_rts_for_test;
    use crate::response::ErrorCode;

    fn r(n: i128) -> Rational {
        Rational::integer(n)
    }
    fn atom(p: Predicate) -> Formula {
        Formula::Atomic(p)
    }

    #[test]
    fn never_exceeds_is_always_less_than_or_equal() {
        ensure_rts_for_test(); // the builder checks its formula, the description renders through the kernel
                               // Inclusive: never_exceeds(v) compiles to G(s <= v), so s == v passes
                               // (matches Agda's LessThanOrEqual and the dual never_below's >=).
        let c = signal("Speed").never_exceeds(120).expect("valid");
        assert_eq!(
            *c.formula(),
            Formula::Always(Box::new(atom(Predicate::LessThanOrEqual {
                signal: "Speed".to_string(),
                value: r(120),
            })))
        );
        assert_eq!(c.signal_name(), "Speed");
        assert_eq!(c.condition_desc().unwrap(), "<= 120");
    }

    #[test]
    fn never_below_is_always_gte() {
        ensure_rts_for_test(); // the builder checks its formula through the kernel
        let c = signal("V").never_below(5).expect("valid");
        assert_eq!(
            *c.formula(),
            Formula::Always(Box::new(atom(Predicate::GreaterThanOrEqual {
                signal: "V".to_string(),
                value: r(5),
            })))
        );
    }

    #[test]
    fn never_equals_is_never_of_equals() {
        ensure_rts_for_test(); // the builder checks its formula, the description renders through the kernel
        let c = signal("Mode").never_equals(3).expect("valid");
        assert_eq!(
            *c.formula(),
            Formula::never(Predicate::Equals {
                signal: "Mode".to_string(),
                value: r(3),
            })
        );
        assert_eq!(c.condition_desc().unwrap(), "!= 3");
    }

    #[test]
    fn equals_always_and_stays_between() {
        ensure_rts_for_test(); // each builder checks its formula through the kernel
        let eq = signal("S").equals(1).always().expect("valid");
        assert_eq!(
            *eq.formula(),
            Formula::Always(Box::new(atom(Predicate::Equals {
                signal: "S".to_string(),
                value: r(1),
            })))
        );
        let sb = signal("S").stays_between(0, 100).expect("valid range");
        assert_eq!(
            *sb.formula(),
            Formula::Always(Box::new(atom(Predicate::Between {
                signal: "S".to_string(),
                min: r(0),
                max: r(100),
            })))
        );
    }

    #[test]
    fn settles_between_within_is_always_within() {
        ensure_rts_for_test(); // the builder checks its formula, the description renders through the kernel
        let c = signal("S")
            .settles_between(0, 10)
            .within(TimeBound(100_000))
            .expect("valid");
        assert_eq!(
            *c.formula(),
            Formula::MetricAlways {
                bound: TimeBound(100_000),
                inner: Box::new(atom(Predicate::Between {
                    signal: "S".to_string(),
                    min: r(0),
                    max: r(10),
                })),
            }
        );
        assert_eq!(
            c.condition_desc().unwrap(),
            "between 0 and 10 within 100000µs"
        );
    }

    #[test]
    fn when_then_within_is_always_implies_eventually_within() {
        ensure_rts_for_test(); // the builder checks its formula, the description renders through the kernel
        let c = when("Brake")
            .exceeds(50)
            .then("Light")
            .equals(1)
            .within(TimeBound(1_500))
            .expect("valid");
        assert_eq!(
            *c.formula(),
            Formula::Always(Box::new(Formula::implies(
                atom(Predicate::GreaterThan {
                    signal: "Brake".to_string(),
                    value: r(50),
                }),
                Formula::MetricEventually {
                    bound: TimeBound(1_500),
                    inner: Box::new(atom(Predicate::Equals {
                        signal: "Light".to_string(),
                        value: r(1),
                    })),
                }
            )))
        );
        assert_eq!(c.signal_name(), "Light");
        assert_eq!(c.condition_desc().unwrap(), "= 1 within 1500µs");
    }

    #[test]
    fn metadata_is_chainable() {
        ensure_rts_for_test(); // the builder checks its formula through the kernel
        let c = signal("S")
            .never_exceeds(1)
            .expect("valid")
            .named("limit")
            .with_severity("error");
        assert_eq!(c.name(), "limit");
        assert_eq!(c.severity(), "error");
    }

    /// Assert that `built` is the kernel's refusal of an inverted range: a
    /// validation error carrying the kernel's code and its message.
    fn assert_inverted(built: Result<Check, Error>, min: i32, max: i32) {
        let err = built.expect_err("an inverted range is refused");
        assert!(
            matches!(&err, Error::Validation { code: Some(code), located: None, .. }
                if *code == ErrorCode::HandlerPropertyRefused),
            "got: {err:?}"
        );
        assert_eq!(
            err.to_string(),
            format!("between: min {min} exceeds max {max}")
        );
    }

    #[test]
    fn an_inverted_range_is_the_kernels_refusal_where_the_chain_finishes() {
        ensure_rts_for_test(); // each builder checks its formula through the kernel
        assert_inverted(signal("S").stays_between(10, 5), 10, 5);
        assert_inverted(
            signal("S").settles_between(10, 5).within(TimeBound(100)),
            10,
            5,
        );
        assert_inverted(
            when("A")
                .exceeds(1)
                .then("B")
                .stays_between(10, 5)
                .within(TimeBound(100)),
            10,
            5,
        );
    }

    #[test]
    fn a_window_reaches_from_zero_to_the_largest_time_bound() {
        ensure_rts_for_test(); // each builder checks its formula through the kernel
        for bound in [TimeBound(0), TimeBound(u64::MAX)] {
            signal("S")
                .settles_between(0, 10)
                .within(bound)
                .unwrap_or_else(|e| panic!("settles within {bound:?}: {e}"));
            when("A")
                .exceeds(1)
                .then("B")
                .equals(1)
                .within(bound)
                .unwrap_or_else(|e| panic!("when then within {bound:?}: {e}"));
        }
    }
}
