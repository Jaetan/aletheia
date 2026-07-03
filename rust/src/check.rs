// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Fluent check DSL — domain-friendly builders that compile to LTL [`Formula`]s
//! plus display metadata. The "engineers / CI" tier above the raw enums.
//!
//! Two entry points mirror the other bindings' check builders:
//! - [`signal`] — single-signal invariants:
//!   `check::signal("Speed").never_exceeds(120)`.
//! - [`when`] — causal when/then:
//!   `check::when("Brake").exceeds(50).then("Light").equals(1).within(100)`.
//!
//! Numeric values take `impl Into<Rational>`, so an `i64` literal works directly
//! (`never_exceeds(120)`); fractions use `Rational::new(1, 4)?`. The raw LTL
//! combinators (until / release / metric / and / or) stay on [`Formula`] for
//! power users — this module covers the common check vocabulary the peers expose.

use crate::backend::format_rational;
use crate::error::Error;
use crate::ltl::{Formula, Predicate};
use crate::types::{Rational, TimeBound};

const US_PER_MS: u64 = 1000;

/// One piece of a check's deferred condition description. Literal text is fixed
/// when the check is built; a [`Rational`] is rendered lazily at
/// [`Check::condition_desc`] read-time via the kernel `formatℚ` (the SSOT
/// renderer). Deferring keeps check *construction* infallible — only reading the
/// description can surface a library-load error — so the fluent builder chain
/// (`when().then().equals().within()`) stays `?`-free.
#[derive(Debug, Clone, PartialEq, Eq)]
enum DescPart {
    /// Fixed text — an operator, a separator, or the `within {n}ms` suffix.
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

/// Render a rational into an inverted-range **validation error message** (`5`, or
/// `1/4`). Display descriptions delegate to the kernel `formatℚ` (see [`DescPart`]
/// / [`render_desc`]); `rat_str` is retained only for these error strings, which
/// must report a bad range without depending on a fallible FFI library load.
fn rat_str(r: Rational) -> String {
    // Exact via the kernel format_rational when the RTS is up (a terminating
    // decimal or fraction, matching enrich.rs and the C++/Go/Python bindings);
    // else a bare "num/den" fraction fallback — a range-validation error can be
    // constructed before any backend exists, so this must not depend on the RTS
    // and must never emit a lossy float.
    if let Ok(s) = format_rational(r) {
        return s;
    }
    if r.denominator() == 1 {
        r.numerator().to_string()
    } else {
        format!("{}/{}", r.numerator(), r.denominator())
    }
}

/// Convert milliseconds to a microsecond [`TimeBound`], guarding overflow.
fn ms_to_bound(ms: u64) -> Result<TimeBound, Error> {
    let micros = ms.checked_mul(US_PER_MS).ok_or_else(|| {
        Error::Validation(format!("time {ms} ms overflows microsecond conversion"))
    })?;
    Ok(TimeBound(micros))
}

/// `G(predicate)` — the predicate holds at every step.
fn always_pred(p: Predicate) -> Formula {
    Formula::Always(Box::new(Formula::Atomic(p)))
}

/// A built check: an LTL [`Formula`] plus display/reporting metadata.
///
/// The metadata (`name`, `severity`, condition description) is **not** sent to
/// the core — [`Client::add_checks`](crate::Client::add_checks) binds only the
/// formula. It is for the caller's reporting (and, later, violation enrichment).
/// Immutable; [`Check::named`] / [`Check::with_severity`] return a new value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Check {
    formula: Formula,
    name: String,
    severity: String,
    signal_name: String,
    condition_desc: Vec<DescPart>,
}

impl Check {
    fn new(formula: Formula, signal_name: String, condition_desc: Vec<DescPart>) -> Check {
        Check {
            formula,
            name: String::new(),
            severity: String::new(),
            signal_name,
            condition_desc,
        }
    }

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
    /// Severity label (empty if unset) — free-form, matching the other bindings.
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
    /// bindings).
    ///
    /// # Errors
    /// [`Error`] if the kernel renderer's shared library cannot be loaded. The
    /// renderer loads `libaletheia-ffi.so` itself, independently of any backend, so
    /// this depends only on whether the library is locatable (see `ALETHEIA_LIB`) —
    /// not on whether a [`Client`](crate::Client) exists (a `MockBackend` client
    /// does not load the `.so` for you).
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

/// Begin a single-signal check: `check::signal("Speed").never_exceeds(120)`.
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
    /// `G(signal <= value)` — the signal never goes above `value`; `value`
    /// itself is allowed (inclusive — matches the Agda core's `LessThanOrEqual`
    /// and the dual [`never_below`](Self::never_below) `>=`; "never exceeds 220"
    /// lets 220 pass).
    #[must_use]
    pub fn never_exceeds(self, value: impl Into<Rational>) -> Check {
        let v = value.into();
        let f = always_pred(Predicate::LessThanOrEqual {
            signal: self.name.clone(),
            value: v,
        });
        Check::new(f, self.name, op_desc("<= ", v))
    }

    /// `G(signal >= value)` — the signal never drops below `value`.
    #[must_use]
    pub fn never_below(self, value: impl Into<Rational>) -> Check {
        let v = value.into();
        let f = always_pred(Predicate::GreaterThanOrEqual {
            signal: self.name.clone(),
            value: v,
        });
        Check::new(f, self.name, op_desc(">= ", v))
    }

    /// `G(lo <= signal <= hi)`.
    ///
    /// # Errors
    /// [`Error::Validation`] if `lo > hi` (an inverted, always-false range).
    pub fn stays_between(
        self,
        lo: impl Into<Rational>,
        hi: impl Into<Rational>,
    ) -> Result<Check, Error> {
        let (lo, hi) = (lo.into(), hi.into());
        if !lo.le(hi) {
            return Err(Error::Validation(format!(
                "stays_between: lo ({}) must be <= hi ({})",
                rat_str(lo),
                rat_str(hi)
            )));
        }
        let f = always_pred(Predicate::Between {
            signal: self.name.clone(),
            min: lo,
            max: hi,
        });
        Ok(Check::new(f, self.name, between_desc(lo, hi)))
    }

    /// `G(¬(signal == value))` — the signal never equals `value`.
    #[must_use]
    pub fn never_equals(self, value: impl Into<Rational>) -> Check {
        let v = value.into();
        let f = Formula::never(Predicate::Equals {
            signal: self.name.clone(),
            value: v,
        });
        Check::new(f, self.name, op_desc("!= ", v))
    }

    /// Begin an `equals(value).always()` chain.
    #[must_use]
    pub fn equals(self, value: impl Into<Rational>) -> SignalEquals {
        SignalEquals {
            name: self.name,
            value: value.into(),
        }
    }

    /// Begin a `settles_between(lo, hi).within(ms)` chain. An inverted range is
    /// captured and surfaced from [`Settles::within`] so the chain stays fluent.
    #[must_use]
    pub fn settles_between(self, lo: impl Into<Rational>, hi: impl Into<Rational>) -> Settles {
        let (lo, hi) = (lo.into(), hi.into());
        Settles {
            range_ok: lo.le(hi),
            name: self.name,
            lo,
            hi,
        }
    }
}

/// Intermediate from [`Signal::equals`] — finish with [`SignalEquals::always`].
#[derive(Debug, Clone)]
pub struct SignalEquals {
    name: String,
    value: Rational,
}

impl SignalEquals {
    /// `G(signal == value)` — the signal equals `value` at every step.
    #[must_use]
    pub fn always(self) -> Check {
        let f = always_pred(Predicate::Equals {
            signal: self.name.clone(),
            value: self.value,
        });
        Check::new(f, self.name, op_desc("= ", self.value))
    }
}

/// Intermediate from [`Signal::settles_between`] — finish with [`Settles::within`].
#[derive(Debug, Clone)]
pub struct Settles {
    name: String,
    lo: Rational,
    hi: Rational,
    range_ok: bool,
}

impl Settles {
    /// `G≤ms(lo <= signal <= hi)` — the signal stays within `[lo, hi]` over the
    /// first `ms` milliseconds.
    ///
    /// # Errors
    /// [`Error::Validation`] if the range was inverted (`lo > hi`) or `ms`
    /// overflows the microsecond conversion.
    pub fn within(self, ms: u64) -> Result<Check, Error> {
        if !self.range_ok {
            return Err(Error::Validation(format!(
                "settles_between: lo ({}) must be <= hi ({})",
                rat_str(self.lo),
                rat_str(self.hi)
            )));
        }
        let bound = ms_to_bound(ms)?;
        let f = Formula::always_within(
            bound,
            Formula::Atomic(Predicate::Between {
                signal: self.name.clone(),
                min: self.lo,
                max: self.hi,
            }),
        );
        let mut desc = between_desc(self.lo, self.hi);
        desc.push(DescPart::Lit(format!(" within {ms}ms")));
        Ok(Check::new(f, self.name, desc))
    }
}

// ── Causal when/then checks ──────────────────────────────────────────────────

/// Begin a causal when/then check:
/// `check::when("Brake").exceeds(50).then("Light").equals(1).within(100)`.
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
        self.respond(response, op_desc("= ", v), None)
    }
    /// Response: the then-signal exceeds `value`.
    #[must_use]
    pub fn exceeds(self, value: impl Into<Rational>) -> ThenCondition {
        let v = value.into();
        let response = Predicate::GreaterThan {
            signal: self.name.clone(),
            value: v,
        };
        self.respond(response, op_desc("> ", v), None)
    }
    /// Response: the then-signal stays between `lo` and `hi` (inverted range is
    /// surfaced from [`ThenCondition::within`]).
    #[must_use]
    pub fn stays_between(self, lo: impl Into<Rational>, hi: impl Into<Rational>) -> ThenCondition {
        let (lo, hi) = (lo.into(), hi.into());
        let range_err = if lo.le(hi) {
            None
        } else {
            Some(format!(
                "then stays_between: lo ({}) must be <= hi ({})",
                rat_str(lo),
                rat_str(hi)
            ))
        };
        let response = Predicate::Between {
            signal: self.name.clone(),
            min: lo,
            max: hi,
        };
        self.respond(response, between_desc(lo, hi), range_err)
    }

    fn respond(
        self,
        response: Predicate,
        desc: Vec<DescPart>,
        range_err: Option<String>,
    ) -> ThenCondition {
        ThenCondition {
            trigger: self.trigger,
            response,
            then_signal: self.name,
            then_desc: desc,
            range_err,
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
    /// The rendered inverted-range error (with `lo`/`hi`), captured from
    /// `stays_between` and surfaced here so the chain stays fluent.
    range_err: Option<String>,
}

impl ThenCondition {
    /// `G(trigger → F≤ms(response))` — whenever the trigger holds, the response
    /// must follow within `ms` milliseconds.
    ///
    /// # Errors
    /// [`Error::Validation`] if a `stays_between` response range was inverted or
    /// `ms` overflows the microsecond conversion.
    pub fn within(self, ms: u64) -> Result<Check, Error> {
        if let Some(err) = self.range_err {
            return Err(Error::Validation(err));
        }
        let bound = ms_to_bound(ms)?;
        let f = Formula::Always(Box::new(Formula::implies(
            Formula::Atomic(self.trigger),
            Formula::eventually_within(bound, Formula::Atomic(self.response)),
        )));
        let mut desc = self.then_desc;
        desc.push(DescPart::Lit(format!(" within {ms}ms")));
        Ok(Check::new(f, self.then_signal, desc))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::backend::ensure_rts_for_test;

    fn r(n: i64) -> Rational {
        Rational::integer(n)
    }
    fn atom(p: Predicate) -> Formula {
        Formula::Atomic(p)
    }

    #[test]
    fn never_exceeds_is_always_less_than_or_equal() {
        // Inclusive: never_exceeds(v) compiles to G(s <= v), so s == v passes
        // (matches Agda's LessThanOrEqual and the dual never_below's >=).
        let c = signal("Speed").never_exceeds(120);
        assert_eq!(
            *c.formula(),
            Formula::Always(Box::new(atom(Predicate::LessThanOrEqual {
                signal: "Speed".to_string(),
                value: r(120),
            })))
        );
        assert_eq!(c.signal_name(), "Speed");
        ensure_rts_for_test(); // condition_desc renders the threshold via the kernel
        assert_eq!(c.condition_desc().unwrap(), "<= 120");
    }

    #[test]
    fn never_below_is_always_gte() {
        let c = signal("V").never_below(5);
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
        let c = signal("Mode").never_equals(3);
        assert_eq!(
            *c.formula(),
            Formula::never(Predicate::Equals {
                signal: "Mode".to_string(),
                value: r(3),
            })
        );
        ensure_rts_for_test(); // condition_desc renders the threshold via the kernel
        assert_eq!(c.condition_desc().unwrap(), "!= 3");
    }

    #[test]
    fn equals_always_and_stays_between() {
        let eq = signal("S").equals(1).always();
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
        let c = signal("S")
            .settles_between(0, 10)
            .within(100)
            .expect("valid");
        assert_eq!(
            *c.formula(),
            Formula::always_within(
                TimeBound(100_000),
                atom(Predicate::Between {
                    signal: "S".to_string(),
                    min: r(0),
                    max: r(10),
                })
            )
        );
        ensure_rts_for_test(); // condition_desc renders the threshold via the kernel
        assert_eq!(c.condition_desc().unwrap(), "between 0 and 10 within 100ms");
    }

    #[test]
    fn when_then_within_is_always_implies_eventually_within() {
        let c = when("Brake")
            .exceeds(50)
            .then("Light")
            .equals(1)
            .within(100)
            .expect("valid");
        assert_eq!(
            *c.formula(),
            Formula::Always(Box::new(Formula::implies(
                atom(Predicate::GreaterThan {
                    signal: "Brake".to_string(),
                    value: r(50),
                }),
                Formula::eventually_within(
                    TimeBound(100_000),
                    atom(Predicate::Equals {
                        signal: "Light".to_string(),
                        value: r(1),
                    })
                )
            )))
        );
        assert_eq!(c.signal_name(), "Light");
    }

    #[test]
    fn metadata_is_chainable() {
        let c = signal("S")
            .never_exceeds(1)
            .named("limit")
            .with_severity("error");
        assert_eq!(c.name(), "limit");
        assert_eq!(c.severity(), "error");
    }

    #[test]
    fn inverted_and_overflow_ranges_error() {
        assert!(signal("S").stays_between(10, 5).is_err());
        assert!(signal("S").settles_between(10, 5).within(100).is_err());
        assert!(signal("S").settles_between(0, 10).within(u64::MAX).is_err());
        assert!(when("A")
            .exceeds(1)
            .then("B")
            .stays_between(10, 5)
            .within(100)
            .is_err());
    }

    #[test]
    fn inverted_range_error_renders_rational_via_kernel() {
        ensure_rts_for_test(); // RTS up -> rat_str routes through format_rational
        let err = signal("Speed")
            .stays_between(Rational::new(1, 2).unwrap(), 0)
            .unwrap_err();
        // 1/2 renders as the exact decimal "0.5" (kernel format_rational, matching
        // enrich.rs and the C++/Go/Python bindings), not rat_str's bare "1/2".
        assert!(
            format!("{err}").contains("0.5"),
            "error should render 1/2 as the kernel decimal 0.5; got: {err}"
        );
    }
}
