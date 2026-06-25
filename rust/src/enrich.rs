// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Client-side violation enrichment (Slice R4b).
//!
//! The verified core reports a violation with a raw `reason` string but no
//! signal context. This module reconstructs that context **client-side** — the
//! same approach as the Go (`enrich.go`) and Python (`_enrichment.py`) bindings:
//! from each registered [`Formula`] it derives a [`PropertyDiagnostic`] (the
//! signals the formula references + a human-readable description), and on a
//! violation it pairs those signals with their last-known values to build an
//! [`Enrichment`](crate::Enrichment).
//!
//! Rational values render through the verified kernel's `formatℚ` (via
//! [`format_rational`]) — the same renderer the
//! check DSL's `condition_desc` now uses, so a threshold and a signal value render
//! identically across both surfaces *and* byte-identically to the Python / Go /
//! C++ bindings (the single source of truth lives in Agda; there is no local
//! fallback). `enriched_reason` is a human-readable diagnostic; no gate pins it to
//! the peers' byte-for-byte output (their tests assert substrings, not equality).

use crate::backend::format_rational;
use crate::error::Error;
use crate::ltl::{Formula, Predicate};
use crate::types::{Rational, TimeBound};

/// Diagnostic metadata derived from a formula, cached per registered property.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PropertyDiagnostic {
    /// Signals referenced by the formula, deduplicated in first-seen order.
    pub signals: Vec<String>,
    /// Human-readable rendering of the formula.
    pub formula_desc: String,
}

/// Build the diagnostic for a formula.
///
/// # Errors
/// Propagates an [`Error`] if the kernel rational renderer's library cannot be
/// loaded (see [`format_rational`]); callers render thresholds at property-setup
/// time, where a load failure is a legitimate setup error.
pub(crate) fn build_diagnostic(f: &Formula) -> Result<PropertyDiagnostic, Error> {
    Ok(PropertyDiagnostic {
        signals: collect_signals(f),
        formula_desc: format_formula(f)?,
    })
}

// ── Signal collection ─────────────────────────────────────────────────────────

/// The signal a predicate concerns.
fn predicate_signal(p: &Predicate) -> &str {
    match p {
        Predicate::Equals { signal, .. }
        | Predicate::LessThan { signal, .. }
        | Predicate::GreaterThan { signal, .. }
        | Predicate::LessThanOrEqual { signal, .. }
        | Predicate::GreaterThanOrEqual { signal, .. }
        | Predicate::Between { signal, .. }
        | Predicate::ChangedBy { signal, .. }
        | Predicate::StableWithin { signal, .. } => signal,
    }
}

/// All signals referenced in a formula, deduplicated in first-seen order.
fn collect_signals(f: &Formula) -> Vec<String> {
    let mut out = Vec::new();
    collect_into(f, &mut out);
    out
}

fn collect_into(f: &Formula, out: &mut Vec<String>) {
    match f {
        Formula::Atomic(p) => {
            let s = predicate_signal(p);
            if !out.iter().any(|x| x == s) {
                out.push(s.to_string());
            }
        }
        Formula::Not(inner)
        | Formula::Next(inner)
        | Formula::WeakNext(inner)
        | Formula::Always(inner)
        | Formula::Eventually(inner)
        | Formula::MetricAlways { inner, .. }
        | Formula::MetricEventually { inner, .. } => collect_into(inner, out),
        Formula::And(l, r)
        | Formula::Or(l, r)
        | Formula::Until(l, r)
        | Formula::Release(l, r)
        | Formula::MetricUntil {
            left: l, right: r, ..
        }
        | Formula::MetricRelease {
            left: l, right: r, ..
        } => {
            collect_into(l, out);
            collect_into(r, out);
        }
    }
}

// ── Formatting ────────────────────────────────────────────────────────────────

fn format_predicate(p: &Predicate) -> Result<String, Error> {
    Ok(match p {
        Predicate::Equals { signal, value } => format!("{signal} = {}", format_rational(*value)?),
        Predicate::LessThan { signal, value } => format!("{signal} < {}", format_rational(*value)?),
        Predicate::GreaterThan { signal, value } => {
            format!("{signal} > {}", format_rational(*value)?)
        }
        Predicate::LessThanOrEqual { signal, value } => {
            format!("{signal} <= {}", format_rational(*value)?)
        }
        Predicate::GreaterThanOrEqual { signal, value } => {
            format!("{signal} >= {}", format_rational(*value)?)
        }
        Predicate::Between { signal, min, max } => {
            format!(
                "{} <= {signal} <= {}",
                format_rational(*min)?,
                format_rational(*max)?
            )
        }
        Predicate::ChangedBy { signal, delta } => {
            if delta.numerator() >= 0 {
                format!("Δ{signal} >= {}", format_rational(*delta)?)
            } else {
                format!("Δ{signal} <= {}", format_rational(*delta)?)
            }
        }
        Predicate::StableWithin { signal, tolerance } => {
            format!("|Δ{signal}| <= {}", format_rational(*tolerance)?)
        }
    })
}

const US_PER_SECOND: u64 = 1_000_000;
const US_PER_MILLISECOND: u64 = 1_000;

fn format_timebound(t: TimeBound) -> String {
    let us = t.micros();
    if us.is_multiple_of(US_PER_SECOND) {
        format!("{}s", us / US_PER_SECOND)
    } else if us.is_multiple_of(US_PER_MILLISECOND) {
        format!("{}ms", us / US_PER_MILLISECOND)
    } else {
        format!("{us}μs")
    }
}

/// Human-readable rendering of a formula (the `never P` shorthand mirrors the peers).
fn format_formula(f: &Formula) -> Result<String, Error> {
    format_inner(f, false)
}

/// `parenthesize` wraps binary operators when nested in another binary operator.
fn format_inner(f: &Formula, parenthesize: bool) -> Result<String, Error> {
    let wrap = |s: String| if parenthesize { format!("({s})") } else { s };
    Ok(match f {
        Formula::Atomic(p) => format_predicate(p)?,
        Formula::Not(inner) => format!("not({})", format_inner(inner, false)?),
        Formula::And(l, r) => wrap(format!(
            "{} and {}",
            format_inner(l, true)?,
            format_inner(r, true)?
        )),
        Formula::Or(l, r) => wrap(format!(
            "{} or {}",
            format_inner(l, true)?,
            format_inner(r, true)?
        )),
        Formula::Next(inner) => format!("next({})", format_inner(inner, false)?),
        Formula::WeakNext(inner) => format!("weak_next({})", format_inner(inner, false)?),
        Formula::Always(inner) => {
            // Detect the `never P` shape: Always(Not(Atomic(p))).
            if let Formula::Not(n) = inner.as_ref() {
                if let Formula::Atomic(p) = n.as_ref() {
                    return Ok(format!("never {}", format_predicate(p)?));
                }
            }
            format!("always({})", format_inner(inner, false)?)
        }
        Formula::Eventually(inner) => format!("eventually({})", format_inner(inner, false)?),
        Formula::Until(l, r) => wrap(format!(
            "{} until {}",
            format_inner(l, true)?,
            format_inner(r, true)?
        )),
        Formula::Release(l, r) => wrap(format!(
            "{} release {}",
            format_inner(l, true)?,
            format_inner(r, true)?
        )),
        Formula::MetricAlways { bound, inner } => {
            format!(
                "always within {} ({})",
                format_timebound(*bound),
                format_inner(inner, false)?
            )
        }
        Formula::MetricEventually { bound, inner } => {
            format!(
                "eventually within {} ({})",
                format_timebound(*bound),
                format_inner(inner, false)?
            )
        }
        Formula::MetricUntil { bound, left, right } => wrap(format!(
            "{} until within {} {}",
            format_inner(left, true)?,
            format_timebound(*bound),
            format_inner(right, true)?
        )),
        Formula::MetricRelease { bound, left, right } => wrap(format!(
            "{} release within {} {}",
            format_inner(left, true)?,
            format_timebound(*bound),
            format_inner(right, true)?
        )),
    })
}

/// Append the raw core reason to a base reason, if present.
fn with_core(base: String, core_reason: &str) -> String {
    if core_reason.is_empty() {
        base
    } else {
        format!("{base} [core: {core_reason}]")
    }
}

/// The enriched reason when no signal values are available — the formula
/// description plus the raw core reason. Renders no rationals, so it is infallible
/// and doubles as the graceful degrade target if observed-value rendering ever
/// fails (unreachable: the values came from an extraction that already loaded the
/// library, so the renderer's library is loaded too).
pub(crate) fn reason_without_values(diag: &PropertyDiagnostic, core_reason: &str) -> String {
    with_core(format!("violated: {}", diag.formula_desc), core_reason)
}

/// Build the enriched reason string from a diagnostic, the values extracted for
/// its signals, and the raw core reason. Mirrors the Go / Python formatters.
///
/// # Errors
/// Propagates an [`Error`] if the kernel rational renderer's library cannot be
/// loaded while rendering an observed value (see [`format_rational`]). Callers on
/// the eval path degrade to [`reason_without_values`] rather than fail an
/// already-processed frame.
pub(crate) fn format_enriched_reason(
    diag: &PropertyDiagnostic,
    values: &[(String, Rational)],
    core_reason: &str,
) -> Result<String, Error> {
    let mut parts: Vec<String> = Vec::new();
    for sig in &diag.signals {
        if let Some((_, v)) = values.iter().find(|(n, _)| n == sig) {
            parts.push(format!("{sig} = {}", format_rational(*v)?));
        }
    }
    if parts.is_empty() {
        return Ok(reason_without_values(diag, core_reason));
    }
    Ok(with_core(
        format!("{} (formula: {})", parts.join(", "), diag.formula_desc),
        core_reason,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::check;

    fn r(n: i64) -> Rational {
        Rational::integer(n)
    }

    #[test]
    fn never_shape_and_signals() {
        let f = check::signal("Speed").never_exceeds(220);
        let d = build_diagnostic(f.formula()).unwrap();
        assert_eq!(d.signals, vec!["Speed".to_string()]);
        assert_eq!(d.formula_desc, "always(Speed <= 220)");
    }

    #[test]
    fn never_equals_renders_as_never() {
        // never_equals builds Always(Not(Atomic(Equals))) → the `never P` shape.
        let f = check::signal("Mode").never_equals(3);
        assert_eq!(
            build_diagnostic(f.formula()).unwrap().formula_desc,
            "never Mode = 3"
        );
    }

    #[test]
    fn collect_dedups_across_when_then() {
        let f = check::when("Brake")
            .exceeds(50)
            .then("Light")
            .equals(1)
            .within(100)
            .unwrap();
        let d = build_diagnostic(f.formula()).unwrap();
        // Both signals referenced, in first-seen order; metric bound rendered.
        assert_eq!(d.signals, vec!["Brake".to_string(), "Light".to_string()]);
        assert!(
            d.formula_desc.contains("within 100ms"),
            "got: {}",
            d.formula_desc
        );
    }

    #[test]
    fn enriched_reason_with_and_without_values() {
        let diag = PropertyDiagnostic {
            signals: vec!["Speed".to_string()],
            formula_desc: "always(Speed < 220)".to_string(),
        };
        let with = format_enriched_reason(&diag, &[("Speed".to_string(), r(245))], "").unwrap();
        assert_eq!(with, "Speed = 245 (formula: always(Speed < 220))");
        let without = format_enriched_reason(&diag, &[], "window expired").unwrap();
        assert_eq!(
            without,
            "violated: always(Speed < 220) [core: window expired]"
        );
    }
}
