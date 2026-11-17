// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! YAML check loader (feature `yaml`, on by default).
//!
//! Loads a set of named [`Check`]s from a YAML document whose schema is shared
//! with the Python (`load_checks`) and Go (`LoadChecksFromYAML`) loaders, so a
//! check file authored for one binding loads identically here. The document is a
//! mapping with a single `checks:` list; each entry is either a single-signal
//! check (`signal` + `condition` + operands) or a causal `when`/`then` check
//! (with a top-level `within_us`). The scalar under a number key, plain, quoted
//! or tagged with a core-schema tag other than `!!null`, is parsed EXACTLY from the text the document
//! spells it with by the kernel [`Rational::from_decimal`] (the cross-binding
//! single source of truth): the YAML library resolves no integer, hexadecimal,
//! float or boolean of its own, so the kernel decides what a valid number is
//! and refuses any other text, located, rather than clamping it; a null or a
//! missing number is the loader's own refusal. A time window, the `within_us`
//! a `settles_between` or a `when`/`then` check requires, is a whole number of
//! microseconds the kernel reads from its text the same way, through
//! [`TimeBound::parse`]. Loading a check needs the GHC runtime up, every
//! number being read and every check built by the kernel: a program that
//! loads before it builds a client calls
//! [`start_runtime`](crate::start_runtime) first. Unknown keys are ignored
//! (matching the peers).

use std::path::Path;

use yaml_rust2::parser::{Event, MarkedEventReceiver, Parser, Tag};
use yaml_rust2::scanner::{Marker, TScalarStyle};
use yaml_rust2::{Yaml, YamlLoader};

use crate::check::{self, Check};
use crate::error::Error;
use crate::types::{Rational, TimeBound};

/// The shared 64 MiB input-length cap (Python `MAX_DBC_TEXT_BYTES`, Go
/// `MaxDBCTextBytes`). Applied at this trust boundary so an adversarial check
/// file cannot force unbounded allocation / parse time before it is rejected.
const MAX_INPUT_BYTES: usize = 64 * 1024 * 1024;

fn invalid(msg: impl Into<String>) -> Error {
    Error::validation(msg)
}

/// Whether a node is present (a missing mapping key yields [`Yaml::BadValue`]).
fn present(y: &Yaml) -> bool {
    !matches!(y, Yaml::BadValue)
}

/// The core schema's tag prefix, which the parser resolves `!!` to.
const CORE_TAG: &str = "tag:yaml.org,2002:";

/// Builds the documents as [`YamlLoader`] does, except that a scalar
/// [`kept_as_text`] names reaches the loader single-quoted and untagged, so it
/// holds the text the document spells it with as [`Yaml::String`]. A null, or
/// a scalar under another tag, resolves as the loader resolves it.
#[derive(Default)]
struct ScalarText {
    loader: YamlLoader,
    /// The documents the parser ended. The loader holds fewer when it refused
    /// a node, which it does for a key repeated in a mapping.
    ended: usize,
}

/// The core-schema tags under which a scalar is held as its text, the ones
/// the Python loader holds so: a number, a YAML 1.1 boolean, a date or the
/// `=` value key. A `!!null` scalar stays null, so it reads as missing.
const TEXT_TAGS: [&str; 5] = ["int", "float", "bool", "timestamp", "value"];

/// Whether a scalar is held as its text: tagged with one of [`TEXT_TAGS`], in
/// any style and whatever it spells, or plain, untagged and no null word (`~`,
/// `null` or nothing, as [`Yaml::from_str`] reads them). A quoted untagged
/// scalar is text to the loader already.
fn kept_as_text(text: &str, style: TScalarStyle, tag: Option<&Tag>) -> bool {
    match tag {
        Some(Tag { handle, suffix }) => handle == CORE_TAG && TEXT_TAGS.contains(&suffix.as_str()),
        None => style == TScalarStyle::Plain && !matches!(Yaml::from_str(text), Yaml::Null),
    }
}

impl MarkedEventReceiver for ScalarText {
    fn on_event(&mut self, ev: Event, mark: Marker) {
        let ev = match ev {
            Event::Scalar(text, style, anchor, tag) if kept_as_text(&text, style, tag.as_ref()) => {
                Event::Scalar(text, TScalarStyle::SingleQuoted, anchor, None)
            }
            Event::DocumentEnd => {
                self.ended += 1;
                Event::DocumentEnd
            }
            other => other,
        };
        self.loader.on_event(ev, mark);
    }
}

/// Load checks from inline YAML content.
///
/// Rejects input larger than the shared 64 MiB bound (`MAX_INPUT_BYTES`).
///
/// # Errors
/// [`Error::Validation`] if the input exceeds the size bound, the document is
/// malformed, a check is missing a required field, a condition keyword is
/// unknown, or a number is out of the kernel's decimal grammar (carrying the
/// kernel's `code`); [`Error::InputBoundExceeded`] if a number crosses the
/// rational component magnitude bound. Both number refusals are
/// [`Rational::from_decimal`]'s, or [`TimeBound::parse`]'s for `within_us`,
/// with the kernel's message, code and fields, located (see
/// [`Error::located`]) at `Check '<name>'` (`<unnamed>` for a check with no
/// name) under the number's key. A check the kernel refuses where it is built
/// keeps the builder's error, located at the check with no key (see
/// [`Error::located_at`]), so it prints `Check '<name>': <the kernel's
/// message>`; [`Error::RtsNotInitialized`] if the runtime has not started.
pub fn load_checks_from_yaml(content: &str) -> Result<Vec<Check>, Error> {
    load_checks_within(content, MAX_INPUT_BYTES)
}

/// Inline loader with an injectable size bound (the public entry point fixes it
/// to [`MAX_INPUT_BYTES`]; tests use a small bound to exercise the boundary
/// without allocating 64 MiB).
fn load_checks_within(content: &str, limit: usize) -> Result<Vec<Check>, Error> {
    if content.len() > limit {
        return Err(invalid(format!(
            "YAML check input exceeds the {limit}-byte input bound ({} bytes)",
            content.len()
        )));
    }
    let mut scalars = ScalarText::default();
    Parser::new_from_str(content)
        .load(&mut scalars, true)
        .map_err(|e| invalid(format!("invalid YAML: {e}")))?;
    let docs = scalars.loader.documents();
    if docs.len() != scalars.ended {
        // The loader refused a repeated key and keeps its reason private; the
        // stock loader states it with its place, unless the key repeats only
        // once scalars are text (`1` and `'1'`).
        let reason = YamlLoader::load_from_str(content).map_or_else(
            |e| e.to_string(),
            |_| "duplicated key in mapping".to_owned(),
        );
        return Err(invalid(format!("invalid YAML: {reason}")));
    }
    let doc = docs
        .first()
        .ok_or_else(|| invalid("YAML must contain a 'checks' list"))?;
    let entries = doc["checks"]
        .as_vec()
        .ok_or_else(|| invalid("YAML must contain a 'checks' list"))?;
    entries.iter().map(parse_check).collect()
}

/// A refusal no single key holds, such as a check its builder refused, located
/// at `location` with no key: a refusal carrying the kernel's code, or a bound
/// refusal, that no reader located gains the place; one a reader located, or
/// one without a code (the loader's own words, the runtime down), comes back
/// as it was.
fn locate_refusal(err: Error, location: &str) -> Error {
    let coded = matches!(
        &err,
        Error::Validation { code: Some(_), .. } | Error::InputBoundExceeded(_)
    );
    if coded && err.location().is_none() {
        err.located_at(location)
    } else {
        err
    }
}

/// Load checks from a YAML file.
///
/// Mirrors the Go and Python loaders' trust-boundary hardening: the path is
/// rejected if it is a symbolic link or a non-regular file, and the file's size
/// is checked against the shared 64 MiB bound (`MAX_INPUT_BYTES`) **before** it
/// is read, so an adversarial path cannot trigger a huge read.
///
/// # Errors
/// [`Error::Validation`] if the path is a symlink / non-regular file, the file
/// exceeds the size bound, an I/O error occurs, or the document is malformed (see
/// [`load_checks_from_yaml`]).
pub fn load_checks_from_yaml_file(path: impl AsRef<Path>) -> Result<Vec<Check>, Error> {
    read_checks_file(path.as_ref(), MAX_INPUT_BYTES)
}

/// File loader with an injectable size bound (see [`load_checks_within`]).
fn read_checks_file(path: &Path, limit: usize) -> Result<Vec<Check>, Error> {
    // symlink_metadata is an lstat — it does NOT follow a symlink, so a symlinked
    // path is detected here rather than silently dereferenced.
    let meta = std::fs::symlink_metadata(path)
        .map_err(|e| invalid(format!("cannot stat {}: {e}", path.display())))?;
    let file_type = meta.file_type();
    if file_type.is_symlink() {
        return Err(invalid(format!(
            "refusing to load {}: symbolic link (resolve the link and pass the real path)",
            path.display()
        )));
    }
    if !file_type.is_file() {
        return Err(invalid(format!(
            "refusing to load {}: not a regular file",
            path.display()
        )));
    }
    if meta.len() > limit as u64 {
        return Err(invalid(format!(
            "YAML check file {} exceeds the {limit}-byte input bound ({} bytes)",
            path.display(),
            meta.len()
        )));
    }
    let content = std::fs::read_to_string(path)
        .map_err(|e| invalid(format!("cannot read {}: {e}", path.display())))?;
    load_checks_within(&content, limit)
}

fn parse_check(entry: &Yaml) -> Result<Check, Error> {
    let name = entry["name"].as_str().unwrap_or("");
    let ctx = if name.is_empty() { "<unnamed>" } else { name };

    let built = if present(&entry["when"]) {
        parse_when_then(entry, ctx)
    } else if present(&entry["signal"]) {
        parse_simple(entry, ctx)
    } else {
        return Err(invalid(format!(
            "check '{ctx}': must have 'signal' or 'when'/'then'"
        )));
    };
    let check = built.map_err(|err| locate_refusal(err, &format!("Check '{ctx}'")))?;

    // Metadata is applied only when non-empty (matching the peers).
    let check = if name.is_empty() {
        check
    } else {
        check.named(name)
    };
    let severity = entry["severity"].as_str().unwrap_or("");
    let check = if severity.is_empty() {
        check
    } else {
        check.with_severity(severity)
    };
    Ok(check)
}

fn parse_simple(entry: &Yaml, ctx: &str) -> Result<Check, Error> {
    let signal = entry["signal"]
        .as_str()
        .ok_or_else(|| invalid(format!("check '{ctx}': 'signal' must be a string")))?;
    let condition = entry["condition"]
        .as_str()
        .ok_or_else(|| invalid(format!("check '{ctx}': missing 'condition'")))?;
    let sig = check::signal(signal);
    match condition {
        "never_exceeds" => sig.never_exceeds(number(entry, "value", ctx, condition)?),
        "never_below" => sig.never_below(number(entry, "value", ctx, condition)?),
        "never_equals" => sig.never_equals(number(entry, "value", ctx, condition)?),
        "equals" => sig.equals(number(entry, "value", ctx, condition)?).always(),
        "stays_between" => {
            let (lo, hi) = range(entry, ctx, condition)?;
            sig.stays_between(lo, hi)
        }
        "settles_between" => {
            let (lo, hi) = range(entry, ctx, condition)?;
            let bound = within_us(
                entry,
                ctx,
                format!("check '{ctx}': condition '{condition}' requires 'within_us'"),
            )?;
            sig.settles_between(lo, hi).within(bound)
        }
        other => Err(invalid(format!(
            "check '{ctx}': unknown condition '{other}'"
        ))),
    }
}

fn parse_when_then(entry: &Yaml, ctx: &str) -> Result<Check, Error> {
    let when = &entry["when"];
    let then = &entry["then"];
    if !present(then) {
        return Err(invalid(format!(
            "check '{ctx}': must have 'signal' or 'when'/'then'"
        )));
    }
    // within_us lives at the entry's top level and is mandatory for when/then.
    let bound = within_us(
        entry,
        ctx,
        format!("check '{ctx}': when/then checks require 'within_us'"),
    )?;

    let when_signal = when["signal"]
        .as_str()
        .ok_or_else(|| invalid(format!("check '{ctx}': when clause requires 'signal'")))?;
    let when_cond = when["condition"]
        .as_str()
        .ok_or_else(|| invalid(format!("check '{ctx}': when clause requires 'condition'")))?;
    let trigger = check::when(when_signal);
    let when_condition = match when_cond {
        "exceeds" => trigger.exceeds(number(when, "value", ctx, when_cond)?),
        "equals" => trigger.equals(number(when, "value", ctx, when_cond)?),
        "drops_below" => trigger.drops_below(number(when, "value", ctx, when_cond)?),
        other => {
            return Err(invalid(format!(
                "check '{ctx}': unknown when condition '{other}'"
            )))
        }
    };

    let then_signal = then["signal"]
        .as_str()
        .ok_or_else(|| invalid(format!("check '{ctx}': then clause requires 'signal'")))?;
    let then_cond = then["condition"]
        .as_str()
        .ok_or_else(|| invalid(format!("check '{ctx}': then clause requires 'condition'")))?;
    let response = when_condition.then(then_signal);
    let then_condition = match then_cond {
        "equals" => response.equals(number(then, "value", ctx, then_cond)?),
        "exceeds" => response.exceeds(number(then, "value", ctx, then_cond)?),
        "stays_between" => {
            let (lo, hi) = range(then, ctx, then_cond)?;
            response.stays_between(lo, hi)
        }
        other => {
            return Err(invalid(format!(
                "check '{ctx}': unknown then condition '{other}'"
            )))
        }
    };
    then_condition.within(bound)
}

/// The kernel's reading of a number's text: a refusal keeps the kernel's error
/// and gains the check as its location and `key` as its key.
fn decimal(text: &str, key: &str, ctx: &str) -> Result<Rational, Error> {
    Rational::from_decimal(text).map_err(|e| e.located(format!("Check '{ctx}'"), key))
}

/// Extract a numeric operand as a [`Rational`], parsed EXACTLY by the kernel
/// [`Rational::from_decimal`] from the text the document spells it with (see
/// [`ScalarText`]), so no float ever materialises. A null (a `!!null` scalar
/// included), a collection or a missing key is refused; any other scalar's
/// text, a `!!bool` one included, is the kernel's to read, and text it refuses
/// is refused as [`decimal`] locates it. Decimal parsing needs the GHC runtime
/// up.
fn number(node: &Yaml, key: &str, ctx: &str, cond: &str) -> Result<Rational, Error> {
    match &node[key] {
        Yaml::String(text) => decimal(text, key, ctx),
        _ => Err(invalid(format!(
            "check '{ctx}': condition '{cond}' requires '{key}'"
        ))),
    }
}

/// Extract the `min` and `max` operands of a range condition (both required).
fn range(node: &Yaml, ctx: &str, cond: &str) -> Result<(Rational, Rational), Error> {
    if !present(&node["min"]) || !present(&node["max"]) {
        return Err(invalid(format!(
            "check '{ctx}': condition '{cond}' requires 'min' and 'max'"
        )));
    }
    Ok((
        number(node, "min", ctx, cond)?,
        number(node, "max", ctx, cond)?,
    ))
}

/// Extract the required `within_us` operand, a whole number of microseconds
/// the kernel reads from the text the document spells it with through
/// [`TimeBound::parse`]: a refusal keeps the kernel's error and gains the check
/// as its location and `within_us` as its key. A null, a collection or a
/// missing key is refused with `missing`; any other scalar is the kernel's to
/// read (see [`ScalarText`]). Reading the bound needs the GHC runtime up.
fn within_us(node: &Yaml, ctx: &str, missing: String) -> Result<TimeBound, Error> {
    match &node["within_us"] {
        Yaml::String(text) => {
            TimeBound::parse(text).map_err(|e| e.located(format!("Check '{ctx}'"), "within_us"))
        }
        _ => Err(invalid(missing)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::response::ErrorCode;
    use crate::types::Rational;

    fn one(yaml: &str) -> Check {
        let mut checks = load_checks_from_yaml(yaml).expect("load");
        assert_eq!(checks.len(), 1, "expected exactly one check");
        checks.pop().unwrap()
    }

    /// Start the GHC runtime: every number is parsed via the kernel decimal SSOT
    /// (`Rational::from_decimal`), which needs it up, so any test that loads a
    /// check opens a client first; the runtime stays up for the process.
    fn test_backend() -> crate::Client {
        crate::Client::new().expect(
            "init GHC RTS for decimal-loader test (is ALETHEIA_LIB set to a built libaletheia-ffi.so?)",
        )
    }

    #[test]
    fn simple_conditions_match_the_builders() {
        // Each loaded check must compile to the same formula as the DSL builder.
        let _rts = test_backend();
        assert_eq!(
            one("checks:\n  - signal: Speed\n    condition: never_exceeds\n    value: 220\n")
                .formula(),
            check::signal("Speed").never_exceeds(220).unwrap().formula()
        );
        assert_eq!(
            one("checks:\n  - signal: V\n    condition: never_below\n    value: 5\n").formula(),
            check::signal("V").never_below(5).unwrap().formula()
        );
        assert_eq!(
            one("checks:\n  - signal: E\n    condition: never_equals\n    value: 255\n").formula(),
            check::signal("E").never_equals(255).unwrap().formula()
        );
        assert_eq!(
            one("checks:\n  - signal: G\n    condition: equals\n    value: 0\n").formula(),
            check::signal("G").equals(0).always().unwrap().formula()
        );
        assert_eq!(
            one("checks:\n  - signal: T\n    condition: stays_between\n    min: 60\n    max: 80\n")
                .formula(),
            check::signal("T").stays_between(60, 80).unwrap().formula()
        );
        assert_eq!(
            one("checks:\n  - signal: T\n    condition: settles_between\n    min: 60\n    max: 80\n    within_us: 500000\n")
                .formula(),
            check::signal("T")
                .settles_between(60, 80)
                .within(TimeBound(500_000))
                .unwrap()
                .formula()
        );
    }

    #[test]
    fn when_then_matches_the_builder() {
        let _rts = test_backend();
        let c = one(concat!(
            "checks:\n",
            "  - when:\n      signal: Brake\n      condition: exceeds\n      value: 50\n",
            "    then:\n      signal: Light\n      condition: equals\n      value: 1\n",
            "    within_us: 100000\n",
        ));
        assert_eq!(
            c.formula(),
            check::when("Brake")
                .exceeds(50)
                .then("Light")
                .equals(1)
                .within(TimeBound(100_000))
                .unwrap()
                .formula()
        );
        assert_eq!(c.signal_name(), "Light");
    }

    #[test]
    fn decimal_value_uses_the_shared_conversion() {
        // "100.5" parses EXACTLY to 201/2 via the kernel decimal SSOT — the same
        // Rational every binding produces. Decimal parsing is RTS-gated.
        let _rts = test_backend();
        let c = one("checks:\n  - signal: S\n    condition: never_exceeds\n    value: 100.5\n");
        let expected = check::signal("S")
            .never_exceeds(Rational::new(201, 2).unwrap())
            .unwrap();
        assert_eq!(c.formula(), expected.formula());
    }

    #[test]
    fn metadata_name_and_severity_are_applied() {
        let _rts = test_backend();
        let c = one(concat!(
            "checks:\n  - name: speed-limit\n    severity: critical\n",
            "    signal: Speed\n    condition: never_exceeds\n    value: 220\n",
        ));
        assert_eq!(c.name(), "speed-limit");
        assert_eq!(c.severity(), "critical");
    }

    #[test]
    fn multiple_checks_and_unknown_keys_ignored() {
        let _rts = test_backend();
        let checks = load_checks_from_yaml(concat!(
            "checks:\n",
            "  - signal: A\n    condition: never_exceeds\n    value: 1\n    bogus_key: 7\n",
            "  - signal: B\n    condition: never_below\n    value: 2\n",
        ))
        .expect("load");
        assert_eq!(checks.len(), 2);
    }

    #[test]
    fn errors_on_malformed_documents() {
        // A live backend, so the inverted range is refused for its order and
        // not for the RTS being down.
        let _rts = test_backend();
        // No checks list.
        assert!(load_checks_from_yaml("not_checks: []\n").is_err());
        // Unknown condition.
        assert!(load_checks_from_yaml(
            "checks:\n  - signal: S\n    condition: bogus\n    value: 1\n"
        )
        .is_err());
        // Missing value.
        assert!(
            load_checks_from_yaml("checks:\n  - signal: S\n    condition: never_exceeds\n")
                .is_err()
        );
        // when/then without within_us.
        assert!(load_checks_from_yaml(concat!(
            "checks:\n  - when:\n      signal: A\n      condition: exceeds\n      value: 1\n",
            "    then:\n      signal: B\n      condition: equals\n      value: 1\n",
        ))
        .is_err());
        // Inverted range: the kernel refuses the check where it is built, and
        // the loader locates the refusal at the check.
        let inverted = load_checks_from_yaml(
            "checks:\n  - signal: S\n    condition: stays_between\n    min: 10\n    max: 0\n",
        )
        .expect_err("an inverted range is refused");
        assert!(
            matches!(&inverted, Error::Validation { code: Some(code), .. }
                if *code == ErrorCode::HandlerPropertyRefused),
            "got: {inverted:?}"
        );
        assert_eq!(
            (inverted.location(), inverted.key()),
            (Some("Check '<unnamed>'"), None)
        );
        assert_eq!(
            inverted.to_string(),
            "Check '<unnamed>': between: min 10 exceeds max 0"
        );
        // Neither signal nor when.
        assert!(load_checks_from_yaml("checks:\n  - severity: warning\n").is_err());
    }

    #[test]
    fn rejects_non_finite_and_overflowing_values() {
        // `.nan` / `.inf` are out of the kernel decimal grammar; 2^128 crosses
        // the kernel's rational component magnitude bound, 2^128-1, which
        // 99999999999999999999.5 is within. The loader rejects the three
        // (never clamps), as every binding's decimal SSOT does. RTS-gated.
        let _rts = test_backend();
        assert!(load_checks_from_yaml(
            "checks:\n  - signal: S\n    condition: never_exceeds\n    value: .nan\n"
        )
        .is_err());
        assert!(load_checks_from_yaml(
            "checks:\n  - signal: S\n    condition: never_exceeds\n    value: .inf\n"
        )
        .is_err());
        let past = load_checks_from_yaml(
            "checks:\n  - signal: S\n    condition: never_exceeds\n    value: 340282366920938463463374607431768211456\n",
        )
        .expect_err("2^128 is past the bound");
        assert!(
            matches!(&past, Error::InputBoundExceeded(refusal)
                if refusal.field.as_deref() == Some("decimal")),
            "got: {past:?}"
        );
        assert_eq!(past.key(), Some("value"));
        load_checks_from_yaml(
            "checks:\n  - signal: S\n    condition: never_exceeds\n    value: 99999999999999999999.5\n",
        )
        .expect("a 20-digit integer part is within the bound");
    }

    /// The kernel's message for `1.5x`: the literal `1.5`, then text it cannot
    /// read from column 4 on.
    const TRAILING_AT_4: &str =
        "parse failed at line 1, column 4 (first unparseable statement starts at line 1, column 4)";
    /// The kernel's message for a hexadecimal: the digit `0`, then text it
    /// cannot read from column 2 on.
    const TRAILING_AT_2: &str =
        "parse failed at line 1, column 2 (first unparseable statement starts at line 1, column 2)";
    /// The kernel's message for text that opens with no decimal literal.
    const NO_LITERAL: &str = "parse failed at line 1, column 1";

    /// Assert that a document's number is refused as the kernel refused it,
    /// with the code `text_trailing_input`, located at `location` under `key`
    /// and printed `<location>: invalid '<key>': <message>`.
    fn assert_trailing(yaml: &str, location: &str, key: &str, message: &str) {
        let err = load_checks_from_yaml(yaml).expect_err("the number is refused");
        let Error::Validation { code, .. } = &err else {
            panic!("expected a validation refusal, got {err:?}");
        };
        assert_eq!(*code, Some(ErrorCode::TextTrailingInput), "{err:?}");
        assert_eq!(err.location(), Some(location), "{err:?}");
        assert_eq!(err.key(), Some(key), "{err:?}");
        assert_eq!(
            err.to_string(),
            format!("{location}: invalid '{key}': {message}")
        );
    }

    #[test]
    fn a_refused_number_is_located_under_its_key() {
        let _rts = test_backend();
        let range = |min: &str, max: &str| {
            format!(
                "checks:\n  - name: R\n    signal: S\n    condition: stays_between\n    min: {min}\n    max: {max}\n"
            )
        };
        assert_trailing(&range("1.5x", "2"), "Check 'R'", "min", TRAILING_AT_4);
        assert_trailing(&range("0", "1.5x"), "Check 'R'", "max", TRAILING_AT_4);
        // A then clause's operand: the check's name, the clause's key.
        assert_trailing(
            concat!(
                "checks:\n  - name: W\n",
                "    when:\n      signal: A\n      condition: exceeds\n      value: 1\n",
                "    then:\n      signal: B\n      condition: equals\n      value: 1.5x\n",
                "    within_us: 100000\n",
            ),
            "Check 'W'",
            "value",
            TRAILING_AT_4,
        );
        // A check with no name is located as the loader names it.
        assert_trailing(
            "checks:\n  - signal: S\n    condition: never_exceeds\n    value: 1.5x\n",
            "Check '<unnamed>'",
            "value",
            TRAILING_AT_4,
        );
    }

    #[test]
    fn a_number_reaches_the_kernel_as_spelled() {
        let _rts = test_backend();
        let value = |v: &str| {
            format!(
                "checks:\n  - name: N\n    signal: S\n    condition: never_exceeds\n    value: {v}\n"
            )
        };
        // Tagged `!!int` or single-quoted, a number is its text.
        for spelled in ["!!int 017", "'17'"] {
            assert_eq!(
                one(&value(spelled)).formula(),
                check::signal("S").never_exceeds(17).unwrap().formula(),
                "{spelled}"
            );
        }
        // Tagged `!!int`, a hexadecimal is the kernel's to read, and it refuses one.
        assert_trailing(&value("!!int 0x1F"), "Check 'N'", "value", TRAILING_AT_2);
        // A boolean word is text the kernel refuses.
        assert_eq!(
            load_checks_from_yaml(&value("true"))
                .expect_err("refused")
                .to_string(),
            format!("Check 'N': invalid 'value': {NO_LITERAL}")
        );
        // A null word, or nothing, is no number.
        for spelled in ["~", "null", ""] {
            assert_eq!(
                load_checks_from_yaml(&value(spelled))
                    .expect_err("refused")
                    .to_string(),
                "check 'N': condition 'never_exceeds' requires 'value'",
                "{spelled}"
            );
        }
    }

    #[test]
    fn within_us_is_read_by_the_kernel() {
        let _rts = test_backend();
        let settles = |us: &str| {
            format!(
                "checks:\n  - name: T\n    signal: T\n    condition: settles_between\n    min: 60\n    max: 80\n    within_us: {us}\n"
            )
        };
        // A quoted whole number is the same text as the plain one.
        assert_eq!(
            one(&settles("\"500\"")).formula(),
            check::signal("T")
                .settles_between(60, 80)
                .within(TimeBound(500))
                .unwrap()
                .formula()
        );
        assert_trailing(&settles("1.5x"), "Check 'T'", "within_us", TRAILING_AT_4);
        // A hexadecimal is the kernel's to read, and it refuses one.
        assert_trailing(&settles("0x1F4"), "Check 'T'", "within_us", TRAILING_AT_2);
        // A fraction and a negative are the kernel's time-bound refusals, as
        // a boolean word is its decimal refusal; a null keeps the loader's own.
        let refused = |us: &str| load_checks_from_yaml(&settles(us)).expect_err("refused");
        for (us, message) in [
            ("1.5", "timebound 1.5 is not a whole number"),
            ("-1", "timebound -1 is negative"),
        ] {
            let err = refused(us);
            assert!(
                matches!(&err, Error::Validation { code: Some(code), .. }
                    if *code == ErrorCode::HandlerPropertyRefused),
                "{us}: {err:?}"
            );
            assert_eq!(
                err.to_string(),
                format!("Check 'T': invalid 'within_us': {message}")
            );
        }
        assert_eq!(
            refused("~").to_string(),
            "check 'T': condition 'settles_between' requires 'within_us'"
        );
        assert_eq!(
            refused("true").to_string(),
            format!("Check 'T': invalid 'within_us': {NO_LITERAL}")
        );
    }

    #[test]
    fn a_repeated_key_refuses_the_whole_stream() {
        // In the first document or a later one, with the stock loader's reason
        // and its place.
        for yaml in [
            "checks: []\nchecks: []\n",
            "checks: []\n---\nkey: 1\nkey: 2\n",
        ] {
            let shown = load_checks_from_yaml(yaml)
                .expect_err("refused")
                .to_string();
            assert!(
                shown.starts_with("invalid YAML: ")
                    && shown.contains("duplicated key in mapping at byte"),
                "{yaml:?}: {shown}"
            );
        }
        // A key repeated only once numbers are text.
        assert_eq!(
            load_checks_from_yaml("checks: []\n1: a\n'1': b\n")
                .expect_err("refused")
                .to_string(),
            "invalid YAML: duplicated key in mapping"
        );
    }

    // --- Trust-boundary hardening (parity with the Go / Python loaders) -------

    use std::path::PathBuf;

    const SAMPLE: &str = "checks:\n  - signal: S\n    condition: never_exceeds\n    value: 1\n";

    /// A temp path that removes its file on drop.
    struct TempFile(PathBuf);
    impl Drop for TempFile {
        fn drop(&mut self) {
            let _ = std::fs::remove_file(&self.0);
        }
    }
    fn temp_path(tag: &str) -> PathBuf {
        let mut p = std::env::temp_dir();
        p.push(format!("aletheia_yaml_{}_{tag}", std::process::id()));
        p
    }

    #[test]
    fn inline_input_bound_is_enforced() {
        let _rts = test_backend();
        // A small injectable bound exercises the boundary without a 64 MiB alloc;
        // the public entry point fixes the real bound at MAX_INPUT_BYTES.
        assert!(load_checks_within(SAMPLE, 8).is_err());
        assert!(load_checks_within(SAMPLE, SAMPLE.len()).is_ok());
    }

    #[test]
    fn file_loads_and_size_bound_is_enforced() {
        let _rts = test_backend();
        let path = temp_path("ok");
        let _guard = TempFile(path.clone());
        std::fs::write(&path, SAMPLE).expect("write temp");
        assert_eq!(read_checks_file(&path, MAX_INPUT_BYTES).unwrap().len(), 1);
        // Rejected (before reading) when the file exceeds a small bound.
        assert!(read_checks_file(&path, 8).is_err());
    }

    #[test]
    fn rejects_non_regular_file() {
        let dir = temp_path("dir");
        std::fs::create_dir(&dir).expect("create dir");
        let err = load_checks_from_yaml_file(&dir).unwrap_err();
        let _ = std::fs::remove_dir(&dir);
        assert!(
            format!("{err}").contains("not a regular file"),
            "got: {err}"
        );
    }

    #[cfg(unix)]
    #[test]
    fn rejects_symlink() {
        let target = temp_path("sym_target");
        let link = temp_path("sym_link");
        let _gt = TempFile(target.clone());
        let _gl = TempFile(link.clone());
        std::fs::write(&target, SAMPLE).expect("write target");
        if std::os::unix::fs::symlink(&target, &link).is_err() {
            return; // symlink creation not permitted — skip (mirrors the Go test)
        }
        let err = load_checks_from_yaml_file(&link).unwrap_err();
        assert!(format!("{err}").contains("symbolic link"), "got: {err}");
    }

    #[test]
    fn stat_failure_surfaces_errno_not_missing() {
        // A path component over NAME_MAX makes symlink_metadata (lstat) fail
        // with ENAMETOOLONG — a stat *failure*, not an absent file. The loader
        // embeds the raw io::Error ("cannot stat …: <errno>"), so a
        // resource/permission failure under load can never be mislabelled a
        // missing file (the cross-binding ec-vs-not-found invariant; cf. the
        // C++ validate_loader_path split and Go's os.ErrNotExist branch).
        // ENAMETOOLONG is deterministic and root-safe.
        let long = temp_path(&"a".repeat(5000));
        let err = load_checks_from_yaml_file(&long).unwrap_err();
        let msg = format!("{err}");
        assert!(msg.contains("cannot stat"), "got: {msg}");
        assert!(
            !msg.contains("No such file"),
            "stat failure mislabelled as a missing file: {msg}"
        );
    }
}
