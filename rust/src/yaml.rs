// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! YAML check loader (feature `yaml`, on by default).
//!
//! Loads a set of named [`Check`]s from a YAML document whose schema is shared
//! with the Python (`load_checks`) and Go (`LoadChecksFromYAML`) loaders, so a
//! check file authored for one binding loads identically here. The document is a
//! mapping with a single `checks:` list; each entry is either a single-signal
//! check (`signal` + `condition` + operands) or a causal `when`/`then` check
//! (with a top-level `within_ms`). Decimal values are parsed EXACTLY from their
//! original text via the kernel [`Rational::from_decimal`] (the cross-binding
//! single source of truth), so an out-of-grammar or overflowing value fails
//! rather than silently clamping — and loading a check file with decimal operands
//! requires a live backend (decimal parsing is RTS-gated). Unknown keys are
//! ignored (matching the peers).
//!
//! Note: a decimal operand renders in a check's *description* as the exact reduced
//! fraction (`11.5` → `"11.5"`'s value shows as `23/2`), matching the Rust check
//! DSL; the peers' loaders print the original decimal. This is display-only — the
//! compiled formula and wire value are identical across bindings.

use std::path::Path;

use yaml_rust2::{Yaml, YamlLoader};

use crate::check::{self, Check};
use crate::error::Error;
use crate::types::Rational;

/// The shared 64 MiB input-length cap (Python `MAX_DBC_TEXT_BYTES`, Go
/// `MaxDBCTextBytes`). Applied at this trust boundary so an adversarial check
/// file cannot force unbounded allocation / parse time before it is rejected.
const MAX_INPUT_BYTES: usize = 64 * 1024 * 1024;

fn invalid(msg: impl Into<String>) -> Error {
    Error::Validation(msg.into())
}

/// Whether a node is present (a missing mapping key yields [`Yaml::BadValue`]).
fn present(y: &Yaml) -> bool {
    !matches!(y, Yaml::BadValue)
}

/// Load checks from inline YAML content.
///
/// Rejects input larger than the shared 64 MiB bound (`MAX_INPUT_BYTES`).
///
/// # Errors
/// [`Error::Validation`] if the input exceeds the size bound, the document is
/// malformed, a check is missing a required field, a condition keyword is
/// unknown, or a numeric value is out of the decimal grammar or overflows `i64`
/// (see [`Rational::from_decimal`]); [`Error::RtsNotInitialized`] if no backend
/// is up (decimal parsing is RTS-gated).
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
    let docs =
        YamlLoader::load_from_str(content).map_err(|e| invalid(format!("invalid YAML: {e}")))?;
    let doc = docs
        .first()
        .ok_or_else(|| invalid("YAML must contain a 'checks' list"))?;
    let entries = doc["checks"]
        .as_vec()
        .ok_or_else(|| invalid("YAML must contain a 'checks' list"))?;
    entries.iter().map(parse_check).collect()
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

    let check = if present(&entry["when"]) {
        parse_when_then(entry, ctx)?
    } else if present(&entry["signal"]) {
        parse_simple(entry, ctx)?
    } else {
        return Err(invalid(format!(
            "check '{ctx}': must have 'signal' or 'when'/'then'"
        )));
    };

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
        "never_exceeds" => Ok(sig.never_exceeds(number(entry, "value", ctx, condition)?)),
        "never_below" => Ok(sig.never_below(number(entry, "value", ctx, condition)?)),
        "never_equals" => Ok(sig.never_equals(number(entry, "value", ctx, condition)?)),
        "equals" => Ok(sig.equals(number(entry, "value", ctx, condition)?).always()),
        "stays_between" => {
            let (lo, hi) = range(entry, ctx, condition)?;
            sig.stays_between(lo, hi)
        }
        "settles_between" => {
            let (lo, hi) = range(entry, ctx, condition)?;
            let ms = within_ms(entry, ctx, condition)?;
            sig.settles_between(lo, hi).within(ms)
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
    // within_ms lives at the entry's top level and is mandatory for when/then.
    let ms = within_ms(entry, ctx, "when/then")?;

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
    then_condition.within(ms)
}

/// Extract a numeric operand as a [`Rational`] — an integer scalar becomes `n/1`,
/// a decimal scalar is parsed EXACTLY from its original text via the kernel
/// [`Rational::from_decimal`] (no float ever materialises; `yaml_rust2` keeps the
/// literal as [`Yaml::Real`]). A boolean or non-number is rejected, as is a
/// missing key. Because decimal parsing is RTS-gated, loading a check file with
/// decimal operands requires a live backend.
fn number(node: &Yaml, key: &str, ctx: &str, cond: &str) -> Result<Rational, Error> {
    match &node[key] {
        Yaml::Integer(i) => Ok(Rational::integer(*i)),
        Yaml::Real(s) => Rational::from_decimal(s),
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

/// Extract the required integer-millisecond `within_ms` operand (non-negative).
fn within_ms(node: &Yaml, ctx: &str, cond: &str) -> Result<u64, Error> {
    let v = &node["within_ms"];
    if !present(v) {
        return Err(invalid(format!(
            "check '{ctx}': condition '{cond}' requires 'within_ms'"
        )));
    }
    let ms = v
        .as_i64()
        .ok_or_else(|| invalid(format!("check '{ctx}': 'within_ms' must be an integer")))?;
    u64::try_from(ms)
        .map_err(|_| invalid(format!("check '{ctx}': 'within_ms' must be non-negative")))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::Rational;

    fn one(yaml: &str) -> Check {
        let mut checks = load_checks_from_yaml(yaml).expect("load");
        assert_eq!(checks.len(), 1, "expected exactly one check");
        checks.pop().unwrap()
    }

    /// Bring the GHC RTS up: decimal operands are parsed via the kernel decimal
    /// SSOT (`Rational::from_decimal`), which is RTS-gated, so any test that loads
    /// a check with a decimal value needs a live backend first. `Client::new()` is
    /// the sole RTS initialiser; the process-global one-shot latch keeps it up.
    fn test_backend() -> crate::Client {
        crate::Client::new().expect(
            "init GHC RTS for decimal-loader test (is ALETHEIA_LIB set to a built libaletheia-ffi.so?)",
        )
    }

    #[test]
    fn simple_conditions_match_the_builders() {
        // Each loaded check must compile to the same formula as the DSL builder.
        assert_eq!(
            one("checks:\n  - signal: Speed\n    condition: never_exceeds\n    value: 220\n")
                .formula(),
            check::signal("Speed").never_exceeds(220).formula()
        );
        assert_eq!(
            one("checks:\n  - signal: V\n    condition: never_below\n    value: 5\n").formula(),
            check::signal("V").never_below(5).formula()
        );
        assert_eq!(
            one("checks:\n  - signal: E\n    condition: never_equals\n    value: 255\n").formula(),
            check::signal("E").never_equals(255).formula()
        );
        assert_eq!(
            one("checks:\n  - signal: G\n    condition: equals\n    value: 0\n").formula(),
            check::signal("G").equals(0).always().formula()
        );
        assert_eq!(
            one("checks:\n  - signal: T\n    condition: stays_between\n    min: 60\n    max: 80\n")
                .formula(),
            check::signal("T").stays_between(60, 80).unwrap().formula()
        );
        assert_eq!(
            one("checks:\n  - signal: T\n    condition: settles_between\n    min: 60\n    max: 80\n    within_ms: 500\n")
                .formula(),
            check::signal("T")
                .settles_between(60, 80)
                .within(500)
                .unwrap()
                .formula()
        );
    }

    #[test]
    fn when_then_matches_the_builder() {
        let c = one(concat!(
            "checks:\n",
            "  - when:\n      signal: Brake\n      condition: exceeds\n      value: 50\n",
            "    then:\n      signal: Light\n      condition: equals\n      value: 1\n",
            "    within_ms: 100\n",
        ));
        assert_eq!(
            c.formula(),
            check::when("Brake")
                .exceeds(50)
                .then("Light")
                .equals(1)
                .within(100)
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
        let expected = check::signal("S").never_exceeds(Rational::new(201, 2).unwrap());
        assert_eq!(c.formula(), expected.formula());
    }

    #[test]
    fn metadata_name_and_severity_are_applied() {
        let c = one(concat!(
            "checks:\n  - name: speed-limit\n    severity: critical\n",
            "    signal: Speed\n    condition: never_exceeds\n    value: 220\n",
        ));
        assert_eq!(c.name(), "speed-limit");
        assert_eq!(c.severity(), "critical");
    }

    #[test]
    fn multiple_checks_and_unknown_keys_ignored() {
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
        // when/then without within_ms.
        assert!(load_checks_from_yaml(concat!(
            "checks:\n  - when:\n      signal: A\n      condition: exceeds\n      value: 1\n",
            "    then:\n      signal: B\n      condition: equals\n      value: 1\n",
        ))
        .is_err());
        // Inverted range.
        assert!(load_checks_from_yaml(
            "checks:\n  - signal: S\n    condition: stays_between\n    min: 10\n    max: 0\n"
        )
        .is_err());
        // Neither signal nor when.
        assert!(load_checks_from_yaml("checks:\n  - severity: warning\n").is_err());
    }

    #[test]
    fn rejects_non_finite_and_overflowing_values() {
        // `.nan` / `.inf` are out of the kernel decimal grammar; the 20-digit
        // integer part overflows the i64 wire range. The loader rejects all three
        // (never clamps) — matching every binding's decimal SSOT. RTS-gated.
        let _rts = test_backend();
        assert!(load_checks_from_yaml(
            "checks:\n  - signal: S\n    condition: never_exceeds\n    value: .nan\n"
        )
        .is_err());
        assert!(load_checks_from_yaml(
            "checks:\n  - signal: S\n    condition: never_exceeds\n    value: .inf\n"
        )
        .is_err());
        assert!(load_checks_from_yaml(
            "checks:\n  - signal: S\n    condition: never_exceeds\n    value: 99999999999999999999.5\n"
        )
        .is_err());
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
        // A small injectable bound exercises the boundary without a 64 MiB alloc;
        // the public entry point fixes the real bound at MAX_INPUT_BYTES.
        assert!(load_checks_within(SAMPLE, 8).is_err());
        assert!(load_checks_within(SAMPLE, SAMPLE.len()).is_ok());
    }

    #[test]
    fn file_loads_and_size_bound_is_enforced() {
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
