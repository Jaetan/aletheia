// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! The `#[repr(C)]` mirrors lay out as `haskell-shim/include/aletheia.h` fixes them. The
//! expected sizes and offsets are read from the header's own
//! `static_assert` lines, which the C compiler holds to the real layout, so
//! a field moved on either side fails here rather than misreading across
//! the ABI.

use std::mem::{offset_of, size_of};
use std::path::Path;

use super::{FfiBuffer, FfiDecimal, FfiFrame, FfiRational, FfiSignalValues, FfiText, ABI_VERSION};

/// The size and the fields, in order, the header asserts for `name`.
fn asserted(name: &str) -> (usize, Vec<(String, usize)>) {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../haskell-shim/include/aletheia.h");
    let text = std::fs::read_to_string(&path).expect("read haskell-shim/include/aletheia.h");
    let number = |s: &str| -> usize {
        let digits: String = s.chars().take_while(char::is_ascii_digit).collect();
        digits.parse().expect("an asserted number")
    };
    let size_prefix = format!("static_assert(sizeof(struct {name}) == ");
    let offset_prefix = format!("static_assert(offsetof(struct {name}, ");
    let mut size = None;
    let mut fields = Vec::new();
    for line in text.lines() {
        if let Some(rest) = line.strip_prefix(&size_prefix) {
            size = Some(number(rest));
        } else if let Some(rest) = line.strip_prefix(&offset_prefix) {
            let (field, value) = rest.split_once(") == ").expect("an offset assertion");
            fields.push((field.to_string(), number(value)));
        }
    }
    (size.expect("a size assertion"), fields)
}

fn owned(fields: &[(&str, usize)]) -> Vec<(String, usize)> {
    fields.iter().map(|&(f, o)| (f.to_string(), o)).collect()
}

#[test]
fn abi_version_is_the_headers() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../haskell-shim/include/aletheia.h");
    let text = std::fs::read_to_string(&path).expect("read haskell-shim/include/aletheia.h");
    let prefix = "enum { ALETHEIA_ABI_VERSION = ";
    let line = text
        .lines()
        .find_map(|line| line.strip_prefix(prefix))
        .expect("the header defines ALETHEIA_ABI_VERSION");
    let digits: String = line.chars().take_while(char::is_ascii_digit).collect();
    assert_eq!(
        digits.parse::<u32>().expect("a version number"),
        ABI_VERSION
    );
}

#[test]
fn text_matches_header() {
    let mirror = owned(&[
        ("data", offset_of!(FfiText, data)),
        ("size", offset_of!(FfiText, size)),
    ]);
    assert_eq!(asserted("aletheia_text"), (size_of::<FfiText>(), mirror));
}

#[test]
fn frame_matches_header() {
    let mirror = owned(&[
        ("timestamp", offset_of!(FfiFrame, timestamp)),
        ("data", offset_of!(FfiFrame, data)),
        ("can_id", offset_of!(FfiFrame, can_id)),
        ("extended", offset_of!(FfiFrame, extended)),
        ("dlc", offset_of!(FfiFrame, dlc)),
        ("data_len", offset_of!(FfiFrame, data_len)),
        ("brs_present", offset_of!(FfiFrame, brs_present)),
        ("brs_value", offset_of!(FfiFrame, brs_value)),
        ("esi_present", offset_of!(FfiFrame, esi_present)),
        ("esi_value", offset_of!(FfiFrame, esi_value)),
    ]);
    assert_eq!(asserted("aletheia_frame"), (size_of::<FfiFrame>(), mirror));
}

#[test]
fn signal_values_match_header() {
    let mirror = owned(&[
        ("indices", offset_of!(FfiSignalValues, indices)),
        ("numerators", offset_of!(FfiSignalValues, numerators)),
        ("denominators", offset_of!(FfiSignalValues, denominators)),
        ("count", offset_of!(FfiSignalValues, count)),
    ]);
    assert_eq!(
        asserted("aletheia_signal_values"),
        (size_of::<FfiSignalValues>(), mirror)
    );
}

#[test]
fn rational_matches_header() {
    let mirror = owned(&[
        ("numerator", offset_of!(FfiRational, numerator)),
        ("denominator", offset_of!(FfiRational, denominator)),
    ]);
    assert_eq!(
        asserted("aletheia_rational"),
        (size_of::<FfiRational>(), mirror)
    );
}

#[test]
fn decimal_matches_header() {
    let mirror = owned(&[
        ("value", offset_of!(FfiDecimal, value)),
        ("err", offset_of!(FfiDecimal, err)),
    ]);
    assert_eq!(
        asserted("aletheia_decimal"),
        (size_of::<FfiDecimal>(), mirror)
    );
}

#[test]
fn buffer_matches_header() {
    let mirror = owned(&[
        ("data", offset_of!(FfiBuffer, data)),
        ("err", offset_of!(FfiBuffer, err)),
        ("size", offset_of!(FfiBuffer, size)),
    ]);
    assert_eq!(
        asserted("aletheia_buffer"),
        (size_of::<FfiBuffer>(), mirror)
    );
}
