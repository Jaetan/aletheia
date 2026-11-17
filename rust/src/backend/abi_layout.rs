// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! The `#[repr(C)]` mirrors lay out as `haskell-shim/include/aletheia.h` fixes them. The
//! expected sizes, alignments and offsets are read from the header's own
//! `static_assert` lines, which the C compiler holds to the real layout, so
//! a field moved on either side fails here rather than misreading across
//! the ABI.

use std::mem::{align_of, offset_of, size_of};
use std::path::Path;

use super::{
    FfiBuffer, FfiDecimal, FfiFrame, FfiPropertyCheck, FfiRational, FfiSignalValues, FfiText,
    FfiTimeBound, FfiUint128, ABI_VERSION,
};

/// A structure's layout: its size, its alignment and its fields' offsets in
/// order.
type Layout = (usize, usize, Vec<(String, usize)>);

/// The header's text.
fn header() -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../haskell-shim/include/aletheia.h");
    std::fs::read_to_string(&path).expect("read haskell-shim/include/aletheia.h")
}

/// The decimal digits `s` starts with, as a number.
fn number(s: &str) -> usize {
    let digits: String = s.chars().take_while(char::is_ascii_digit).collect();
    digits.parse().expect("an asserted number")
}

/// The layout the header asserts for `name`.
fn asserted(name: &str) -> Layout {
    let size_prefix = format!("static_assert(sizeof(struct {name}) == ");
    let align_prefix = format!("static_assert(alignof(struct {name}) == ");
    let offset_prefix = format!("static_assert(offsetof(struct {name}, ");
    let mut size = None;
    let mut align = None;
    let mut fields = Vec::new();
    for line in header().lines() {
        if let Some(rest) = line.strip_prefix(&size_prefix) {
            size = Some(number(rest));
        } else if let Some(rest) = line.strip_prefix(&align_prefix) {
            align = Some(number(rest));
        } else if let Some(rest) = line.strip_prefix(&offset_prefix) {
            let (field, value) = rest.split_once(") == ").expect("an offset assertion");
            fields.push((field.to_string(), number(value)));
        }
    }
    (
        size.expect("a size assertion"),
        align.expect("an alignment assertion"),
        fields,
    )
}

/// The mirror's layout: `T`'s size and alignment and the offsets given.
fn mirror<T>(fields: &[(&str, usize)]) -> Layout {
    (
        size_of::<T>(),
        align_of::<T>(),
        fields.iter().map(|&(f, o)| (f.to_string(), o)).collect(),
    )
}

#[test]
fn abi_version_is_the_headers() {
    let prefix = "constexpr uint32_t ALETHEIA_ABI_VERSION = ";
    let text = header();
    let line = text
        .lines()
        .find_map(|line| line.strip_prefix(prefix))
        .expect("the header defines ALETHEIA_ABI_VERSION");
    assert_eq!(
        u32::try_from(number(line)).expect("a version number"),
        ABI_VERSION
    );
}

#[test]
fn text_matches_header() {
    let mirror = mirror::<FfiText>(&[
        ("data", offset_of!(FfiText, data)),
        ("size", offset_of!(FfiText, size)),
    ]);
    assert_eq!(asserted("aletheia_text"), mirror);
}

#[test]
fn frame_matches_header() {
    let mirror = mirror::<FfiFrame>(&[
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
    assert_eq!(asserted("aletheia_frame"), mirror);
}

#[test]
fn uint128_matches_header() {
    let mirror = mirror::<FfiUint128>(&[
        ("lo", offset_of!(FfiUint128, lo)),
        ("hi", offset_of!(FfiUint128, hi)),
    ]);
    assert_eq!(asserted("aletheia_uint128"), mirror);
}

#[test]
fn rational_matches_header() {
    let mirror = mirror::<FfiRational>(&[
        ("numerator", offset_of!(FfiRational, numerator)),
        ("denominator", offset_of!(FfiRational, denominator)),
        ("negative", offset_of!(FfiRational, negative)),
    ]);
    assert_eq!(asserted("aletheia_rational"), mirror);
}

#[test]
fn signal_values_match_header() {
    let mirror = mirror::<FfiSignalValues>(&[
        ("indices", offset_of!(FfiSignalValues, indices)),
        ("values", offset_of!(FfiSignalValues, values)),
        ("count", offset_of!(FfiSignalValues, count)),
    ]);
    assert_eq!(asserted("aletheia_signal_values"), mirror);
}

#[test]
fn buffer_matches_header() {
    let mirror = mirror::<FfiBuffer>(&[
        ("data", offset_of!(FfiBuffer, data)),
        ("err", offset_of!(FfiBuffer, err)),
        ("size", offset_of!(FfiBuffer, size)),
    ]);
    assert_eq!(asserted("aletheia_buffer"), mirror);
}

#[test]
fn decimal_matches_header() {
    let mirror = mirror::<FfiDecimal>(&[
        ("value", offset_of!(FfiDecimal, value)),
        ("err", offset_of!(FfiDecimal, err)),
    ]);
    assert_eq!(asserted("aletheia_decimal"), mirror);
}

#[test]
fn time_bound_matches_header() {
    let mirror = mirror::<FfiTimeBound>(&[
        ("microseconds", offset_of!(FfiTimeBound, microseconds)),
        ("err", offset_of!(FfiTimeBound, err)),
    ]);
    assert_eq!(asserted("aletheia_time_bound"), mirror);
}

#[test]
fn property_check_matches_header() {
    let mirror = mirror::<FfiPropertyCheck>(&[("err", offset_of!(FfiPropertyCheck, err))]);
    assert_eq!(asserted("aletheia_property_check"), mirror);
}
