// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! The runtime's argument vector carries the cap whatever the core count
//! and puts the override's flags after it, the override's bytes split on the
//! six ASCII whitespace bytes alone and kept whether UTF-8 or not, and a core
//! count is held to one through the CPUs the runtime counts. An internal
//! `#[cfg(test)]` module so it reads the private constants directly, which are
//! private here as they are in every other binding.

use std::ffi::OsString;
use std::os::unix::ffi::OsStringExt;

use super::{build_rts_argv, core_count_refusal, rts_override_bytes, RTS_HEAP_CAP_FLAG};

#[test]
fn a_core_count_is_held_to_one_through_the_cpus_the_runtime_counts() {
    // Both ends of the range, so a bound moved by one either way is caught.
    assert_eq!(core_count_refusal(1, 20), None);
    assert_eq!(core_count_refusal(20, 20), None);
    for (cores, available) in [(0, 20), (21, 20)] {
        assert_eq!(
            core_count_refusal(cores, available),
            Some(format!(
                "core count {cores} is outside 1 to {available}, the CPUs this process may use"
            ))
        );
    }
}

#[test]
fn argv_always_carries_the_cap() {
    let cap = RTS_HEAP_CAP_FLAG.as_bytes();
    // One core: cap present, no -N.
    assert_eq!(
        build_rts_argv(1, b""),
        [&b"aletheia"[..], b"+RTS", cap, b"-RTS"]
    );
    // Multi-core: -N appended after the cap.
    assert_eq!(
        build_rts_argv(4, b""),
        [&b"aletheia"[..], b"+RTS", cap, b"-N4", b"-RTS"]
    );
    // Override flags land after the cap (so a caller -M occurs last, wins).
    assert_eq!(
        build_rts_argv(1, b"  -M12M   -hT "),
        [&b"aletheia"[..], b"+RTS", cap, b"-M12M", b"-hT", b"-RTS"]
    );
}

#[test]
fn the_override_is_split_on_the_six_ascii_whitespace_bytes_alone() {
    let cap = RTS_HEAP_CAP_FLAG.as_bytes();
    // Space, TAB, LF, CR, VT and FF each separate two flags.
    assert_eq!(
        build_rts_argv(1, b"-a -b\t-c\n-d\r-e\x0B-f\x0C-g"),
        [
            &b"aletheia"[..],
            b"+RTS",
            cap,
            b"-a",
            b"-b",
            b"-c",
            b"-d",
            b"-e",
            b"-f",
            b"-g",
            b"-RTS"
        ]
    );
    // A no-break space (U+00A0), a next line (U+0085) and the byte 0x1C stay
    // inside their flag.
    let word = b"-a\xC2\xA0-b\xC2\x85-c\x1C-d";
    assert_eq!(
        build_rts_argv(1, word),
        [&b"aletheia"[..], b"+RTS", cap, word, b"-RTS"]
    );
}

#[test]
fn a_value_that_is_not_utf8_reaches_the_runtime_inside_its_flag() {
    let cap = RTS_HEAP_CAP_FLAG.as_bytes();
    let argv = |value: &[u8]| {
        build_rts_argv(
            1,
            &rts_override_bytes(Some(OsString::from_vec(value.to_vec()))),
        )
    };
    assert_eq!(
        argv(b"-a\xFF-b"),
        [&b"aletheia"[..], b"+RTS", cap, b"-a\xFF-b", b"-RTS"]
    );
    assert_eq!(
        argv(b"-a\xFF-b -c"),
        [&b"aletheia"[..], b"+RTS", cap, b"-a\xFF-b", b"-c", b"-RTS"]
    );
    // An unset variable adds no flag.
    assert_eq!(
        build_rts_argv(1, &rts_override_bytes(None)),
        [&b"aletheia"[..], b"+RTS", cap, b"-RTS"]
    );
}
