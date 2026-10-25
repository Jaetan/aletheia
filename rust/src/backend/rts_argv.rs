// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! The runtime's argument vector carries the cap whatever the core count
//! and puts the override's flags after it, and a core count is held to one
//! through the CPUs the runtime counts. An internal `#[cfg(test)]` module so
//! it reads the private constants directly, which are private here as they
//! are in every other binding.

use super::{build_rts_argv, core_count_refusal, RTS_HEAP_CAP_FLAG};

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
    // One core: cap present, no -N.
    assert_eq!(
        build_rts_argv(1, ""),
        vec!["aletheia", "+RTS", RTS_HEAP_CAP_FLAG, "-RTS"]
    );
    // Multi-core: -N appended after the cap.
    assert_eq!(
        build_rts_argv(4, ""),
        vec!["aletheia", "+RTS", RTS_HEAP_CAP_FLAG, "-N4", "-RTS"]
    );
    // Override flags land after the cap (so a caller -M occurs last, wins).
    assert_eq!(
        build_rts_argv(1, "  -M12M   -hT "),
        vec![
            "aletheia",
            "+RTS",
            RTS_HEAP_CAP_FLAG,
            "-M12M",
            "-hT",
            "-RTS"
        ]
    );
}
