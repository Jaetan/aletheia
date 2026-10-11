// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! The runtime's argument vector carries the cap whatever the core count
//! and puts the override's flags after it. An internal `#[cfg(test)]`
//! module so it reads the private constants directly, which are private
//! here as they are in every other binding.

use super::{build_rts_argv, RTS_HEAP_CAP_FLAG};

#[test]
fn argv_always_carries_the_cap() {
    // Default cores: cap present, no -N.
    assert_eq!(
        build_rts_argv(None, ""),
        vec!["aletheia", "+RTS", RTS_HEAP_CAP_FLAG, "-RTS"]
    );
    assert_eq!(
        build_rts_argv(Some(1), ""),
        vec!["aletheia", "+RTS", RTS_HEAP_CAP_FLAG, "-RTS"]
    );
    // Multi-core: -N appended after the cap.
    assert_eq!(
        build_rts_argv(Some(4), ""),
        vec!["aletheia", "+RTS", RTS_HEAP_CAP_FLAG, "-N4", "-RTS"]
    );
    // Override flags land after the cap (so a caller -M occurs last, wins).
    assert_eq!(
        build_rts_argv(Some(1), "  -M12M   -hT "),
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
