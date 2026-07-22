// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Runtime GHC RTS heap-cap containment — Rust behavioural test.
//!
//! CONTAINMENT-BY-ABORT: the heap cap is NOT a recoverable error.  When it fires
//! the process TERMINATES (a GHC HeapExhausted abort of the foreign-export
//! wrapper) so the HOST survives.  Proven out-of-process (the abort is
//! process-terminating and the GHC RTS is one-shot per process) via the classic
//! re-exec idiom: the child is this same test binary run again with a sentinel
//! env var, which makes the test body run the workload and exit instead of the
//! assertions.
//!
//!   positive — the correct path (hs_init_with_rtsopts + -M3G) boots and parses;
//!   negative — a tight ALETHEIA_RTS_OPTS=-M12M cap over a large DBC aborts.
//!
//! The parity leg (mirror constants vs docs/RESOURCE_BUDGETS.yaml) lives in an
//! internal `#[cfg(test)]` module in src/backend.rs, since it reads the private
//! mirror constants directly.

use std::io::Write;
use std::process::Command;

use aletheia::Client;

const CHILD_ENV: &str = "ALETHEIA_RTS_WORKLOAD_CHILD";
const N_ENV: &str = "ALETHEIA_RTS_WORKLOAD_N";
const SENTINEL: &str = "ALETHEIA_RTS_OK";

/// A VALID DBC of `n` messages; a large `n` builds a parse tree past a tight -M
/// cap (so it aborts mid-parse), a small `n` fits any cap and parses cleanly.
fn workload_dbc(n: usize) -> String {
    let mut s = String::from("VERSION \"\"\n\nNS_ :\n\nBS_:\n\nBU_: ECU\n\n");
    for i in 0..n {
        s.push_str(&format!("BO_ {} Msg{i}: 8 ECU\n", 256 + i));
        s.push_str(&format!(
            " SG_ Sig{i} : 0|16@1+ (0.25,0) [0|8000] \"u\" ECU\n\n"
        ));
    }
    s
}

/// The re-exec'd child: boot the real FFI client and parse the workload DBC,
/// then print the sentinel and exit 0.  Under a tight cap the parse aborts the
/// process before this returns.  `std::process::exit` does not flush stdout, so
/// the sentinel is flushed explicitly first.
fn run_child_workload() -> ! {
    let client = Client::new().expect("Client::new — is ALETHEIA_LIB set to a built .so?");
    let n: usize = std::env::var(N_ENV)
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(3);
    match client.parse_dbc_text(&workload_dbc(n)) {
        Ok(_) => {
            println!("{SENTINEL}");
            std::io::stdout().flush().ok();
            std::process::exit(0);
        }
        // A valid DBC never reaches here; 3 marks a parse error, distinct from
        // the heap abort, so the negative case can tell them apart.
        Err(_) => std::process::exit(3),
    }
}

#[test]
fn heap_cap_containment() {
    if std::env::var(CHILD_ENV).as_deref() == Ok("1") {
        run_child_workload();
    }

    // The child does the real work; skip if the library is not locatable.
    if std::env::var_os("ALETHEIA_LIB").is_none() {
        eprintln!("ALETHEIA_LIB not set; skipping heap-cap containment test");
        return;
    }
    let exe = std::env::current_exe().expect("current_exe");

    let run = |n: &str, rts: Option<&str>| -> (i32, bool) {
        let mut cmd = Command::new(&exe);
        cmd.args(["--exact", "heap_cap_containment", "--nocapture"])
            .env(CHILD_ENV, "1")
            .env(N_ENV, n);
        match rts {
            Some(v) => {
                cmd.env("ALETHEIA_RTS_OPTS", v);
            }
            None => {
                cmd.env_remove("ALETHEIA_RTS_OPTS");
            }
        }
        let out = cmd.output().expect("spawn re-exec child");
        let code = out.status.code().unwrap_or(-1);
        let sentinel = String::from_utf8_lossy(&out.stdout).contains(SENTINEL);
        (code, sentinel)
    };

    // Positive: the correct path boots and parses cleanly.
    let (code, sentinel) = run("3", None);
    assert_eq!(code, 0, "default cap should boot + parse (exit 0)");
    assert!(sentinel, "success sentinel expected under the default cap");

    // Negative (the teeth): a tight cap aborts the process.  A non-zero exit that
    // is neither 3 (parse error) is the GHC heap abort — containment, not a
    // masked failure.
    let (code, sentinel) = run("1000", Some("-M12M"));
    assert_ne!(code, 0, "tight cap should abort the process");
    assert!(!sentinel, "no success sentinel under a tight cap");
    assert_ne!(code, 3, "must be a heap abort, not a parse error");
}
