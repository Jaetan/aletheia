// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! The kernel reads and writes its strings as UTF-8 whatever the locale of the
//! process that loaded it. The GHC runtime reads the locale once, when it
//! starts, so the test re-runs this binary with `LC_ALL=C` and a sentinel
//! variable, which makes the test body run the checks instead: non-ASCII text
//! must still cross the kernel intact both ways. The child prints its sentinel
//! last, so the parent tells a child that ran every check from one that stopped
//! early.

use std::io::Write;
use std::process::Command;

use aletheia::{Client, Error, Rational};

const CHILD_ENV: &str = "ALETHEIA_TEST_LOCALE_CHILD";
const SENTINEL: &str = "ALETHEIA_LOCALE_OK";

/// One message whose signal has the unit "°C": the text reaches the kernel as
/// UTF-8 and the unit comes back in its response.
const DBC_TEXT: &str = "VERSION \"1.0\"\n\nNS_ :\n\nBS_:\n\nBU_: ECU\n\n\
    BO_ 256 M: 8 ECU\n SG_ T : 0|16@1+ (1,0) [0|65535] \"\u{b0}C\" Vector__XXX\n";

/// The checks, answering what went wrong, each as one line.
fn failures() -> Vec<String> {
    match std::env::var("LC_ALL") {
        Ok(v) if v == "C" => {}
        other => {
            return vec![format!(
                "the child runs under LC_ALL={other:?}, not C, so it proves nothing"
            )]
        }
    }
    let client = Client::new().expect("Client::new: is ALETHEIA_LIB set to a built .so?");
    let mut failures = Vec::new();
    match Rational::from_decimal("1.5\u{20ac}") {
        Err(Error::Validation(_)) => {}
        other => failures.push(format!(
            "from_decimal answered {other:?} for 1.5 and a euro sign"
        )),
    }
    match client.parse_dbc_text(DBC_TEXT) {
        Ok(parsed) => {
            let unit = &parsed.dbc.messages[0].signals[0].unit;
            if unit != "\u{b0}C" {
                failures.push(format!("the unit came back as {unit:?}"));
            }
        }
        Err(e) => failures.push(format!("parse_dbc_text refused the DBC: {e}")),
    }
    failures
}

/// The re-run child: print each failure, or the sentinel when there is none.
/// `std::process::exit` does not flush stdout, so it is flushed first.
fn run_child() -> ! {
    let failures = failures();
    for line in &failures {
        println!("{line}");
    }
    if failures.is_empty() {
        println!("{SENTINEL}");
    }
    std::io::stdout().flush().ok();
    std::process::exit(i32::from(!failures.is_empty()));
}

#[test]
fn kernel_strings_do_not_depend_on_the_locale() {
    if std::env::var(CHILD_ENV).as_deref() == Ok("1") {
        run_child();
    }
    if std::env::var_os("ALETHEIA_LIB").is_none() {
        eprintln!("ALETHEIA_LIB not set; skipping the locale test");
        return;
    }
    let exe = std::env::current_exe().expect("current_exe");
    let out = Command::new(exe)
        .args([
            "--exact",
            "kernel_strings_do_not_depend_on_the_locale",
            "--nocapture",
        ])
        .env(CHILD_ENV, "1")
        .env("LC_ALL", "C")
        .output()
        .expect("spawn the child");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let report = format!(
        "stdout: {stdout}\nstderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(
        out.status.success(),
        "child under LC_ALL=C failed\n{report}"
    );
    assert!(
        stdout.contains(SENTINEL),
        "child under LC_ALL=C did not reach its sentinel\n{report}"
    );
}
