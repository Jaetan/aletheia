// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! A command holding one long number is refused, and the process that sent it
//! lives.
//!
//! The kernel refuses a JSON number whose rational components pass the signed
//! 64-bit range, and its refusal reports the measured magnitude up to 2^64-1
//! and that ceiling past it, with "at least" before the ceiling in the message.
//! A command of about 100 KB whose one number has 100,001 digits gets that
//! refusal. No typed method can send such a number, so the command goes
//! through [`Client::process`], from a child: this same test binary run again
//! with a variable set. A kernel that echoes the number whole ends the process
//! that called it, so the parent reads the child's reply and exit status rather
//! than sharing its end.

use std::io::Write;
use std::process::Command;

use aletheia::Client;

const CHILD_ENV: &str = "ALETHEIA_LITERAL_BOUND_CHILD";
const TEST_NAME: &str = "long_literal_refused_at_the_ceiling";

/// Marks the child's reply in its stdout, which the test harness writes to too.
const REPLY_MARKER: &str = "ALETHEIA_LITERAL_REPLY:";

/// The digits after the leading 1 of the command's one number.
const ZEROS: usize = 100_000;

/// The largest rational component the kernel accepts, `max-rational-component-magnitude`.
const LIMIT: u64 = 9_223_372_036_854_775_807;

/// The child's exit when the call returned an error rather than a reply,
/// distinct from the end under test.
const CALL_FAILED: i32 = 3;

/// The child: send the command through the raw entry and print the reply after
/// its marker. `std::process::exit` does not flush stdout, so it is flushed
/// first.
fn run_child() -> ! {
    let client = Client::new().expect("Client::new — is ALETHEIA_LIB set to a built .so?");
    let command = format!(
        r#"{{"type": "command", "command": "startStream", "x": 1{}}}"#,
        "0".repeat(ZEROS)
    );
    match client.process(&command) {
        Ok(reply) => {
            println!("{REPLY_MARKER}{reply}");
            std::io::stdout().flush().ok();
            std::process::exit(0);
        }
        Err(e) => {
            eprintln!("child call: {e}");
            std::process::exit(CALL_FAILED);
        }
    }
}

#[test]
fn long_literal_refused_at_the_ceiling() {
    if std::env::var(CHILD_ENV).as_deref() == Ok("1") {
        run_child();
    }

    // The child loads the kernel ALETHEIA_LIB names; without it the test returns.
    if std::env::var_os("ALETHEIA_LIB").is_none() {
        eprintln!("ALETHEIA_LIB not set; skipping the long-literal test");
        return;
    }
    let exe = std::env::current_exe().expect("current_exe");
    let out = Command::new(exe)
        .args(["--exact", TEST_NAME, "--nocapture"])
        .env(CHILD_ENV, "1")
        // Removed so a shell that set the runtime's flags does not decide what
        // the child runs under.
        .env_remove("ALETHEIA_RTS_OPTS")
        .output()
        .expect("spawn re-exec child");
    assert!(
        out.status.success(),
        "the child ended with {}:\n{}",
        out.status,
        String::from_utf8_lossy(&out.stderr)
    );

    let stdout = String::from_utf8(out.stdout).expect("the child's stdout is UTF-8");
    let reply = stdout
        .split_once(REPLY_MARKER)
        .and_then(|(_, rest)| rest.lines().next())
        .expect("the child printed its reply");
    let reply: serde_json::Value = serde_json::from_str(reply).expect("the reply is JSON");
    assert_eq!(reply["status"], "error", "{reply}");
    assert_eq!(reply["code"], "input_bound_exceeded", "{reply}");
    assert_eq!(
        reply["bound_kind"], "rational_component_magnitude",
        "{reply}"
    );
    assert_eq!(reply["observed"].as_u64(), Some(u64::MAX), "{reply}");
    assert_eq!(reply["limit"].as_u64(), Some(LIMIT), "{reply}");
    assert_eq!(
        reply["message"],
        format!(
            "rational component magnitude at least {} exceeds limit {LIMIT}",
            u64::MAX
        ),
        "{reply}"
    );
}
