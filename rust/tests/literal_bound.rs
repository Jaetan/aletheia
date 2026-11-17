// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! A command or a DBC text holding one long number is refused, and the process
//! that sent it lives.
//!
//! The kernel refuses a number whose rational components pass 2^128-1, and
//! its refusal reports the measured magnitude up to that bound and the bound
//! itself past it, the message then naming no number.
//! A command of about 100 KB whose one number has 100,001 digits gets that
//! refusal, and so does a DBC text whose one VAL_ key has 100,000 digits,
//! naming the field. No typed method can send such a number, so each goes
//! through [`Client::process`], from a child: this same test binary run again
//! with a variable set. A kernel that echoes or folds the number whole ends the
//! process that called it, so the parent reads the child's reply and exit
//! status rather than sharing its end.

use std::collections::BTreeMap;
use std::io::Write;
use std::process::Command;

use aletheia::limits::BOUND_KIND_RATIONAL_COMPONENT_MAGNITUDE;
use aletheia::Client;
use serde_json::value::RawValue;

const CHILD_ENV: &str = "ALETHEIA_LITERAL_BOUND_CHILD";
const TEST_NAME: &str = "long_literal_refused_at_the_ceiling";

/// Marks the child's reply in its stdout, which the test harness writes to too.
const REPLY_MARKER: &str = "ALETHEIA_LITERAL_REPLY:";

/// The digits after the leading 1 of the command's one number.
const ZEROS: usize = 100_000;

/// The largest rational component the kernel accepts, `max-rational-component-magnitude`.
const LIMIT: u128 = u128::MAX;

/// A reply's places, each kept as the JSON text the kernel wrote, so a number
/// past 64 bits is read exactly.
type Reply = BTreeMap<String, Box<RawValue>>;

/// The string a reply place holds.
fn text(reply: &Reply, key: &str) -> String {
    serde_json::from_str(reply[key].get())
        .unwrap_or_else(|e| panic!("reply {key}: {e}: {}", reply[key].get()))
}

/// The natural number a reply place holds, read from its digits.
fn natural(reply: &Reply, key: &str) -> u128 {
    reply[key]
        .get()
        .parse()
        .unwrap_or_else(|e| panic!("reply {key}: {e}: {}", reply[key].get()))
}

/// Asserts `reply` is the bound refusal of a rational component past the
/// bound, its places exactly the triple, the code, the message `message` and,
/// when `field` names one, the field: the measured magnitude past the bound is
/// reported as the bound itself.
fn assert_the_bound_refusal(reply: &str, field: Option<&str>, message: &str) {
    let reply: Reply = serde_json::from_str(reply).expect("the reply is a JSON object");
    let mut keys = vec![
        "bound_kind",
        "code",
        "limit",
        "message",
        "observed",
        "status",
    ];
    keys.extend(field.map(|_| "field"));
    keys.sort_unstable();
    assert_eq!(
        reply.keys().map(String::as_str).collect::<Vec<_>>(),
        keys,
        "the reply's places"
    );
    assert_eq!(text(&reply, "status"), "error");
    assert_eq!(text(&reply, "code"), "input_bound_exceeded");
    assert_eq!(
        text(&reply, "bound_kind"),
        BOUND_KIND_RATIONAL_COMPONENT_MAGNITUDE
    );
    if let Some(field) = field {
        assert_eq!(text(&reply, "field"), field);
    }
    assert_eq!(natural(&reply, "observed"), LIMIT);
    assert_eq!(natural(&reply, "limit"), LIMIT);
    assert_eq!(text(&reply, "message"), message);
}

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
    assert_the_bound_refusal(
        reply,
        None,
        &format!("rational component magnitude exceeds limit {LIMIT}"),
    );
}

/// The child's selector for the DBC text case.
const TEXT_CHILD_VALUE: &str = "text";
const TEXT_TEST_NAME: &str = "long_dbc_text_key_refused_at_the_ceiling";
/// The digits of the text's one VAL_ key.
const KEY_DIGITS: usize = 100_000;

/// The child for the DBC text case: load the text through the raw entry and
/// print the reply after its marker.
fn run_text_child() -> ! {
    let client = Client::new().expect("Client::new — is ALETHEIA_LIB set to a built .so?");
    let text = format!(
        concat!(
            r#"VERSION \"\"\n\nNS_ :\n\nBS_:\n\nBU_: ECU\n\n"#,
            r#"BO_ 200 Msg: 8 ECU\n SG_ Sel : 0|8@1+ (1,0) [0|255] \"\" ECU\n\n"#,
            r#"VAL_ 200 Sel {} \"Big\" 1 \"On\" ;\n"#
        ),
        "9".repeat(KEY_DIGITS)
    );
    let command = format!(r#"{{"type": "command", "command": "parseDBCText", "text": "{text}"}}"#);
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
fn long_dbc_text_key_refused_at_the_ceiling() {
    if std::env::var(CHILD_ENV).as_deref() == Ok(TEXT_CHILD_VALUE) {
        run_text_child();
    }
    if std::env::var_os("ALETHEIA_LIB").is_none() {
        eprintln!("ALETHEIA_LIB not set; skipping the long-key test");
        return;
    }
    let exe = std::env::current_exe().expect("current_exe");
    let out = Command::new(exe)
        .args(["--exact", TEXT_TEST_NAME, "--nocapture"])
        .env(CHILD_ENV, TEXT_CHILD_VALUE)
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
    assert_the_bound_refusal(
        reply,
        Some("value description key"),
        &format!(
            "ParseDBCText: value description key: rational component magnitude exceeds limit {LIMIT}"
        ),
    );
}
