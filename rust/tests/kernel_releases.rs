// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! The backend releases what the kernel hands it: the string a command
//! answered is freed once it has been copied, and the state the backend opened
//! is closed when the client is dropped. The real kernel acknowledges both
//! without reading, so the one library whose releases can be read is the
//! recording kernel the build makes beside the library, which counts them. Its
//! own test binary (= its own process) because a library stays loaded for the
//! process lifetime, and this one must be the first the process loads.

mod stand_in;

use std::ffi::c_int;

use aletheia::Client;
use libloading::{Library, Symbol};

type CountFn = unsafe extern "C" fn() -> c_int;

/// One of the recording kernel's counters, read through a second handle on
/// the same path, which is the same mapping and so the backend's own counts.
fn count(counters: &Library, name: &[u8]) -> c_int {
    // SAFETY: the recording kernel exports each counter as `int name(void)`.
    unsafe {
        let read: Symbol<CountFn> = counters
            .get(name)
            .expect("the recording kernel exports its counters");
        read()
    }
}

#[test]
fn the_backend_frees_the_strings_it_was_handed_and_closes_the_state_it_opened() {
    let path = stand_in::stand_in("recording_kernel");
    std::env::set_var("ALETHEIA_LIB", &path);
    // SAFETY: the stand-in runs no initialiser that needs the process's cooperation.
    let counters = unsafe { Library::new(&path) }.expect("the recording kernel loads");

    let closes = count(&counters, b"aletheia_test_close_count\0");
    let frees = count(&counters, b"aletheia_test_free_count\0");
    let client = Client::new().expect("a client on the recording kernel");

    // The stand-in refuses every command, quoting the size it was handed; the
    // refusal reached the caller as text, so the kernel's block was copied and
    // is to be released.
    let command = r#"{"command":"ping"}"#;
    let answer = client
        .process(command)
        .expect("the refusal is the command's answer");
    assert!(
        answer.contains(&format!("process size={}", command.len())),
        "the stand-in quotes the command's size: {answer}"
    );
    assert_eq!(
        count(&counters, b"aletheia_test_free_count\0"),
        frees + 1,
        "one string was handed back, and it was freed"
    );

    drop(client);
    assert_eq!(
        count(&counters, b"aletheia_test_close_count\0"),
        closes + 1,
        "the state the backend opened was closed when the client was dropped"
    );
}
