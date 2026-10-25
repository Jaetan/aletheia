// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! `ClientBuilder` refuses a core count outside 1 to the CPUs the process may
//! use, the bound read from the library's runtime, before anything is started
//! with it. The bound's own figure is the machine's, which
//! `start_runtime_stand_in.rs` holds whole on the recording kernel's four CPUs.

use aletheia::{Client, Error};

fn refused(cores: u32) -> Error {
    // `Client` is not `Debug`, so match rather than `unwrap_err`.
    match Client::builder().rts_cores(cores).build() {
        Ok(_) => panic!("rts_cores({cores}) must be rejected"),
        Err(e) => e,
    }
}

#[test]
fn rts_cores_zero_is_rejected() {
    let e = refused(0);
    assert!(
        matches!(&e, Error::Validation { message, .. }
            if message.starts_with("core count 0 is outside 1 to ")),
        "got: {e}"
    );
}

#[test]
fn rts_cores_past_every_machine_s_cpus_is_rejected() {
    let e = refused(u32::MAX);
    assert!(
        matches!(&e, Error::Validation { message, .. }
            if message.starts_with(&format!("core count {} is outside 1 to ", u32::MAX))),
        "got: {e}"
    );
}
