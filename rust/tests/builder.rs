// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! `ClientBuilder` validation (Slice R4a). These cases are rejected before the
//! core library is loaded, so they need no `libaletheia-ffi.so`.

use aletheia::Client;

#[test]
fn rts_cores_zero_is_rejected() {
    // `Client` is not `Debug`, so match rather than `unwrap_err`.
    match Client::builder().rts_cores(0).build() {
        Ok(_) => panic!("rts_cores(0) must be rejected"),
        Err(e) => assert!(format!("{e}").contains("rts_cores"), "got: {e}"),
    }
}

#[test]
fn rts_cores_over_c_int_range_is_rejected() {
    assert!(Client::builder().rts_cores(u32::MAX).build().is_err());
}
