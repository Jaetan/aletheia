// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! The count of the bytes the kernel's runtime has allocated in the process:
//! over the library `ALETHEIA_LIB` names, a DBC load between two reads raises
//! it.

use aletheia::Client;

/// A DBC text of one message carrying one signal.
const DBC_TEXT: &str = concat!(
    "VERSION \"\"\n\nNS_ :\n\nBS_:\n\nBU_: ECU\n\n",
    "BO_ 200 Msg: 8 ECU\n",
    " SG_ Sel : 0|8@1+ (1,0) [0|255] \"\" ECU\n",
);

#[test]
fn a_dbc_load_between_two_reads_raises_the_count() {
    let client =
        Client::new().expect("init client: is ALETHEIA_LIB set to a built libaletheia-ffi.so?");
    let before =
        aletheia::allocated_bytes().expect("an open client has started the runtime it counts");
    client.parse_dbc_text(DBC_TEXT).expect("the DBC text loads");
    let after =
        aletheia::allocated_bytes().expect("an open client has started the runtime it counts");
    assert!(
        after > before,
        "the load allocated nothing: the count read {before}, then {after}"
    );
}
