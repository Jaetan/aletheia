// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Two reads of the kernel's allocation count bracket exactly what ran between
//! them, the bytes the runtime holds in a capability's current block of pinned
//! objects included, over the library `ALETHEIA_LIB` names. Loads of one small
//! DBC read alike from the second on, where a count leaving out the current
//! pinned block books, in the second load, bytes the first load allocated.
//! Its own test binary (= its own process), since the claim is about the
//! process's first loads.

use aletheia::{ByteOrder, Client, Dbc, DbcMessage, DbcSignal, Presence, Rational};

/// One message carrying one 16-bit signal, every other list empty: a command
/// small enough that its decode buffer shares a pinned block with what the
/// first load leaves there.
fn one_signal() -> Dbc {
    Dbc {
        version: "1.0".to_owned(),
        messages: vec![DbcMessage {
            id: 256,
            extended: false,
            name: "TestMessage".to_owned(),
            dlc: 8,
            sender: "ECU".to_owned(),
            senders: Vec::new(),
            signals: vec![DbcSignal {
                name: "TestSignal".to_owned(),
                start_bit: 0,
                length: 16,
                byte_order: ByteOrder::LittleEndian,
                signed: false,
                factor: Rational::integer(1),
                offset: Rational::integer(0),
                minimum: Rational::integer(0),
                maximum: Rational::integer(65535),
                unit: String::new(),
                receivers: Vec::new(),
                value_descriptions: Vec::new(),
                presence: Presence::Always,
            }],
        }],
        nodes: Vec::new(),
        value_tables: Vec::new(),
        environment_vars: Vec::new(),
        signal_groups: Vec::new(),
        comments: Vec::new(),
        attributes: Vec::new(),
        unresolved_value_descs: Vec::new(),
    }
}

fn read() -> u64 {
    aletheia::allocated_bytes().expect("an open client has started the runtime it counts")
}

#[test]
fn reads_bracket_exactly_what_ran_between_them() {
    let client =
        Client::new().expect("init client: is ALETHEIA_LIB set to a built libaletheia-ffi.so?");
    let dbc = one_signal();
    let first = read();
    assert_eq!(read() - first, 0, "two reads with nothing between them");
    let mut reads = vec![read()];
    for _ in 0..3 {
        client.parse_dbc(&dbc).expect("the DBC loads");
        reads.push(read());
    }
    let loads: Vec<u64> = reads.windows(2).map(|pair| pair[1] - pair[0]).collect();
    assert_eq!(
        loads[1], loads[2],
        "the second and third loads of one DBC, each load's bytes {loads:?}"
    );
}
