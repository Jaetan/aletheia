// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! A DBC load builds some of the kernel's top-level constants the first time a
//! load needs them, once per process: the order its key checks sort by, the
//! words a message joining two names is written with. One load of a DBC of two
//! messages carrying the same two signal names takes every such path a load of
//! the shapes below meets, so after it each shape's loads read the same
//! allocation, the first as the second. A cost a later load pays once that the
//! warm-up does not fails here. Its own test binary (= its own process), since
//! the claim is about the process's first loads.

use aletheia::{ByteOrder, Client, Dbc, DbcMessage, DbcSignal, Presence, Rational};

/// A 16-bit unsigned signal at `start_bit`.
fn signal(name: &str, start_bit: u32) -> DbcSignal {
    DbcSignal {
        name: name.to_owned(),
        start_bit,
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
    }
}

/// A standard 8-byte message sent by one node.
fn message(id: u32, name: &str, signals: Vec<DbcSignal>) -> DbcMessage {
    DbcMessage {
        id,
        extended: false,
        name: name.to_owned(),
        dlc: 8,
        sender: "ECU".to_owned(),
        senders: Vec::new(),
        signals,
    }
}

/// A DBC of `messages`, every other list empty.
fn dbc(messages: Vec<DbcMessage>) -> Dbc {
    Dbc {
        version: "1.0".to_owned(),
        messages,
        nodes: Vec::new(),
        value_tables: Vec::new(),
        environment_vars: Vec::new(),
        signal_groups: Vec::new(),
        comments: Vec::new(),
        attributes: Vec::new(),
        unresolved_value_descs: Vec::new(),
    }
}

/// Two messages carrying the same two signal names: the key checks sort and
/// tie, and the shared names are reported joined.
fn warm_up() -> Dbc {
    dbc(vec![
        message(
            256,
            "TestMessage",
            vec![signal("SigA", 0), signal("SigB", 16)],
        ),
        message(
            257,
            "TestMessageB",
            vec![signal("SigA", 0), signal("SigB", 16)],
        ),
    ])
}

/// The shapes held: one signal, two signals, and two messages with a signal
/// name in both or with every name distinct.
fn shapes() -> Vec<(&'static str, Dbc)> {
    vec![
        (
            "one signal",
            dbc(vec![message(
                256,
                "TestMessage",
                vec![signal("TestSignal", 0)],
            )]),
        ),
        (
            "two signals",
            dbc(vec![message(
                256,
                "TestMessage",
                vec![signal("TestSignal", 0), signal("TestSignal2", 16)],
            )]),
        ),
        (
            "two messages sharing a signal name",
            dbc(vec![
                message(256, "TestMessage", vec![signal("TestSignal", 0)]),
                message(257, "TestMessageB", vec![signal("TestSignal", 0)]),
            ]),
        ),
        (
            "two messages of distinct names",
            dbc(vec![
                message(256, "TestMessage", vec![signal("SigA", 0)]),
                message(257, "TestMessageB", vec![signal("SigC", 0)]),
            ]),
        ),
    ]
}

/// The kernel's allocated bytes for one load of `dbc`.
fn load(client: &Client, dbc: &Dbc) -> u64 {
    let before = aletheia::allocated_bytes().expect("an open client has started the runtime");
    client.parse_dbc(dbc).expect("the DBC loads");
    aletheia::allocated_bytes().expect("the runtime still runs") - before
}

#[test]
fn after_the_warm_up_every_load_reads_as_the_next() {
    let client =
        Client::new().expect("init client: is ALETHEIA_LIB set to a built libaletheia-ffi.so?");
    let _ = load(&client, &warm_up());
    for (shape, dbc) in shapes() {
        let first = load(&client, &dbc);
        let second = load(&client, &dbc);
        assert_eq!(
            first, second,
            "the first two loads of {shape} after the warm-up"
        );
    }
}
