// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! The fixtures the modes measure with: the DBC documents, the frame
//! payloads, the LTL properties and the signal values frames are built from.

use aletheia::{
    ByteOrder, Comment, CommentTarget, Dbc, DbcMessage, DbcSignal, Formula, Node, Predicate,
    Presence, Rational, SignalValue,
};

// ---------------------------------------------------------------------------
// DBC construction (programmatic, matching examples/*.dbc and the Go / C++
// benchmark definitions so every binding measures the same map-backed lookup
// path a real user exercises).
// ---------------------------------------------------------------------------

/// Shorthand for an exact rational used in the benchmark DBC definitions.
pub(crate) fn r(num: i64, den: i64) -> Rational {
    Rational::new(num, den).expect("benchmark rationals have non-zero positive denominators")
}

/// Build a little-endian, always-present signal. `scale` is `(factor, offset)`
/// and `bounds` is `(minimum, maximum)` — bundling them keeps the parameter
/// count within clippy's limit while covering the fields the benchmark varies.
fn sig(
    name: &str,
    start: u32,
    len: u32,
    signed: bool,
    scale: (Rational, Rational),
    bounds: (Rational, Rational),
    unit: &str,
) -> DbcSignal {
    DbcSignal {
        name: name.to_string(),
        start_bit: start,
        length: len,
        byte_order: ByteOrder::LittleEndian,
        signed,
        factor: scale.0,
        offset: scale.1,
        minimum: bounds.0,
        maximum: bounds.1,
        unit: unit.to_string(),
        receivers: Vec::new(),
        value_descriptions: Vec::new(),
        presence: Presence::Always,
    }
}

/// Build a standard-id (11-bit) message with the given signals.
fn msg(id: u32, name: &str, dlc: u32, sender: &str, signals: Vec<DbcSignal>) -> DbcMessage {
    DbcMessage {
        id,
        extended: false,
        name: name.to_string(),
        dlc,
        sender: sender.to_string(),
        senders: Vec::new(),
        signals,
    }
}

/// Wrap messages in an otherwise-empty DBC document.
fn dbc(messages: Vec<DbcMessage>) -> Dbc {
    Dbc {
        version: String::new(),
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

/// CAN 2.0B database: EngineStatus (0x100) + BrakeStatus (0x200).
pub(crate) fn can20_dbc() -> Dbc {
    let engine = msg(
        0x100,
        "EngineStatus",
        8,
        "ECU1",
        vec![
            sig(
                "EngineSpeed",
                0,
                16,
                false,
                (r(1, 4), r(0, 1)),
                (r(0, 1), r(8000, 1)),
                "rpm",
            ),
            sig(
                "EngineTemp",
                16,
                8,
                false,
                (r(1, 1), r(-40, 1)),
                (r(-40, 1), r(215, 1)),
                "celsius",
            ),
        ],
    );
    let brake = msg(
        0x200,
        "BrakeStatus",
        8,
        "ECU2",
        vec![
            sig(
                "BrakePressure",
                0,
                16,
                false,
                (r(1, 10), r(0, 1)),
                (r(0, 1), r(65535, 10)),
                "bar",
            ),
            sig(
                "BrakePressed",
                16,
                1,
                false,
                (r(1, 1), r(0, 1)),
                (r(0, 1), r(1, 1)),
                "",
            ),
        ],
    );
    dbc(vec![engine, brake])
}

/// CAN-FD database: a 25-signal SensorFusion message (0x200, DLC 15 = 64 bytes).
pub(crate) fn canfd_dbc() -> Dbc {
    let signals = vec![
        sig(
            "GPSLatitude",
            0,
            32,
            true,
            (r(1, 10_000_000), r(0, 1)),
            (r(-90, 1), r(90, 1)),
            "deg",
        ),
        sig(
            "GPSLongitude",
            32,
            32,
            true,
            (r(1, 10_000_000), r(0, 1)),
            (r(-180, 1), r(180, 1)),
            "deg",
        ),
        sig(
            "GPSAltitude",
            64,
            16,
            true,
            (r(1, 10), r(0, 1)),
            (r(-1000, 1), r(32767, 10)),
            "m",
        ),
        sig(
            "GPSSpeed",
            80,
            16,
            false,
            (r(1, 100), r(0, 1)),
            (r(0, 1), r(65535, 100)),
            "m/s",
        ),
        sig(
            "YawRate",
            96,
            16,
            true,
            (r(1, 100), r(0, 1)),
            (r(-32768, 100), r(32767, 100)),
            "deg/s",
        ),
        sig(
            "LateralAccel",
            112,
            16,
            true,
            (r(1, 100), r(0, 1)),
            (r(-32768, 100), r(32767, 100)),
            "m/s2",
        ),
        sig(
            "LongAccel",
            128,
            16,
            true,
            (r(1, 100), r(0, 1)),
            (r(-32768, 100), r(32767, 100)),
            "m/s2",
        ),
        sig(
            "SteeringAngle",
            144,
            16,
            true,
            (r(1, 10), r(0, 1)),
            (r(-32768, 10), r(32767, 10)),
            "deg",
        ),
        sig(
            "WheelSpeedFL",
            160,
            16,
            false,
            (r(1, 100), r(0, 1)),
            (r(0, 1), r(65535, 100)),
            "m/s",
        ),
        sig(
            "WheelSpeedFR",
            176,
            16,
            false,
            (r(1, 100), r(0, 1)),
            (r(0, 1), r(65535, 100)),
            "m/s",
        ),
        sig(
            "WheelSpeedRL",
            192,
            16,
            false,
            (r(1, 100), r(0, 1)),
            (r(0, 1), r(65535, 100)),
            "m/s",
        ),
        sig(
            "WheelSpeedRR",
            208,
            16,
            false,
            (r(1, 100), r(0, 1)),
            (r(0, 1), r(65535, 100)),
            "m/s",
        ),
        sig(
            "BrakeTempFL",
            224,
            12,
            false,
            (r(1, 10), r(0, 1)),
            (r(0, 1), r(4095, 10)),
            "celsius",
        ),
        sig(
            "BrakeTempFR",
            236,
            12,
            false,
            (r(1, 10), r(0, 1)),
            (r(0, 1), r(4095, 10)),
            "celsius",
        ),
        sig(
            "BrakeTempRL",
            248,
            12,
            false,
            (r(1, 10), r(0, 1)),
            (r(0, 1), r(4095, 10)),
            "celsius",
        ),
        sig(
            "BrakeTempRR",
            260,
            12,
            false,
            (r(1, 10), r(0, 1)),
            (r(0, 1), r(4095, 10)),
            "celsius",
        ),
        sig(
            "TirePressFL",
            272,
            8,
            false,
            (r(1, 100), r(0, 1)),
            (r(0, 1), r(255, 100)),
            "bar",
        ),
        sig(
            "TirePressFR",
            280,
            8,
            false,
            (r(1, 100), r(0, 1)),
            (r(0, 1), r(255, 100)),
            "bar",
        ),
        sig(
            "TirePressRL",
            288,
            8,
            false,
            (r(1, 100), r(0, 1)),
            (r(0, 1), r(255, 100)),
            "bar",
        ),
        sig(
            "TirePressRR",
            296,
            8,
            false,
            (r(1, 100), r(0, 1)),
            (r(0, 1), r(255, 100)),
            "bar",
        ),
        sig(
            "SensorStatus",
            304,
            8,
            false,
            (r(1, 1), r(0, 1)),
            (r(0, 1), r(255, 1)),
            "",
        ),
        sig(
            "IMUTemp",
            312,
            8,
            false,
            (r(1, 1), r(-40, 1)),
            (r(-40, 1), r(215, 1)),
            "celsius",
        ),
        sig(
            "BatteryVolt",
            320,
            12,
            false,
            (r(1, 100), r(0, 1)),
            (r(0, 1), r(4095, 100)),
            "V",
        ),
        sig(
            "GPSHeading",
            332,
            16,
            false,
            (r(1, 100), r(0, 1)),
            (r(0, 1), r(65535, 100)),
            "deg",
        ),
        sig(
            "TimestampMs",
            348,
            32,
            false,
            (r(1, 1), r(0, 1)),
            (r(0, 1), r(4_294_967_295, 1)),
            "ms",
        ),
    ];
    // The message `dlc` field is a byte count on the wire (Go serializes
    // `DLC.ToBytes()`); DLC code 15 = 64 bytes. The DLC *code* 15 is what the
    // send / extract / build calls use (`Dlc::new(15)`).
    dbc(vec![msg(
        0x200,
        "SensorFusion",
        64,
        "SensorGateway",
        signals,
    )])
}

/// The DBC-size sweep's document: version `1.0`, the nodes `N0` … `N{count-1}`,
/// `count` messages `M{i}` (extended id `0x100000 + i`, 8 bytes, sent by `N{i}`
/// with the additional sender `N{(i+1) % count}`), each carrying one 8-bit
/// unsigned signal `S{i}` received by `N{i}`, and one comment per message
/// targeting it by its id. Every kind of reference grows with the messages,
/// every name resolves, and no two messages share an id, a name or a signal
/// name, so the load succeeds.
pub(crate) fn sized_dbc(count: u32) -> Dbc {
    let id = |i: u32| 0x10_0000 + i;
    let messages = (0..count)
        .map(|i| {
            let signal = DbcSignal {
                receivers: vec![format!("N{i}")],
                ..sig(
                    &format!("S{i}"),
                    0,
                    8,
                    false,
                    (r(1, 1), r(0, 1)),
                    (r(0, 1), r(255, 1)),
                    "",
                )
            };
            DbcMessage {
                extended: true,
                senders: vec![format!("N{}", (i + 1) % count)],
                ..msg(id(i), &format!("M{i}"), 8, &format!("N{i}"), vec![signal])
            }
        })
        .collect();
    Dbc {
        version: "1.0".to_string(),
        nodes: (0..count)
            .map(|i| Node {
                name: format!("N{i}"),
            })
            .collect(),
        comments: (0..count)
            .map(|i| Comment {
                target: CommentTarget::Message {
                    id: id(i),
                    extended: true,
                },
                text: "c".to_owned(),
            })
            .collect(),
        ..dbc(messages)
    }
}

// ---------------------------------------------------------------------------
// Frame payloads
// ---------------------------------------------------------------------------

/// CAN 2.0B payload (8 bytes): EngineSpeed raw 0x1F40 -> 2000 * 0.25 = ...
pub(crate) fn can20_frame() -> Vec<u8> {
    vec![0x40, 0x1F, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00]
}

/// CAN-FD payload (64 bytes) with realistic sensor-fusion values, zero-padded.
pub(crate) fn canfd_frame() -> Vec<u8> {
    let mut frame = vec![
        0x00, 0xE1, 0xF5, 0x05, // GPSLatitude
        0x00, 0x6C, 0xDC, 0x02, // GPSLongitude
        0xE8, 0x03, // GPSAltitude
        0xD0, 0x07, // GPSSpeed
        0x00, 0x00, // YawRate
        0x00, 0x00, // LateralAccel
        0x00, 0x00, // LongAccel
        0x00, 0x00, // SteeringAngle
        0xE8, 0x03, // WheelSpeedFL
        0xE8, 0x03, // WheelSpeedFR
        0xE8, 0x03, // WheelSpeedRL
        0xE8, 0x03, // WheelSpeedRR
    ];
    frame.resize(64, 0x00);
    frame
}

// ---------------------------------------------------------------------------
// LTL properties and build-frame signal values
// ---------------------------------------------------------------------------

/// `G(min <= signal <= max)` over integer bounds.
pub(crate) fn always_between(signal: &str, min: i64, max: i64) -> Formula {
    Formula::Always(Box::new(Formula::Atomic(Predicate::Between {
        signal: signal.to_string(),
        min: Rational::integer(min),
        max: Rational::integer(max),
    })))
}

/// `G(signal < value)`.
pub(crate) fn always_less_than(signal: &str, value: Rational) -> Formula {
    Formula::Always(Box::new(Formula::Atomic(Predicate::less_than(
        signal, value,
    ))))
}

pub(crate) fn can20_properties() -> Vec<Formula> {
    vec![
        always_between("EngineSpeed", 0, 8000),
        always_between("EngineTemp", -40, 215),
    ]
}

pub(crate) fn canfd_properties() -> Vec<Formula> {
    vec![
        always_between("GPSSpeed", 0, 655),
        always_between("YawRate", -327, 327),
        always_between("WheelSpeedFL", 0, 655),
    ]
}

/// The property templates for the scaling sweep (rotated to reach a count).
fn scaling_property(index: usize) -> Formula {
    match index % 10 {
        0 => always_between("EngineSpeed", 0, 8000),
        1 => always_between("EngineTemp", -40, 215),
        2 => always_less_than("BrakePressure", r(13107, 2)),
        3 => always_less_than("EngineSpeed", Rational::integer(7000)),
        4 => always_less_than("EngineTemp", Rational::integer(200)),
        5 => always_less_than("BrakePressure", Rational::integer(5000)),
        6 => always_between("EngineSpeed", 500, 7500),
        7 => always_between("EngineTemp", -20, 180),
        8 => always_between("BrakePressure", 0, 4000),
        _ => always_less_than("EngineSpeed", Rational::integer(6000)),
    }
}

pub(crate) fn make_properties(count: usize) -> Vec<Formula> {
    (0..count).map(scaling_property).collect()
}

pub(crate) fn can20_signals() -> Vec<SignalValue> {
    vec![
        SignalValue {
            name: "EngineSpeed".to_string(),
            value: Rational::integer(2000),
        },
        SignalValue {
            name: "EngineTemp".to_string(),
            value: Rational::integer(90),
        },
    ]
}

pub(crate) fn canfd_signals() -> Vec<SignalValue> {
    vec![
        SignalValue {
            name: "GPSSpeed".to_string(),
            value: Rational::integer(20),
        },
        SignalValue {
            name: "YawRate".to_string(),
            value: Rational::integer(0),
        },
        SignalValue {
            name: "WheelSpeedFL".to_string(),
            value: Rational::integer(10),
        },
        SignalValue {
            name: "WheelSpeedFR".to_string(),
            value: Rational::integer(10),
        },
    ]
}
