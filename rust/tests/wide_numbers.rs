// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! The numbers the kernel carries past 64 bits, through the real library.
//! Each number kind has its own bound, decided by the kernel when it reads the
//! number: a rational's numerator magnitude and denominator at most 2^128-1, a
//! multiplex value at most 2^128-1, a value-description key signed with its
//! magnitude at most 2^128-1, and a time bound at most 2^64-1 microseconds. A
//! refusal past a bound whose measured value passes the reported ceiling names
//! no number. The cases are those of the Go binding's `wide_numbers_test.go`
//! and the C++ binding's `integration_tests_wide_numbers.cpp`. Set
//! `ALETHEIA_LIB` to the built shared library (run_ci / CI does).

use aletheia::{
    BoundRefusal, ByteOrder, CanId, Client, Dbc, DbcMessage, DbcSignal, Dlc, Error,
    ExtractionResult, Formula, MockBackend, Predicate, Presence, Rational, SignMagnitude,
    SignalValue, TimeBound, ValueDescription, ValueTable,
};

/// 2^128-1 as a DBC text writes it.
const U128_MAX_DIGITS: &str = "340282366920938463463374607431768211455";

/// 2^128 as a DBC text writes it.
const TWO_TO_128_DIGITS: &str = "340282366920938463463374607431768211456";

/// The factor opendbc's vw_mlb.dbc gives OBD_Abs_Load_Val, 100/255 printed to
/// 17 places, so a value's reduced numerator passes 64 bits on most raw values.
const VW_MLB_NUMERATOR: u128 = 39_215_686_274_509_803;
const VW_MLB_DENOMINATOR: u128 = 100_000_000_000_000_000;

/// The one message every built DBC carries.
const MESSAGE_ID: u16 = 0x100;

fn client() -> Client {
    Client::new().expect("init client: is ALETHEIA_LIB set to a built libaletheia-ffi.so?")
}

fn message_id() -> CanId {
    CanId::standard(MESSAGE_ID).expect("an 11-bit id")
}

fn eight_bytes() -> Dlc {
    Dlc::new(8).expect("DLC 8")
}

/// `numerator / denominator`, reduced.
fn ratio(numerator: u128, denominator: u128) -> Rational {
    Rational::from_parts(false, numerator, denominator).expect("a positive denominator")
}

/// A little-endian unsigned signal at bit zero, offset zero, its range from
/// zero.
fn unsigned_signal(name: &str, length: u32, factor: Rational, maximum: Rational) -> DbcSignal {
    DbcSignal {
        name: name.to_owned(),
        start_bit: 0,
        length,
        byte_order: ByteOrder::LittleEndian,
        signed: false,
        factor,
        offset: Rational::integer(0),
        minimum: Rational::integer(0),
        maximum,
        unit: String::new(),
        receivers: Vec::new(),
        value_descriptions: Vec::new(),
        presence: Presence::Always,
    }
}

/// The DBC whose one 8-byte message, 0x100, carries the signal.
fn one_signal_dbc(signal: DbcSignal) -> Dbc {
    Dbc {
        version: "1.0".to_owned(),
        messages: vec![DbcMessage {
            id: u32::from(MESSAGE_ID),
            extended: false,
            name: "Msg".to_owned(),
            dlc: 8,
            sender: "ECU".to_owned(),
            senders: Vec::new(),
            signals: vec![signal],
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

/// The `parseDBC` command line `Client::parse_dbc` writes for `dbc`, as a
/// client over a mock records it.
fn parse_dbc_command(dbc: &Dbc) -> String {
    let mock = MockBackend::new();
    mock.respond_err(Error::NullResponse);
    let refused = Client::with_backend(Box::new(mock.clone())).parse_dbc(dbc);
    assert!(
        matches!(refused, Err(Error::NullResponse)),
        "the mock answers the queued error, got: {refused:?}"
    );
    let mut captured = mock.captured();
    assert_eq!(captured.len(), 1, "one command: {captured:?}");
    captured.remove(0)
}

/// A DBC loaded twice: by a client through the typed `parse_dbc`, whose
/// `extract_signals` then takes the binary route, and by a client through the
/// raw `parseDBC` command, which leaves its signal-name cache empty, so its
/// `extract_signals` reads the JSON extraction reply.
struct BothRoutes {
    binary: Client,
    json: Client,
}

impl BothRoutes {
    fn new(dbc: &Dbc) -> Self {
        let binary = client();
        binary.parse_dbc(dbc).expect("parse_dbc");
        let json = client();
        let reply = json
            .process(&parse_dbc_command(dbc))
            .expect("parseDBC round-trip");
        let status = serde_json::from_str::<serde_json::Value>(&reply)
            .ok()
            .and_then(|v| v.get("status").and_then(|s| s.as_str().map(str::to_owned)));
        assert_eq!(
            status.as_deref(),
            Some("success"),
            "the document loads through parseDBC, got: {reply}"
        );
        BothRoutes { binary, json }
    }

    /// The frame of message 0x100 read on each route.
    fn read(&self, payload: &[u8]) -> [(&'static str, ExtractionResult); 2] {
        let read = |route: &'static str, client: &Client| {
            let result = client
                .extract_signals(message_id(), eight_bytes(), payload)
                .unwrap_or_else(|e| panic!("{route} route: {e:?}"));
            (route, result)
        };
        [read("binary", &self.binary), read("JSON", &self.json)]
    }
}

/// Holds that a route read the one value `name` = `want` and no error.
fn assert_one_value(route: &str, read: &ExtractionResult, name: &str, want: Rational) {
    let expected = vec![SignalValue {
        name: name.to_owned(),
        value: want,
    }];
    assert_eq!(read.values, expected, "{route} route: {read:?}");
    assert!(read.errors.is_empty(), "{route} route: {read:?}");
}

/// A one-message, 64-byte DBC text carrying the given SG_ and VAL_ lines,
/// after a value table section holding `tables`.
fn wide_dbc_text(tables: &str, body: &str) -> String {
    format!("VERSION \"\"\n\nNS_ :\n\nBS_:\n\nBU_: ECU\n\n{tables}BO_ 256 M: 64 ECU\n{body}")
}

/// Loads the DBC text, failing the test on a refusal.
fn parse_wide_text(client: &Client, text: &str) -> Dbc {
    client
        .parse_dbc_text(text)
        .unwrap_or_else(|e| panic!("parse_dbc_text: {e:?}"))
        .dbc
}

/// The decimal digits of 5^n.
fn digits_of_five_to(n: usize) -> String {
    let mut digits = vec![1u8];
    for _ in 0..n {
        let mut carry = 0;
        for digit in digits.iter_mut().rev() {
            let product = *digit * 5 + carry;
            *digit = product % 10;
            carry = product / 10;
        }
        if carry > 0 {
            digits.insert(0, carry);
        }
    }
    digits.iter().map(|d| char::from(b'0' + d)).collect()
}

/// The text and the fields of the bound refusal `result` holds.
fn bound_refusal<T: std::fmt::Debug>(result: Result<T, Error>) -> (String, BoundRefusal) {
    let err = match result {
        Err(err) => err,
        Ok(value) => panic!("want Error::InputBoundExceeded, got {value:?}"),
    };
    let text = err.to_string();
    match err {
        Error::InputBoundExceeded(refusal) => (text, *refusal),
        other => panic!("want Error::InputBoundExceeded, got {other:?}"),
    }
}

/// A 64-bit signal declaring its full range reads its largest raw value,
/// 2^64-1, exactly on both extraction routes.
#[test]
fn a_64_bit_raw_value_extracts_exactly_on_both_routes() {
    let u64_max = Rational::from(u64::MAX);
    let routes = BothRoutes::new(&one_signal_dbc(unsigned_signal(
        "Big",
        64,
        Rational::integer(1),
        u64_max,
    )));
    for (route, read) in routes.read(&[0xFF; 8]) {
        assert_one_value(route, &read, "Big", u64_max);
    }
}

/// Building a frame from the largest value a 64-bit signal carries, 2^64-1,
/// sets every bit.
#[test]
fn a_frame_built_from_a_64_bit_value_sets_every_bit() {
    let u64_max = Rational::from(u64::MAX);
    let c = client();
    let parsed = c
        .parse_dbc(&one_signal_dbc(unsigned_signal(
            "Big",
            64,
            Rational::integer(1),
            u64_max,
        )))
        .expect("parse_dbc");
    let frame = c
        .build_frame(
            &parsed.dbc.messages[0],
            eight_bytes(),
            &[SignalValue {
                name: "Big".to_owned(),
                value: u64_max,
            }],
        )
        .expect("build_frame");
    assert_eq!(frame, vec![0xFF; 8]);
}

/// vw_mlb's factor on 16 bits loads and reads its raw values exactly on both
/// extraction routes; the reduced numerators at 471, 4097, 65534 and 65535
/// pass 64 bits.
#[test]
fn a_17_place_factor_extracts_its_raw_values_exactly_on_both_routes() {
    let routes = BothRoutes::new(&one_signal_dbc(unsigned_signal(
        "Load",
        16,
        ratio(VW_MLB_NUMERATOR, VW_MLB_DENOMINATOR),
        ratio(VW_MLB_NUMERATOR * 0xFFFF, VW_MLB_DENOMINATOR),
    )));
    for raw in [0u16, 1, 255, 470, 471, 4097, 0xFFFE, 0xFFFF] {
        let mut payload = [0u8; 8];
        payload[..2].copy_from_slice(&raw.to_le_bytes());
        let want = ratio(VW_MLB_NUMERATOR * u128::from(raw), VW_MLB_DENOMINATOR);
        for (route, read) in routes.read(&payload) {
            assert_one_value(&format!("raw {raw}, {route}"), &read, "Load", want);
        }
    }
}

/// 2^128 as a signal maximum is refused with the saturated bound refusal: its
/// observed size and limit are both 2^128-1, read at 128 bits, and its message
/// names only the limit.
#[test]
fn a_number_past_the_bound_is_refused_naming_no_number() {
    let text = wide_dbc_text(
        "",
        &format!(" SG_ S : 0|8@1+ (1,0) [0|{TWO_TO_128_DIGITS}] \"\" ECU\n"),
    );
    let (message, refusal) = bound_refusal(client().parse_dbc_text(&text));
    assert_eq!(
        message,
        format!(
            "ParseDBCText: signal maximum: rational component magnitude exceeds limit \
             {U128_MAX_DIGITS}"
        )
    );
    assert_eq!(
        (refusal.observed, refusal.limit),
        (u128::MAX, u128::MAX),
        "{refusal:?}"
    );
}

/// 0.<the 65 digits of 5^92> is 5^27 / 2^65, within the bound, and the factor
/// reads back exactly, its denominator past 64 bits.
#[test]
fn a_fraction_of_65_significant_digits_that_fits_loads_exactly() {
    let digits = digits_of_five_to(92);
    assert_eq!(digits.len(), 65, "5^92 has 65 digits");
    let dbc = parse_wide_text(
        &client(),
        &wide_dbc_text(
            "",
            &format!(" SG_ S : 0|8@1+ (0.{digits},0) [0|1] \"\" ECU\n"),
        ),
    );
    let five_to_27: u128 = 7_450_580_596_923_828_125;
    assert_eq!(
        dbc.messages[0].signals[0].factor,
        ratio(five_to_27, 1 << 65)
    );
}

/// m4294967296 on a 40-bit multiplexor loads, and the client reads the
/// multiplex value 2^32 back.
#[test]
fn a_multiplex_value_past_32_bits_loads_and_reads_back() {
    let body = format!(
        " SG_ Mx M : 0|40@1+ (1,0) [0|{}] \"\" ECU\n SG_ A m4294967296 : 40|8@1+ (1,0) [0|255] \
         \"\" ECU\n",
        (1u64 << 40) - 1
    );
    let dbc = parse_wide_text(&client(), &wide_dbc_text("", &body));
    let selected = &dbc.messages[0].signals[1];
    assert_eq!(
        selected.presence,
        Presence::Multiplexed {
            multiplexor: "Mx".to_owned(),
            values: vec![1 << 32],
        },
        "signal {}",
        selected.name
    );
}

/// Tesla's "SNA" at a signed signal's most negative raw value, -32768, loads
/// as a value description keyed below zero.
#[test]
fn a_negative_value_description_key_loads() {
    let body = " SG_ Rpm : 0|16@1- (1,0) [-32768|32767] \"\" ECU\n\n\
                VAL_ 256 Rpm -32768 \"SNA\" 0 \"Stopped\" ;\n";
    let dbc = parse_wide_text(&client(), &wide_dbc_text("", body));
    let sna = ValueDescription {
        value: SignMagnitude {
            negative: true,
            magnitude: 32_768,
        },
        description: "SNA".to_owned(),
    };
    let descriptions = &dbc.messages[0].signals[0].value_descriptions;
    assert!(
        descriptions.contains(&sna),
        "value descriptions {descriptions:?}, want them to hold {sna:?}"
    );
}

/// A value table's key is signed too, and the client reads the table back.
#[test]
fn a_negative_value_table_key_loads_and_reads_back() {
    let tables = "VAL_TABLE_ Levels -1 \"Below\" 0 \"Zero\" ;\n\n";
    let body = " SG_ S : 0|8@1- (1,0) [-128|127] \"\" ECU\n";
    let dbc = parse_wide_text(&client(), &wide_dbc_text(tables, body));
    let entry = |negative, magnitude, description: &str| ValueDescription {
        value: SignMagnitude {
            negative,
            magnitude,
        },
        description: description.to_owned(),
    };
    assert_eq!(
        dbc.value_tables,
        vec![ValueTable {
            name: "Levels".to_owned(),
            entries: vec![entry(true, 1, "Below"), entry(false, 0, "Zero")],
        }]
    );
}

/// Holds that a value description reads the key 2^128-1 with the given sign
/// and the text.
fn assert_extreme_entry(entry: &ValueDescription, negative: bool, description: &str) {
    assert_eq!(
        *entry,
        ValueDescription {
            value: SignMagnitude {
                negative,
                magnitude: u128::MAX,
            },
            description: description.to_owned(),
        }
    );
}

/// Holds the extreme DBC's numbers as a reply reads them back: the multiplex
/// value 2^128-1, and the keys -(2^128-1) and 2^128-1 of the signal's value
/// descriptions and of the value table.
fn assert_extremes(source: &str, dbc: &Dbc) {
    assert_eq!(dbc.messages.len(), 1, "{source}");
    let signals = &dbc.messages[0].signals;
    assert_eq!(signals.len(), 3, "{source}");
    assert_eq!(
        signals[1].presence,
        Presence::Multiplexed {
            multiplexor: "Mx".to_owned(),
            values: vec![u128::MAX],
        },
        "{source}"
    );
    let descriptions = &signals[2].value_descriptions;
    assert_eq!(descriptions.len(), 2, "{source}: {descriptions:?}");
    assert_extreme_entry(&descriptions[0], true, "Lowest");
    assert_extreme_entry(&descriptions[1], false, "Highest");
    assert_eq!(dbc.value_tables.len(), 1, "{source}");
    assert_eq!(dbc.value_tables[0].name, "Extremes", "{source}");
    let entries = &dbc.value_tables[0].entries;
    assert_eq!(entries.len(), 2, "{source}: {entries:?}");
    assert_extreme_entry(&entries[0], true, "Below");
    assert_extreme_entry(&entries[1], false, "Above");
}

/// A 128-bit multiplexor selecting at 2^128-1, a 129-bit signed signal
/// describing -(2^128-1) and 2^128-1, and a value table keyed at both, read
/// from the load's reply and again from the formatted DBC.
#[test]
fn a_multiplex_value_and_value_description_keys_at_2_128_minus_1_load_and_read_back() {
    let max = U128_MAX_DIGITS;
    let tables = format!("VAL_TABLE_ Extremes -{max} \"Below\" {max} \"Above\" ;\n\n");
    let body = format!(
        " SG_ Mx M : 0|128@1+ (1,0) [0|{max}] \"\" ECU\n SG_ A m{max} : 128|8@1+ (1,0) [0|255] \
         \"\" ECU\n SG_ Key : 136|129@1- (1,0) [-{max}|{max}] \"\" ECU\n\nVAL_ 256 Key -{max} \
         \"Lowest\" {max} \"Highest\" ;\n"
    );
    let c = client();
    assert_extremes("load", &parse_wide_text(&c, &wide_dbc_text(&tables, &body)));
    assert_extremes("format_dbc", &c.format_dbc().expect("format_dbc"));
}

/// 2^64-1 microseconds, the largest time bound, is read from text and accepted
/// by the metric builders' check.
#[test]
fn a_time_bound_of_2_64_minus_1_microseconds_reaches_its_limit() {
    aletheia::start_runtime(1, None).expect("the kernel's runtime");
    let bound = TimeBound::parse(&u64::MAX.to_string()).expect("2^64-1 is a time bound");
    assert_eq!(bound, TimeBound(u64::MAX));
    let below = Predicate::less_than("S", 10).expect("S < 10");
    let eventually = Formula::eventually_within(bound, Formula::Atomic(below.clone()));
    assert!(
        eventually.is_ok(),
        "eventually_within(2^64-1): {eventually:?}"
    );
    let always = Formula::always_within(bound, Formula::Atomic(below));
    assert!(always.is_ok(), "always_within(2^64-1): {always:?}");
}

/// 2^64 microseconds is past every timestamp: refused with the time bound's
/// own limit, its observed size read at 128 bits.
#[test]
fn a_time_bound_past_the_timestamp_range_is_refused_with_its_observed_size_at_128_bits() {
    aletheia::start_runtime(1, None).expect("the kernel's runtime");
    let past = u128::from(u64::MAX) + 1;
    let (message, refusal) = bound_refusal(TimeBound::parse(&past.to_string()));
    assert_eq!(
        message,
        format!(
            "time bound: rational component magnitude {past} exceeds limit {}",
            u64::MAX
        )
    );
    assert_eq!(
        (refusal.observed, refusal.limit, refusal.field.as_deref()),
        (past, u128::from(u64::MAX), Some("time bound")),
        "{refusal:?}"
    );
}
