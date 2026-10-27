// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// Signal-geometry parse errors, the RTS cores mismatch, and event acks through
// the real libaletheia-ffi.so.

#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>

#include <aletheia/aletheia.hpp>
#include <aletheia/detail/checked.hpp>

#include <cstdint>
#include <expected>
#include <memory>
#include <optional>
#include <span>
#include <string>
#include <utility>
#include <vector>

#include "find_lib.hpp"
#include "integration_fixtures.hpp"
#include "required.hpp"

using aletheia::test::required;

using aletheia::test::find_lib;
using aletheia::test::make_integration_dbc;
using Catch::Matchers::StartsWith;

using namespace aletheia;

// ---------------------------------------------------------------------------
// Parse error codes from the signal-geometry entry gate
// ---------------------------------------------------------------------------
// The JSON parser refuses out-of-capacity signal geometry at parse time via
// the shared gate (DBC/Decidable/SignalGeometry.agda's geometryRefusal,
// applied to the SUBMITTED pre-conversion values against dlcBytes * 8):
//   • bitLength ≥ 1                     → SignalBitLengthZero
//   • startBit < frameBytes * 8         → SignalStartBitExceedsFrame
//   • bitLength ≤ frameBytes * 8        → SignalBitLengthExceedsFrame
//   • no wrap past the frame end        → SignalBigEndianOverflow (BE only)
// These tests verify the C++ binding surfaces each parse error code via
// AletheiaError::code() when feeding a malformed DBC through the real FFI.

// Minimal DBC helper that wraps a single signal of the given byte order
// inside a one-message DBC. Callers supply the signal's start_bit,
// bit_length, byte order, and the message DLC.
static auto make_single_signal_dbc(std::uint16_t start_bit, std::uint16_t bit_length,
                                   ByteOrder byte_order, std::uint8_t dlc_bytes) -> DbcDefinition {
    const DbcSignal sig{
        .name = SignalName{"Bad"},
        .start_bit = BitPosition{start_bit},
        .bit_length = BitLength{bit_length},
        .byte_order = byte_order,
        .is_signed = false,
        .factor = RationalFactor{Rational{1, 1}},
        .offset = RationalOffset{Rational{0, 1}},
        .minimum = RationalBound{Rational{0, 1}},
        .maximum = RationalBound{Rational{255, 1}},
        .unit = Unit{""},
        .presence = AlwaysPresent{},
    };
    auto const id = StandardId::create(0x100).value();
    // dlc_bytes is a PAYLOAD byte count; Dlc::create takes the DLC CODE, so a
    // CAN-FD size like 64 must go through the bytes→code mapping (they only
    // coincide for classic-CAN sizes up to code 8).
    auto const dlc = bytes_to_dlc(dlc_bytes).value();
    return DbcDefinition{
        .version = "1.0",
        .messages = {DbcMessage{
            .id = CanId{id},
            .name = MessageName{"Msg1"},
            .dlc = dlc,
            .sender = NodeName{"ECU"},
            .signals = {sig},
        }},
    };
}

// The big-endian case, which most of the geometry tests want.
static auto make_single_be_signal_dbc(std::uint16_t start_bit, std::uint16_t bit_length,
                                      std::uint8_t dlc_bytes) -> DbcDefinition {
    return make_single_signal_dbc(start_bit, bit_length, ByteOrder::BigEndian, dlc_bytes);
}

TEST_CASE("parse DBC: BigEndian signal with length=0 → parse_signal_bit_length_zero",
          "[integration][parse_error]") {
    auto const lib = find_lib();
    auto backend = required(make_ffi_backend(lib));
    auto client = required(AletheiaClient::create(std::move(backend)));

    // BE signal, length=0 → the shared geometry gate's positive-length
    // condition fails → SignalBitLengthZero.
    auto const dbc = make_single_be_signal_dbc(/*start_bit=*/7, /*bit_length=*/0, /*dlc_bytes=*/1);

    auto const result = client.parse_dbc(std::stop_token{}, dbc);
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().code() == ErrorCode::ParseSignalBitLengthZero);
    CHECK(result.error().kind() == ErrorKind::Protocol);
}

TEST_CASE("parse DBC: LittleEndian signal with length=0 → parse_signal_bit_length_zero",
          "[integration][parse_error]") {
    auto const lib = find_lib();
    auto backend = required(make_ffi_backend(lib));
    auto client = required(AletheiaClient::create(std::move(backend)));

    // LE signal, length=0 → the shared geometry gate's positive-length
    // condition fails → SignalBitLengthZero (identical for both byte orders).
    auto const dbc =
        make_single_signal_dbc(/*start_bit=*/0, /*bit_length=*/0, ByteOrder::LittleEndian,
                               /*dlc_bytes=*/1);

    auto const result = client.parse_dbc(std::stop_token{}, dbc);
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().code() == ErrorCode::ParseSignalBitLengthZero);
    CHECK(result.error().kind() == ErrorKind::Protocol);
}

TEST_CASE(
    "parse DBC: BigEndian signal wider than the frame → parse_signal_bit_length_exceeds_frame",
    "[integration][parse_error]") {
    auto const lib = find_lib();
    auto backend = required(make_ffi_backend(lib));
    auto client = required(AletheiaClient::create(std::move(backend)));

    // BE signal: start_bit=7 (MSB of byte 0), length=33, dlc=4 → 32 bits of
    // frame.  The entry gate refuses the SUBMITTED length against the frame
    // capacity (33 ≤ 32 fails), before any start-bit conversion.
    // Mirrors python/tests/test_dbc_validator_layout.py::test_big_endian_signal_exceeds_dlc.
    auto const dbc = make_single_be_signal_dbc(/*start_bit=*/7, /*bit_length=*/33, /*dlc_bytes=*/4);

    auto const result = client.parse_dbc(std::stop_token{}, dbc);
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().code() == ErrorCode::ParseSignalBitLengthExceedsFrame);
    CHECK(result.error().kind() == ErrorKind::Protocol);
}

TEST_CASE("parse DBC: BigEndian run past the frame end → parse_signal_big_endian_overflow",
          "[integration][parse_error]") {
    auto const lib = find_lib();
    auto backend = required(make_ffi_backend(lib));
    auto client = required(AletheiaClient::create(std::move(backend)));

    // BE signal: start_bit=0, length=2, dlc=1.  The Motorola MSB anchor is
    // the frame's LAST bit position (physicalBitPos(1, BE, 0) = 0), so a
    // descending run of two bits leaves the frame — the pre-conversion
    // no-wrap condition (bl − 1 ≤ physicalBitPos) fails and the gate
    // refuses (the former post-conversion check would have silently
    // relocated the run via the monus floor).
    auto const dbc = make_single_be_signal_dbc(/*start_bit=*/0, /*bit_length=*/2, /*dlc_bytes=*/1);

    auto const result = client.parse_dbc(std::stop_token{}, dbc);
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().code() == ErrorCode::ParseSignalBigEndianOverflow);
    CHECK(result.error().kind() == ErrorKind::Protocol);
}

TEST_CASE("parse DBC: out-of-frame start bit → parse_signal_start_bit_exceeds_frame",
          "[integration][parse_error]") {
    auto const lib = find_lib();
    auto backend = required(make_ffi_backend(lib));
    auto client = required(AletheiaClient::create(std::move(backend)));

    // LE signal whose start bit is the first position past the 1-byte frame.
    auto const dbc =
        make_single_signal_dbc(/*start_bit=*/8, /*bit_length=*/8, ByteOrder::LittleEndian,
                               /*dlc_bytes=*/1);

    auto const result = client.parse_dbc(std::stop_token{}, dbc);
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().code() == ErrorCode::ParseSignalStartBitExceedsFrame);
    CHECK(result.error().kind() == ErrorKind::Protocol);
}

TEST_CASE("parse DBC: text-loaded Motorola full-frame signal is accepted back by the JSON route",
          "[integration][parse_error]") {
    // Kernel closure under its own emission: the textbook Motorola layout
    // (MSB at bit 7, descending through the whole DLC-2 frame) loads on the
    // text route, and the SAME document is accepted back by parse_dbc.
    auto const lib = find_lib();
    auto backend = required(make_ffi_backend(lib));
    auto client = required(AletheiaClient::create(std::move(backend)));

    const std::string text = "VERSION \"\"\n\nNS_ :\n\nBS_:\n\nBU_: Engine\n\n"
                             "BO_ 100 Msg: 2 Engine\n"
                             " SG_ Sig : 7|16@0+ (1,0) [0|0] \"\" Engine\n";
    auto const loaded = client.parse_dbc_text(std::stop_token{}, text);
    REQUIRE(loaded.has_value());
    auto const& sig = loaded->dbc.messages.at(0).signals.at(0);
    CHECK(sig.start_bit.get() == 7);
    CHECK(sig.bit_length.get() == 16);

    auto const echoed = client.parse_dbc(std::stop_token{}, loaded->dbc);
    CHECK(echoed.has_value());
}

TEST_CASE("parse DBC: full-frame CAN-FD signal decodes back through format_dbc",
          "[integration][parse_error]") {
    // A signal spanning the whole 64-byte frame is kernel-legal (the entry
    // gate checks per-frame fit), so the binding's response decoder must
    // accept the echo rather than re-rejecting it with a stale classic-CAN
    // bit-length cap — the decode guard is only the type-level ceiling.
    auto const lib = find_lib();
    auto backend = required(make_ffi_backend(lib));
    auto client = required(AletheiaClient::create(std::move(backend)));

    auto const dbc =
        make_single_signal_dbc(/*start_bit=*/0, /*bit_length=*/512, ByteOrder::LittleEndian,
                               /*dlc_bytes=*/64);
    REQUIRE(client.parse_dbc(std::stop_token{}, dbc).has_value());

    auto const echoed = client.format_dbc(std::stop_token{});
    REQUIRE(echoed.has_value());
    auto const& sig = echoed->messages.at(0).signals.at(0);
    CHECK(sig.start_bit.get() == 0);
    CHECK(sig.bit_length.get() == 512);
}

TEST_CASE("validate DBC: LittleEndian signal with length=0 rejected at parse",
          "[integration][parse_error]") {
    // The shared geometry gate's positive-length condition fires for BOTH
    // byte orders, so LE length=0 surfaces as a parse error from
    // validate_dbc.  The validator's IssueCode::BitLengthZero arm remains
    // as defense-in-depth but is proven unreachable from the public parse
    // routes (Aletheia.DBC.Properties.GeometryGateDeadness).
    auto const lib = find_lib();
    auto backend = required(make_ffi_backend(lib));
    auto client = required(AletheiaClient::create(std::move(backend)));

    const DbcSignal sig{
        .name = SignalName{"ZeroLenLE"},
        .start_bit = BitPosition{0},
        .bit_length = BitLength{0},
        .byte_order = ByteOrder::LittleEndian,
        .is_signed = false,
        .factor = RationalFactor{Rational{1, 1}},
        .offset = RationalOffset{Rational{0, 1}},
        .minimum = RationalBound{Rational{0, 1}},
        .maximum = RationalBound{Rational{255, 1}},
        .unit = Unit{""},
        .presence = AlwaysPresent{},
    };
    const DbcDefinition dbc{
        .version = "1.0",
        .messages = {DbcMessage{
            .id = CanId{StandardId::create(0x100).value()},
            .name = MessageName{"Msg1"},
            .dlc = Dlc::create(8).value(),
            .sender = NodeName{"ECU"},
            .signals = {sig},
        }},
    };

    auto const validation = client.validate_dbc(std::stop_token{}, dbc);
    REQUIRE_FALSE(validation.has_value());
    CHECK(validation.error().code() == ErrorCode::ParseSignalBitLengthZero);
    // validate_dbc routes an error response through `parse_validation`, which
    // tags it Validation, where `parse_dbc` tags the same wire code Protocol.
    // The code is the same; the kind reflects the C++ entry point, not the
    // underlying failure.
    CHECK(validation.error().kind() == ErrorKind::Validation);
}

// ---------------------------------------------------------------------------
// RTS cores mismatch
// ---------------------------------------------------------------------------
// make_ffi_backend's rts_cores argument only takes effect on the first call
// in a process. A later call asking for a different count records the pair
// through rts_mismatch_info, which is what these tests read.

TEST_CASE("make_ffi_backend warns on mismatched rts_cores", "[integration][ffi_backend]") {
    auto const lib = find_lib();

    // Establish deterministic RTS state: first call initializes to 1 if the
    // RTS has not yet been touched this process, else a no-op if a prior
    // test already initialized with the default (1). Either way, the RTS
    // cores count is 1 after this block.
    {
        auto const backend = required(make_ffi_backend(lib));
        REQUIRE(backend != nullptr);
    }

    // Second call with rts_cores != 1 must populate the structured mismatch.
    // Two is within the CPUs of every machine the suite runs on.
    auto const backend = required(make_ffi_backend(lib, /*rts_cores=*/2));
    REQUIRE(backend != nullptr);
    auto const mismatch = backend->rts_mismatch_info();

    REQUIRE(mismatch.has_value());
    CHECK(mismatch->first == 1);
    CHECK(mismatch->second == 2);
}

TEST_CASE("make_ffi_backend is silent on matching rts_cores", "[integration][ffi_backend]") {
    auto const lib = find_lib();

    // Ensure the RTS is already initialized (1 core) from prior tests or
    // this test's first call.
    {
        auto const backend = required(make_ffi_backend(lib));
        REQUIRE(backend != nullptr);
    }

    // Second call with matching rts_cores (1) must NOT warn.
    auto const backend = required(make_ffi_backend(lib, /*rts_cores=*/1));
    REQUIRE(backend != nullptr);

    CHECK_FALSE(backend->rts_mismatch_info().has_value());
}

TEST_CASE("rts.cores_mismatch structured fields match Go/Python schema",
          "[integration][ffi_backend]") {
    auto const lib = find_lib();

    // First init fixes the core count to 1 (deterministic prior state).
    {
        auto const backend = required(make_ffi_backend(lib));
        REQUIRE(backend != nullptr);
    }

    auto const backend = required(make_ffi_backend(lib, /*rts_cores=*/4));
    REQUIRE(backend != nullptr);

    auto const info = backend->rts_mismatch_info();
    REQUIRE(info.has_value());
    // The first is what the RTS was already running with and the second what
    // this call asked for. Both must be populated, for parity with the
    // `active_cores` and `requested_cores` fields Go logs and Python's own
    // logging record.
    CHECK(info->first == 1);
    CHECK(info->second == 4);
}

TEST_CASE("make_ffi_backend rejects rts_cores < 1", "[integration][ffi_backend]") {
    auto const lib = find_lib();
    // A count below 1 is refused with kind Validation so callers can branch on
    // `kind()` like every other typed error; the text names the bound, the
    // CPUs the runtime counts, which is the machine's.
    for (auto const cores : {0, -1}) {
        auto const backend = make_ffi_backend(lib, cores);
        CHECK(detail::error_of(backend).kind() == ErrorKind::Validation);
        CHECK_THAT(detail::error_of(backend).text(),
                   StartsWith("core count " + std::to_string(cores) + " is outside 1 to "));
    }
}

// ---------------------------------------------------------------------------
// Event ack wire-contract tests.
//
// send_error and send_remote go through `parse_event_ack`, which is
// authoritative for the `{"status":"ack"}` wire the real FFI returns, as
// Aletheia.Protocol.StreamState states. MockBackend's default
// happens to return `"success"` — these tests exercise the real `"ack"`
// path end-to-end, catching regressions where parse_success and
// parse_event_ack drift or the Agda handler stops emitting `"ack"`.
// ---------------------------------------------------------------------------

TEST_CASE("send_error returns ack via real FFI", "[integration][event_ack]") {
    auto const lib = find_lib();
    auto backend = required(make_ffi_backend(lib));
    auto client = required(AletheiaClient::create(std::move(backend)));

    REQUIRE(client.parse_dbc(std::stop_token{}, make_integration_dbc()).has_value());
    REQUIRE(client.set_properties(std::stop_token{}, {}).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    // send_error carries only a timestamp; the real FFI must return
    // {"status":"ack"} and the Client must accept it.
    auto const r = client.send_error(std::stop_token{}, Timestamp{1'000});
    REQUIRE(r.has_value());

    auto const end = client.end_stream(std::stop_token{});
    REQUIRE(end.has_value());
}

TEST_CASE("send_remote returns ack via real FFI", "[integration][event_ack]") {
    auto const lib = find_lib();
    auto backend = required(make_ffi_backend(lib));
    auto client = required(AletheiaClient::create(std::move(backend)));

    REQUIRE(client.parse_dbc(std::stop_token{}, make_integration_dbc()).has_value());
    REQUIRE(client.set_properties(std::stop_token{}, {}).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    // send_remote carries a timestamp + CAN id; the real FFI must return
    // {"status":"ack"} and the Client must accept it.
    auto const id = CanId{StandardId::create(0x100).value()};
    auto const r = client.send_remote(std::stop_token{}, Timestamp{1'000}, id);
    REQUIRE(r.has_value());

    auto const end = client.end_stream(std::stop_token{});
    REQUIRE(end.has_value());
}
