// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// Integration tests with real libaletheia-ffi.so.
// Requires: cabal run shake -- build (produces build/libaletheia-ffi.so)
// Run with: ctest -R integration (or ./integration_tests)
#include <catch2/catch_test_macros.hpp>
#include <catch2/generators/catch_generators.hpp>
#include <catch2/matchers/catch_matchers.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>

#include <aletheia/aletheia.hpp>
#include <aletheia/detail/rational_renderer.hpp>

#include <algorithm>
#include <array>
#include <barrier>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <dlfcn.h>
#include <exception>
#include <expected>
#include <filesystem>
#include <functional>
#include <memory>
#include <optional>
#include <span>
#include <string>
#include <string_view>
#include <system_error>
#include <thread>
#include <utility>
#include <variant>
#include <vector>

#include "loaded_library.hpp"
#include "repo_root.hpp"
#include "temp_path.hpp"
#include <catch2/catch_message.hpp>

using aletheia::test::repo_root;

using namespace aletheia;
namespace fs = std::filesystem;

// ---------------------------------------------------------------------------
// Find the shared library
// ---------------------------------------------------------------------------

static auto find_lib() -> fs::path {
    // The environment first, for CI and custom builds, but only when it names
    // a file that is there: an empty or stale value must not shadow a library
    // that is, else a missing file becomes a construction failure rather than
    // the skip this function exists for.
    if (auto* env = std::getenv("ALETHEIA_LIB")) {
        if (const fs::path p{env}; !p.empty() && fs::exists(p))
            return p;
    }

    // Default: project build directory
    auto const project_root = repo_root();
    auto lib = project_root / "build" / "libaletheia-ffi.so";
    if (fs::exists(lib))
        return lib;

    // Dist directory
    auto dist = project_root / "dist" / "aletheia" / "lib" / "libaletheia-ffi.so";
    if (fs::exists(dist))
        return dist;

    SKIP("libaletheia-ffi.so not found — run 'cabal run shake -- build' first");
    return {};
}

// ---------------------------------------------------------------------------
// Test DBC for integration tests
// ---------------------------------------------------------------------------

static auto make_integration_dbc() -> DbcDefinition {
    auto speed_id = StandardId::create(0x100).value();
    auto const speed_dlc = Dlc::create(8).value();

    DbcSignal speed_sig{
        .name = SignalName{"Speed"},
        .start_bit = BitPosition{0},
        .bit_length = BitLength{16},
        .byte_order = ByteOrder::LittleEndian,
        .is_signed = false,
        .factor = RationalFactor{Rational{1, 10}},
        .offset = RationalOffset{Rational{0, 1}},
        .minimum = RationalBound{Rational{0, 1}},
        .maximum = RationalBound{Rational{65535, 100}},
        .unit = Unit{"km/h"},
        .presence = AlwaysPresent{},
    };

    DbcSignal rpm_sig{
        .name = SignalName{"RPM"},
        .start_bit = BitPosition{16},
        .bit_length = BitLength{16},
        .byte_order = ByteOrder::LittleEndian,
        .is_signed = false,
        .factor = RationalFactor{Rational{1, 1}},
        .offset = RationalOffset{Rational{0, 1}},
        .minimum = RationalBound{Rational{0, 1}},
        .maximum = RationalBound{Rational{65535, 1}},
        .unit = Unit{"rpm"},
        .presence = AlwaysPresent{},
    };

    return DbcDefinition{
        .version = "1.0",
        .messages = {DbcMessage{
            .id = CanId{speed_id},
            .name = MessageName{"VehicleSpeed"},
            .dlc = speed_dlc,
            .sender = NodeName{"ECU1"},
            .signals = {speed_sig, rpm_sig},
        }},
    };
}

// A DBC with a mux signal present for MULTIPLE selector values.  The JSON side
// admits it, but the .dbc text form cannot express it, so re-parsing the emitted
// text does not reproduce the input DBC — format_dbc_text refuses it.
static auto make_multi_value_mux_dbc() -> DbcDefinition {
    auto id = StandardId::create(0x123).value();
    auto const dlc = Dlc::create(8).value();

    DbcSignal selector{
        .name = SignalName{"Selector"},
        .start_bit = BitPosition{0},
        .bit_length = BitLength{8},
        .byte_order = ByteOrder::LittleEndian,
        .is_signed = false,
        .factor = RationalFactor{Rational{1, 1}},
        .offset = RationalOffset{Rational{0, 1}},
        .minimum = RationalBound{Rational{0, 1}},
        .maximum = RationalBound{Rational{255, 1}},
        .unit = Unit{""},
        .presence = AlwaysPresent{},
    };
    DbcSignal payload{
        .name = SignalName{"Payload"},
        .start_bit = BitPosition{8},
        .bit_length = BitLength{8},
        .byte_order = ByteOrder::LittleEndian,
        .is_signed = false,
        .factor = RationalFactor{Rational{1, 1}},
        .offset = RationalOffset{Rational{0, 1}},
        .minimum = RationalBound{Rational{0, 1}},
        .maximum = RationalBound{Rational{255, 1}},
        .unit = Unit{""},
        .presence = Multiplexed{.multiplexor = SignalName{"Selector"},
                                .multiplex_values = {MultiplexValue{1}, MultiplexValue{2}}},
    };
    return DbcDefinition{
        .version = "",
        .messages = {DbcMessage{
            .id = CanId{id},
            .name = MessageName{"MultiMux"},
            .dlc = dlc,
            .sender = NodeName{"ECU"},
            .signals = {selector, payload},
        }},
    };
}

// A DBC with slaves under TWO Always masters (the split-master shape).  Every
// error-class mux check passes — each named master exists and there is no
// cycle — but .dbc text keeps a single M marker, so re-parsing the emitted
// text would rebind every slave to one master; the JSON side admits the shape.
static auto make_split_master_mux_dbc() -> DbcDefinition {
    auto id = StandardId::create(0x124).value();
    auto const dlc = Dlc::create(8).value();

    auto const make_sig = [](std::string_view name, std::uint16_t start_bit,
                             SignalPresence presence) -> DbcSignal {
        return DbcSignal{
            .name = SignalName{std::string{name}},
            .start_bit = BitPosition{start_bit},
            .bit_length = BitLength{8},
            .byte_order = ByteOrder::LittleEndian,
            .is_signed = false,
            .factor = RationalFactor{Rational{1, 1}},
            .offset = RationalOffset{Rational{0, 1}},
            .minimum = RationalBound{Rational{0, 1}},
            .maximum = RationalBound{Rational{255, 1}},
            .unit = Unit{""},
            .presence = std::move(presence),
        };
    };
    return DbcDefinition{
        .version = "",
        .messages = {DbcMessage{
            .id = CanId{id},
            .name = MessageName{"SplitMaster"},
            .dlc = dlc,
            .sender = NodeName{"ECU"},
            .signals =
                {
                    make_sig("MuxA", 0, AlwaysPresent{}),
                    make_sig("MuxB", 8, AlwaysPresent{}),
                    make_sig("A", 16,
                             Multiplexed{.multiplexor = SignalName{"MuxA"},
                                         .multiplex_values = {MultiplexValue{0}}}),
                    make_sig("B", 24,
                             Multiplexed{.multiplexor = SignalName{"MuxB"},
                                         .multiplex_values = {MultiplexValue{0}}}),
                },
        }},
    };
}

// ---------------------------------------------------------------------------
// Integration tests
// ---------------------------------------------------------------------------

TEST_CASE("parse DBC via real FFI", "[integration]") {
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    auto const result = client.parse_dbc(std::stop_token{}, make_integration_dbc());
    CHECK(result.has_value());
}

TEST_CASE("Tier 1 DBC metadata round-trips through real FFI", "[integration][dbc][metadata]") {
    // Mirrors python/tests/test_dbc_metadata_tier1.py::test_full_roundtrip.
    // Proves the Agda core preserves signalGroups, environmentVars, and
    // valueTables across parse_dbc → format_dbc.
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    auto dbc = make_integration_dbc();
    dbc.signal_groups.push_back(
        DbcSignalGroup{.name = "Powertrain", .signals = {SignalName{"Speed"}, SignalName{"RPM"}}});
    dbc.environment_vars.push_back(DbcEnvironmentVar{
        .name = "AmbientTemp",
        .var_type = DbcVarType::Float,
        .initial = Rational{22, 1},
        .minimum = Rational{-40, 1},
        .maximum = Rational{85, 1},
    });
    dbc.value_tables.push_back(DbcValueTable{
        .name = "GearStates",
        .entries = {DbcValueEntry{.value = 0, .description = "Park"},
                    DbcValueEntry{.value = 1, .description = "Drive"},
                    DbcValueEntry{.value = 2, .description = "Reverse"}},
    });

    REQUIRE(client.parse_dbc(std::stop_token{}, dbc).has_value());
    auto round_tripped = client.format_dbc(std::stop_token{});
    REQUIRE(round_tripped.has_value());

    REQUIRE(round_tripped->signal_groups.size() == 1);
    CHECK(round_tripped->signal_groups[0].name == "Powertrain");
    CHECK(round_tripped->signal_groups[0].signals.size() == 2);

    REQUIRE(round_tripped->environment_vars.size() == 1);
    CHECK(round_tripped->environment_vars[0].name == "AmbientTemp");
    CHECK(round_tripped->environment_vars[0].var_type == DbcVarType::Float);
    CHECK(round_tripped->environment_vars[0].initial == Rational{22, 1});

    REQUIRE(round_tripped->value_tables.size() == 1);
    CHECK(round_tripped->value_tables[0].name == "GearStates");
    CHECK(round_tripped->value_tables[0].entries.size() == 3);
    CHECK(round_tripped->value_tables[0].entries[0].description == "Park");
    CHECK(round_tripped->value_tables[0].entries[2].description == "Reverse");
}

TEST_CASE("env var with non-terminating rational is rejected") {
    auto const lib = find_lib();
    if (lib.empty())
        return;
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    // Fraction 1/3 has no 2^a·5^b denominator form, so fromℚ? returns
    // nothing and the parser emits parse_non_terminating_rational: the
    // canonical "user built a Rational outside DBC's decimal grammar"
    // failure.
    auto dbc = make_integration_dbc();
    dbc.environment_vars.push_back(DbcEnvironmentVar{
        .name = "Repeating",
        .var_type = DbcVarType::Float,
        .initial = Rational{1, 3},
        .minimum = Rational{0, 1},
        .maximum = Rational{1, 1},
    });

    auto result = client.parse_dbc(std::stop_token{}, dbc);
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().code() == ErrorCode::ParseNonTerminatingRational);
}

TEST_CASE("signal with non-terminating rational factor is rejected") {
    // Parallel coverage for the SG_ fields: factor, offset, minimum and
    // maximum go through the same `fromℚ? ∘ lookupRational` path
    // as EV_, so a Rational{1,3} in any of those fields triggers
    // parse_non_terminating_rational.  This test pins the `factor` lane —
    // the remaining three lanes are exercised by the Python parametrised
    // test (`test_signal_non_terminating_rational_rejected`).
    auto const lib = find_lib();
    if (lib.empty())
        return;
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    auto dbc = make_integration_dbc();
    // Override the first signal's factor to a repeating rational.
    dbc.messages[0].signals[0].factor = RationalFactor{Rational{1, 3}};

    auto result = client.parse_dbc(std::stop_token{}, dbc);
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().code() == ErrorCode::ParseNonTerminatingRational);
}

TEST_CASE("extract signals via real FFI", "[integration]") {
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    auto const dbc = make_integration_dbc();
    REQUIRE(client.parse_dbc(std::stop_token{}, dbc).has_value());

    // Speed = 1000 raw * 0.1 factor = 100.0 km/h
    // RPM   = 3000 raw * 1.0 factor = 3000 rpm
    auto const id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value();
    FramePayload data{std::byte{0xE8}, std::byte{0x03}, // 1000 LE
                      std::byte{0xB8}, std::byte{0x0B}, // 3000 LE
                      std::byte{0},    std::byte{0},    std::byte{0}, std::byte{0}};

    auto result = client.extract_signals(std::stop_token{}, id, dlc, data);
    REQUIRE(result.has_value());
    CHECK(result->values.size() == 2);
    CHECK(result->get(SignalName{"Speed"}).get() == Rational{100, 1});
    CHECK(result->get(SignalName{"RPM"}).get() == Rational{3000, 1});
}

// Delegates every backend operation to a real FFI backend so parse_dbc (which
// populates the client's signal-name cache and thus arms the binary extraction
// path) works for real — except extract_signals_bin, which hands back a
// caller-supplied result.  Lets us drive parse_extraction_bin's validation
// paths through the public API with crafted wire buffers (truncation, size
// mismatch, offset-table violations, invalid UTF-8 — each must surface a
// Protocol error, not decode as a silent success), or force the JSON fallback
// by handing back an ErrorKind::BinaryUnsupported error.
namespace {
class FixedBinExtractBackend : public IBackend {
public:
    FixedBinExtractBackend(std::unique_ptr<IBackend> inner,
                           std::expected<std::vector<std::byte>, AletheiaError> buf)
        : inner_(std::move(inner))
        , buf_(std::move(buf)) {}

    // The handle the inner backend hands out closes through that backend, so
    // this decorator neither owns nor releases state and needs no close.
    auto init() -> BackendState override { return inner_->init(); }
    auto process(const BackendState& state, std::string_view input) -> std::string override {
        return inner_->process(state, input);
    }

    auto send_frame_binary(const BackendState& state, Timestamp ts, const CanId& id, Dlc dlc,
                           std::span<const std::byte> data, std::optional<bool> brs,
                           std::optional<bool> esi) -> std::string override {
        return inner_->send_frame_binary(state, ts, id, dlc, data, brs, esi);
    }
    auto send_error_binary(const BackendState& state, Timestamp ts) -> std::string override {
        return inner_->send_error_binary(state, ts);
    }
    auto send_remote_binary(const BackendState& state, Timestamp ts, const CanId& id)
        -> std::string override {
        return inner_->send_remote_binary(state, ts, id);
    }
    auto start_stream_binary(const BackendState& state) -> std::string override {
        return inner_->start_stream_binary(state);
    }
    auto end_stream_binary(const BackendState& state) -> std::string override {
        return inner_->end_stream_binary(state);
    }
    auto format_dbc_binary(const BackendState& state) -> std::string override {
        return inner_->format_dbc_binary(state);
    }
    auto extract_signals_binary(const BackendState& state, const CanId& id, Dlc dlc,
                                std::span<const std::byte> data) -> std::string override {
        return inner_->extract_signals_binary(state, id, dlc, data);
    }

    // The method under test: hand back the caller-supplied result verbatim.
    auto extract_signals_bin(const BackendState& /*state*/, const CanId& /*id*/, Dlc /*dlc*/,
                             std::span<const std::byte> /*data*/)
        -> std::expected<std::vector<std::byte>, AletheiaError> override {
        return buf_;
    }

protected:
    // Never called: the handle this decorator hands out belongs to the inner
    // backend and closes there.
    auto close(void* /*state*/) -> void override {}

private:
    std::unique_ptr<IBackend> inner_;
    std::expected<std::vector<std::byte>, AletheiaError> buf_;
};

// Little-endian builder for crafted extraction wire buffers (native byte
// order; the client refuses to compile on big-endian hosts). Layout under
// test: src/Aletheia/Main/Binary.agda, processExtractBin header comment.
struct WireBuf {
    std::vector<std::byte> bytes;

    void u8(std::uint8_t v) { bytes.push_back(std::byte{v}); }
    void u16(std::uint16_t v) {
        u8(static_cast<std::uint8_t>(v & 0xFFU));
        u8(static_cast<std::uint8_t>(std::uint32_t{v} >> 8U));
    }
    void u32(std::uint32_t v) {
        u16(static_cast<std::uint16_t>(v & 0xFFFFU));
        u16(static_cast<std::uint16_t>(v >> 16U));
    }
    void i64(std::int64_t v) {
        auto u = static_cast<std::uint64_t>(v);
        for (unsigned i = 0; i < 8; ++i)
            u8(static_cast<std::uint8_t>((u >> (8U * i)) & 0xFFU));
    }
    void str(std::string_view s) {
        for (const char c : s)
            u8(static_cast<std::uint8_t>(c));
    }
    void header(std::uint16_t nvals, std::uint16_t nerrs, std::uint16_t nabss,
                std::uint32_t reason_bytes) {
        u16(nvals);
        u16(nerrs);
        u16(nabss);
        u32(reason_bytes);
    }
};

// Runs extract_signals against a crafted binary extraction buffer through the
// public API (real .so for parse_dbc; the fixed buffer for the binary path).
} // namespace

static auto extract_with_crafted_buf(std::vector<std::byte> buf) -> Result<ExtractionResult> {
    auto backend = std::make_unique<FixedBinExtractBackend>(make_ffi_backend(find_lib()),
                                                            /*buf=*/std::move(buf));
    AletheiaClient client(std::move(backend));
    REQUIRE(client.parse_dbc(std::stop_token{}, make_integration_dbc()).has_value());

    auto const id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value();
    FramePayload data(8, std::byte{0});
    return client.extract_signals(std::stop_token{}, id, dlc, data);
}

static auto expect_protocol_error(std::vector<std::byte> buf) {
    auto result = extract_with_crafted_buf(std::move(buf));
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Protocol);
    return result.error();
}

TEST_CASE("binary extraction decodes values, wire reasons, and absent exactly", "[integration]") {
    // One value, two errors with distinct kernel-minted reasons — the first
    // contains multi-byte UTF-8, so the second slice's byte offset differs
    // from its character offset (proves the offsets are byte counts) — and
    // one absent signal.  The second error carries an unknown u8 code (42):
    // codes are transported, never rejected — the wire reason is
    // authoritative.
    const std::string_view reason_a = "value Δ out of bounds: 16383.75 not in [0, 8000]";
    const std::string_view reason_b = "signal 'X' not found in message";
    WireBuf w;
    w.header(/*nvals=*/1, /*nerrs=*/2, /*nabss=*/1,
             static_cast<std::uint32_t>(reason_a.size() + reason_b.size()));
    // Values: Speed (idx 0) = 250/2 = 125.
    w.u16(0);
    w.i64(250);
    w.i64(2);
    // Errors: RPM (idx 1, code 1 = OutOfBounds) + idx 7 (not in the message
    // → placeholder name) with unknown code 42.
    w.u16(1);
    w.u8(1);
    w.u16(7);
    w.u8(42);
    // Offsets (nerrs + 1 entries, cumulative byte counts into Reasons).
    w.u32(0);
    w.u32(static_cast<std::uint32_t>(reason_a.size()));
    w.u32(static_cast<std::uint32_t>(reason_a.size() + reason_b.size()));
    // Reasons blob, then Absent: idx 6 (placeholder name).
    w.str(reason_a);
    w.str(reason_b);
    w.u16(6);

    auto result = extract_with_crafted_buf(std::move(w.bytes));
    REQUIRE(result.has_value());
    REQUIRE(result->values.size() == 1);
    CHECK(result->values[0].name == SignalName{"Speed"});
    CHECK(result->values[0].value == PhysicalValue{Rational{125, 1}});
    REQUIRE(result->errors.size() == 2);
    CHECK(result->errors[0].name == SignalName{"RPM"});
    CHECK(result->errors[0].reason == reason_a);
    CHECK(result->errors[1].name == SignalName{"signal_7"});
    CHECK(result->errors[1].reason == reason_b);
    REQUIRE(result->absent.size() == 1);
    CHECK(result->absent[0] == SignalName{"signal_6"});
}

TEST_CASE("binary extraction with zero errors decodes the lone offset entry", "[integration]") {
    // With nErrors == 0 the offsets segment is still present: exactly one
    // u32 entry that must be 0 (== reasonBytes).
    WireBuf w;
    w.header(/*nvals=*/1, /*nerrs=*/0, /*nabss=*/0, /*reason_bytes=*/0);
    w.u16(1); // RPM
    w.i64(3000);
    w.i64(1);
    w.u32(0); // lone offsets entry

    auto result = extract_with_crafted_buf(std::move(w.bytes));
    REQUIRE(result.has_value());
    REQUIRE(result->values.size() == 1);
    CHECK(result->values[0].name == SignalName{"RPM"});
    CHECK(result->errors.empty());
    CHECK(result->absent.empty());
}

TEST_CASE("truncated binary extraction surfaces a Protocol error", "[integration]") {
    // A 9-byte buffer is one byte short of the mandatory 10-byte header
    // (3×u16 counts + u32 reasonBytes).
    auto const err = expect_protocol_error(std::vector<std::byte>(9, std::byte{0}));
    CHECK(std::string_view{err.message()}.contains("9 bytes, need >= 10"));
}

TEST_CASE("binary extraction with trailing bytes surfaces a Protocol error", "[integration]") {
    // An all-zero 10-byte header (0 values / 0 errors / 0 absent, 0 reason
    // bytes) plus the mandatory lone offsets entry is exactly expected_size
    // == 14; the 15th byte is trailing data the layout does not account for,
    // so the decoder must reject it rather than ignore the tail.
    auto const err = expect_protocol_error(std::vector<std::byte>(15, std::byte{0}));
    CHECK(std::string_view{err.message()}.contains("15 bytes, expected exactly 14"));
}

TEST_CASE("binary extraction with a bare header is a size mismatch, not a truncation",
          "[integration]") {
    // Ten bytes is the whole header, so the truncation check passes and the
    // exact-size check is the one that refuses: the lone offsets entry is
    // missing.
    auto const err = expect_protocol_error(std::vector<std::byte>(10, std::byte{0}));
    CHECK(std::string_view{err.message()}.contains("10 bytes, expected exactly 14"));
}

TEST_CASE("binary extraction rejects a nonzero first reason offset", "[integration]") {
    WireBuf w;
    w.header(/*nvals=*/0, /*nerrs=*/1, /*nabss=*/0, /*reason_bytes=*/4);
    w.u16(0);
    w.u8(1);
    w.u32(1); // off[0] must be 0
    w.u32(4);
    w.str("abcd");
    auto const err = expect_protocol_error(std::move(w.bytes));
    CHECK(std::string_view{err.message()}.contains("first offset is 1"));
}

TEST_CASE("binary extraction rejects non-monotone reason offsets", "[integration]") {
    WireBuf w;
    w.header(/*nvals=*/0, /*nerrs=*/2, /*nabss=*/0, /*reason_bytes=*/4);
    w.u16(0);
    w.u8(1);
    w.u16(1);
    w.u8(1);
    w.u32(0);
    w.u32(5); // decreases into off[2] = 4
    w.u32(4);
    w.str("abcd");
    auto const err = expect_protocol_error(std::move(w.bytes));
    CHECK(std::string_view{err.message()}.contains("offset 2 decreases"));
}

TEST_CASE("binary extraction rejects a final offset that mismatches reasonBytes", "[integration]") {
    WireBuf w;
    w.header(/*nvals=*/0, /*nerrs=*/1, /*nabss=*/0, /*reason_bytes=*/4);
    w.u16(0);
    w.u8(1);
    w.u32(0);
    w.u32(3); // off[nErrors] must equal reasonBytes (4)
    w.str("abcd");
    auto const err = expect_protocol_error(std::move(w.bytes));
    CHECK(std::string_view{err.message()}.contains("last offset 3 != reason bytes 4"));
}

TEST_CASE("binary extraction decodes adjacent reasons, an empty one included", "[integration]") {
    // Three errors whose offsets are 0, 2, 2, 6: the second reason is empty,
    // which equal consecutive offsets denote, and the others are the bytes
    // between their offsets and nothing else.
    WireBuf w;
    w.header(/*nvals=*/0, /*nerrs=*/3, /*nabss=*/0, /*reason_bytes=*/6);
    for (std::uint16_t i = 0; i < 3; ++i) {
        w.u16(i);
        w.u8(1);
    }
    w.u32(0);
    w.u32(2);
    w.u32(2);
    w.u32(6);
    w.str("abcdef");
    auto result = extract_with_crafted_buf(std::move(w.bytes));
    REQUIRE(result.has_value());
    REQUIRE(result->errors.size() == 3);
    CHECK(result->errors[0].reason == "ab");
    CHECK(result->errors[1].reason.empty());
    CHECK(result->errors[2].reason == "cdef");
}

TEST_CASE("binary extraction names a wire index one past the message's signals by placeholder",
          "[integration]") {
    // The integration DBC has two signals, so index 2 is the first one the
    // message does not have.
    WireBuf w;
    w.header(/*nvals=*/1, /*nerrs=*/0, /*nabss=*/1, /*reason_bytes=*/0);
    w.u16(2);
    w.i64(1);
    w.i64(1);
    w.u32(0);
    w.u16(2);
    auto result = extract_with_crafted_buf(std::move(w.bytes));
    REQUIRE(result.has_value());
    REQUIRE(result->values.size() == 1);
    CHECK(result->values[0].name == SignalName{"signal_2"});
    REQUIRE(result->absent.size() == 1);
    CHECK(result->absent[0] == SignalName{"signal_2"});
}

TEST_CASE("binary extraction rejects invalid UTF-8 in a reason slice", "[integration]") {
    WireBuf w;
    w.header(/*nvals=*/0, /*nerrs=*/1, /*nabss=*/0, /*reason_bytes=*/2);
    w.u16(0);
    w.u8(1);
    w.u32(0);
    w.u32(2);
    w.u8(0xFF); // 0xFF is never valid in UTF-8
    w.u8(0xFE);
    auto const err = expect_protocol_error(std::move(w.bytes));
    CHECK(std::string_view{err.message()}.contains("UTF-8"));
}

// One error whose reason is exactly `reason`, so the validator sees the
// sequence at the start and the end of a slice at once.
static auto single_reason_buf(std::span<const std::uint8_t> reason) -> std::vector<std::byte> {
    WireBuf w;
    w.header(/*nvals=*/0, /*nerrs=*/1, /*nabss=*/0, static_cast<std::uint32_t>(reason.size()));
    w.u16(0);
    w.u8(1);
    w.u32(0);
    w.u32(static_cast<std::uint32_t>(reason.size()));
    for (auto const b : reason)
        w.u8(b);
    return std::move(w.bytes);
}

TEST_CASE("binary extraction accepts every well-formed UTF-8 boundary in a reason slice",
          "[integration]") {
    // The smallest and largest code point of each encoding length, the two
    // code points that bracket the surrogate range, and a multi-byte sequence
    // that ends the slice: each is exactly on a boundary the validator draws.
    auto const reason = GENERATE(
        std::vector<std::uint8_t>{0x7F},                    // U+007F, the last one-byte point
        std::vector<std::uint8_t>{0xC2, 0x80},              // U+0080, the first two-byte point
        std::vector<std::uint8_t>{0xE0, 0xA0, 0x80},        // U+0800, the first three-byte point
        std::vector<std::uint8_t>{0xED, 0x9F, 0xBF},        // U+D7FF, just below the surrogates
        std::vector<std::uint8_t>{0xEE, 0x80, 0x80},        // U+E000, just above the surrogates
        std::vector<std::uint8_t>{0xF0, 0x90, 0x80, 0x80},  // U+10000, the first four-byte point
        std::vector<std::uint8_t>{0xF4, 0x8F, 0xBF, 0xBF}); // U+10FFFF, the last code point
    auto result = extract_with_crafted_buf(single_reason_buf(reason));
    REQUIRE(result.has_value());
    REQUIRE(result->errors.size() == 1);
    CHECK(std::ranges::equal(result->errors[0].reason, reason, [](char c, std::uint8_t b) {
        return static_cast<std::uint8_t>(c) == b;
    }));
}

TEST_CASE("binary extraction rejects every malformed UTF-8 shape in a reason slice",
          "[integration]") {
    auto const reason = GENERATE(
        std::vector<std::uint8_t>{0x80},                   // a lone continuation byte
        std::vector<std::uint8_t>{'a', 0x80},              // after an ASCII byte, too
        std::vector<std::uint8_t>{0xC0, 0x80},             // overlong two-byte encoding of U+0000
        std::vector<std::uint8_t>{0xE0, 0x80, 0x80},       // overlong three-byte encoding
        std::vector<std::uint8_t>{0xF0, 0x80, 0x80, 0x80}, // overlong four-byte encoding
        std::vector<std::uint8_t>{0xED, 0xA0, 0x80},       // U+D800, the first surrogate
        std::vector<std::uint8_t>{0xED, 0xBF, 0xBF},       // U+DFFF, the last surrogate
        std::vector<std::uint8_t>{0xF4, 0x90, 0x80, 0x80}, // U+110000, past the last code point
        std::vector<std::uint8_t>{0xC3},                   // a two-byte lead that ends the slice
        std::vector<std::uint8_t>{'a', 0xE2, 0x82},        // a three-byte sequence cut short
        std::vector<std::uint8_t>{0xE2, 0x41, 0xAC});      // a non-continuation second byte
    auto const err = expect_protocol_error(single_reason_buf(reason));
    CHECK(std::string_view{err.message()}.contains("UTF-8"));
}

TEST_CASE("binary extraction rejects a non-positive denominator", "[integration]") {
    // den == 0 hits the zero-denominator guard; den < 0 is rejected by the
    // Rational newtype (denominators are strictly positive on the wire).
    auto const den = GENERATE(std::int64_t{0}, std::int64_t{-3});
    WireBuf w;
    w.header(/*nvals=*/1, /*nerrs=*/0, /*nabss=*/0, /*reason_bytes=*/0);
    w.u16(0);
    w.i64(250);
    w.i64(den);
    w.u32(0); // lone offsets entry
    expect_protocol_error(std::move(w.bytes));
}

TEST_CASE("binary and JSON extraction agree byte-for-byte on error reasons",
          "[integration][parity]") {
    // Same out-of-bounds frame through both wire paths: the binary path
    // (kernel-minted reason carried on the wire) and the JSON path (reason
    // formatted by the same kernel resultToString) must surface identical
    // reason strings — reason parity is machine-checked kernel-side
    // (Aletheia.CAN.Batch.Properties.ReasonParity); this pins the C++
    // binding's end of it.
    auto const lib = find_lib();
    auto const id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value();
    // Speed raw 0xFFFF → 6553.5 km/h, above the DBC maximum of 655.35.
    FramePayload data{std::byte{0xFF}, std::byte{0xFF}, std::byte{0}, std::byte{0},
                      std::byte{0},    std::byte{0},    std::byte{0}, std::byte{0}};

    AletheiaClient bin_client(make_ffi_backend(lib));
    REQUIRE(bin_client.parse_dbc(std::stop_token{}, make_integration_dbc()).has_value());
    auto bin = bin_client.extract_signals(std::stop_token{}, id, dlc, data);
    REQUIRE(bin.has_value());

    // Force the JSON fallback by handing the fixed-result backend a
    // BinaryUnsupported error (the same sentinel MockBackend uses).
    auto json_backend = std::make_unique<FixedBinExtractBackend>(
        make_ffi_backend(lib),
        std::unexpected(AletheiaError{ErrorKind::BinaryUnsupported,
                                      "binary path not supported by this backend"}));
    AletheiaClient json_client(std::move(json_backend));
    REQUIRE(json_client.parse_dbc(std::stop_token{}, make_integration_dbc()).has_value());
    auto json = json_client.extract_signals(std::stop_token{}, id, dlc, data);
    REQUIRE(json.has_value());

    REQUIRE(bin->errors.size() == 1);
    REQUIRE(json->errors.size() == 1);
    CHECK(bin->errors[0].name == SignalName{"Speed"});
    CHECK(bin->errors[0].name == json->errors[0].name);
    CHECK(bin->errors[0].reason == json->errors[0].reason);
    // The reason is the kernel's detailed out-of-bounds string, not a
    // generic per-code message.
    CHECK(std::string_view{bin->errors[0].reason}.contains("not in ["));
}

TEST_CASE("the FFI backend is refused a library path that is empty", "[integration]") {
    REQUIRE_THROWS_WITH(make_ffi_backend(std::filesystem::path{}),
                        Catch::Matchers::ContainsSubstring("library path is empty"));
}

// The backend's endpoints are the public IBackend interface, so a call the
// client would never make, a 65-byte payload or a message the DBC lacks, is
// a legitimate call on that interface and not a fabricated state.
TEST_CASE("the FFI backend's own guards answer on its interface", "[integration]") {
    auto backend = make_ffi_backend(find_lib());
    auto const state = backend->init();
    // No DBC is loaded, so every binary endpoint the kernel reaches refuses.
    auto const id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(15).value();
    const std::vector<std::byte> data65(65, std::byte{0});
    const std::vector<std::byte> data64(64, std::byte{0});
    const std::vector<std::uint32_t> indices{0};
    const std::vector<std::int64_t> ones{1};
    auto const injection = SignalInjection::create(indices, ones, ones).value();
    constexpr std::string_view too_long = "data length exceeds 64 bytes (CAN-FD max)";

    SECTION("a payload past the CAN-FD maximum is refused before the kernel sees it") {
        CHECK_THROWS_WITH(backend->send_frame_binary(state, Timestamp{0}, id, dlc, data65,
                                                     std::nullopt, std::nullopt),
                          Catch::Matchers::ContainsSubstring(std::string{too_long}));
        CHECK_THROWS_WITH(backend->extract_signals_binary(state, id, dlc, data65),
                          Catch::Matchers::ContainsSubstring(std::string{too_long}));
        auto const updated = backend->update_frame_bin(state, id, dlc, data65, injection, 64);
        REQUIRE_FALSE(updated.has_value());
        CHECK(std::string_view{updated.error().message()}.contains(too_long));
        auto const extracted = backend->extract_signals_bin(state, id, dlc, data65);
        REQUIRE_FALSE(extracted.has_value());
        CHECK(std::string_view{extracted.error().message()}.contains(too_long));
    }
    SECTION("a command past the JSON cap is refused before the kernel sees it") {
        const std::string past_cap(max_json_bytes + 1, 'x');
        auto const answer = backend->process(state, past_cap);
        CHECK(answer.contains(R"("code":"input_bound_exceeded")"));
        CHECK(answer.contains(R"("observed":67108865)"));
    }
    SECTION("a kernel refusal on a binary endpoint is surfaced, not swallowed") {
        auto const built = backend->build_frame_bin(state, id, dlc, injection, 64);
        REQUIRE_FALSE(built.has_value());
        CHECK(built.error().kind() == ErrorKind::Protocol);
        auto const updated = backend->update_frame_bin(state, id, dlc, data64, injection, 64);
        REQUIRE_FALSE(updated.has_value());
        CHECK(updated.error().kind() == ErrorKind::Protocol);
        auto const extracted = backend->extract_signals_bin(state, id, dlc, data64);
        REQUIRE_FALSE(extracted.has_value());
        CHECK(extracted.error().kind() == ErrorKind::Protocol);
    }
}

// The wire carries the DLC as one byte and the kernel sizes the frame it
// builds from it, so a code past 15 is refused at the entry, before any
// signal is placed. The typed API cannot send one, so the test reaches the
// entry the way the backend does, through the library's own symbol.
TEST_CASE("the kernel refuses a DLC code past 15 on the binary build entry", "[integration]") {
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    auto const state = backend->init();
    const aletheia::test::LoadedLibrary handle{dlopen(lib.c_str(), RTLD_NOW | RTLD_NOLOAD)};
    REQUIRE(handle != nullptr);
    using BuildFn = std::int8_t (*)(void*, std::uint32_t, std::uint8_t, std::uint8_t, std::uint32_t,
                                    const std::uint32_t*, const std::int64_t*, const std::int64_t*,
                                    std::uint8_t*, char**);
    using FreeFn = void (*)(char*);
    // dlsym returns void*; POSIX guarantees the round trip through void*
    // preserves function pointers wherever dlopen exists.
    // NOLINTNEXTLINE(cppcoreguidelines-pro-type-reinterpret-cast)
    auto const build = reinterpret_cast<BuildFn>(dlsym(handle.get(), "aletheia_build_frame_bin"));
    // NOLINTNEXTLINE(cppcoreguidelines-pro-type-reinterpret-cast)
    auto const free_str = reinterpret_cast<FreeFn>(dlsym(handle.get(), "aletheia_free_str"));
    REQUIRE(build != nullptr);
    REQUIRE(free_str != nullptr);

    std::array<std::uint8_t, 64> out{};
    char* raw_error = nullptr;
    auto const status =
        build(state.get(), 0x100, 0, 42, 0, nullptr, nullptr, nullptr, out.data(), &raw_error);
    // The kernel allocated the message; it is released by the kernel's own
    // free, from a destructor rather than from a line this test must reach.
    auto const release = [free_str](char* message) { free_str(message); };
    const std::unique_ptr<char, decltype(release)> error{raw_error, release};
    CHECK(status == 1);
    REQUIRE(error != nullptr);
    CHECK(std::string_view{error.get()}.contains("DLC 42 exceeds maximum (15)"));
}

namespace {
// Hides two of the library search's three routes, the environment and the
// working directory, and restores both when the test ends.
class HiddenSearchRoutes {
public:
    HiddenSearchRoutes() : cwd_{fs::current_path()} {
        if (const char* cur = std::getenv("ALETHEIA_LIB"))
            saved_ = cur;
        ::unsetenv("ALETHEIA_LIB");
        // Two levels down, so no relative candidate the search tries from
        // here can land on a build directory a developer keeps under /tmp.
        auto const nowhere = aletheia::test::scratch_dir() / "search" / "nowhere";
        fs::create_directories(nowhere);
        fs::current_path(nowhere);
    }
    ~HiddenSearchRoutes() {
        std::error_code ec;
        fs::current_path(cwd_, ec);
        if (saved_)
            ::setenv("ALETHEIA_LIB", saved_->c_str(), /*overwrite=*/1);
    }
    HiddenSearchRoutes(const HiddenSearchRoutes&) = delete;
    HiddenSearchRoutes(HiddenSearchRoutes&&) = delete;
    auto operator=(const HiddenSearchRoutes&) -> HiddenSearchRoutes& = delete;
    auto operator=(HiddenSearchRoutes&&) -> HiddenSearchRoutes& = delete;

private:
    fs::path cwd_;
    std::optional<std::string> saved_;
};
} // namespace

// The caller's DLC sizes the frame and the DBC places the bits: a message
// whose signals reach past a frame that small has nowhere to put them, and
// the bit writer would drop what does not fit without a word. The kernel
// names the first such signal instead.
TEST_CASE("a frame built at a DLC the message outgrows is refused", "[integration]") {
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));
    REQUIRE(client.parse_dbc(std::stop_token{}, make_integration_dbc()).has_value());

    auto const id = CanId{StandardId::create(0x100).value()};
    const std::vector<SignalValue> speed{
        {.name = SignalName{"Speed"}, .value = PhysicalValue{Rational{100, 1}}}};

    // Speed occupies the first sixteen bits, so one byte cannot hold it.
    auto const refused = client.build_frame(std::stop_token{}, id, Dlc::create(1).value(), speed);
    REQUIRE_FALSE(refused.has_value());
    CHECK_THAT(std::string{refused.error().message()},
               Catch::Matchers::ContainsSubstring("signal 'Speed' does not fit a frame of size 1"));

    // Four bytes hold both signals of the message, and the frame is that long.
    auto const built = client.build_frame(std::stop_token{}, id, Dlc::create(4).value(), speed);
    REQUIRE(built.has_value());
    CHECK(built->size() == 4);
}

// Every binding prints an observed value through the kernel's own rational
// formatter, so a terminating fraction reads as a decimal and a repeating one
// keeps its two parts. The client reaches it while it enriches a violation;
// this reads it directly, which is the only test in this binary that renders
// through a library the search had to find.
TEST_CASE("the kernel renders a rational exactly", "[integration]") {
    auto const backend = make_ffi_backend(find_lib()); // brings the runtime up
    CHECK(detail::format_rational_ffi(1, 2) == "0.5");
    CHECK(detail::format_rational_ffi(85, 2) == "42.5");
    CHECK(detail::format_rational_ffi(1, 3) == "1/3");
    CHECK(detail::format_rational_ffi(3, 1) == "3");
}

// The renderer consults the path the first backend registered when the
// environment names none and the working directory holds no candidate, which
// keeps a renderer in a process that moved elsewhere on the backend's library.
TEST_CASE("the library the first backend loaded is found from anywhere", "[integration]") {
    auto const lib = find_lib();
    auto const backend = make_ffi_backend(lib);
    const HiddenSearchRoutes hidden;
    auto const found = find_ffi_library();
    REQUIRE_FALSE(found.empty());
    CHECK(fs::equivalent(found, lib));
}

TEST_CASE("update then extract round-trip via real FFI", "[integration]") {
    auto backend = make_ffi_backend(find_lib());
    AletheiaClient client(std::move(backend));
    REQUIRE(client.parse_dbc(std::stop_token{}, make_integration_dbc()).has_value());

    auto const id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value();
    const std::vector<SignalValue> both{
        {.name = SignalName{"Speed"}, .value = PhysicalValue{Rational{100, 1}}},
        {.name = SignalName{"RPM"}, .value = PhysicalValue{Rational{3000, 1}}},
    };
    auto const built = client.build_frame(std::stop_token{}, id, dlc, both);
    REQUIRE(built.has_value());

    // Only RPM is written; Speed must come back as built, since the update
    // crosses the wire with the payload, its length, the DLC and the count
    // of values, and a wrong one of those loses a signal or refuses the frame.
    const std::vector<SignalValue> rpm_only{
        {.name = SignalName{"RPM"}, .value = PhysicalValue{Rational{1234, 1}}}};
    auto const updated = client.update_frame(std::stop_token{}, id, dlc, *built, rpm_only);
    REQUIRE(updated.has_value());
    auto const extracted = client.extract_signals(std::stop_token{}, id, dlc, *updated);
    REQUIRE(extracted.has_value());
    CHECK(extracted->get(SignalName{"Speed"}).get() == Rational{100, 1});
    CHECK(extracted->get(SignalName{"RPM"}).get() == Rational{1234, 1});
}

TEST_CASE("build frame via real FFI", "[integration]") {
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(std::stop_token{}, make_integration_dbc()).has_value());

    auto const id = CanId{StandardId::create(0x100).value()};
    std::vector<SignalValue> signals{
        {.name = SignalName{"Speed"}, .value = PhysicalValue{Rational{100, 1}}}, // raw = 1000
        {.name = SignalName{"RPM"}, .value = PhysicalValue{Rational{3000, 1}}},  // raw = 3000
    };

    auto result = client.build_frame(std::stop_token{}, id, Dlc::create(8).value(), signals);
    REQUIRE(result.has_value());
    // Speed: 1000 = 0x03E8 LE → [0xE8, 0x03]
    CHECK((*result)[0] == std::byte{0xE8});
    CHECK((*result)[1] == std::byte{0x03});
    // RPM: 3000 = 0x0BB8 LE → [0xB8, 0x0B]
    CHECK((*result)[2] == std::byte{0xB8});
    CHECK((*result)[3] == std::byte{0x0B});
}

TEST_CASE("build then extract round-trip on an extended CAN ID via real FFI", "[integration]") {
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    // The same message under a 29-bit identifier: the extended bit crosses the
    // wire on every binary call, and the kernel keys its message table on it.
    auto const id = CanId{ExtendedId::create(0x18FEF100).value()};
    auto dbc = make_integration_dbc();
    dbc.messages[0].id = id;
    REQUIRE(client.parse_dbc(std::stop_token{}, dbc).has_value());

    std::vector<SignalValue> signals{
        {.name = SignalName{"Speed"}, .value = PhysicalValue{Rational{85, 2}}},
        {.name = SignalName{"RPM"}, .value = PhysicalValue{Rational{1500, 1}}},
    };
    auto built = client.build_frame(std::stop_token{}, id, Dlc::create(8).value(), signals);
    REQUIRE(built.has_value());

    auto extracted = client.extract_signals(std::stop_token{}, id, Dlc::create(8).value(), *built);
    REQUIRE(extracted.has_value());
    CHECK(extracted->get(SignalName{"Speed"}).get() == Rational{85, 2});
    CHECK(extracted->get(SignalName{"RPM"}).get() == Rational{1500, 1});
}

TEST_CASE("build frame for a CAN ID with no DBC message errors distinctly", "[integration]") {
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(std::stop_token{}, make_integration_dbc()).has_value());

    // 0x200 has no message in the DBC (only 0x100 does). The error must name the
    // missing message ("no DBC message for CAN ID"), distinct from the per-signal
    // "signal not found", matching Go (resolveSignalIndices) and Python.
    auto const id = CanId{StandardId::create(0x200).value()};
    std::vector<SignalValue> signals{
        {.name = SignalName{"Speed"}, .value = PhysicalValue{Rational{100, 1}}},
    };
    auto result = client.build_frame(std::stop_token{}, id, Dlc::create(8).value(), signals);
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Validation);
    CHECK(std::string_view{result.error().message()}.contains("no DBC message for CAN ID"));
}

TEST_CASE("build then extract round-trip via real FFI", "[integration]") {
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(std::stop_token{}, make_integration_dbc()).has_value());

    auto const id = CanId{StandardId::create(0x100).value()};
    std::vector<SignalValue> signals{
        {.name = SignalName{"Speed"}, .value = PhysicalValue{Rational{85, 2}}},
        {.name = SignalName{"RPM"}, .value = PhysicalValue{Rational{1500, 1}}},
    };

    auto built = client.build_frame(std::stop_token{}, id, Dlc::create(8).value(), signals);
    REQUIRE(built.has_value());

    auto extracted = client.extract_signals(std::stop_token{}, id, Dlc::create(8).value(), *built);
    REQUIRE(extracted.has_value());
    // Round-trip: values should match (within quantization)
    CHECK(extracted->get(SignalName{"Speed"}).get() == Rational{85, 2});
    CHECK(extracted->get(SignalName{"RPM"}).get() == Rational{1500, 1});
}

TEST_CASE("FFI payload guards accept exactly 64 bytes (CAN-FD boundary)",
          "[integration][boundary]") {
    // Every FfiBackend method that takes a payload calls one guard,
    // `payload_bound_error`, which refuses anything longer than the CAN-FD
    // maximum, behind the client's own `data.size() == dlc_to_bytes(dlc)`
    // pre-check.  That makes the guard defense in depth: a longer payload is
    // intercepted by the client first, so the guard is only ever reached at
    // exactly the maximum, where it must pass.  Mutating its comparison flips
    // that boundary call from accept to reject, and these calls, one per
    // method that reaches the guard, are what kill those mutants: the
    // streaming send, the binary extraction for an identifier the DBC knows,
    // the JSON extraction for one it does not, and the frame update.  Two of
    // them report by throwing and two by returning an unexpected value; the
    // helper below covers both.  Per the no-defense-removal rule the guard
    // stays: this is the complement that proves it accepts the legal
    // maximum.
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));
    REQUIRE(client.parse_dbc(std::stop_token{}, make_integration_dbc()).has_value());

    const std::vector<std::byte> data64(64, std::byte{0});
    auto const dlc = Dlc::create(15).value();                      // CAN-FD DLC 15 = 64 bytes
    auto const known = CanId{StandardId::create(0x100).value()};   // in the DBC → binary path
    auto const unknown = CanId{StandardId::create(0x7FF).value()}; // not in DBC → JSON fallback
    const std::vector<SignalValue> signals{
        {.name = SignalName{"Speed"}, .value = PhysicalValue{Rational{100, 1}}}};

    auto const mentions_exceeds = [](std::string_view msg) {
        return msg.contains("data length exceeds");
    };
    // A 64-byte call must NOT produce the >64 guard error, whether the guard
    // reports by throwing or by returning std::unexpected.  The original
    // passes the guard (any non-exceeds outcome is fine); both mutants reject
    // with "data length exceeds …", failing the check.
    auto const accepts_64 = [&](auto&& call) {
        try {
            auto result = call();
            if (!result.has_value())
                CHECK_FALSE(mentions_exceeds(result.error().message()));
        } catch (const AletheiaException& e) {
            CHECK_FALSE(mentions_exceeds(e.what()));
        }
    };

    REQUIRE(client.start_stream(std::stop_token{}).has_value());
    accepts_64([&] {
        return client.send_frame(std::stop_token{}, Timestamp{1'000'000}, known, dlc, data64);
    });
    accepts_64([&] { return client.extract_signals(std::stop_token{}, known, dlc, data64); });
    accepts_64([&] { return client.extract_signals(std::stop_token{}, unknown, dlc, data64); });
    accepts_64([&] { return client.update_frame(std::stop_token{}, known, dlc, data64, signals); });
}

TEST_CASE("streaming LTL check via real FFI — property holds", "[integration]") {
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(std::stop_token{}, make_integration_dbc()).has_value());

    // Property: always(Speed < 200)
    auto formula = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{200, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));

    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto const id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value();

    // Speed 100, 120 and 150 km/h at the DBC's factor of one tenth, all
    // under the threshold.
    for (std::uint16_t raw : {std::uint16_t{1000}, std::uint16_t{1200}, std::uint16_t{1500}}) {
        FramePayload data{static_cast<std::byte>(raw & 0xFFU),
                          static_cast<std::byte>((std::uint32_t{raw} >> 8U) & 0xFFU),
                          std::byte{0},
                          std::byte{0},
                          std::byte{0},
                          std::byte{0},
                          std::byte{0},
                          std::byte{0}};
        auto result = client.send_frame(std::stop_token{}, Timestamp{1'000'000}, id, dlc, data);
        REQUIRE(result.has_value());
        CHECK(std::holds_alternative<Ack>(*result));
    }

    auto end = client.end_stream(std::stop_token{});
    REQUIRE(end.has_value());
    REQUIRE(end->results.size() == 1);
    CHECK(end->results[0].verdict == Verdict::Holds);
}

TEST_CASE("streaming LTL check via real FFI — property violated", "[integration]") {
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(std::stop_token{}, make_integration_dbc()).has_value());

    // Property: always(Speed < 120) — will be violated by Speed=150
    auto formula = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{120, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));

    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto const id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value();
    bool got_violation = false;

    // Speed 100, 110 and 150 km/h at the DBC's factor of one tenth; the last
    // one breaks the threshold.
    for (std::uint16_t raw : {std::uint16_t{1000}, std::uint16_t{1100}, std::uint16_t{1500}}) {
        FramePayload data{static_cast<std::byte>(raw & 0xFFU),
                          static_cast<std::byte>((std::uint32_t{raw} >> 8U) & 0xFFU),
                          std::byte{0},
                          std::byte{0},
                          std::byte{0},
                          std::byte{0},
                          std::byte{0},
                          std::byte{0}};
        auto result = client.send_frame(std::stop_token{}, Timestamp{1'000'000}, id, dlc, data);
        REQUIRE(result.has_value());
        if (std::holds_alternative<PropertyBatch>(*result))
            got_violation = true;
    }

    auto end = client.end_stream(std::stop_token{});
    REQUIRE(end.has_value());

    // Either got a mid-stream violation or end-of-stream violation
    const bool eos_violation = !end->results.empty() && end->results[0].verdict == Verdict::Fails;
    CHECK((got_violation || eos_violation));
}

TEST_CASE("non-monotonic timestamp rejected by Agda via real FFI", "[integration][monotonic]") {
    // Backward timestamps would make metric LTL operators silently produce
    // wrong verdicts (∸ clamps to 0 on negative differences). Agda's
    // handleDataFrame refuses them — this is the single source of truth
    // across all bindings, proven in
    // Aletheia.Protocol.FrameProcessor.Properties.Monotonic (PROPERTY 28).
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(std::stop_token{}, make_integration_dbc()).has_value());

    auto formula = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{500, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));

    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto const id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value();
    FramePayload payload{std::byte{10}, std::byte{0}, std::byte{0}, std::byte{0},
                         std::byte{0},  std::byte{0}, std::byte{0}, std::byte{0}};

    // First frame at t=5000 µs — accepted.
    auto ok = client.send_frame(std::stop_token{}, Timestamp{5000}, id, dlc, payload);
    REQUIRE(ok.has_value());
    CHECK(std::holds_alternative<Ack>(*ok));

    // Regressing to t=4999 µs — rejected by Agda.
    auto err = client.send_frame(std::stop_token{}, Timestamp{4999}, id, dlc, payload);
    REQUIRE_FALSE(err.has_value());
    CHECK(err.error().code() == ErrorCode::HandlerNonMonotonicTimestamp);

    // Same-timestamp frames (≥, not >) are accepted.
    auto eq = client.send_frame(std::stop_token{}, Timestamp{5000}, id, dlc, payload);
    REQUIRE(eq.has_value());
    CHECK(std::holds_alternative<Ack>(*eq));

    // Anchor unchanged after rejection — next ≥ 5000 still accepted.
    auto fwd = client.send_frame(std::stop_token{}, Timestamp{6000}, id, dlc, payload);
    REQUIRE(fwd.has_value());
    CHECK(std::holds_alternative<Ack>(*fwd));

    auto const end = client.end_stream(std::stop_token{});
    REQUIRE(end.has_value());
}

TEST_CASE("validate DBC via real FFI", "[integration]") {
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    auto result = client.validate_dbc(std::stop_token{}, make_integration_dbc());
    REQUIRE(result.has_value());
    // Our test DBC is well-formed — no errors expected
    CHECK_FALSE(result->has_errors);
}

TEST_CASE("VAL_ value descriptions round-trip via real FFI",
          "[integration][dbc][value_descriptions]") {
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    constexpr std::string_view text = R"(VERSION ""

NS_ :

BS_:

BU_: ECU

BO_ 300 Transmission: 8 ECU
 SG_ EngineState : 8|2@1+ (1,0) [0|3] "" Vector__XXX

VAL_ 300 EngineState 0 "Off" 1 "Cranking" 2 "Running" 3 "Stall" ;
)";

    auto parsed = client.parse_dbc_text(std::stop_token{}, text);
    REQUIRE(parsed.has_value());
    REQUIRE(parsed->dbc.messages.size() == 1);
    REQUIRE(parsed->dbc.messages[0].signals.size() == 1);
    auto const& sig = parsed->dbc.messages[0].signals[0];
    REQUIRE(sig.value_descriptions.size() == 4);
    CHECK(sig.value_descriptions[0].value == 0);
    CHECK(sig.value_descriptions[0].description == "Off");
    CHECK(sig.value_descriptions[1].value == 1);
    CHECK(sig.value_descriptions[1].description == "Cranking");
    CHECK(sig.value_descriptions[2].value == 2);
    CHECK(sig.value_descriptions[2].description == "Running");
    CHECK(sig.value_descriptions[3].value == 3);
    CHECK(sig.value_descriptions[3].description == "Stall");

    auto formatted = client.format_dbc_text(std::stop_token{}, parsed->dbc);
    REQUIRE(formatted.has_value());
    constexpr std::string_view want_line =
        R"(VAL_ 300 EngineState 0 "Off" 1 "Cranking" 2 "Running" 3 "Stall" ;)";
    CHECK(formatted->text.contains(want_line));
    // format_dbc_text is always strict: this DBC round-trips, so it yields a
    // DbcText carrying the (advisory, here empty) wfTextIssues diagnostics.
    CHECK(formatted->issues.empty());
}

TEST_CASE("format_dbc_text refuses a multi-value mux via real FFI",
          "[integration][dbc][format][roundtrip]") {
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    // A multi-value mux selector does not round-trip through .dbc text, so the
    // always-strict formatter refuses it with a typed round-trip error rather
    // than emitting lossy text.
    auto result = client.format_dbc_text(std::stop_token{}, make_multi_value_mux_dbc());
    REQUIRE_FALSE(result.has_value());
    auto const& err = result.error();
    CHECK(err.kind() == ErrorKind::TextRoundtrip);
    CHECK(err.code() == ErrorCode::HandlerTextRoundtripFailed);
    REQUIRE(err.issues().has_value());

    // Led by the error-severity text_roundtrip_divergence issue the handler
    // prepends, plus the multi_value_mux_selector diagnostic.
    bool has_divergence = false;
    bool has_mux = false;
    for (auto const& issue : *err.issues()) {
        if (issue.code == IssueCode::TextRoundtripDivergence)
            has_divergence = true;
        if (issue.code == IssueCode::MultiValueMuxSelector)
            has_mux = true;
    }
    CHECK(has_divergence);
    CHECK(has_mux);
}

TEST_CASE("CHECK 23 unknown_value_description_target warning via real FFI",
          "[integration][dbc][value_descriptions][validator]") {
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    constexpr std::string_view text = R"(VERSION ""

NS_ :

BS_:

BU_: ECU

BO_ 256 Engine: 8 ECU
 SG_ Rpm : 0|16@1+ (1,0) [0|8000] "rpm" Vector__XXX

VAL_ 999 GhostSignal 0 "Off" 1 "On" ;
)";

    auto parsed = client.parse_dbc_text(std::stop_token{}, text);
    REQUIRE(parsed.has_value());
    const bool hit = std::ranges::any_of(parsed->warnings, [](const ValidationIssue& issue) {
        return issue.code == IssueCode::UnknownValueDescriptionTarget;
    });
    CHECK(hit);
}

static auto has_warning(const std::vector<ValidationIssue>& issues, IssueCode code) -> bool {
    return std::ranges::any_of(issues, [code](const ValidationIssue& issue) {
        return issue.code == code && issue.severity == IssueSeverity::Warning;
    });
}

TEST_CASE("CHECK 24 multi_value_mux_selector warning via real FFI",
          "[integration][dbc][validator][mux]") {
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    // validate_dbc mirrors the round-trip diagnostic warning-class: the shape
    // loads and streams fine, so has_errors stays false.
    auto result = client.validate_dbc(std::stop_token{}, make_multi_value_mux_dbc());
    REQUIRE(result.has_value());
    CHECK_FALSE(result->has_errors);
    CHECK(has_warning(result->issues, IssueCode::MultiValueMuxSelector));

    // The load route surfaces the same warning without blocking.
    auto parsed = client.parse_dbc(std::stop_token{}, make_multi_value_mux_dbc());
    REQUIRE(parsed.has_value());
    CHECK(has_warning(parsed->warnings, IssueCode::MultiValueMuxSelector));
}

TEST_CASE("CHECK 25 mux_master_incoherent warning via real FFI",
          "[integration][dbc][validator][mux]") {
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    // The split-master shape passes every error-class mux check, so only the
    // warning-class mirror names it.
    auto result = client.validate_dbc(std::stop_token{}, make_split_master_mux_dbc());
    REQUIRE(result.has_value());
    CHECK_FALSE(result->has_errors);
    CHECK(has_warning(result->issues, IssueCode::MuxMasterIncoherent));

    // The load route surfaces the same warning without blocking.
    auto parsed = client.parse_dbc(std::stop_token{}, make_split_master_mux_dbc());
    REQUIRE(parsed.has_value());
    CHECK(has_warning(parsed->warnings, IssueCode::MuxMasterIncoherent));
}

TEST_CASE("rejected DBC text parse carries typed validation issues via real FFI",
          "[integration][dbc][validation]") {
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    // minimal.dbc's EngineStatus message with EngineTemp renamed to
    // EngineSpeed — a duplicate signal name, an error-severity issue, so the
    // kernel rejects the parse with handler_validation_failed carrying the
    // structured issues alongside the legacy message text.
    constexpr std::string_view text = R"(VERSION "1.0"

NS_ :

BS_:

BU_: Engine Gateway

BO_ 256 EngineStatus: 8 Engine
 SG_ EngineSpeed : 0|16@1+ (0.25,0) [0|8000] "rpm" Gateway
 SG_ EngineSpeed : 16|8@1+ (1,-40) [-40|215] "degC" Gateway
)";

    auto parsed = client.parse_dbc_text(std::stop_token{}, text);
    REQUIRE_FALSE(parsed.has_value());
    CHECK(parsed.error().code() == ErrorCode::HandlerValidationFailed);
    CHECK(std::string{parsed.error().message()}.contains("duplicate signal name"));
    REQUIRE(parsed.error().issues().has_value());
    const bool hit =
        std::ranges::any_of(*parsed.error().issues(), [](const ValidationIssue& issue) {
            return issue.severity == IssueSeverity::Error &&
                   issue.code == IssueCode::DuplicateSignalName;
        });
    CHECK(hit);
}

// ---------------------------------------------------------------------------
// Concurrent client isolation test
// ---------------------------------------------------------------------------
// Two threads operate on independent AletheiaClient instances, synchronized
// via std::barrier so that operations interleave deterministically:
//
//   Thread A (lenient)                Thread B (strict)
//   ────────────────                  ────────────────
//   parse_dbc(dbc)                    parse_dbc(dbc)
//   ── barrier ──                     ── barrier ──
//   set_properties(Speed < 200)       set_properties(Speed < 100)
//   ── barrier ──                     ── barrier ──
//   start_stream()                    start_stream()
//   ── barrier ──                     ── barrier ──
//   send_frame(Speed = 150)           send_frame(Speed = 150)
//   ── barrier ──                     ── barrier ──
//   end_stream() → Holds              end_stream() → Fails
//
// Same DBC, same frame data, different properties → different verdicts.
// This proves each client owns independent state.

namespace {
// One participant of the isolation test: its own client over the real
// library, stepped through the workflow in lockstep with its peer.
struct ThreadResult {
    bool ok = false;
    Verdict verdict = Verdict::Fails;
    std::string error;
};
} // namespace

static void run_concurrent_client(const fs::path& lib, std::barrier<>& sync,
                                  PhysicalValue threshold, ThreadResult& out) {
    try {
        auto backend = make_ffi_backend(lib);
        AletheiaClient client(std::move(backend));

        // Step 1: parse DBC
        auto const dbc = make_integration_dbc();
        auto const parse_result = client.parse_dbc(std::stop_token{}, dbc);
        if (!parse_result.has_value()) {
            out.error = "parse_dbc failed";
            sync.arrive_and_drop();
            return;
        }
        sync.arrive_and_wait();

        // Step 2: set properties, each thread with a different threshold
        auto formula = ltl::always(ltl::atomic(ltl::less_than(SignalName{"Speed"}, threshold)));
        std::vector<LtlFormula> props;
        props.push_back(std::move(formula));
        if (!client.set_properties(std::stop_token{}, props).has_value()) {
            out.error = "set_properties failed";
            sync.arrive_and_drop();
            return;
        }
        sync.arrive_and_wait();

        // Step 3: start stream
        if (!client.start_stream(std::stop_token{}).has_value()) {
            out.error = "start_stream failed";
            sync.arrive_and_drop();
            return;
        }
        sync.arrive_and_wait();

        // Step 4: send frame with Speed = 150
        auto const id = CanId{StandardId::create(0x100).value()};
        auto const dlc = Dlc::create(8).value();
        const std::uint16_t raw = 1500; // Speed 150 km/h at factor one tenth
        FramePayload data{static_cast<std::byte>(raw & 0xFFU),
                          static_cast<std::byte>((std::uint32_t{raw} >> 8U) & 0xFFU),
                          std::byte{0},
                          std::byte{0},
                          std::byte{0},
                          std::byte{0},
                          std::byte{0},
                          std::byte{0}};
        auto send_result =
            client.send_frame(std::stop_token{}, Timestamp{1'000'000}, id, dlc, data);
        if (!send_result.has_value()) {
            out.error = "send_frame failed";
            sync.arrive_and_drop();
            return;
        }
        sync.arrive_and_wait();

        // Step 5: end stream and capture verdict
        auto end = client.end_stream(std::stop_token{});
        if (!end.has_value() || end->results.empty()) {
            out.error = "end_stream failed or empty results";
            return;
        }

        // Check both mid-stream and EOS for the verdict
        const bool mid_violation = std::holds_alternative<PropertyBatch>(*send_result);
        out.verdict = (mid_violation || end->results[0].verdict == Verdict::Fails) ? Verdict::Fails
                                                                                   : Verdict::Holds;
        out.ok = true;
    } catch (const std::exception& e) {
        out.error = e.what();
    }
}

TEST_CASE("concurrent clients have independent state via real FFI", "[integration][concurrent]") {
    auto const lib = find_lib();

    // Barrier with 2 participants — blocks until both threads arrive.
    std::barrier sync(2);

    ThreadResult result_lenient; // threshold = 200: Speed 150 < 200 → Holds
    ThreadResult result_strict;  // threshold = 100: Speed 150 >= 100 → Fails

    std::thread thread_a(run_concurrent_client, std::cref(lib), std::ref(sync),
                         PhysicalValue{Rational{200, 1}}, std::ref(result_lenient));
    std::thread thread_b(run_concurrent_client, std::cref(lib), std::ref(sync),
                         PhysicalValue{Rational{100, 1}}, std::ref(result_strict));

    thread_a.join();
    thread_b.join();

    INFO("Thread A error: " << result_lenient.error);
    INFO("Thread B error: " << result_strict.error);
    REQUIRE(result_lenient.ok);
    REQUIRE(result_strict.ok);

    // Same data, different properties → different verdicts proves isolation
    CHECK(result_lenient.verdict == Verdict::Holds);
    CHECK(result_strict.verdict == Verdict::Fails);
}

// ---------------------------------------------------------------------------
// Nested multiplexing
// ---------------------------------------------------------------------------
//
// Three signals on message 0x300:
//   Mode    : always present (8 bits @ 0)
//   SubMode : present when Mode == 3 (8 bits @ 8)
//   Detail  : present when SubMode == 7 (16 bits @ 16)
//
// Detail is reachable only when Mode == 3 AND SubMode == 7. The Aletheia core
// walks the multiplexor chain bottom-up — both ancestors must validate before
// the leaf is extracted. This DBC mirrors the Python and Go nested-mux tests.

static auto make_nested_mux_dbc() -> DbcDefinition {
    auto sid = StandardId::create(0x300).value();
    auto const dlc = Dlc::create(8).value();

    auto const unit_factor = RationalFactor{Rational{1, 1}};
    auto const zero_offset = RationalOffset{Rational{0, 1}};
    auto const zero_min = RationalBound{Rational{0, 1}};
    auto const byte_max = RationalBound{Rational{255, 1}};
    auto const u16_max = RationalBound{Rational{65535, 1}};

    DbcSignal mode_sig{
        .name = SignalName{"Mode"},
        .start_bit = BitPosition{0},
        .bit_length = BitLength{8},
        .byte_order = ByteOrder::LittleEndian,
        .is_signed = false,
        .factor = unit_factor,
        .offset = zero_offset,
        .minimum = zero_min,
        .maximum = byte_max,
        .unit = Unit{""},
        .presence = AlwaysPresent{},
    };

    DbcSignal submode_sig{
        .name = SignalName{"SubMode"},
        .start_bit = BitPosition{8},
        .bit_length = BitLength{8},
        .byte_order = ByteOrder::LittleEndian,
        .is_signed = false,
        .factor = unit_factor,
        .offset = zero_offset,
        .minimum = zero_min,
        .maximum = byte_max,
        .unit = Unit{""},
        .presence =
            Multiplexed{.multiplexor = SignalName{"Mode"}, .multiplex_values = {MultiplexValue{3}}},
    };

    DbcSignal detail_sig{
        .name = SignalName{"Detail"},
        .start_bit = BitPosition{16},
        .bit_length = BitLength{16},
        .byte_order = ByteOrder::LittleEndian,
        .is_signed = false,
        .factor = unit_factor,
        .offset = zero_offset,
        .minimum = zero_min,
        .maximum = u16_max,
        .unit = Unit{""},
        .presence = Multiplexed{.multiplexor = SignalName{"SubMode"},
                                .multiplex_values = {MultiplexValue{7}}},
    };

    return DbcDefinition{
        .version = "1.0",
        .messages = {DbcMessage{
            .id = CanId{sid},
            .name = MessageName{"NestedMuxMessage"},
            .dlc = dlc,
            .sender = NodeName{"ECU"},
            .signals = {mode_sig, submode_sig, detail_sig},
        }},
    };
}

static auto contains_signal(const std::vector<SignalName>& names, std::string_view want) -> bool {
    return std::ranges::any_of(names, [&](auto const& n) { return n.get() == want; });
}

TEST_CASE("nested mux DBC validates without errors via real FFI", "[integration][nested_mux]") {
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    // No error-class issue blocks the nested-mux shape; the validator's
    // warning-class round-trip mirror does flag it (a nested multiplexor
    // chain is outside the .dbc text round-trip envelope — format_dbc_text
    // refuses the identical shape with the same code).
    auto result = client.validate_dbc(std::stop_token{}, make_nested_mux_dbc());
    REQUIRE(result.has_value());
    CHECK_FALSE(result->has_errors);
    CHECK(has_warning(result->issues, IssueCode::MuxMasterIncoherent));
}

TEST_CASE("nested mux full chain match extracts leaf via real FFI", "[integration][nested_mux]") {
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(std::stop_token{}, make_nested_mux_dbc()).has_value());

    // Mode=3, SubMode=7, Detail=0xABCD (43981)
    auto const id = CanId{StandardId::create(0x300).value()};
    auto const dlc = Dlc::create(8).value();
    FramePayload data{std::byte{0x03}, std::byte{0x07}, std::byte{0xCD}, std::byte{0xAB},
                      std::byte{0},    std::byte{0},    std::byte{0},    std::byte{0}};

    auto result = client.extract_signals(std::stop_token{}, id, dlc, data);
    REQUIRE(result.has_value());
    CHECK(result->values.size() == 3);
    CHECK(result->absent.empty());
    CHECK(result->get(SignalName{"Mode"}).get() == Rational{3, 1});
    CHECK(result->get(SignalName{"SubMode"}).get() == Rational{7, 1});
    CHECK(result->get(SignalName{"Detail"}).get() == Rational{43981, 1});
}

TEST_CASE("nested mux inner mismatch marks leaf absent via real FFI", "[integration][nested_mux]") {
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(std::stop_token{}, make_nested_mux_dbc()).has_value());

    // Mode=3 (matches), SubMode=5 (≠7) — Detail should be reported absent.
    auto const id = CanId{StandardId::create(0x300).value()};
    auto const dlc = Dlc::create(8).value();
    FramePayload data{std::byte{0x03}, std::byte{0x05}, std::byte{0xCD}, std::byte{0xAB},
                      std::byte{0},    std::byte{0},    std::byte{0},    std::byte{0}};

    auto result = client.extract_signals(std::stop_token{}, id, dlc, data);
    REQUIRE(result.has_value());
    CHECK(result->values.size() == 2); // Mode and SubMode extracted
    CHECK(result->absent.size() == 1);
    CHECK(contains_signal(result->absent, "Detail"));
    CHECK(result->get(SignalName{"Mode"}).get() == Rational{3, 1});
    CHECK(result->get(SignalName{"SubMode"}).get() == Rational{5, 1});
}

TEST_CASE("nested mux outer mismatch marks inner and leaf absent via real FFI",
          "[integration][nested_mux]") {
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(std::stop_token{}, make_nested_mux_dbc()).has_value());

    // Mode=2 (≠3) — both SubMode and Detail should be reported absent.
    auto const id = CanId{StandardId::create(0x300).value()};
    auto const dlc = Dlc::create(8).value();
    FramePayload data{std::byte{0x02}, std::byte{0x07}, std::byte{0xCD}, std::byte{0xAB},
                      std::byte{0},    std::byte{0},    std::byte{0},    std::byte{0}};

    auto result = client.extract_signals(std::stop_token{}, id, dlc, data);
    REQUIRE(result.has_value());
    CHECK(result->values.size() == 1); // only Mode extracted
    CHECK(result->absent.size() == 2);
    CHECK(contains_signal(result->absent, "SubMode"));
    CHECK(contains_signal(result->absent, "Detail"));
    CHECK(result->get(SignalName{"Mode"}).get() == Rational{2, 1});
}

TEST_CASE("mux cycle rejected by validator via real FFI", "[integration][nested_mux]") {
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    // Two signals A and B that mutually multiplex on each other → cycle.
    auto sid = StandardId::create(0x301).value();
    auto const dlc = Dlc::create(8).value();

    auto const unit_factor = RationalFactor{Rational{1, 1}};
    auto const zero_offset = RationalOffset{Rational{0, 1}};
    auto const zero_min = RationalBound{Rational{0, 1}};
    auto const byte_max = RationalBound{Rational{255, 1}};

    DbcSignal sig_a{
        .name = SignalName{"A"},
        .start_bit = BitPosition{0},
        .bit_length = BitLength{8},
        .byte_order = ByteOrder::LittleEndian,
        .is_signed = false,
        .factor = unit_factor,
        .offset = zero_offset,
        .minimum = zero_min,
        .maximum = byte_max,
        .unit = Unit{""},
        .presence =
            Multiplexed{.multiplexor = SignalName{"B"}, .multiplex_values = {MultiplexValue{1}}},
    };

    DbcSignal sig_b{
        .name = SignalName{"B"},
        .start_bit = BitPosition{8},
        .bit_length = BitLength{8},
        .byte_order = ByteOrder::LittleEndian,
        .is_signed = false,
        .factor = unit_factor,
        .offset = zero_offset,
        .minimum = zero_min,
        .maximum = byte_max,
        .unit = Unit{""},
        .presence =
            Multiplexed{.multiplexor = SignalName{"A"}, .multiplex_values = {MultiplexValue{1}}},
    };

    const DbcDefinition cycle_dbc{
        .version = "1.0",
        .messages = {DbcMessage{
            .id = CanId{sid},
            .name = MessageName{"CycleMsg"},
            .dlc = dlc,
            .sender = NodeName{"ECU"},
            .signals = {sig_a, sig_b},
        }},
    };

    auto result = client.validate_dbc(std::stop_token{}, cycle_dbc);
    REQUIRE(result.has_value());
    REQUIRE(result->has_errors);
    const bool found_cycle = std::ranges::any_of(result->issues, [](auto const& issue) {
        return issue.code == IssueCode::MultiplexorCycle;
    });
    CHECK(found_cycle);
}

// ---------------------------------------------------------------------------
// End-of-stream three-valued Kleene finalization
// ---------------------------------------------------------------------------
//
// These tests mirror python/tests/test_eos_finalization.py::TestMissingSignalFinalization
// to give C++ client-level coverage of the Unresolved (Unsure) verdict. The
// Agda coalgebra finalizes an Atomic whose signal was never observed to
// FinalVerdict.Unsure; this propagates through And/Or via the Kleene truth
// tables (Unsure ∧ Holds = Unsure, Unsure ∨ Fails = Unsure) and reaches the
// binding as Verdict::Unresolved.
//
// make_two_message_dbc() gives two messages: Msg256 carries Speed, Msg512
// carries Rpm. The LTL property references Speed; sending only Msg512 frames
// leaves the Speed atomic unresolved.

static auto make_two_message_dbc() -> DbcDefinition {
    auto speed_id = StandardId::create(0x100).value();
    auto rpm_id = StandardId::create(0x200).value();
    auto const dlc = Dlc::create(8).value();

    DbcSignal speed_sig{
        .name = SignalName{"Speed"},
        .start_bit = BitPosition{0},
        .bit_length = BitLength{16},
        .byte_order = ByteOrder::LittleEndian,
        .is_signed = false,
        .factor = RationalFactor{Rational{1, 1}},
        .offset = RationalOffset{Rational{0, 1}},
        .minimum = RationalBound{Rational{0, 1}},
        .maximum = RationalBound{Rational{65535, 1}},
        .unit = Unit{"kph"},
        .presence = AlwaysPresent{},
    };

    DbcSignal rpm_sig{
        .name = SignalName{"Rpm"},
        .start_bit = BitPosition{0},
        .bit_length = BitLength{16},
        .byte_order = ByteOrder::LittleEndian,
        .is_signed = false,
        .factor = RationalFactor{Rational{1, 1}},
        .offset = RationalOffset{Rational{0, 1}},
        .minimum = RationalBound{Rational{0, 1}},
        .maximum = RationalBound{Rational{65535, 1}},
        .unit = Unit{"rpm"},
        .presence = AlwaysPresent{},
    };

    return DbcDefinition{
        .version = "1.0",
        .messages =
            {
                DbcMessage{
                    .id = CanId{speed_id},
                    .name = MessageName{"Msg256"},
                    .dlc = dlc,
                    .sender = NodeName{"ECU"},
                    .signals = {speed_sig},
                },
                DbcMessage{
                    .id = CanId{rpm_id},
                    .name = MessageName{"Msg512"},
                    .dlc = dlc,
                    .sender = NodeName{"ECU"},
                    .signals = {rpm_sig},
                },
            },
    };
}

static auto bytes_of(std::uint16_t raw) -> FramePayload {
    return FramePayload{static_cast<std::byte>(raw & 0xFFU),
                        static_cast<std::byte>((std::uint32_t{raw} >> 8U) & 0xFFU),
                        std::byte{0},
                        std::byte{0},
                        std::byte{0},
                        std::byte{0},
                        std::byte{0},
                        std::byte{0}};
}

TEST_CASE("end_stream: Always on never-observed signal after 1 frame → Unresolved",
          "[integration][eos][unresolved]") {
    // A single Msg512 frame (no Speed) leaves the Always(Speed<100)
    // atomic unresolved. Under three-valued Kleene this propagates via
    // And (Atomic) (Always _) as Unsure ∧ Holds = Unsure.
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(std::stop_token{}, make_two_message_dbc()).has_value());

    auto formula = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{100, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));
    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto const rpm_id = CanId{StandardId::create(0x200).value()};
    auto const dlc = Dlc::create(8).value();
    auto ack = client.send_frame(std::stop_token{}, Timestamp{0}, rpm_id, dlc, bytes_of(5));
    REQUIRE(ack.has_value());
    CHECK(std::holds_alternative<Ack>(*ack));

    auto end = client.end_stream(std::stop_token{});
    REQUIRE(end.has_value());
    REQUIRE(end->results.size() == 1);
    CHECK(end->results[0].verdict == Verdict::Unresolved);
}

TEST_CASE("end_stream: Always on never-observed signal after 5 frames → Unresolved",
          "[integration][eos][unresolved]") {
    // Multiple frames without the referenced signal should still finalize to
    // Unresolved — the Kleene fixed point persists regardless of progression
    // count.
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(std::stop_token{}, make_two_message_dbc()).has_value());

    auto formula = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{100, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));
    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto const rpm_id = CanId{StandardId::create(0x200).value()};
    auto const dlc = Dlc::create(8).value();
    for (std::uint64_t i = 0; i < 5; ++i) {
        auto const ack =
            client.send_frame(std::stop_token{}, Timestamp{i * 1000}, rpm_id, dlc, bytes_of(5));
        REQUIRE(ack.has_value());
    }

    auto end = client.end_stream(std::stop_token{});
    REQUIRE(end.has_value());
    REQUIRE(end->results.size() == 1);
    CHECK(end->results[0].verdict == Verdict::Unresolved);
}

TEST_CASE("end_stream: changed_by on one-frame trace → Unresolved",
          "[integration][eos][unresolved]") {
    // A single frame gives changed_by(0) no prior observation to compare
    // against, so it finalizes to Unsure. The negation stays Unsure (Kleene
    // fixed point) and Always on a non-empty trace leaves behind And (Not
    // Atomic) (Always ...) which reduces to Unsure ∧ Holds = Unsure.
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(std::stop_token{}, make_two_message_dbc()).has_value());

    auto formula = ltl::always(
        ltl::negate(ltl::atomic(ltl::changed_by(SignalName{"Speed"}, Delta{Rational{0, 1}}))));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));
    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto const speed_id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value();
    auto const ack =
        client.send_frame(std::stop_token{}, Timestamp{0}, speed_id, dlc, bytes_of(10));
    REQUIRE(ack.has_value());

    auto end = client.end_stream(std::stop_token{});
    REQUIRE(end.has_value());
    REQUIRE(end->results.size() == 1);
    CHECK(end->results[0].verdict == Verdict::Unresolved);
}

TEST_CASE("end_stream: Eventually on never-observed signal → Unresolved",
          "[integration][eos][unresolved]") {
    // The Or φ (Eventually ψ) → Eventually ψ absorption is guarded by
    // finalizesFails φ = true, and a bare Atomic finalizes to Unsure, so the
    // Or persists and finalizes via Unsure ∨ Fails = Unsure.
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(std::stop_token{}, make_two_message_dbc()).has_value());

    auto formula = ltl::eventually(
        ltl::atomic(ltl::greater_than(SignalName{"Speed"}, PhysicalValue{Rational{10, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));
    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto const rpm_id = CanId{StandardId::create(0x200).value()};
    auto const dlc = Dlc::create(8).value();
    for (std::uint64_t i = 0; i < 5; ++i) {
        auto const ack =
            client.send_frame(std::stop_token{}, Timestamp{i * 1000}, rpm_id, dlc, bytes_of(5));
        REQUIRE(ack.has_value());
    }

    auto end = client.end_stream(std::stop_token{});
    REQUIRE(end.has_value());
    REQUIRE(end->results.size() == 1);
    CHECK(end->results[0].verdict == Verdict::Unresolved);
}

TEST_CASE("end_stream: Eventually on 0 frames still finalizes to Fails",
          "[integration][eos][unresolved]") {
    // Contrast with the N ≥ 1 case above. With no progression, finalizeL is
    // applied directly to Eventually _ which returns Fails (liveness
    // operators do not get three-valued absorption on the empty trace).
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(std::stop_token{}, make_two_message_dbc()).has_value());

    auto formula = ltl::eventually(
        ltl::atomic(ltl::greater_than(SignalName{"Speed"}, PhysicalValue{Rational{10, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));
    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto end = client.end_stream(std::stop_token{});
    REQUIRE(end.has_value());
    REQUIRE(end->results.size() == 1);
    CHECK(end->results[0].verdict == Verdict::Fails);
}

TEST_CASE("end_stream: 0 frames + Always(missing) → Holds (vacuous)",
          "[integration][eos][unresolved]") {
    // Standard LTLf vacuous truth: G φ on the empty trace holds regardless
    // of whether φ's signal is observable. This differentiates the
    // empty-trace path (direct finalizeL on Always) from the non-empty path
    // (finalizeL after progression leaves an And behind).
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(std::stop_token{}, make_two_message_dbc()).has_value());

    auto formula = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{100, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));
    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto end = client.end_stream(std::stop_token{});
    REQUIRE(end.has_value());
    REQUIRE(end->results.size() == 1);
    CHECK(end->results[0].verdict == Verdict::Holds);
}

TEST_CASE("end_stream: signal recovers after missing → Holds", "[integration][eos][unresolved]") {
    // Once the signal is observed at least once with a true value, the
    // And (Atomic) (Always ...) absorption collapses back to Always (Atomic)
    // via combineAnd Satisfied l. Confirms the Unresolved path only bites
    // when the signal is missing for the entire stream.
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(std::stop_token{}, make_two_message_dbc()).has_value());

    auto formula = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{100, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));
    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto const speed_id = CanId{StandardId::create(0x100).value()};
    auto const rpm_id = CanId{StandardId::create(0x200).value()};
    auto const dlc = Dlc::create(8).value();

    // Three frames of Msg512 (Speed absent).
    for (std::uint64_t i = 0; i < 3; ++i) {
        auto const ack =
            client.send_frame(std::stop_token{}, Timestamp{i * 1000}, rpm_id, dlc, bytes_of(5));
        REQUIRE(ack.has_value());
    }
    // Two frames of Msg256 with Speed = 10 (< 100).
    auto const ack1 =
        client.send_frame(std::stop_token{}, Timestamp{3000}, speed_id, dlc, bytes_of(10));
    REQUIRE(ack1.has_value());
    auto const ack2 =
        client.send_frame(std::stop_token{}, Timestamp{4000}, speed_id, dlc, bytes_of(10));
    REQUIRE(ack2.has_value());

    auto end = client.end_stream(std::stop_token{});
    REQUIRE(end.has_value());
    REQUIRE(end->results.size() == 1);
    CHECK(end->results[0].verdict == Verdict::Holds);
}

TEST_CASE("end_stream: K3 combination — Unresolved And Holds = Unresolved",
          "[integration][eos][unresolved]") {
    // Kleene truth table: Unsure ∧ Holds = Unsure. Left conjunct references
    // Speed (never observed → Unsure), right conjunct references Rpm
    // (observed < 100 → Holds). End result must be Unresolved.
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(std::stop_token{}, make_two_message_dbc()).has_value());

    auto lhs = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{100, 1}})));
    auto rhs = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Rpm"}, PhysicalValue{Rational{100, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(ltl::both(std::move(lhs), std::move(rhs)));
    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto const rpm_id = CanId{StandardId::create(0x200).value()};
    auto const dlc = Dlc::create(8).value();
    for (std::uint64_t i = 0; i < 3; ++i) {
        auto const ack =
            client.send_frame(std::stop_token{}, Timestamp{i * 1000}, rpm_id, dlc, bytes_of(5));
        REQUIRE(ack.has_value());
    }

    auto end = client.end_stream(std::stop_token{});
    REQUIRE(end.has_value());
    REQUIRE(end->results.size() == 1);
    CHECK(end->results[0].verdict == Verdict::Unresolved);
}

TEST_CASE("end_stream: K3 combination — Unresolved Or Fails = Unresolved",
          "[integration][eos][unresolved]") {
    // Kleene truth table: Unsure ∨ Fails = Unsure. Left disjunct references
    // Speed (never observed → Unsure), right disjunct is an Eventually that
    // references Rpm but requires an unsatisfiable threshold (→ Fails under
    // direct finalization). The right disjunct is an Eventually on a
    // threshold Rpm never reaches: a liveness operator that no progression
    // satisfied finalizes to Fails on a non-empty trace. An Always would not
    // do, since it holds vacuously when nothing matches.
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(std::stop_token{}, make_two_message_dbc()).has_value());

    auto lhs = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{100, 1}})));
    auto rhs = ltl::eventually(
        ltl::atomic(ltl::greater_than(SignalName{"Rpm"}, PhysicalValue{Rational{999999, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(ltl::either(std::move(lhs), std::move(rhs)));
    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto const rpm_id = CanId{StandardId::create(0x200).value()};
    auto const dlc = Dlc::create(8).value();
    for (std::uint64_t i = 0; i < 3; ++i) {
        auto const ack =
            client.send_frame(std::stop_token{}, Timestamp{i * 1000}, rpm_id, dlc, bytes_of(5));
        REQUIRE(ack.has_value());
    }

    auto end = client.end_stream(std::stop_token{});
    REQUIRE(end.has_value());
    REQUIRE(end->results.size() == 1);
    CHECK(end->results[0].verdict == Verdict::Unresolved);
}

TEST_CASE("end_stream: Unresolved result carries enrichment when diagnostics present",
          "[integration][eos][unresolved][enrich]") {
    // client.cpp end_stream() calls enrich_end_stream_results, which collects
    // both Fails and Unresolved verdicts. Verify the enrichment pipeline runs
    // on the Unresolved branch by checking that reason and enrichment are
    // populated.
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(std::stop_token{}, make_two_message_dbc()).has_value());

    auto formula = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{100, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));
    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto const rpm_id = CanId{StandardId::create(0x200).value()};
    auto const dlc = Dlc::create(8).value();
    for (std::uint64_t i = 0; i < 3; ++i) {
        auto const ack =
            client.send_frame(std::stop_token{}, Timestamp{i * 1000}, rpm_id, dlc, bytes_of(5));
        REQUIRE(ack.has_value());
    }

    auto end = client.end_stream(std::stop_token{});
    REQUIRE(end.has_value());
    REQUIRE(end->results.size() == 1);
    auto const& pr = end->results[0];
    CHECK(pr.verdict == Verdict::Unresolved);
    // The Agda core emits a human-readable reason for Unresolved verdicts.
    CHECK_FALSE(pr.reason.empty());
    // end-of-stream enrichment attaches unconditionally for Unresolved — the
    // ViolationEnrichment field should be populated.
    REQUIRE(pr.enrichment.has_value());
    CHECK_FALSE(pr.enrichment->enriched_reason.empty());
}

TEST_CASE("end_stream: enrichment carries the newest payload of a repeated CAN id",
          "[integration][eos][unresolved][enrich]") {
    // The last-frame cache updates an entry in place, assigning the identifier,
    // then the length, then the payload.  A second frame on one CAN id has to
    // replace the bytes and not only the two fields before them, or enrichment
    // reports the newest frame's header beside the oldest frame's values.  The
    // frames carry different values for that reason: with one value the
    // assignment is unobservable and the cache could drop it unnoticed.
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(std::stop_token{}, make_two_message_dbc()).has_value());

    // A liveness property no frame witnesses: both frames carry a Speed under
    // the bound, so the Eventually finalizes to Fails, which is what attaches
    // an enrichment.  The diagnostic names Speed, which is what keeps Speed in
    // the enrichment's signal map, since that map is filtered to the
    // diagnostic's own signals.
    auto formula = ltl::eventually(
        ltl::atomic(ltl::greater_than(SignalName{"Speed"}, PhysicalValue{Rational{10, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));
    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    // Speed is the signal of message 0x100 in this DBC, scaled by one with no
    // offset, so a frame built from a raw value carries that value.
    auto const speed_id = CanId{StandardId::create(0x100).value()};
    auto const dlc = Dlc::create(8).value();
    REQUIRE(
        client.send_frame(std::stop_token{}, Timestamp{0}, speed_id, dlc, bytes_of(5)).has_value());
    REQUIRE(client.send_frame(std::stop_token{}, Timestamp{1000}, speed_id, dlc, bytes_of(7))
                .has_value());

    auto end = client.end_stream(std::stop_token{});
    REQUIRE(end.has_value());
    REQUIRE(end->results.size() == 1);
    auto const& pr = end->results[0];
    CHECK(pr.verdict == Verdict::Fails);
    REQUIRE(pr.enrichment.has_value());
    REQUIRE(pr.enrichment->signals.contains(SignalName{"Speed"}));
    // Seven, the second frame's value, and not five, the first frame's.
    CHECK(pr.enrichment->signals.at(SignalName{"Speed"}) == PhysicalValue{Rational{7, 1}});
}

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
    DbcSignal sig{
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
    auto id = StandardId::create(0x100).value();
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
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    // BE signal, length=0 → the shared geometry gate's positive-length
    // condition fails → SignalBitLengthZero.
    auto const dbc = make_single_be_signal_dbc(/*start_bit=*/7, /*bit_length=*/0, /*dlc_bytes=*/1);

    auto result = client.parse_dbc(std::stop_token{}, dbc);
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().code() == ErrorCode::ParseSignalBitLengthZero);
    CHECK(result.error().kind() == ErrorKind::Protocol);
}

TEST_CASE("parse DBC: LittleEndian signal with length=0 → parse_signal_bit_length_zero",
          "[integration][parse_error]") {
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    // LE signal, length=0 → the shared geometry gate's positive-length
    // condition fails → SignalBitLengthZero (identical for both byte orders).
    auto const dbc =
        make_single_signal_dbc(/*start_bit=*/0, /*bit_length=*/0, ByteOrder::LittleEndian,
                               /*dlc_bytes=*/1);

    auto result = client.parse_dbc(std::stop_token{}, dbc);
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().code() == ErrorCode::ParseSignalBitLengthZero);
    CHECK(result.error().kind() == ErrorKind::Protocol);
}

TEST_CASE(
    "parse DBC: BigEndian signal wider than the frame → parse_signal_bit_length_exceeds_frame",
    "[integration][parse_error]") {
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    // BE signal: start_bit=7 (MSB of byte 0), length=33, dlc=4 → 32 bits of
    // frame.  The entry gate refuses the SUBMITTED length against the frame
    // capacity (33 ≤ 32 fails), before any start-bit conversion.
    // Mirrors python/tests/test_dbc_validator.py::test_big_endian_signal_exceeds_dlc.
    auto const dbc = make_single_be_signal_dbc(/*start_bit=*/7, /*bit_length=*/33, /*dlc_bytes=*/4);

    auto result = client.parse_dbc(std::stop_token{}, dbc);
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().code() == ErrorCode::ParseSignalBitLengthExceedsFrame);
    CHECK(result.error().kind() == ErrorKind::Protocol);
}

TEST_CASE("parse DBC: BigEndian run past the frame end → parse_signal_big_endian_overflow",
          "[integration][parse_error]") {
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    // BE signal: start_bit=0, length=2, dlc=1.  The Motorola MSB anchor is
    // the frame's LAST bit position (physicalBitPos(1, BE, 0) = 0), so a
    // descending run of two bits leaves the frame — the pre-conversion
    // no-wrap condition (bl − 1 ≤ physicalBitPos) fails and the gate
    // refuses (the former post-conversion check would have silently
    // relocated the run via the monus floor).
    auto const dbc = make_single_be_signal_dbc(/*start_bit=*/0, /*bit_length=*/2, /*dlc_bytes=*/1);

    auto result = client.parse_dbc(std::stop_token{}, dbc);
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().code() == ErrorCode::ParseSignalBigEndianOverflow);
    CHECK(result.error().kind() == ErrorKind::Protocol);
}

TEST_CASE("parse DBC: out-of-frame start bit → parse_signal_start_bit_exceeds_frame",
          "[integration][parse_error]") {
    auto const lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    // LE signal whose start bit is the first position past the 1-byte frame.
    auto const dbc =
        make_single_signal_dbc(/*start_bit=*/8, /*bit_length=*/8, ByteOrder::LittleEndian,
                               /*dlc_bytes=*/1);

    auto result = client.parse_dbc(std::stop_token{}, dbc);
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
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    const std::string text = "VERSION \"\"\n\nNS_ :\n\nBS_:\n\nBU_: Engine\n\n"
                             "BO_ 100 Msg: 2 Engine\n"
                             " SG_ Sig : 7|16@0+ (1,0) [0|0] \"\" Engine\n";
    auto loaded = client.parse_dbc_text(std::stop_token{}, text);
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
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    auto const dbc =
        make_single_signal_dbc(/*start_bit=*/0, /*bit_length=*/512, ByteOrder::LittleEndian,
                               /*dlc_bytes=*/64);
    REQUIRE(client.parse_dbc(std::stop_token{}, dbc).has_value());

    auto echoed = client.format_dbc(std::stop_token{});
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
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    DbcSignal sig{
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

    auto validation = client.validate_dbc(std::stop_token{}, dbc);
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
        auto backend = make_ffi_backend(lib);
        REQUIRE(backend != nullptr);
    }

    // Second call with rts_cores != 1 must populate the structured mismatch.
    auto backend = make_ffi_backend(lib, /*rts_cores=*/8);
    REQUIRE(backend != nullptr);
    auto mismatch = backend->rts_mismatch_info();

    REQUIRE(mismatch.has_value());
    CHECK(mismatch->first == 1);
    CHECK(mismatch->second == 8);
}

TEST_CASE("make_ffi_backend is silent on matching rts_cores", "[integration][ffi_backend]") {
    auto const lib = find_lib();

    // Ensure the RTS is already initialized (1 core) from prior tests or
    // this test's first call.
    {
        auto backend = make_ffi_backend(lib);
        REQUIRE(backend != nullptr);
    }

    // Second call with matching rts_cores (1) must NOT warn.
    auto backend = make_ffi_backend(lib, /*rts_cores=*/1);
    REQUIRE(backend != nullptr);

    CHECK_FALSE(backend->rts_mismatch_info().has_value());
}

TEST_CASE("rts.cores_mismatch structured fields match Go/Python schema",
          "[integration][ffi_backend]") {
    auto const lib = find_lib();

    // First init fixes the core count to 1 (deterministic prior state).
    {
        auto backend = make_ffi_backend(lib);
        REQUIRE(backend != nullptr);
    }

    auto backend = make_ffi_backend(lib, /*rts_cores=*/4);
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
    // `rts_cores < 1` raises `AletheiaException(ErrorKind::Validation)` rather
    // than `std::invalid_argument` so callers can branch on `kind()` like
    // every other typed FFI error.
    CHECK_THROWS_AS(make_ffi_backend(lib, /*rts_cores=*/0), AletheiaException);
    CHECK_THROWS_AS(make_ffi_backend(lib, /*rts_cores=*/-1), AletheiaException);
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
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

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
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

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
