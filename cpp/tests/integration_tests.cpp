// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// Integration tests with real libaletheia-ffi.so.
// Requires: cabal run shake -- build (produces build/libaletheia-ffi.so)
// Run with: ctest -R integration, which sets ALETHEIA_REPO_ROOT; a direct run
// of ./integration_tests needs ALETHEIA_REPO_ROOT set to the repository root.
#include <catch2/catch_test_macros.hpp>
#include <catch2/generators/catch_generators.hpp>

#include <aletheia/aletheia.hpp>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <expected>
#include <filesystem>
#include <memory>
#include <optional>
#include <ranges>
#include <span>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "find_lib.hpp"
#include "integration_fixtures.hpp"

using aletheia::test::find_lib;
using aletheia::test::make_integration_dbc;

using namespace aletheia;

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
        for (auto const i : std::views::iota(0U, 8U))
            u8(static_cast<std::uint8_t>((u >> (8U * i)) & 0xFFU));
    }
    void str(std::string_view s) {
        for (auto const c : s)
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
    for (auto const i : std::views::iota(std::uint16_t{0}, std::uint16_t{3})) {
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
