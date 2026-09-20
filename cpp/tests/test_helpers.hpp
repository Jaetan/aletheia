// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// test_helpers.hpp — shared fixture builder for unit_tests_*.cpp split targets.
//
// This header is included by several translation units inside the unit_tests
// executable, so every helper it defines is marked `inline` and the linker
// folds the identical copies rather than rejecting them. The header
// deliberately pulls in no `using namespace` directive: each translation unit
// adds its own after its includes.

#include <aletheia/aletheia.hpp>

#include "detail/json.hpp"
#include "detail/mock_backend.hpp"

#include <algorithm>
#include <cstddef>
#include <expected>
#include <span>
#include <utility>
#include <vector>

namespace aletheia::test {

// MockBackend answers binary extraction with BinaryUnsupported, so a client
// whose name cache misses a frame's message falls back to JSON and reads the
// same as one whose cache hit. This double answers with a caller-supplied
// result instead, so the binary path is observable: a cache hit takes it,
// its decoding is exercised, and the JSON endpoint is never asked.
class BinExtractMockBackend : public ::aletheia::MockBackend {
public:
    using BinResult = std::expected<std::vector<std::byte>, ::aletheia::AletheiaError>;

    // The default is a header of three zero counts and zero reason bytes,
    // then the lone offsets entry: the smallest buffer the decoder accepts.
    explicit BinExtractMockBackend(BinResult result = std::vector<std::byte>(14, std::byte{0}))
        : result_(std::move(result)) {}

    auto extract_signals_bin(const ::aletheia::BackendState& /*state*/,
                             const ::aletheia::CanId& /*id*/, ::aletheia::Dlc /*dlc*/,
                             std::span<const std::byte> /*data*/) -> BinResult override {
        return result_;
    }

private:
    BinResult result_;
};

// One extracted value, wire index 0, worth 7/1, and nothing else.
inline auto one_value_at_index_zero() -> std::vector<std::byte> {
    std::vector<std::byte> buf(14 + 18, std::byte{0});
    buf[0] = std::byte{1};  // nvals
    buf[12] = std::byte{7}; // numerator, little-endian
    buf[20] = std::byte{1}; // denominator
    return buf;
}

inline auto took_json_extraction(const ::aletheia::MockBackend& mock) -> bool {
    return std::ranges::contains(mock.captured(), "<binary:extractAllSignals>");
}

// parsed_dbc_response_for(dbc) — render the canonical
// `{"status":"success","dbc":...,"warnings":[]}` wire image so MockBackend
// callers can feed it as a parse_dbc / parse_dbc_text response without
// hand-writing JSON.
inline auto parsed_dbc_response_for(const ::aletheia::DbcDefinition& dbc) -> std::string {
    return ::aletheia::detail::serialize_parsed_dbc_response(dbc);
}

// make_test_dbc() — minimal single-message DBC with one always-present signal.
// Used by the JSON serialize tests, the mock-backend client tests, enrichment
// tests, and validation tests. Kept here (not in a .cpp) so each translation
// unit in the split gets the same definition without a separate library.
inline auto make_test_dbc() -> ::aletheia::DbcDefinition {
    auto id = ::aletheia::StandardId::create(0x100).value();
    auto const dlc = ::aletheia::Dlc::create(8).value();

    ::aletheia::DbcSignal sig{
        .name = ::aletheia::SignalName{"Speed"},
        .start_bit = ::aletheia::BitPosition{0},
        .bit_length = ::aletheia::BitLength{16},
        .byte_order = ::aletheia::ByteOrder::LittleEndian,
        .is_signed = false,
        .factor = ::aletheia::RationalFactor{::aletheia::Rational{1, 10}},
        .offset = ::aletheia::RationalOffset{::aletheia::Rational{0, 1}},
        .minimum = ::aletheia::RationalBound{::aletheia::Rational{0, 1}},
        .maximum = ::aletheia::RationalBound{::aletheia::Rational{300, 1}},
        .unit = ::aletheia::Unit{"km/h"},
        .presence = ::aletheia::AlwaysPresent{},
    };

    ::aletheia::DbcMessage msg{
        .id = ::aletheia::CanId{id},
        .name = ::aletheia::MessageName{"VehicleSpeed"},
        .dlc = dlc,
        .sender = ::aletheia::NodeName{"ECU1"},
        .signals = {sig},
    };

    return ::aletheia::DbcDefinition{.version = "1.0", .messages = {msg}};
}

} // namespace aletheia::test
