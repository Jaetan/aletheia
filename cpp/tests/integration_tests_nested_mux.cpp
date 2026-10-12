// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// Nested multiplexing through the real libaletheia-ffi.so.

#include <catch2/catch_test_macros.hpp>

#include <aletheia/aletheia.hpp>

#include <algorithm>
#include <cstddef>
#include <expected>
#include <memory>
#include <span>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "find_lib.hpp"
#include "integration_fixtures.hpp"

using aletheia::test::find_lib;
using aletheia::test::has_warning;

using namespace aletheia;

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
    auto const found_cycle = std::ranges::any_of(result->issues, [](auto const& issue) {
        return issue.code == IssueCode::MultiplexorCycle;
    });
    CHECK(found_cycle);
}
