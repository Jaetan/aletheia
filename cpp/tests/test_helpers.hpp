// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// test_helpers.hpp — shared fixture builder for unit_tests_*.cpp split targets.
//
// This header is included by multiple translation units inside the unit_tests
// executable. To avoid ODR / multiple-definition errors at link time the one
// helper defined here is marked `inline` so the linker may fold identical
// copies. The header deliberately does NOT pull in any `using namespace`
// directives — each .cpp translation unit adds its own after its includes.

#include <aletheia/aletheia.hpp>

namespace aletheia::test {

// make_test_dbc() — minimal single-message DBC with one always-present signal.
// Used by the JSON serialize tests, the mock-backend client tests, enrichment
// tests, and validation tests. Kept here (not in a .cpp) so each translation
// unit in the split gets the same definition without a separate library.
inline auto make_test_dbc() -> ::aletheia::DbcDefinition {
    auto id = ::aletheia::StandardId::create(0x100).value();
    auto dlc = ::aletheia::Dlc::create(8).value();

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
