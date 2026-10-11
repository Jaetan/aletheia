// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// The DBC the size-bound tests grow one list of past its bound, and the one
// the nesting-depth test loads before its property: message 256 carrying the
// one-bit signal S, built from a one-bit signal and a message of such signals.

#include <aletheia/dbc.hpp>
#include <aletheia/types.hpp>

#include <cstdint>
#include <format>
#include <string>
#include <utility>
#include <vector>

namespace aletheia::test {

inline auto make_bit_signal(std::string name) -> DbcSignal {
    return DbcSignal{
        .name = SignalName{std::move(name)},
        .start_bit = BitPosition{0},
        .bit_length = BitLength{1},
        .byte_order = ByteOrder::LittleEndian,
        .is_signed = false,
        .factor = RationalFactor{Rational{1, 1}},
        .offset = RationalOffset{Rational{0, 1}},
        .minimum = RationalBound{Rational{0, 1}},
        .maximum = RationalBound{Rational{1, 1}},
        .unit = Unit{""},
        .presence = AlwaysPresent{},
    };
}

inline auto make_bit_message(std::uint16_t id, std::vector<DbcSignal> signals) -> DbcMessage {
    return DbcMessage{
        .id = CanId{StandardId::create(id).value()},
        .name = MessageName{std::format("M{}", id)},
        .dlc = Dlc::create(8).value(),
        .sender = NodeName{"ECU"},
        .signals = std::move(signals),
    };
}

// Message 256 carrying the one-bit signal S.
inline auto make_bounds_dbc() -> DbcDefinition {
    return DbcDefinition{.version = "1.0",
                         .messages = {make_bit_message(256, {make_bit_signal("S")})}};
}

} // namespace aletheia::test
