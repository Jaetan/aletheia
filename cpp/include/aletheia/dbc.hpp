// SPDX-License-Identifier: BSD-2-Clause
#pragma once

#include <aletheia/types.hpp>

#include <string>
#include <variant>
#include <vector>

namespace aletheia {

// ---------------------------------------------------------------------------
// Signal presence (always vs multiplexed)
// ---------------------------------------------------------------------------

struct AlwaysPresent {};

struct Multiplexed {
    SignalName multiplexor;
    MultiplexValue mux_value;
};

using SignalPresence = std::variant<AlwaysPresent, Multiplexed>;

// ---------------------------------------------------------------------------
// DBC signal definition
// ---------------------------------------------------------------------------

struct DbcSignal {
    SignalName name;
    BitPosition start_bit;
    BitLength bit_length;
    ByteOrder byte_order;
    bool is_signed;
    ScaleFactor factor;
    ScaleOffset offset;
    PhysicalValue minimum;
    PhysicalValue maximum;
    Unit unit;
    SignalPresence presence;
};

// ---------------------------------------------------------------------------
// DBC message definition
// ---------------------------------------------------------------------------

struct DbcMessage {
    CanId id;
    MessageName name;
    Dlc dlc;
    NodeName sender;
    std::vector<DbcSignal> signals;
};

// ---------------------------------------------------------------------------
// Complete DBC definition
// ---------------------------------------------------------------------------

struct DbcDefinition {
    std::string version; // plain string (not a domain identifier)
    std::vector<DbcMessage> messages;
};

} // namespace aletheia
