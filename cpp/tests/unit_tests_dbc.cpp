// SPDX-License-Identifier: BSD-2-Clause
// Unit tests: DBC multiplexing query helpers + message/signal lookup.
//
// Covers DbcMessage::is_multiplexed, always_present_signals, multiplexed_signals,
// multiplexor_names, mux_values, signals_for_mux_value, signal_by_name, and the
// DbcDefinition::message_by_id / message_by_name paths (including the lazy
// index cache used by the latter two).
#include "test_helpers.hpp"

#include <catch2/catch_test_macros.hpp>

#include <aletheia/aletheia.hpp>

#include <utility>
#include <variant>
#include <vector>

using namespace aletheia;
using aletheia::test::make_test_dbc;

// ---------------------------------------------------------------------------
// Local helper: multiplexed DBC fixture used only by this translation unit.
// ---------------------------------------------------------------------------

namespace {

auto make_mux_dbc() -> DbcDefinition {
    auto id = StandardId::create(0x200).value();
    auto dlc = Dlc::create(8).value();

    std::vector<DbcSignal> sigs;
    sigs.push_back(DbcSignal{.name = SignalName{"MuxSelector"},
                             .start_bit = BitPosition{0},
                             .bit_length = BitLength{8},
                             .byte_order = ByteOrder::LittleEndian,
                             .is_signed = false,
                             .factor = RationalFactor{Rational{1, 1}},
                             .offset = RationalOffset{Rational{0, 1}},
                             .minimum = RationalBound{Rational{0, 1}},
                             .maximum = RationalBound{Rational{255, 1}},
                             .unit = Unit{""},
                             .presence = AlwaysPresent{}});
    sigs.push_back(DbcSignal{.name = SignalName{"Temperature"},
                             .start_bit = BitPosition{8},
                             .bit_length = BitLength{16},
                             .byte_order = ByteOrder::LittleEndian,
                             .is_signed = true,
                             .factor = RationalFactor{Rational{1, 10}},
                             .offset = RationalOffset{Rational{-40, 1}},
                             .minimum = RationalBound{Rational{-40, 1}},
                             .maximum = RationalBound{Rational{215, 1}},
                             .unit = Unit{"degC"},
                             .presence = Multiplexed{.multiplexor = SignalName{"MuxSelector"},
                                                     .mux_values = {MultiplexValue{0}}}});
    sigs.push_back(DbcSignal{.name = SignalName{"Pressure"},
                             .start_bit = BitPosition{8},
                             .bit_length = BitLength{16},
                             .byte_order = ByteOrder::LittleEndian,
                             .is_signed = false,
                             .factor = RationalFactor{Rational{1, 100}},
                             .offset = RationalOffset{Rational{0, 1}},
                             .minimum = RationalBound{Rational{0, 1}},
                             .maximum = RationalBound{Rational{655, 1}},
                             .unit = Unit{"bar"},
                             .presence = Multiplexed{.multiplexor = SignalName{"MuxSelector"},
                                                     .mux_values = {MultiplexValue{1}}}});
    sigs.push_back(DbcSignal{.name = SignalName{"Voltage"},
                             .start_bit = BitPosition{40},
                             .bit_length = BitLength{16},
                             .byte_order = ByteOrder::LittleEndian,
                             .is_signed = false,
                             .factor = RationalFactor{Rational{1, 100}},
                             .offset = RationalOffset{Rational{0, 1}},
                             .minimum = RationalBound{Rational{0, 1}},
                             .maximum = RationalBound{Rational{65, 1}},
                             .unit = Unit{"V"},
                             .presence = AlwaysPresent{}});

    DbcMessage msg{.id = CanId{id},
                   .name = MessageName{"MuxMessage"},
                   .dlc = dlc,
                   .sender = NodeName{"ECU"},
                   .signals = std::move(sigs)};
    return DbcDefinition{.version = "1.0", .messages = {std::move(msg)}};
}

} // namespace

TEST_CASE("DbcMessage::is_multiplexed", "[dbc][mux]") {
    auto dbc = make_mux_dbc();
    CHECK(dbc.messages[0].is_multiplexed());

    auto plain = make_test_dbc();
    CHECK_FALSE(plain.messages[0].is_multiplexed());
}

TEST_CASE("DbcMessage::always_present_signals", "[dbc][mux]") {
    auto dbc = make_mux_dbc();
    auto ap = dbc.messages[0].always_present_signals();
    REQUIRE(ap.size() == 2);
    CHECK(ap[0].name == SignalName{"MuxSelector"});
    CHECK(ap[1].name == SignalName{"Voltage"});
}

TEST_CASE("DbcMessage::multiplexed_signals", "[dbc][mux]") {
    auto dbc = make_mux_dbc();
    auto ms = dbc.messages[0].multiplexed_signals();
    REQUIRE(ms.size() == 2);
    CHECK(ms[0].name == SignalName{"Temperature"});
    CHECK(ms[1].name == SignalName{"Pressure"});
}

TEST_CASE("DbcMessage::multiplexor_names", "[dbc][mux]") {
    auto dbc = make_mux_dbc();
    auto mn = dbc.messages[0].multiplexor_names();
    REQUIRE(mn.size() == 1);
    CHECK(mn[0] == SignalName{"MuxSelector"});
}

TEST_CASE("DbcMessage::mux_values", "[dbc][mux]") {
    auto dbc = make_mux_dbc();
    auto mv = dbc.messages[0].mux_values(SignalName{"MuxSelector"});
    REQUIRE(mv.size() == 2);
    CHECK(mv[0] == MultiplexValue{0});
    CHECK(mv[1] == MultiplexValue{1});

    auto empty = dbc.messages[0].mux_values(SignalName{"NonExistent"});
    CHECK(empty.empty());
}

TEST_CASE("DbcMessage::signals_for_mux_value", "[dbc][mux]") {
    auto dbc = make_mux_dbc();

    auto s0 = dbc.messages[0].signals_for_mux_value(SignalName{"MuxSelector"}, MultiplexValue{0});
    REQUIRE(s0.size() == 3); // MuxSelector + Temperature + Voltage
    CHECK(s0[0].name == SignalName{"MuxSelector"});
    CHECK(s0[1].name == SignalName{"Temperature"});
    CHECK(s0[2].name == SignalName{"Voltage"});

    auto s1 = dbc.messages[0].signals_for_mux_value(SignalName{"MuxSelector"}, MultiplexValue{1});
    REQUIRE(s1.size() == 3); // MuxSelector + Pressure + Voltage
    CHECK(s1[1].name == SignalName{"Pressure"});

    auto s99 = dbc.messages[0].signals_for_mux_value(SignalName{"MuxSelector"}, MultiplexValue{99});
    CHECK(s99.size() == 2); // only always-present

    // Unknown multiplexor name — only always-present signals returned.
    auto su = dbc.messages[0].signals_for_mux_value(SignalName{"NonExistent"}, MultiplexValue{0});
    CHECK(su.size() == 2);
    CHECK(su[0].name == SignalName{"MuxSelector"});
    CHECK(su[1].name == SignalName{"Voltage"});
}

TEST_CASE("DbcMessage::multiplexor_names non-mux message", "[dbc][mux]") {
    auto plain = make_test_dbc();
    CHECK(plain.messages[0].multiplexor_names().empty());
}

TEST_CASE("DbcMessage::always_present_signals non-mux message", "[dbc][mux]") {
    auto plain = make_test_dbc();
    auto ap = plain.messages[0].always_present_signals();
    CHECK(ap.size() == plain.messages[0].signals.size());
}

TEST_CASE("DbcMessage::signal_by_name", "[dbc]") {
    auto dbc = make_mux_dbc();
    auto* sig = dbc.messages[0].signal_by_name(SignalName{"Temperature"});
    REQUIRE(sig != nullptr);
    CHECK(sig->is_signed == true);

    // Always-present signal.
    auto* mux_sel = dbc.messages[0].signal_by_name(SignalName{"MuxSelector"});
    REQUIRE(mux_sel != nullptr);
    CHECK(std::holds_alternative<AlwaysPresent>(mux_sel->presence));

    CHECK(dbc.messages[0].signal_by_name(SignalName{"NoSuch"}) == nullptr);
}

TEST_CASE("DbcMessage::mux_values non-mux message", "[dbc][mux]") {
    auto plain = make_test_dbc();
    CHECK(plain.messages[0].mux_values(SignalName{"Anything"}).empty());
}

TEST_CASE("DbcMessage::signals_for_mux_value non-mux message", "[dbc][mux]") {
    auto plain = make_test_dbc();
    // Unknown multiplexor on a non-mux message returns all signals (all always-present).
    auto sigs = plain.messages[0].signals_for_mux_value(SignalName{"Anything"}, MultiplexValue{0});
    CHECK(sigs.size() == plain.messages[0].signals.size());
}

TEST_CASE("DbcDefinition::message_by_id", "[dbc]") {
    auto dbc = make_mux_dbc();
    auto id = StandardId::create(0x200).value();
    auto* msg = dbc.message_by_id(CanId{id});
    REQUIRE(msg != nullptr);
    CHECK(msg->name == MessageName{"MuxMessage"});

    auto missing = StandardId::create(0x7FF).value(); // valid 11-bit, not in DBC
    CHECK(dbc.message_by_id(CanId{missing}) == nullptr);

    // Extended ID 0x200 should not match standard ID 0x200.
    auto ext = ExtendedId::create(0x200).value();
    CHECK(dbc.message_by_id(CanId{ext}) == nullptr);
}

TEST_CASE("DbcDefinition::message_by_id with extended ID", "[dbc]") {
    auto std_id = StandardId::create(0x200).value();
    auto ext_id = ExtendedId::create(0x200).value();
    DbcMessage std_msg{.id = CanId{std_id},
                       .name = MessageName{"StdMsg"},
                       .dlc = Dlc::create(8).value(),
                       .sender = NodeName{"ECU"},
                       .signals = {}};
    DbcMessage ext_msg{.id = CanId{ext_id},
                       .name = MessageName{"ExtMsg"},
                       .dlc = Dlc::create(8).value(),
                       .sender = NodeName{"ECU"},
                       .signals = {}};
    DbcDefinition dbc{.version = "1.0", .messages = {std_msg, ext_msg}};

    auto* found_std = dbc.message_by_id(CanId{std_id});
    REQUIRE(found_std != nullptr);
    CHECK(found_std->name == MessageName{"StdMsg"});

    auto* found_ext = dbc.message_by_id(CanId{ext_id});
    REQUIRE(found_ext != nullptr);
    CHECK(found_ext->name == MessageName{"ExtMsg"});
}

TEST_CASE("DbcDefinition::message_by_name", "[dbc]") {
    auto dbc = make_mux_dbc();
    auto* msg = dbc.message_by_name(MessageName{"MuxMessage"});
    REQUIRE(msg != nullptr);
    CHECK(msg->signals.size() == 4);

    CHECK(dbc.message_by_name(MessageName{"NoSuch"}) == nullptr);

    // Empty DBC returns nullptr.
    DbcDefinition empty{.version = "1.0", .messages = {}};
    CHECK(empty.message_by_name(MessageName{"Anything"}) == nullptr);
}
