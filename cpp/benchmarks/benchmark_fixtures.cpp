// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// The fixtures every benchmark mode measures against: two DBC definitions built
// in code, a frame and a set of signal values for each, and their LTL properties.

#include "benchmark_fixtures.hpp"

#include <aletheia/aletheia.hpp>

#include <cstddef>
#include <cstdint>
#include <vector>

using aletheia::FramePayload;

// ---------------------------------------------------------------------------
// DBC definitions, built in code. The signal layouts are those of
// examples/example.dbc (EngineStatus, BrakeStatus) and examples/example_canfd.dbc
// (SensorFusion); senders and the files' other messages are not needed here, and
// every binding's benchmark builds these same definitions.
// ---------------------------------------------------------------------------

namespace aletheia::bench {

auto make_can20_dbc() -> DbcDefinition {
    // EngineStatus: ID=0x100, DLC=8, sender=ECU1
    DbcSignal engine_speed{
        .name = SignalName{"EngineSpeed"},
        .start_bit = BitPosition{0},
        .bit_length = BitLength{16},
        .byte_order = ByteOrder::LittleEndian,
        .is_signed = false,
        .factor = RationalFactor{Rational{1, 4}},
        .offset = RationalOffset{Rational{0, 1}},
        .minimum = RationalBound{Rational{0, 1}},
        .maximum = RationalBound{Rational{8000, 1}},
        .unit = Unit{"rpm"},
        .presence = AlwaysPresent{},
    };
    DbcSignal engine_temp{
        .name = SignalName{"EngineTemp"},
        .start_bit = BitPosition{16},
        .bit_length = BitLength{8},
        .byte_order = ByteOrder::LittleEndian,
        .is_signed = false,
        .factor = RationalFactor{Rational{1, 1}},
        .offset = RationalOffset{Rational{-40, 1}},
        .minimum = RationalBound{Rational{-40, 1}},
        .maximum = RationalBound{Rational{215, 1}},
        .unit = Unit{"celsius"},
        .presence = AlwaysPresent{},
    };

    DbcMessage engine_msg{
        .id = CanId{StandardId::create(0x100).value()},
        .name = MessageName{"EngineStatus"},
        .dlc = Dlc::create(8).value(),
        .sender = NodeName{"ECU1"},
        .signals = {engine_speed, engine_temp},
    };

    // BrakeStatus: ID=0x200, DLC=8, sender=ECU2
    DbcSignal brake_pressure{
        .name = SignalName{"BrakePressure"},
        .start_bit = BitPosition{0},
        .bit_length = BitLength{16},
        .byte_order = ByteOrder::LittleEndian,
        .is_signed = false,
        .factor = RationalFactor{Rational{1, 10}},
        .offset = RationalOffset{Rational{0, 1}},
        .minimum = RationalBound{Rational{0, 1}},
        .maximum = RationalBound{Rational{65535, 10}},
        .unit = Unit{"bar"},
        .presence = AlwaysPresent{},
    };
    DbcSignal brake_pressed{
        .name = SignalName{"BrakePressed"},
        .start_bit = BitPosition{16},
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

    DbcMessage brake_msg{
        .id = CanId{StandardId::create(0x200).value()},
        .name = MessageName{"BrakeStatus"},
        .dlc = Dlc::create(8).value(),
        .sender = NodeName{"ECU2"},
        .signals = {brake_pressure, brake_pressed},
    };

    return DbcDefinition{.version = "", .messages = {engine_msg, brake_msg}};
}

auto make_canfd_dbc() -> DbcDefinition {
    // Helper to build a signal with common defaults
    auto const sig = [](const char* name, std::uint16_t start, std::uint8_t len, bool is_signed,
                        Rational factor, Rational offset, Rational min_val, Rational max_val,
                        const char* unit) -> DbcSignal {
        return DbcSignal{
            .name = SignalName{name},
            .start_bit = BitPosition{start},
            .bit_length = BitLength{len},
            .byte_order = ByteOrder::LittleEndian,
            .is_signed = is_signed,
            .factor = RationalFactor{factor},
            .offset = RationalOffset{offset},
            .minimum = RationalBound{min_val},
            .maximum = RationalBound{max_val},
            .unit = Unit{unit},
            .presence = AlwaysPresent{},
        };
    };

    DbcMessage sensor_fusion{
        .id = CanId{StandardId::create(0x200).value()},
        .name = MessageName{"SensorFusion"},
        .dlc = Dlc::create(15).value(),
        .sender = NodeName{"SensorGateway"},
        .signals =
            {
                sig("GPSLatitude", 0, 32, true, {1, 10000000}, {0, 1}, {-90, 1}, {90, 1}, "deg"),
                sig("GPSLongitude", 32, 32, true, {1, 10000000}, {0, 1}, {-180, 1}, {180, 1},
                    "deg"),
                sig("GPSAltitude", 64, 16, true, {1, 10}, {0, 1}, {-1000, 1}, {32767, 10}, "m"),
                sig("GPSSpeed", 80, 16, false, {1, 100}, {0, 1}, {0, 1}, {65535, 100}, "m/s"),
                sig("YawRate", 96, 16, true, {1, 100}, {0, 1}, {-32768, 100}, {32767, 100},
                    "deg/s"),
                sig("LateralAccel", 112, 16, true, {1, 100}, {0, 1}, {-32768, 100}, {32767, 100},
                    "m/s2"),
                sig("LongAccel", 128, 16, true, {1, 100}, {0, 1}, {-32768, 100}, {32767, 100},
                    "m/s2"),
                sig("SteeringAngle", 144, 16, true, {1, 10}, {0, 1}, {-32768, 10}, {32767, 10},
                    "deg"),
                sig("WheelSpeedFL", 160, 16, false, {1, 100}, {0, 1}, {0, 1}, {65535, 100}, "m/s"),
                sig("WheelSpeedFR", 176, 16, false, {1, 100}, {0, 1}, {0, 1}, {65535, 100}, "m/s"),
                sig("WheelSpeedRL", 192, 16, false, {1, 100}, {0, 1}, {0, 1}, {65535, 100}, "m/s"),
                sig("WheelSpeedRR", 208, 16, false, {1, 100}, {0, 1}, {0, 1}, {65535, 100}, "m/s"),
                sig("BrakeTempFL", 224, 12, false, {1, 10}, {0, 1}, {0, 1}, {819, 2}, "celsius"),
                sig("BrakeTempFR", 236, 12, false, {1, 10}, {0, 1}, {0, 1}, {819, 2}, "celsius"),
                sig("BrakeTempRL", 248, 12, false, {1, 10}, {0, 1}, {0, 1}, {819, 2}, "celsius"),
                sig("BrakeTempRR", 260, 12, false, {1, 10}, {0, 1}, {0, 1}, {819, 2}, "celsius"),
                sig("TirePressFL", 272, 8, false, {1, 100}, {0, 1}, {0, 1}, {255, 100}, "bar"),
                sig("TirePressFR", 280, 8, false, {1, 100}, {0, 1}, {0, 1}, {255, 100}, "bar"),
                sig("TirePressRL", 288, 8, false, {1, 100}, {0, 1}, {0, 1}, {255, 100}, "bar"),
                sig("TirePressRR", 296, 8, false, {1, 100}, {0, 1}, {0, 1}, {255, 100}, "bar"),
                sig("SensorStatus", 304, 8, false, {1, 1}, {0, 1}, {0, 1}, {255, 1}, ""),
                sig("IMUTemp", 312, 8, false, {1, 1}, {-40, 1}, {-40, 1}, {215, 1}, "celsius"),
                sig("BatteryVolt", 320, 12, false, {1, 100}, {0, 1}, {0, 1}, {4095, 100}, "V"),
                sig("GPSHeading", 332, 16, false, {1, 100}, {0, 1}, {0, 1}, {65535, 100}, "deg"),
                sig("TimestampMs", 348, 32, false, {1, 1}, {0, 1}, {0, 1}, {4294967295, 1}, "ms"),
            },
    };

    return DbcDefinition{.version = "", .messages = {sensor_fusion}};
}

// ---------------------------------------------------------------------------
// Frame payloads
// ---------------------------------------------------------------------------

// The payload fixtures are function-local: a container at namespace scope
// runs its constructor before main, where a throw cannot be caught.
auto can20_frame() -> const FramePayload& {
    static const FramePayload frame = {
        std::byte{0x40}, std::byte{0x1F}, std::byte{0x82}, std::byte{0x00},
        std::byte{0x00}, std::byte{0x00}, std::byte{0x00}, std::byte{0x00},
    };
    return frame;
}

} // namespace aletheia::bench

static auto make_canfd_frame() -> FramePayload {
    FramePayload frame(64, std::byte{0x00});
    // GPSLatitude  (raw ~100000000 -> 10.0 deg)
    frame.at(0) = std::byte{0x00};
    frame.at(1) = std::byte{0xE1};
    frame.at(2) = std::byte{0xF5};
    frame.at(3) = std::byte{0x05};
    // GPSLongitude (raw ~48100000 -> 4.81 deg)
    frame.at(4) = std::byte{0x00};
    frame.at(5) = std::byte{0x6C};
    frame.at(6) = std::byte{0xDC};
    frame.at(7) = std::byte{0x02};
    // GPSAltitude  (raw 1000 -> 100.0 m)
    frame.at(8) = std::byte{0xE8};
    frame.at(9) = std::byte{0x03};
    // GPSSpeed     (raw 2000 -> 20.0 m/s)
    frame.at(10) = std::byte{0xD0};
    frame.at(11) = std::byte{0x07};
    // YawRate, LateralAccel, LongAccel, SteeringAngle: all 0
    // WheelSpeedFL (raw 1000 -> 10.0 m/s)
    frame.at(20) = std::byte{0xE8};
    frame.at(21) = std::byte{0x03};
    // WheelSpeedFR
    frame.at(22) = std::byte{0xE8};
    frame.at(23) = std::byte{0x03};
    // WheelSpeedRL
    frame.at(24) = std::byte{0xE8};
    frame.at(25) = std::byte{0x03};
    // WheelSpeedRR
    frame.at(26) = std::byte{0xE8};
    frame.at(27) = std::byte{0x03};
    return frame;
}

namespace aletheia::bench {

auto canfd_frame() -> const FramePayload& {
    static auto const frame = make_canfd_frame();
    return frame;
}

// CAN 2.0B signal values for frame building
auto can20_signals() -> const std::vector<SignalValue>& {
    static const std::vector<SignalValue> values = {
        {.name = SignalName{"EngineSpeed"}, .value = PhysicalValue{Rational{2000, 1}}},
        {.name = SignalName{"EngineTemp"}, .value = PhysicalValue{Rational{90, 1}}},
    };
    return values;
}

// CAN-FD signal values for frame building
auto canfd_signals() -> const std::vector<SignalValue>& {
    static const std::vector<SignalValue> values = {
        {.name = SignalName{"GPSSpeed"}, .value = PhysicalValue{Rational{20, 1}}},
        {.name = SignalName{"YawRate"}, .value = PhysicalValue{Rational{}}},
        {.name = SignalName{"WheelSpeedFL"}, .value = PhysicalValue{Rational{10, 1}}},
        {.name = SignalName{"WheelSpeedFR"}, .value = PhysicalValue{Rational{10, 1}}},
    };
    return values;
}

// ---------------------------------------------------------------------------
// LTL properties
// ---------------------------------------------------------------------------

auto make_can20_properties() -> std::vector<LtlFormula> {
    std::vector<LtlFormula> props;
    props.push_back(ltl::always(ltl::atomic(ltl::between(
        SignalName{"EngineSpeed"}, PhysicalValue{Rational{}}, PhysicalValue{Rational{8000, 1}}))));
    props.push_back(ltl::always(
        ltl::atomic(ltl::between(SignalName{"EngineTemp"}, PhysicalValue{Rational{-40, 1}},
                                 PhysicalValue{Rational{215, 1}}))));
    return props;
}

auto make_canfd_properties() -> std::vector<LtlFormula> {
    std::vector<LtlFormula> props;
    props.push_back(ltl::always(ltl::atomic(ltl::between(
        SignalName{"GPSSpeed"}, PhysicalValue{Rational{}}, PhysicalValue{Rational{655, 1}}))));
    props.push_back(ltl::always(
        ltl::atomic(ltl::between(SignalName{"YawRate"}, PhysicalValue{Rational{-327, 1}},
                                 PhysicalValue{Rational{327, 1}}))));
    props.push_back(ltl::always(ltl::atomic(ltl::between(
        SignalName{"WheelSpeedFL"}, PhysicalValue{Rational{}}, PhysicalValue{Rational{655, 1}}))));
    return props;
}

} // namespace aletheia::bench
