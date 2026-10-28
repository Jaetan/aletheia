// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// The DBC most integration tests load, and the test for a warning of one code
// among the issues a validation reports.

#include <aletheia/dbc.hpp>
#include <aletheia/types.hpp>
#include <aletheia/validation_issue.hpp>

#include <algorithm>
#include <vector>

namespace aletheia::test {

// ---------------------------------------------------------------------------
// Test DBC for integration tests
// ---------------------------------------------------------------------------

inline auto make_integration_dbc() -> DbcDefinition {
    auto const speed_id = StandardId::create(0x100).value();
    auto const speed_dlc = Dlc::create(8).value();

    DbcSignal const speed_sig{
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

    DbcSignal const rpm_sig{
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

inline auto has_warning(std::vector<ValidationIssue> const& issues, IssueCode code) -> bool {
    return std::ranges::any_of(issues, [code](ValidationIssue const& issue) {
        return issue.code == code && issue.severity == IssueSeverity::Warning;
    });
}

} // namespace aletheia::test
