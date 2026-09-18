// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// The decoders and the builders fill their containers one element at a time,
// and a container that grows can throw. These tests fail each allocation of a
// call in turn, so every one of those throws happens, and read the count of
// blocks the program holds afterwards: a cleanup path that drops what it owns
// leaves the count above where it started. Every name below is long enough to
// carry its characters on the heap, where a dropped string is a block and a
// short one would be invisible.
#include "alloc_fault.hpp"

#include <catch2/catch_test_macros.hpp>

#include "detail/ffi_logic.hpp"
#include "detail/json.hpp"
#include "detail/mock_backend.hpp"
#include <aletheia/aletheia.hpp>

#include <cstddef>
#include <cstdint>
#include <memory>
#include <new>
#include <stop_token>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

using aletheia::test::alloc_fault::Arm;
using aletheia::test::alloc_fault::live_blocks;
using aletheia::test::alloc_fault::sweep;

namespace {

constexpr std::string_view k_dbc_response = R"({
    "status": "success",
    "dbc": {
        "version": "an unusually long version string, longer than a short one",
        "messages": [{
            "id": 256, "name": "PowertrainStatusMessage", "dlc": 8,
            "sender": "EngineControlUnitNodeName", "extended": false,
            "senders": ["EngineControlUnitNodeName", "TransmissionControlNodeName"],
            "signals": [{
                "name": "EngineSpeedInRevolutionsPerMinute",
                "startBit": 0, "length": 16, "byteOrder": "little_endian",
                "signed": false, "factor": 1, "offset": 0,
                "minimum": 0, "maximum": 65535,
                "unit": "revolutions per minute", "presence": "always",
                "receivers": ["InstrumentClusterNodeName", "BodyControlModuleNodeName"],
                "valueDescriptions": [
                    {"value": 0, "description": "the engine is not turning over"},
                    {"value": 1, "description": "the engine is turning over"}
                ]
            }, {
                "name": "VehicleSpeedInKilometresPerHour",
                "startBit": 16, "length": 16, "byteOrder": "little_endian",
                "signed": false, "factor": 1, "offset": 0,
                "minimum": 0, "maximum": 65535,
                "unit": "kilometres per hour", "presence": "always",
                "receivers": ["InstrumentClusterNodeName"]
            }]
        }],
        "valueTables": [{
            "name": "TransmissionGearStateTable",
            "entries": [
                {"value": 0, "description": "the gear selector rests in park"},
                {"value": 1, "description": "the gear selector rests in reverse"}
            ]
        }],
        "attributes": [{
            "kind": "definition", "name": "TransmissionGearAttribute", "scope": "signal",
            "attrType": {"kind": "enum", "values": [
                "the gear selector rests in park",
                "the gear selector rests in reverse"
            ]}
        }],
        "unresolvedValueDescs": [{
            "id": 512, "extended": false, "signalName": "UnresolvedSignalNameOnTheWire",
            "entries": [
                {"value": 0, "description": "the description of the first entry"},
                {"value": 1, "description": "the description of the second entry"}
            ]
        }],
        "environmentVars": [], "nodes": [], "comments": [], "signalGroups": []
    }
})";

constexpr std::string_view k_extraction = R"({
    "status": "success",
    "values": [
        {"name": "EngineSpeedInRevolutionsPerMinute", "value": {"numerator": 3000, "denominator": 1}},
        {"name": "VehicleSpeedInKilometresPerHour", "value": {"numerator": 85, "denominator": 2}}
    ],
    "errors": [
        {"name": "CoolantTemperatureInDegreesCelsius",
         "reason": "the signal extends past the end of the frame this message carries"},
        {"name": "IntakeAirTemperatureInDegreesCelsius",
         "reason": "the multiplexor selects another signal for this frame"}
    ],
    "absent": ["FuelLevelAsAPercentageOfTankCapacity", "AmbientAirTemperatureInDegreesCelsius"]
})";

constexpr std::string_view k_property_batch = R"({
    "status": "success",
    "type": "property_batch",
    "results": [
        {"type": "property", "status": "holds", "property_index": 0},
        {"type": "property", "status": "fails", "property_index": 1, "timestamp": 3000000,
         "reason": "the speed rose above the bound the property names before the timer expired"}
    ]
})";

constexpr std::string_view k_stream_result = R"({
    "status": "complete",
    "results": [
        {"type": "property", "status": "holds", "property_index": 0},
        {"type": "property", "status": "unresolved", "property_index": 1,
         "reason": "the atomic predicate never resolved before the stream ended"}
    ],
    "warnings": [
        {"property_index": 0, "kind": "multiplexor_mirror",
         "detail": "the multiplexor this property reads is mirrored in another message"},
        {"property_index": 1, "kind": "multiplexor_mirror",
         "detail": "the multiplexor this property reads is mirrored in another message"}
    ]
})";

} // namespace

// Sweeps `call` twice and reports the allocation points it covered and what
// the block count did over the second sweep. The first settles whatever the
// call reaches for once and keeps, which a single sweep would read as a block
// the call lost; anything a cleanup path drops is dropped again on the second.
namespace {
struct SweepResult {
    std::int64_t points;
    std::int64_t held;
};
} // namespace

[[nodiscard]] static auto measure(auto call) -> SweepResult {
    static_cast<void>(sweep(call));
    auto const before = live_blocks();
    auto const points = sweep(call);
    return {.points = points, .held = live_blocks() - before};
}

// Fails each allocation of `call` in turn and asserts it released everything.
static void expect_balanced(auto call) {
    auto const result = measure(call);
    CHECK(result.points > 0);
    CHECK(result.held == 0);
}

TEST_CASE("the allocation-fault harness fails the allocation it arms", "[alloc_fault]") {
    // Nothing that reports goes inside the armed scope: an assertion macro
    // allocates its own message, and the arm would spend itself on that.
    bool refused = false;
    bool fired = false;
    std::size_t produced = 0;
    {
        const Arm arm{1};
        try {
            // A call the compiler cannot see through, so the allocation it
            // makes is one it cannot elide.
            produced = aletheia::detail::rts_init_args(4, "").size();
        } catch (const std::bad_alloc&) {
            refused = true;
        }
        fired = arm.fired();
    }
    CHECK(refused);
    CHECK(fired);
    CHECK(produced == 0);
}

TEST_CASE("the block count rises with a block held and falls with it released", "[alloc_fault]") {
    // Read the count into locals first: an assertion between two readings
    // allocates its own message and would be counted.
    auto const before = live_blocks();
    const auto* held = new std::string(64, 'x'); // NOLINT(cppcoreguidelines-owning-memory)
    auto const holding = live_blocks();
    delete held; // NOLINT(cppcoreguidelines-owning-memory)
    auto const released = live_blocks();
    CHECK(holding > before);
    CHECK(released == before);
}

TEST_CASE("the sweep reads a cleanup path that drops what it holds", "[alloc_fault]") {
    // A loop that owns its strings through raw pointers drops every one it has
    // taken so far when the container it is filling throws, which is the shape
    // the sweep exists to catch. The strings are registered as they are made,
    // so the test releases afterwards what the dropped cleanup did not.
    std::vector<const std::string*> registry;
    auto const drops_what_it_holds = [&registry] {
        std::vector<const std::string*> owned;
        for (int i = 0; i < 8; ++i) {
            const auto* one = new std::string(64, 'x'); // NOLINT(cppcoreguidelines-owning-memory)
            registry.push_back(one);
            owned.push_back(one);
        }
        for (const auto* one : owned)
            delete one; // NOLINT(cppcoreguidelines-owning-memory)
        registry.clear();
    };

    auto const result = measure(drops_what_it_holds);
    CHECK(result.points > 0);
    CHECK(result.held > 0);

    for (const auto* one : registry)
        delete one; // NOLINT(cppcoreguidelines-owning-memory)
}

TEST_CASE("the DBC response decoder releases its temporaries when an allocation fails",
          "[alloc_fault][json]") {
    REQUIRE(aletheia::detail::parse_dbc_response(k_dbc_response).has_value());
    expect_balanced([] { return aletheia::detail::parse_dbc_response(k_dbc_response); });
}

TEST_CASE("the extraction decoder releases its temporaries when an allocation fails",
          "[alloc_fault][json]") {
    REQUIRE(aletheia::detail::parse_extraction(k_extraction).has_value());
    expect_balanced([] { return aletheia::detail::parse_extraction(k_extraction); });
}

TEST_CASE("the frame response decoder releases its temporaries when an allocation fails",
          "[alloc_fault][json]") {
    REQUIRE(aletheia::detail::parse_frame_response(k_property_batch).has_value());
    expect_balanced([] { return aletheia::detail::parse_frame_response(k_property_batch); });
}

TEST_CASE("the stream result decoder releases its temporaries when an allocation fails",
          "[alloc_fault][json]") {
    REQUIRE(aletheia::detail::parse_stream_result(k_stream_result).has_value());
    expect_balanced([] { return aletheia::detail::parse_stream_result(k_stream_result); });
}

TEST_CASE("the DBC command encoder releases its temporaries when an allocation fails",
          "[alloc_fault][json]") {
    auto const parsed = aletheia::detail::parse_dbc_response(k_dbc_response);
    REQUIRE(parsed.has_value());
    auto const& dbc = *parsed;
    expect_balanced([&dbc] { return aletheia::detail::serialize_parse_dbc(dbc); });
}

TEST_CASE("the runtime argument builder releases its temporaries when an allocation fails",
          "[alloc_fault][ffi]") {
    expect_balanced([] { return aletheia::detail::rts_init_args(4, "-s -A64m --nonmoving-gc"); });
}

TEST_CASE("the check builder releases its temporaries when an allocation fails",
          "[alloc_fault][check]") {
    // The client and its backend are built inside the call, so each run owns
    // everything it makes and the count is answerable at the end of it.
    expect_balanced([] {
        auto mock = std::make_unique<aletheia::MockBackend>();
        mock->queue_response(R"({"status": "success"})");
        aletheia::AletheiaClient client(std::move(mock));
        std::vector<aletheia::CheckResult> checks;
        checks.push_back(aletheia::check::signal("EngineSpeedInRevolutionsPerMinute")
                             .never_exceeds(aletheia::PhysicalValue{aletheia::Rational{6000, 1}}));
        checks.push_back(aletheia::check::signal("VehicleSpeedInKilometresPerHour")
                             .stays_between(aletheia::PhysicalValue{aletheia::Rational{0, 1}},
                                            aletheia::PhysicalValue{aletheia::Rational{220, 1}}));
        return client.add_checks(std::stop_token{}, std::move(checks));
    });
}
