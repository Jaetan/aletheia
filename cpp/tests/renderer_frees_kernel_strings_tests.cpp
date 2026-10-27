// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// The rational renderer releases every string the kernel hands it: a render,
// and a decimal parse's refusal. A process of its own, because the renderer
// calls the library the runtime started on, which happens once per process,
// and the one library whose releases can be read is the recording kernel,
// which counts them; the suite that shares a process with the real library
// cannot point the renderer at it. For the same reason the allocation count is
// read here, the recording kernel being the library this process's runtime
// started on, and a client's diagnostics are built here, the recording kernel
// rendering every value but the numerator it refuses.

#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>

#include <aletheia/aletheia.hpp>
#include <aletheia/detail/checked.hpp>
#include <aletheia/detail/rational_renderer.hpp>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <dlfcn.h>
#include <filesystem>
#include <memory>
#include <ranges>
#include <stop_token>
#include <string>
#include <utility>
#include <vector>

#include "detail/mock_backend.hpp"
#include "loaded_library.hpp"
#include "required.hpp"

using aletheia::test::required;

TEST_CASE("the renderer frees the strings the kernel hands it", "[rational_renderer]") {
    // A backend on the stand-in starts the runtime on it, its runtime entry a
    // no-op, so the renderer calls the stand-in.
    const std::filesystem::path stand_in{ALETHEIA_TEST_RECORDING_KERNEL};
    auto const backend = required(aletheia::make_ffi_backend(stand_in));
    const aletheia::test::LoadedLibrary handle{dlopen(stand_in.c_str(), RTLD_NOW | RTLD_NOLOAD)};
    REQUIRE(handle != nullptr);
    using CountFn = int (*)();
    // NOLINTNEXTLINE(cppcoreguidelines-pro-type-reinterpret-cast)
    auto* const frees = reinterpret_cast<CountFn>(dlsym(handle.get(), "aletheia_test_free_count"));
    REQUIRE(frees != nullptr);

    auto before = frees();
    CHECK(aletheia::detail::format_rational_ffi(22, 7) == "22/7");
    CHECK(frees() == before + 1);

    before = frees();
    // The runtime is up, so the answer is the kernel's: the stand-in's refusal.
    auto const parsed = aletheia::detail::parse_decimal_ffi("1.5");
    REQUIRE(parsed.has_value());
    REQUIRE_FALSE(parsed->has_value());
    CHECK_THAT(parsed->error(), Catch::Matchers::ContainsSubstring("parse_decimal"));
    CHECK(frees() == before + 1);
}

TEST_CASE("properties whose diagnostic is refused leave none of the last ones", "[client]") {
    // The first properties render; the second carry the numerator the stand-in
    // refuses, so their diagnostic fails after the kernel accepted them. The
    // client then holds no diagnostic: a violation of property 0 finds none,
    // rather than the first properties'.
    auto const backend =
        required(aletheia::make_ffi_backend(std::filesystem::path{ALETHEIA_TEST_RECORDING_KERNEL}));
    auto mock = std::make_unique<aletheia::MockBackend>();
    // Two set_properties and the start of the stream are accepted.
    std::ranges::for_each(std::views::repeat(std::string{R"({"status": "success"})"}, 3),
                          [&mock](const std::string& accepted) { mock->queue_response(accepted); });
    mock->queue_response(R"({"type": "property_batch", "results": [{"status": "fails",)"
                         R"( "type": "property", "property_index": 0, "timestamp": 1000,)"
                         R"( "reason": "core"}]})");
    auto client = required(aletheia::AletheiaClient::create(std::move(mock)));
    auto const bounded_by = [](std::int64_t bound) {
        std::vector<aletheia::LtlFormula> properties;
        properties.push_back(aletheia::ltl::always(aletheia::ltl::atomic(aletheia::ltl::less_than(
            aletheia::SignalName{"Speed"},
            aletheia::PhysicalValue{aletheia::Rational::integer(bound)}))));
        return properties;
    };
    REQUIRE(client.set_properties(std::stop_token{}, bounded_by(220)).has_value());
    auto const refused = client.set_properties(std::stop_token{}, bounded_by(7919));
    CHECK(aletheia::detail::error_of(refused).kind() == aletheia::ErrorKind::Ffi);
    CHECK(aletheia::detail::error_of(refused).text() ==
          "aletheia_format_rational returned a null pointer");
    REQUIRE(client.start_stream(std::stop_token{}).has_value());
    auto const id = aletheia::CanId{aletheia::StandardId::create(0x100).value()};
    const aletheia::FramePayload data(8, std::byte{0});
    auto const sent = client.send_frame(std::stop_token{}, aletheia::Timestamp{1000}, id,
                                        aletheia::Dlc::create(8).value(), data);
    REQUIRE(sent.has_value());
    auto const& batch = std::get<aletheia::PropertyBatch>(*sent);
    REQUIRE(batch.results.size() == 1);
    CHECK_FALSE(batch.results.front().enrichment.has_value());
}

TEST_CASE("a violation whose observed value is refused keeps its frame and names the formula alone",
          "[client]") {
    // The property renders, so its diagnostic is built; the value the violating
    // frame carries is the numerator the stand-in refuses, so the reason falls
    // back to the formula and the frame's answer stands.
    auto const backend =
        required(aletheia::make_ffi_backend(std::filesystem::path{ALETHEIA_TEST_RECORDING_KERNEL}));
    auto mock = std::make_unique<aletheia::MockBackend>();
    // set_properties and the start of the stream are accepted.
    std::ranges::for_each(std::views::repeat(std::string{R"({"status": "success"})"}, 2),
                          [&mock](const std::string& accepted) { mock->queue_response(accepted); });
    mock->queue_response(R"({"type": "property_batch", "results": [{"status": "fails",)"
                         R"( "type": "property", "property_index": 0, "timestamp": 1000,)"
                         R"( "reason": "core"}]})");
    mock->queue_response(R"({"status": "success", "values": [{"name": "Speed", "value": 7919}],)"
                         R"( "errors": [], "absent": []})");
    auto client = required(aletheia::AletheiaClient::create(std::move(mock)));
    std::vector<aletheia::LtlFormula> properties;
    properties.push_back(aletheia::ltl::always(aletheia::ltl::atomic(
        aletheia::ltl::less_than(aletheia::SignalName{"Speed"},
                                 aletheia::PhysicalValue{aletheia::Rational::integer(220)}))));
    REQUIRE(client.set_properties(std::stop_token{}, properties).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());
    auto const id = aletheia::CanId{aletheia::StandardId::create(0x100).value()};
    const aletheia::FramePayload data(8, std::byte{0});
    auto const sent = client.send_frame(std::stop_token{}, aletheia::Timestamp{1000}, id,
                                        aletheia::Dlc::create(8).value(), data);
    REQUIRE(sent.has_value());
    auto const& batch = std::get<aletheia::PropertyBatch>(*sent);
    REQUIRE(batch.results.size() == 1);
    auto const& enrichment = batch.results.front().enrichment;
    REQUIRE(enrichment.has_value());
    CHECK(enrichment->enriched_reason == "violated: " + enrichment->formula_desc + " [core: core]");
    CHECK(enrichment->signals.at(aletheia::SignalName{"Speed"}) ==
          aletheia::PhysicalValue{aletheia::Rational::integer(7919)});
}

TEST_CASE("the allocation count comes back whole from the library that started the runtime",
          "[ffi]") {
    // The recording kernel answers its count with 2^63 plus the reads made
    // before, and nothing in this process reads it earlier, so the reads give
    // 2^63 and then one more only when each reached the entry and all 64 bits
    // came back: a read that keeps fewer bits reads another number. Every
    // backend this process makes is on the stand-in, so it is the one the
    // runtime started on.
    auto const backend =
        required(aletheia::make_ffi_backend(std::filesystem::path{ALETHEIA_TEST_RECORDING_KERNEL}));
    auto const first = aletheia::allocated_bytes();
    auto const second = aletheia::allocated_bytes();
    REQUIRE(first.has_value());
    REQUIRE(second.has_value());
    CHECK(first.value() == (std::uint64_t{1} << 63U));
    CHECK(second.value() == (std::uint64_t{1} << 63U) + 1);
}
