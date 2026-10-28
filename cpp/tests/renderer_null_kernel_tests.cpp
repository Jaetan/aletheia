// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// A library that answers the decimal entry with failure and no error envelope
// is a wire fault, a Protocol error as in every binding, and one that renders
// a null string an Ffi error. The null kernel the build makes beside the
// library answers both so, and answers its allocation count with zero, which
// the binding hands on as it came. A process of its own,
// because the runtime starts once per process, and the parser and the count
// read the library it started on; for the same reason the backend that
// started it is the first to register its path for the search.

#include <catch2/catch_test_macros.hpp>

#include <aletheia/aletheia.hpp>
#include <aletheia/detail/checked.hpp>
#include <aletheia/detail/rational_renderer.hpp>

#include <cstdint>
#include <filesystem>
#include <optional>
#include <string>
#include <string_view>
#include <utility>

#include "required.hpp"

using aletheia::test::required;

TEST_CASE("a decimal failure without an envelope is a protocol error", "[rational_renderer]") {
    // A backend on the stand-in starts the runtime on it, its runtime entry a
    // no-op, so the parser calls the stand-in.
    std::filesystem::path const stand_in{ALETHEIA_TEST_NULL_KERNEL};
    auto const backend = required(aletheia::make_ffi_backend(stand_in));
    REQUIRE(backend != nullptr);
    auto const parsed = aletheia::Rational::from_decimal("1");
    REQUIRE_FALSE(parsed.has_value());
    CHECK(parsed.error().kind() == aletheia::ErrorKind::Protocol);
    CHECK(parsed.error().code() == aletheia::ErrorCode::Unknown);
    CHECK(parsed.error().text() == "aletheia_parse_decimal failed without an error");
}

TEST_CASE("a render the kernel answers with a null string is an Ffi error", "[rational_renderer]") {
    // The stand-in renders every rational as a null string, so the renderer and
    // a check's description answer the null return, never a fabricated text.
    auto const backend =
        required(aletheia::make_ffi_backend(std::filesystem::path{ALETHEIA_TEST_NULL_KERNEL}));
    auto const check =
        aletheia::check::signal("Speed").never_exceeds(aletheia::PhysicalValue::of(1, 2));
    for (auto const& rendered :
         {aletheia::detail::format_rational_ffi(1, 2), check.condition_desc()}) {
        REQUIRE_FALSE(rendered.has_value());
        CHECK(rendered.error().kind() == aletheia::ErrorKind::Ffi);
        CHECK(rendered.error().text() == "aletheia_format_rational returned a null pointer");
    }
}

TEST_CASE("each text endpoint's null answer is a protocol error, and no state refuses a client",
          "[ffi]") {
    // The stand-in hands out no state and answers every text entry with a null
    // string: each endpoint returns the Protocol error naming its entry, and a
    // client over the backend is refused.
    auto backend =
        required(aletheia::make_ffi_backend(std::filesystem::path{ALETHEIA_TEST_NULL_KERNEL}));
    auto const state = required(backend->init());
    CHECK_FALSE(state);
    auto const id = aletheia::CanId{aletheia::StandardId::create(0x100).value()};
    auto const dlc = aletheia::Dlc::create(0).value();
    auto const ts = aletheia::Timestamp{0};
    auto const refused = [](aletheia::Result<std::string> const& answer, std::string_view text) {
        CHECK(aletheia::detail::error_of(answer).kind() == aletheia::ErrorKind::Protocol);
        CHECK(aletheia::detail::error_of(answer).message() == text);
    };
    refused(backend->process(state, "{}"), "aletheia_process returned null");
    refused(backend->send_frame_binary(state, ts, id, dlc, {}, std::nullopt, std::nullopt),
            "aletheia_send_frame returned null");
    refused(backend->send_error_binary(state, ts), "aletheia_send_error returned null");
    refused(backend->send_remote_binary(state, ts, id), "aletheia_send_remote returned null");
    refused(backend->start_stream_binary(state), "aletheia_start_stream returned null");
    refused(backend->end_stream_binary(state), "aletheia_end_stream returned null");
    refused(backend->format_dbc_binary(state), "aletheia_format_dbc returned null");
    refused(backend->extract_signals_binary(state, id, dlc, {}),
            "aletheia_extract_signals returned null");
    auto const client = aletheia::AletheiaClient::create(std::move(backend));
    CHECK(aletheia::detail::error_of(client).kind() == aletheia::ErrorKind::Ffi);
    CHECK(aletheia::detail::error_of(client).message() == "backend init() returned null state");
}

TEST_CASE("a backend that starts the runtime registers its library for the search", "[ffi]") {
    // Nothing else in this process registers a path before the backend above,
    // and with the variable unset the registered path is the search's first
    // answer, ahead of the build directories around the working directory.
    std::filesystem::path const stand_in{ALETHEIA_TEST_NULL_KERNEL};
    auto const backend = required(aletheia::make_ffi_backend(stand_in));
    REQUIRE(::unsetenv("ALETHEIA_LIB") == 0);
    CHECK(required(aletheia::find_ffi_library()) == stand_in);
}

TEST_CASE("the allocation count is the kernel's answer, zero included", "[ffi]") {
    auto const backend =
        required(aletheia::make_ffi_backend(std::filesystem::path{ALETHEIA_TEST_NULL_KERNEL}));
    CHECK(aletheia::allocated_bytes() == std::optional<std::uint64_t>{0});
}
