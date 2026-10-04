// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// Unit tests for the FfiBackend pure decision helpers (src/detail/ffi_logic.*).
//
// These exercise every branch of the RTS-init and FFI-error logic without a
// live shared library. The branches fire on process-global runtime state or on
// a non-zero return from the kernel, which is why they live in pure helpers
// rather than inline in the backend: here they are reachable. The error helper
// is driven with a record-only mock free function, the buffers being the
// test's own strings, so the mock records whether it was called and with what
// and never frees.

#include <catch2/catch_test_macros.hpp>

#include "detail/ffi_abi.hpp"
#include "detail/ffi_logic.hpp"
#include "detail/rts_params.hpp"

#include <aletheia/error.hpp>

#include <aletheia/limits.hpp>
#include <aletheia/types.hpp>
#include <cstddef>
#include <cstdint>

#include <string>
#include <string_view>
#include <vector>

using namespace aletheia;

// AletheiaFreeStrFn is a C function pointer (void(*)(char*)); a capturing lambda
// cannot bind to it, so the mock is a free function over file-scope state.  It
// records the call but NEVER frees (the buffers below are the tests' own).
static auto free_calls() -> int& {
    static int calls = 0;
    return calls;
}

static auto last_freed() -> char*& {
    static char* freed = nullptr;
    return freed;
}

static void mock_free(char* p) {
    ++free_calls();
    last_freed() = p;
}

static void reset_free() {
    free_calls() = 0;
    last_freed() = nullptr;
}

// --- rts_init_args ---------------------------------------------------------

TEST_CASE("rts_init_args: the heap cap is ALWAYS present, single-core adds no -N",
          "[ffi][logic][rts]") {
    const std::string cap{detail::rts_heap_cap_flag};
    // Kills `rts_cores > rts_default_cores` → `>=`: a >= mutant would inject -N
    // at the default core count.  The cap must be present regardless.
    auto const one = detail::rts_init_args(1, "");
    CHECK(one == std::vector<std::string>{"aletheia", "+RTS", cap, "-RTS"});
    auto const zero = detail::rts_init_args(0, "");
    CHECK(zero == std::vector<std::string>{"aletheia", "+RTS", cap, "-RTS"});
}

TEST_CASE("rts_init_args: multi-core requests append -N<n> after the cap", "[ffi][logic][rts]") {
    const std::string cap{detail::rts_heap_cap_flag};
    // Kills `rts_cores > rts_default_cores` → `<=`: a <= mutant would omit -N at cores == 4.
    auto const four = detail::rts_init_args(4, "");
    CHECK(four == std::vector<std::string>{"aletheia", "+RTS", cap, "-N4", "-RTS"});
    auto const two = detail::rts_init_args(2, "");
    CHECK(two == std::vector<std::string>{"aletheia", "+RTS", cap, "-N2", "-RTS"});
}

TEST_CASE("rts_init_args: ALETHEIA_RTS_OPTS flags land after the cap (so a caller -M wins)",
          "[ffi][logic][rts]") {
    const std::string cap{detail::rts_heap_cap_flag};
    // Override flags are whitespace-split and appended after the cap and any
    // -N, before the closing -RTS — so a caller -M occurs LAST and wins.
    auto const over = detail::rts_init_args(1, "  -M12M   -hT ");
    CHECK(over == std::vector<std::string>{"aletheia", "+RTS", cap, "-M12M", "-hT", "-RTS"});
    // With multi-core: cap, -N, then override.
    auto const both = detail::rts_init_args(2, "-M64M");
    CHECK(both == std::vector<std::string>{"aletheia", "+RTS", cap, "-N2", "-M64M", "-RTS"});
    // Empty / whitespace-only override adds nothing.
    auto const empty = detail::rts_init_args(1, "   ");
    CHECK(empty == std::vector<std::string>{"aletheia", "+RTS", cap, "-RTS"});
}

// --- rts_cores_mismatch ----------------------------------------------------

TEST_CASE("rts_cores_mismatch: matching cores yield no mismatch", "[ffi][logic][rts]") {
    // Kills `requested != active` → `==`: an == mutant would report a mismatch when equal.
    CHECK_FALSE(detail::rts_cores_mismatch(4, 4).has_value());
    CHECK_FALSE(detail::rts_cores_mismatch(1, 1).has_value());
}

TEST_CASE("rts_cores_mismatch: differing cores report {active, requested}", "[ffi][logic][rts]") {
    // A second backend asks for four cores where one is already running.
    auto mismatch = detail::rts_cores_mismatch(4, 1);
    REQUIRE(mismatch.has_value());
    CHECK(mismatch->first == 1);  // active
    CHECK(mismatch->second == 4); // requested
}

// --- ffi_error_from_status -------------------------------------------------

TEST_CASE("ffi_error_from_status: status 0 is success, frees nothing", "[ffi][logic][error]") {
    // Kills `status != 0` → `==`: an == mutant would treat success as an error.
    reset_free();
    auto const err = detail::ffi_error_from_status(0, nullptr, mock_free);
    CHECK_FALSE(err.has_value());
    CHECK(free_calls() == 0);
}

TEST_CASE("ffi_error_from_status: non-zero status decodes the envelope's code and message, frees",
          "[ffi][logic][error]") {
    reset_free();
    // mutable: buf.data() binds to char*
    std::string buf =
        R"({"status": "error", "code": "handler_no_dbc", "message": "no DBC loaded"})";
    auto err = detail::ffi_error_from_status(1, buf.data(), mock_free);
    REQUIRE(err.has_value());
    CHECK(err->kind() == ErrorKind::Protocol);
    CHECK(err->code() == ErrorCode::HandlerNoDbc);
    // The message is the envelope's, not the envelope, and not the fallback a
    // null message reads as.
    CHECK(std::string{err->message()} == "no DBC loaded");
    // The envelope is released once, after it is decoded.
    CHECK(free_calls() == 1);
    CHECK(last_freed() == buf.data());
}

TEST_CASE("ffi_error_from_status: the shim's own refusal keeps its message under no known code",
          "[ffi][logic][error]") {
    // The shim's refusals carry a code the kernel's vocabulary does not hold,
    // which decodes as the JSON path decodes it.
    reset_free();
    std::string buf = R"({"status":"error","code":"ffi_validation_error",)"
                      R"("message":"aletheia_build_frame_bin: null out buffer"})";
    auto err = detail::ffi_error_from_status(1, buf.data(), mock_free);
    REQUIRE(err.has_value());
    CHECK(err->kind() == ErrorKind::Protocol);
    CHECK(err->code() == ErrorCode::Unknown);
    CHECK(std::string{err->message()} == "aletheia_build_frame_bin: null out buffer");
    CHECK(free_calls() == 1);
}

TEST_CASE("ffi_error_from_status: an input-bound envelope carries its kind and its triple",
          "[ffi][logic][error]") {
    reset_free();
    std::string buf = R"({"status":"error","code":"input_bound_exceeded",)"
                      R"("message":"array cardinality 2000 exceeds limit 1024",)"
                      R"("bound_kind":"array_cardinality","observed":2000,"limit":1024})";
    auto err = detail::ffi_error_from_status(1, buf.data(), mock_free);
    REQUIRE(err.has_value());
    CHECK(err->kind() == ErrorKind::InputBoundExceeded);
    CHECK(err->code() == ErrorCode::InputBoundExceeded);
    REQUIRE(err->bound_info().has_value());
    CHECK(err->bound_info()->bound_kind == "array_cardinality");
    CHECK(err->bound_info()->observed == 2000);
    CHECK(err->bound_info()->limit == 1024);
    CHECK(free_calls() == 1);
}

TEST_CASE("ffi_error_from_status: an error that is not an error envelope is a protocol fault",
          "[ffi][logic][error]") {
    reset_free();
    SECTION("text that does not parse") {
        std::string buf = "boom";
        auto err = detail::ffi_error_from_status(1, buf.data(), mock_free);
        REQUIRE(err.has_value());
        CHECK(err->kind() == ErrorKind::Protocol);
        CHECK(err->code() == ErrorCode::Unknown);
        CHECK(std::string_view{err->message()}.starts_with("Malformed error envelope boom: "));
        CHECK(free_calls() == 1);
    }
    SECTION("an envelope whose status is not error") {
        std::string buf = R"({"status":"success","code":"handler_no_dbc","message":"m"})";
        auto err = detail::ffi_error_from_status(1, buf.data(), mock_free);
        REQUIRE(err.has_value());
        CHECK(err->kind() == ErrorKind::Protocol);
        CHECK(err->code() == ErrorCode::Unknown);
        CHECK(std::string{err->message()} == "Error envelope without status \"error\": " + buf);
        CHECK(free_calls() == 1);
    }
    SECTION("an envelope without its message") {
        std::string buf = R"({"status":"error","code":"handler_no_dbc"})";
        auto err = detail::ffi_error_from_status(1, buf.data(), mock_free);
        REQUIRE(err.has_value());
        CHECK(err->kind() == ErrorKind::Protocol);
        CHECK(err->code() == ErrorCode::Unknown);
        CHECK(std::string{err->message()} ==
              "Error response missing or non-string 'message' field");
        CHECK(free_calls() == 1);
    }
}

TEST_CASE("ffi_error_from_status: non-zero status without message falls back, frees nothing",
          "[ffi][logic][error]") {
    reset_free();
    auto err = detail::ffi_error_from_status(1, nullptr, mock_free);
    REQUIRE(err.has_value());
    CHECK(err->kind() == ErrorKind::Protocol);
    CHECK(std::string{err->message()} == "Unknown error");
    // A null envelope is never decoded and never reaches the deleter.
    CHECK(free_calls() == 0);
}

TEST_CASE("json_input_bound_error admits the cap and refuses one byte more, by the wire's words",
          "[ffi][logic][bounds]") {
    CHECK_FALSE(detail::json_input_bound_error(max_json_bytes).has_value());
    auto const refusal = detail::json_input_bound_error(max_json_bytes + 1);
    REQUIRE(refusal.has_value());
    CHECK(*refusal == R"({"status":"error","code":"input_bound_exceeded",)"
                      R"("message":"input length (bytes) 67108865 exceeds limit 67108864",)"
                      R"("bound_kind":"input_length_bytes","observed":67108865,"limit":67108864})");
}

TEST_CASE("wire_count_refusal admits the wire's width and refuses one past it, by count alone",
          "[ffi][logic][bounds]") {
    constexpr auto width = std::size_t{1} << 32U;
    CHECK_FALSE(detail::wire_count_refusal(width - 1).has_value());
    auto const refusal = detail::wire_count_refusal(width);
    REQUIRE(refusal.has_value());
    CHECK(*refusal ==
          "signal injection carries 4294967296 values, more than the wire's count holds");
}

TEST_CASE("abi_version_refusal admits the backend's version and names any other", "[ffi][logic]") {
    CHECK_FALSE(detail::abi_version_refusal(detail::abi_version).has_value());
    auto const newer = detail::abi_version_refusal(detail::abi_version + 1);
    REQUIRE(newer.has_value());
    CHECK(*newer == "the library implements ABI version " +
                        std::to_string(detail::abi_version + 1) + ", and this binding needs " +
                        std::to_string(detail::abi_version));
    CHECK(detail::abi_version_refusal(detail::abi_version - 1).has_value());
}

TEST_CASE("decimal_value builds over a positive denominator and refuses any other",
          "[ffi][logic]") {
    CHECK(detail::decimal_value(3, 1) == Rational{3, 1});
    for (auto const denominator : {std::int64_t{0}, std::int64_t{-1}}) {
        try {
            static_cast<void>(detail::decimal_value(1, denominator));
            FAIL("decimal_value admitted the denominator " << denominator);
        } catch (const AletheiaException& e) {
            CHECK(e.kind() == ErrorKind::Protocol);
            CHECK(std::string_view{e.what()} ==
                  "aletheia_parse_decimal answered a non-positive denominator " +
                      std::to_string(denominator));
        }
    }
}
