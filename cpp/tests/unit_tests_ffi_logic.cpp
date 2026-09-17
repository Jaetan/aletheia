// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// Unit tests for the FfiBackend pure decision helpers (src/detail/ffi_logic.*).
//
// These exercise every branch of the RTS-init and FFI-error logic without a
// live shared library. The branches fire on process-global runtime state or on
// a non-zero return from the kernel, which is why they live in pure helpers
// rather than inline in the backend: here they are reachable. The error helper
// is driven with a record-only mock free function, the buffers being
// stack-allocated, so the mock records whether it was called and with what and
// never frees.

#include <catch2/catch_test_macros.hpp>

#include "detail/ffi_logic.hpp"
#include "detail/rts_params.hpp"

#include <aletheia/error.hpp>

#include <string>
#include <vector>

using namespace aletheia;

// AletheiaFreeStrFn is a C function pointer (void(*)(char*)); a capturing lambda
// cannot bind to it, so the mock is a free function over file-scope state.  It
// records the call but NEVER frees (the buffers below live on the stack).
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

TEST_CASE("ffi_error_from_status: non-zero status with message uses it and frees",
          "[ffi][logic][error]") {
    reset_free();
    std::string buf = "boom"; // mutable: buf.data() binds to char*
    auto err = detail::ffi_error_from_status(1, buf.data(), mock_free);
    REQUIRE(err.has_value());
    CHECK(err->kind() == ErrorKind::Protocol);
    // Kills the ternary `err_str != nullptr ? err_str : "Unknown error"` → `==`:
    // an == mutant would pick "Unknown error" even with a real message.
    CHECK(std::string{err->message()} == "boom");
    // Kills the free guard `err_str != nullptr` → `==`: an == mutant skips the free.
    CHECK(free_calls() == 1);
    CHECK(last_freed() == buf.data());
}

TEST_CASE("ffi_error_from_status: non-zero status without message falls back, frees nothing",
          "[ffi][logic][error]") {
    reset_free();
    auto err = detail::ffi_error_from_status(1, nullptr, mock_free);
    REQUIRE(err.has_value());
    CHECK(err->kind() == ErrorKind::Protocol);
    CHECK(std::string{err->message()} == "Unknown error");
    // Kills the free guard `err_str != nullptr` → `==`: an == mutant frees the null pointer.
    CHECK(free_calls() == 0);
}
