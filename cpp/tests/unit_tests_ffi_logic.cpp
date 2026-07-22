// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// Unit tests for the FfiBackend pure decision helpers (src/detail/ffi_logic.*).
//
// These exercise every branch of the RTS-init and FFI-error logic without a
// live dlopen'd libaletheia-ffi.so — the branches that, inline in FfiBackend,
// fire only on process-global hs_init state or a non-zero Haskell return and so
// were never observed by the test suite.  The FFI error helper is driven with a
// record-only mock free-function: the err_str buffers are stack-allocated, so
// the mock records *whether* it was called (and with what) and never frees.

#include <catch2/catch_test_macros.hpp>

#include "detail/ffi_logic.hpp"
#include "detail/rts_params.hpp"

#include <aletheia/error.hpp>

#include <cstdint>
#include <string>
#include <vector>

using namespace aletheia;

namespace {

// AletheiaFreeStrFn is a C function pointer (void(*)(char*)); a capturing lambda
// cannot bind to it, so the mock is a free function over file-scope state.  It
// records the call but NEVER frees (the buffers below live on the stack).
int g_free_calls = 0;
char* g_last_freed = nullptr;

void mock_free(char* p) {
    ++g_free_calls;
    g_last_freed = p;
}

void reset_free() {
    g_free_calls = 0;
    g_last_freed = nullptr;
}

} // namespace

// --- rts_init_args ---------------------------------------------------------

TEST_CASE("rts_init_args: the heap cap is ALWAYS present, single-core adds no -N",
          "[ffi][logic][rts]") {
    const std::string cap{detail::rts_heap_cap_flag};
    // Kills `rts_cores > rts_default_cores` → `>=`: a >= mutant would inject -N
    // at the default core count.  The cap must be present regardless.
    const auto one = detail::rts_init_args(1, "");
    CHECK(one == std::vector<std::string>{"aletheia", "+RTS", cap, "-RTS"});
    const auto zero = detail::rts_init_args(0, "");
    CHECK(zero == std::vector<std::string>{"aletheia", "+RTS", cap, "-RTS"});
}

TEST_CASE("rts_init_args: multi-core requests append -N<n> after the cap", "[ffi][logic][rts]") {
    const std::string cap{detail::rts_heap_cap_flag};
    // Kills `rts_cores > rts_default_cores` → `<=`: a <= mutant would omit -N at cores == 4.
    const auto four = detail::rts_init_args(4, "");
    CHECK(four == std::vector<std::string>{"aletheia", "+RTS", cap, "-N4", "-RTS"});
    const auto two = detail::rts_init_args(2, "");
    CHECK(two == std::vector<std::string>{"aletheia", "+RTS", cap, "-N2", "-RTS"});
}

TEST_CASE("rts_init_args: ALETHEIA_RTS_OPTS flags land after the cap (so a caller -M wins)",
          "[ffi][logic][rts]") {
    const std::string cap{detail::rts_heap_cap_flag};
    // Override flags are whitespace-split and appended after the cap and any
    // -N, before the closing -RTS — so a caller -M occurs LAST and wins.
    const auto over = detail::rts_init_args(1, "  -M12M   -hT ");
    CHECK(over == std::vector<std::string>{"aletheia", "+RTS", cap, "-M12M", "-hT", "-RTS"});
    // With multi-core: cap, -N, then override.
    const auto both = detail::rts_init_args(2, "-M64M");
    CHECK(both == std::vector<std::string>{"aletheia", "+RTS", cap, "-N2", "-M64M", "-RTS"});
    // Empty / whitespace-only override adds nothing.
    const auto empty = detail::rts_init_args(1, "   ");
    CHECK(empty == std::vector<std::string>{"aletheia", "+RTS", cap, "-RTS"});
}

// --- rts_cores_mismatch ----------------------------------------------------

TEST_CASE("rts_cores_mismatch: matching cores yield no mismatch", "[ffi][logic][rts]") {
    // Kills `requested != active` → `==`: an == mutant would report a mismatch when equal.
    CHECK_FALSE(detail::rts_cores_mismatch(4, 4).has_value());
    CHECK_FALSE(detail::rts_cores_mismatch(1, 1).has_value());
}

TEST_CASE("rts_cores_mismatch: differing cores report {active, requested}", "[ffi][logic][rts]") {
    // requested = 4, active = 1 (the renderer-first downgrade case).
    auto mismatch = detail::rts_cores_mismatch(4, 1);
    REQUIRE(mismatch.has_value());
    CHECK(mismatch->first == 1);  // active
    CHECK(mismatch->second == 4); // requested
}

// --- ffi_error_from_status -------------------------------------------------

TEST_CASE("ffi_error_from_status: status 0 is success, frees nothing", "[ffi][logic][error]") {
    // Kills `status != 0` → `==`: an == mutant would treat success as an error.
    reset_free();
    auto err = detail::ffi_error_from_status(0, nullptr, mock_free);
    CHECK_FALSE(err.has_value());
    CHECK(g_free_calls == 0);
}

TEST_CASE("ffi_error_from_status: non-zero status with message uses it and frees",
          "[ffi][logic][error]") {
    reset_free();
    char buf[] = "boom"; // mutable: binds to char* (a string literal would not)
    auto err = detail::ffi_error_from_status(1, buf, mock_free);
    REQUIRE(err.has_value());
    CHECK(err->kind() == ErrorKind::Protocol);
    // Kills the ternary `err_str != nullptr ? err_str : "Unknown error"` → `==`:
    // an == mutant would pick "Unknown error" even with a real message.
    CHECK(std::string{err->message()} == "boom");
    // Kills the free guard `err_str != nullptr` → `==`: an == mutant skips the free.
    CHECK(g_free_calls == 1);
    CHECK(g_last_freed == buf);
}

TEST_CASE("ffi_error_from_status: non-zero status without message falls back, frees nothing",
          "[ffi][logic][error]") {
    reset_free();
    auto err = detail::ffi_error_from_status(1, nullptr, mock_free);
    REQUIRE(err.has_value());
    CHECK(err->kind() == ErrorKind::Protocol);
    CHECK(std::string{err->message()} == "Unknown error");
    // Kills the free guard `err_str != nullptr` → `==`: an == mutant frees the null pointer.
    CHECK(g_free_calls == 0);
}
