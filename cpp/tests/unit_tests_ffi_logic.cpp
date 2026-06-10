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

#include <aletheia/error.hpp>

#include <cstdint>
#include <string>

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

TEST_CASE("rts_init_args: single-core requests yield no +RTS argv", "[ffi][logic][rts]") {
    // Kills `rts_cores > 1` → `>= 1`: a >= mutant would build argv at cores == 1.
    CHECK_FALSE(detail::rts_init_args(1).has_value());
    CHECK_FALSE(detail::rts_init_args(0).has_value());
}

TEST_CASE("rts_init_args: multi-core requests build +RTS -N<n> argv", "[ffi][logic][rts]") {
    // Kills `rts_cores > 1` → `<= 1`: a <= mutant would yield nullopt at cores == 4.
    auto four = detail::rts_init_args(4);
    REQUIRE(four.has_value());
    CHECK((*four)[0] == "aletheia");
    CHECK((*four)[1] == "+RTS");
    CHECK((*four)[2] == "-N4");
    CHECK((*four)[3] == "-RTS");

    auto two = detail::rts_init_args(2);
    REQUIRE(two.has_value());
    CHECK((*two)[2] == "-N2");
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
