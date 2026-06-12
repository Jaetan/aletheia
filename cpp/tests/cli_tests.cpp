// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// Functional tests for the C++ CLI (aletheia::run_cli) — the counterpart of
// go/cmd/aletheia/main_test.go. Each subcommand is exercised against a .dbc
// fixture through the real verified FFI core (never a stub); the suite skips
// when libaletheia-ffi.so is unavailable, mirroring the other integration
// tests. ALETHEIA_REPO_ROOT (fixtures) and ALETHEIA_LIB (the .so, consumed by
// run_cli's own resolver) are supplied by ctest via set_tests_properties.

#include <aletheia/cli.hpp>

#include <catch2/catch_test_macros.hpp>

#include <cstdlib>
#include <filesystem>
#include <stdexcept>
#include <string>
#include <vector>

namespace {

auto repo_root() -> std::filesystem::path {
    const char* env = std::getenv("ALETHEIA_REPO_ROOT");
    if (env == nullptr || *env == '\0') {
        throw std::runtime_error("ALETHEIA_REPO_ROOT env var not set (ctest sets it)");
    }
    return std::filesystem::path{env};
}

auto lib_available() -> bool {
    if (const char* env = std::getenv("ALETHEIA_LIB"); env != nullptr && *env != '\0') {
        return std::filesystem::exists(env);
    }
    return std::filesystem::exists(repo_root() / "build" / "libaletheia-ffi.so");
}

auto run(std::vector<std::string> args) -> int {
    return aletheia::run_cli(args);
}

} // namespace

TEST_CASE("CLI smoke over the real FFI core", "[cli]") {
    if (!lib_available()) {
        SKIP("libaletheia-ffi.so not found — run 'cabal run shake -- build' first");
    }
    const auto dbc = (repo_root() / "examples" / "example.dbc").string();
    CHECK(run({"validate", "--dbc", dbc}) == 0);
    CHECK(run({"validate", "--dbc", dbc, "--json"}) == 0);
    CHECK(run({"signals", "--dbc", dbc}) == 0);
    CHECK(run({"signals", "--dbc", dbc, "--json"}) == 0);
    CHECK(run({"format-dbc", "--dbc", dbc}) == 0);
    CHECK(run({"extract", "--dbc", dbc, "0x100", "102700000A000000"}) == 0);
    // A flag after positionals must still parse (Python argparse parity).
    CHECK(run({"extract", "--dbc", dbc, "0x100", "102700000A000000", "--json"}) == 0);
    const auto mux =
        (repo_root() / "python" / "tests" / "fixtures" / "dbc_corpus" / "multiplexing.dbc")
            .string();
    CHECK(run({"mux-query", "--dbc", mux, "0x64"}) == 0);
    CHECK(run({"mux-query", "--dbc", mux, "0x64", "--json"}) == 0);
    // Selector mode (--mux/--value) + its mismatch error — CoPilot PR #21 review.
    CHECK(run({"mux-query", "--dbc", mux, "0x64", "--mux", "Mode", "--value", "1"}) == 0);
    CHECK(run({"mux-query", "--dbc", mux, "0x64", "--mux", "Mode", "--value", "1", "--json"}) == 0);
    CHECK(run({"mux-query", "--dbc", mux, "0x64", "--mux", "Mode"}) == 2); // --value missing
}

TEST_CASE("CLI rejects unknown command, deferred check, and empty args", "[cli]") {
    // These fail before touching the FFI core, so they need no .so.
    CHECK(run({"check"}) == 2); // deferred — needs a verified CAN-log reader
    CHECK(run({"bogus"}) == 2);
    CHECK(run({}) == 2); // no subcommand
}
