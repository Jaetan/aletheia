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
#include <nlohmann/json.hpp>

#include <cstdlib>
#include <filesystem>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "temp_path.hpp"

#include "repo_root.hpp"
#include "text_file.hpp"

using aletheia::test::repo_root;

using aletheia::test::TempPath;

using aletheia::test::read_text_file;

static auto lib_available() -> bool {
    if (const char* env = std::getenv("ALETHEIA_LIB"); env != nullptr && *env != '\0') {
        return std::filesystem::exists(env);
    }
    return std::filesystem::exists(repo_root() / "build" / "libaletheia-ffi.so");
}

static auto run(std::vector<std::string> args) -> int {
    return aletheia::run_cli(args);
}

// Run a subcommand capturing stdout, so a test can assert the emitted JSON
// shape (not just the exit code).
static auto run_capture(std::vector<std::string> args) -> std::pair<int, std::string> {
    std::ostringstream oss;
    auto* old = std::cout.rdbuf(oss.rdbuf());
    auto const code = aletheia::run_cli(std::move(args));
    std::cout.rdbuf(old);
    return {code, std::move(oss).str()};
}

// A DBC written into the temp directory for one test and removed by its own
// destructor, so no test repeats the removal by hand or leaves a file behind.

// An invalid DBC derived from the minimal.dbc fixture by renaming EngineTemp
// to EngineSpeed — a duplicate signal name, which the verified parser rejects
// with handler_validation_failed carrying the validation issues.
static auto duplicate_signal_dbc() -> std::string {
    auto const fixture =
        repo_root() / "python" / "tests" / "fixtures" / "dbc_corpus" / "minimal.dbc";
    auto text = read_text_file(fixture);
    auto const pos = text.find("EngineTemp");
    if (pos == std::string::npos) {
        throw std::runtime_error("minimal.dbc no longer contains EngineTemp");
    }
    text.replace(pos, std::string_view{"EngineTemp"}.size(), "EngineSpeed");
    return text;
}

TEST_CASE("CLI smoke over the real FFI core", "[cli]") {
    if (!lib_available()) {
        SKIP("libaletheia-ffi.so not found — run 'cabal run shake -- build' first");
    }
    auto const dbc = (repo_root() / "examples" / "example.dbc").string();
    CHECK(run({"validate", "--dbc", dbc}) == 0);
    CHECK(run({"validate", "--dbc", dbc, "--json"}) == 0);
    CHECK(run({"signals", "--dbc", dbc}) == 0);
    CHECK(run({"signals", "--dbc", dbc, "--json"}) == 0);
    CHECK(run({"format-dbc", "--dbc", dbc}) == 0);
    CHECK(run({"extract", "--dbc", dbc, "0x100", "102700000A000000"}) == 0);
    // A flag after positionals must still parse (Python argparse parity).
    CHECK(run({"extract", "--dbc", dbc, "0x100", "102700000A000000", "--json"}) == 0);
    auto const mux =
        (repo_root() / "python" / "tests" / "fixtures" / "dbc_corpus" / "multiplexing.dbc")
            .string();
    CHECK(run({"mux-query", "--dbc", mux, "0x64"}) == 0);
    CHECK(run({"mux-query", "--dbc", mux, "0x64", "--json"}) == 0);
    // Selector mode (--mux/--value), and --mux without --value is a usage error.
    CHECK(run({"mux-query", "--dbc", mux, "0x64", "--mux", "Mode", "--value", "1"}) == 0);
    CHECK(run({"mux-query", "--dbc", mux, "0x64", "--mux", "Mode", "--value", "1", "--json"}) == 0);
    CHECK(run({"mux-query", "--dbc", mux, "0x64", "--mux", "Mode"}) == 2); // --value missing
}

TEST_CASE("extract refuses a payload that is not a whole number of bytes", "[cli]") {
    if (!lib_available()) {
        SKIP("libaletheia-ffi.so not found — run 'cabal run shake -- build' first");
    }
    auto const dbc = (repo_root() / "examples" / "example.dbc").string();
    // The payload is read two hex digits at a time, so an odd digit count has
    // to be refused before the read: the last digit would otherwise be taken
    // for a byte of its own and a truncated frame would decode as a whole one.
    CHECK(run({"extract", "--dbc", dbc, "0x100", "102700000A00000"}) == 2);
    // The same payload one digit longer is a frame the core decodes.
    CHECK(run({"extract", "--dbc", dbc, "0x100", "102700000A000000"}) == 0);
}

TEST_CASE("extract --json renders signal values as exact rationals, never a lossy float", "[cli]") {
    if (!lib_available()) {
        SKIP("libaletheia-ffi.so not found — run 'cabal run shake -- build' first");
    }
    auto const dbc = (repo_root() / "examples" / "example.dbc").string();
    // EngineSpeed is 16-bit @ factor 0.25; raw 10001 (0x2711, little-endian) =
    // 10001/4 = 2500.25, a non-integer rational -> the exact
    // {"numerator","denominator"} object, never a lossy double like 2500.25.
    // EngineTemp (factor 1, raw 0, offset -40) = -40 -> a bare integer.  Parse
    // the JSON and assert the exact structure (a substring check could
    // false-positive on another field's text).
    auto [code, out] =
        run_capture({"extract", "--dbc", dbc, "0x100", "112700000A000000", "--json"});
    CHECK(code == 0);
    auto const parsed = nlohmann::json::parse(out);
    auto const& values = parsed.at("values");
    CHECK(values.at("EngineSpeed") == nlohmann::json({{"numerator", 10001}, {"denominator", 4}}));
    CHECK(values.at("EngineSpeed").is_object()); // exact rational, never a float
    CHECK(values.at("EngineTemp") == nlohmann::json(-40));
    CHECK(values.at("EngineTemp").is_number_integer()); // integer stays a bare int
}

TEST_CASE("signals text renders a fine-resolution factor exactly via format_rational", "[cli]") {
    if (!lib_available()) {
        SKIP("libaletheia-ffi.so not found — run 'cabal run shake -- build' first");
    }
    // factor 1/8192 = 0.0001220703125, which every digit of must survive the
    // render: a float64 path drops the tail. example.dbc has no such fine
    // factor, so the test writes its own.
    const TempPath dbc{"aletheia_fine_factor.dbc",
                       "VERSION \"\"\n\nNS_ :\n\nBS_:\n\nBU_:\n\n"
                       "BO_ 1024 FineMsg: 8 ECU4\n"
                       " SG_ FineSignal : 0|16@1+ (0.0001220703125,0) [0|8] \"x\" Vector__XXX\n"};
    auto [code, out] = run_capture({"signals", "--dbc", dbc.string()});
    CHECK(code == 0);
    CHECK(out.contains("x0.0001220703125"));
}

TEST_CASE("validate renders the issue list and exits 1 when the parser rejects the DBC", "[cli]") {
    if (!lib_available()) {
        SKIP("libaletheia-ffi.so not found — run 'cabal run shake -- build' first");
    }
    const TempPath dbc{"aletheia_duplicate_signal.dbc", duplicate_signal_dbc()};
    auto [code, out] = run_capture({"validate", "--dbc", dbc.string()});
    CHECK(code == 1);
    CHECK(out.contains("Validation FAILED"));
    CHECK(out.contains("[ERROR] duplicate_signal_name"));
    CHECK(out.contains("  1. ")); // the numbered issue list
}

TEST_CASE("validate --json emits the has_errors fail shape when the parser rejects the DBC",
          "[cli]") {
    if (!lib_available()) {
        SKIP("libaletheia-ffi.so not found — run 'cabal run shake -- build' first");
    }
    const TempPath dbc{"aletheia_duplicate_signal.dbc", duplicate_signal_dbc()};
    auto [code, out] = run_capture({"validate", "--dbc", dbc.string(), "--json"});
    // The exit code reflects the validation outcome in both output modes:
    // --json on a has_errors result exits 1 like text mode.
    CHECK(code == 1);
    auto const parsed = nlohmann::json::parse(out);
    CHECK(parsed.at("status") == "fail");
    CHECK(parsed.at("has_errors") == true);
    REQUIRE(!parsed.at("issues").empty());
    bool hit = false;
    for (auto const& issue : parsed.at("issues"))
        if (issue.at("code") == "duplicate_signal_name" && issue.at("severity") == "error")
            hit = true;
    CHECK(hit);
}

TEST_CASE("validate reports warnings from the single parse pass", "[cli]") {
    if (!lib_available()) {
        SKIP("libaletheia-ffi.so not found — run 'cabal run shake -- build' first");
    }
    // minimal.dbc parses clean but carries one benign offset_scale_range
    // warning. The kernel's parse epilogue IS full validation, so the parse
    // response's warnings are the complete issue list and must survive into
    // the success report — no validate_dbc round-trip to re-collect them.
    auto const dbc =
        (repo_root() / "python" / "tests" / "fixtures" / "dbc_corpus" / "minimal.dbc").string();
    auto [code, out] = run_capture({"validate", "--dbc", dbc});
    CHECK(code == 0);
    CHECK(out.contains("Validation passed with warnings"));
    CHECK(out.contains("offset_scale_range"));
}

TEST_CASE("rejected and unparseable DBCs stay fatal outside the validate report path", "[cli]") {
    if (!lib_available()) {
        SKIP("libaletheia-ffi.so not found — run 'cabal run shake -- build' first");
    }
    // Non-validate subcommands die with the stringified parse error.
    const TempPath dup{"aletheia_duplicate_signal.dbc", duplicate_signal_dbc()};
    CHECK(run({"signals", "--dbc", dup.string()}) == 2);
    // A syntactically unparseable DBC has no issues payload; validate keeps
    // the fatal-error path.
    const TempPath garbage{"aletheia_garbage.dbc", "this is not a dbc file\n"};
    CHECK(run({"validate", "--dbc", garbage.string()}) == 2);
}

TEST_CASE("CLI rejects unknown command, deferred check, and empty args", "[cli]") {
    // These fail before touching the FFI core, so they need no .so.
    CHECK(run({"check"}) == 2); // deferred — needs a verified CAN-log reader
    CHECK(run({"bogus"}) == 2);
    CHECK(run({}) == 2); // no subcommand
}
