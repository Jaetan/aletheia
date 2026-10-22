// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// Functional tests for the C++ CLI (aletheia::run_cli) — the counterpart of
// go/cmd/aletheia/main_test.go. Each subcommand but template is exercised
// against a .dbc fixture through the real verified FFI core (never a stub),
// and those cases skip when libaletheia-ffi.so is unavailable, mirroring the
// other integration tests; template writes through the Excel loader and needs
// no library. ALETHEIA_REPO_ROOT (fixtures) and ALETHEIA_LIB (the .so, consumed by
// run_cli's own resolver) are supplied by ctest via set_tests_properties.

#include <aletheia/cli.hpp>
#include <aletheia/excel.hpp>

#include <catch2/catch_message.hpp>
#include <catch2/catch_test_macros.hpp>
#include <nlohmann/json.hpp>

#include <array>
#include <cerrno>
#include <cstdint>
#include <cstdlib>
#include <filesystem>
#include <ios>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <streambuf>
#include <string>
#include <string_view>
#include <system_error>
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

// The same, capturing stderr, so a test can assert the error line itself.
static auto run_capture_err(std::vector<std::string> args) -> std::pair<int, std::string> {
    std::ostringstream oss;
    auto* old = std::cerr.rdbuf(oss.rdbuf());
    auto const code = aletheia::run_cli(std::move(args));
    std::cerr.rdbuf(old);
    return {code, std::move(oss).str()};
}

namespace {

// Where stdout at /dev/full refuses a report: at the write for a report larger
// than the stream's buffer, at the flush for one it holds whole.
enum class Refusal : std::uint8_t { AtWrite, AtFlush };

// A stream buffer refusing as a full device does, setting errno to ENOSPC, at
// the write or only at the flush.
class FullDeviceBuf : public std::streambuf {
public:
    explicit FullDeviceBuf(Refusal where) : where_{where} {}

protected:
    auto overflow(int_type ch) -> int_type override {
        if (where_ == Refusal::AtFlush)
            return traits_type::not_eof(ch);
        errno = ENOSPC;
        return traits_type::eof();
    }
    auto sync() -> int override {
        errno = ENOSPC;
        return -1;
    }

private:
    Refusal where_;
};

// Both places a full device refuses a report.
constexpr std::array k_refusals{Refusal::AtWrite, Refusal::AtFlush};

} // namespace

// Run a subcommand with stdout on a full device refusing at `where`, capturing
// stderr.
static auto run_unwritable(std::vector<std::string> args, Refusal where)
    -> std::pair<int, std::string> {
    FullDeviceBuf full{where};
    std::ostringstream err;
    auto* old_out = std::cout.rdbuf(&full);
    auto* old_err = std::cerr.rdbuf(err.rdbuf());
    auto const code = aletheia::run_cli(std::move(args));
    std::cerr.rdbuf(old_err);
    std::cout.rdbuf(old_out);
    return {code, std::move(err).str()};
}

// The line a report that cannot be written exits with on a full device.
static auto unwritable_line() -> std::string {
    return "Error: writing the report: " + std::generic_category().message(ENOSPC) + "\n";
}

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
    auto const [code, out] =
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
    // factor, so the test writes its own, its maximum the most the sixteen bits
    // carry, 65535/8192.
    const TempPath dbc{
        "aletheia_fine_factor.dbc",
        "VERSION \"\"\n\nNS_ :\n\nBS_:\n\nBU_:\n\n"
        "BO_ 1024 FineMsg: 8 ECU4\n"
        " SG_ FineSignal : 0|16@1+ (0.0001220703125,0) [0|7.9998779296875] \"x\" Vector__XXX\n"};
    auto const [code, out] = run_capture({"signals", "--dbc", dbc.string()});
    CHECK(code == 0);
    CHECK(out.contains("x0.0001220703125"));
}

TEST_CASE("validate renders the issue list and exits 1 when the parser rejects the DBC", "[cli]") {
    if (!lib_available()) {
        SKIP("libaletheia-ffi.so not found — run 'cabal run shake -- build' first");
    }
    const TempPath dbc{"aletheia_duplicate_signal.dbc", duplicate_signal_dbc()};
    auto const [code, out] = run_capture({"validate", "--dbc", dbc.string()});
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
    auto const [code, out] = run_capture({"validate", "--dbc", dbc.string(), "--json"});
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
    auto const [code, out] = run_capture({"validate", "--dbc", dbc});
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

TEST_CASE("each text report prints its lines exactly", "[cli]") {
    if (!lib_available()) {
        SKIP("libaletheia-ffi.so not found: run 'cabal run shake -- build' first");
    }
    auto const dbc = (repo_root() / "examples" / "example.dbc").string();
    auto const mux =
        (repo_root() / "python" / "tests" / "fixtures" / "dbc_corpus" / "multiplexing.dbc")
            .string();
    const std::string header = "VERSION \"\"\n\nNS_ :\n\nBS_:\n\nBU_:\n\n";
    const TempPath clean{"aletheia_cli_clean.dbc",
                         header + "BO_ 256 Clean: 1 ECU\n"
                                  " SG_ Level : 0|8@1+ (1,0) [0|255] \"%\" Vector__XXX\n"};
    // Every value Small's bits carry above 100 is out of bounds, so a frame of
    // 0xFF decodes no value and one error.
    const TempPath narrow{"aletheia_cli_narrow.dbc",
                          header + "BO_ 512 Narrow: 1 ECU\n"
                                   " SG_ Small : 0|8@1+ (1,0) [0|100] \"\" Vector__XXX\n"};
    const TempPath dup{"aletheia_cli_text_duplicate.dbc", duplicate_signal_dbc()};
    struct Row {
        std::vector<std::string> args;
        std::string text;
        int code = 0;
    };
    const std::vector<Row> rows{
        {.args = {"validate", "--dbc", clean.string()},
         .text = "Validation passed: no issues found\n"},
        {.args = {"validate", "--dbc", dbc},
         .text =
             "Validation passed with warnings (2 issues)\n\n"
             "  1. [WARNING] offset_scale_range: Message 'EngineStatus', signal 'EngineSpeed': its "
             "bits carry values above the declared maximum\n"
             "  2. [WARNING] offset_scale_range: Message 'SteeringData', signal 'SteeringAngle': "
             "its bits carry values above the declared maximum\n"},
        {.args = {"validate", "--dbc", dup.string()},
         .text =
             "Validation FAILED (2 issues)\n\n"
             "  1. [ERROR] duplicate_signal_name: Message 'EngineStatus': duplicate signal name "
             "'EngineSpeed'\n"
             "  2. [WARNING] offset_scale_range: Message 'EngineStatus', signal 'EngineSpeed': its "
             "bits carry values above the declared maximum\n",
         .code = 1},
        {.args = {"extract", "--dbc", dbc, "0x100", "102700000A000000"},
         .text = "CAN ID 0x100 (EngineStatus):\n\n  EngineSpeed = 2500\n  EngineTemp = -40\n"},
        {.args = {"extract", "--dbc", narrow.string(), "0x200", "FF"},
         .text = "CAN ID 0x200 (Narrow):\n\n  (no signals)\n"
                 "  error Small: value out of bounds: 255 not in [0, 100]\n"},
        {.args = {"signals", "--dbc", clean.string()},
         .text = "Message 0x100 Clean\n  Level bits[0:8] LE unsigned x1 0 %\n\n"
                 "1 messages, 1 signals\n"},
        {.args = {"mux-query", "--dbc", mux, "0x64"},
         .text = "Message 0x64 BasicMux (DLC 8)\n  Mode:\n"
                 "    value 0: 3 signals (Mode, PayloadA, CommonCounter)\n"
                 "    value 1: 3 signals (Mode, PayloadB, CommonCounter)\n"
                 "    value 2: 3 signals (Mode, PayloadC, CommonCounter)\n"},
        {.args = {"mux-query", "--dbc", dbc, "0x100"},
         .text = "Message 0x100 EngineStatus (DLC 8)\n"
                 "  Not multiplexed: all 2 signals are always present.\n"},
        {.args = {"mux-query", "--dbc", mux, "0x64", "--mux", "Mode", "--value", "1"},
         .text = "Message 0x64 BasicMux (DLC 8)\nMultiplexor Mode = 1: 3 signals present\n"
                 "  Mode\n  PayloadB\n  CommonCounter\n"},
    };
    for (auto const& row : rows) {
        CAPTURE(row.args);
        auto const [code, out] = run_capture(row.args);
        CHECK(code == row.code);
        CHECK(out == row.text);
    }
}

TEST_CASE("a report that cannot be written exits 2 naming the reason", "[cli]") {
    if (!lib_available()) {
        SKIP("libaletheia-ffi.so not found: run 'cabal run shake -- build' first");
    }
    auto const dbc = (repo_root() / "examples" / "example.dbc").string();
    auto const mux =
        (repo_root() / "python" / "tests" / "fixtures" / "dbc_corpus" / "multiplexing.dbc")
            .string();
    // The duplicate-signal rows exit 1 when their report is written, so they
    // show a failed write outranks the validation outcome.
    const TempPath dup{"aletheia_duplicate_signal.dbc", duplicate_signal_dbc()};
    const std::vector<std::vector<std::string>> reports{
        {"validate", "--dbc", dbc},
        {"validate", "--dbc", dbc, "--json"},
        {"validate", "--dbc", dup.string()},
        {"validate", "--dbc", dup.string(), "--json"},
        {"signals", "--dbc", dbc},
        {"signals", "--dbc", dbc, "--json"},
        {"format-dbc", "--dbc", dbc},
        {"extract", "--dbc", dbc, "0x100", "102700000A000000"},
        {"extract", "--dbc", dbc, "0x100", "102700000A000000", "--json"},
        {"mux-query", "--dbc", dbc, "0x100"},
        {"mux-query", "--dbc", mux, "0x64"},
        {"mux-query", "--dbc", mux, "0x64", "--json"},
        {"mux-query", "--dbc", mux, "0x64", "--mux", "Mode", "--value", "1"},
        {"mux-query", "--dbc", mux, "0x64", "--mux", "Mode", "--value", "1", "--json"},
    };
    for (auto const& args : reports) {
        for (auto const where : k_refusals) {
            CAPTURE(args, where == Refusal::AtWrite);
            auto const [code, err] = run_unwritable(args, where);
            CHECK(code == 2);
            CHECK(err == unwritable_line());
        }
    }
}

TEST_CASE("a subcommand refuses a positional it does not take", "[cli]") {
    // The refusal comes before any DBC is read, so it needs no .so, and a DBC
    // path that resolves nowhere is still refused for its stray.
    auto const dbc = (repo_root() / "examples" / "example.dbc").string();
    auto const missing = (repo_root() / "examples" / "missing.dbc").string();
    const std::vector<std::pair<std::vector<std::string>, std::string>> rows{
        {{"validate", "--dbc", dbc, "stray"}, "Error: unrecognized arguments: stray\n"},
        {{"validate", "stray", "--dbc", dbc, "--json"}, "Error: unrecognized arguments: stray\n"},
        {{"validate", "--dbc", missing, "stray"}, "Error: unrecognized arguments: stray\n"},
        {{"signals", "--dbc", dbc, "stray"}, "Error: unrecognized arguments: stray\n"},
        {{"format-dbc", "--dbc", dbc, "a", "b"}, "Error: unrecognized arguments: a b\n"},
    };
    for (auto const& [args, line] : rows) {
        CAPTURE(args);
        auto const [code, err] = run_capture_err(args);
        CHECK(code == 2);
        CHECK(err == line);
    }
}

TEST_CASE("a subcommand that takes a fixed count names its extras apart from a shortfall",
          "[cli]") {
    // Both refusals come before any DBC is read or any workbook written, so
    // they need no .so and a DBC path that resolves nowhere is refused for its
    // count.
    auto const missing = (repo_root() / "examples" / "missing.dbc").string();
    const TempPath book{"aletheia_cli_template_extra.xlsx"};
    const std::vector<std::pair<std::vector<std::string>, std::string>> rows{
        {{"extract", "--dbc", missing, "0x100", "102700000A000000", "stray"},
         "Error: unrecognized arguments: stray\n"},
        {{"extract", "--dbc", missing, "0x100", "102700000A000000", "a", "--json", "b"},
         "Error: unrecognized arguments: a b\n"},
        {{"mux-query", "--dbc", missing, "0x100", "stray"},
         "Error: unrecognized arguments: stray\n"},
        {{"mux-query", "--dbc", missing, "--", "0x100", "--json"},
         "Error: unrecognized arguments: --json\n"},
        {{"template", book.string(), "stray"}, "Error: unrecognized arguments: stray\n"},
        {{"extract", "--dbc", missing, "0x100"},
         "Error: extract requires <can_id> <data> positional arguments\n"},
        {{"mux-query", "--dbc", missing},
         "Error: mux-query requires a <message> positional argument (CAN ID or name)\n"},
        {{"template"}, "Error: template requires one <path> positional argument\n"},
    };
    for (auto const& [args, line] : rows) {
        CAPTURE(args);
        auto const [code, err] = run_capture_err(args);
        CHECK(code == 2);
        CHECK(err == line);
    }
    CHECK_FALSE(std::filesystem::exists(book.path));
}

TEST_CASE("a positional after -- is taken", "[cli]") {
    if (!lib_available()) {
        SKIP("libaletheia-ffi.so not found: run 'cabal run shake -- build' first");
    }
    auto const mux =
        (repo_root() / "python" / "tests" / "fixtures" / "dbc_corpus" / "multiplexing.dbc")
            .string();
    auto const escaped = run_capture({"mux-query", "--dbc", mux, "--", "0x64"});
    CHECK(escaped.first == 0);
    CHECK(escaped == run_capture({"mux-query", "--dbc", mux, "0x64"}));
}

TEST_CASE("a value flag before -- is still read", "[cli]") {
    if (!lib_available()) {
        SKIP("libaletheia-ffi.so not found: run 'cabal run shake -- build' first");
    }
    auto const mux =
        (repo_root() / "python" / "tests" / "fixtures" / "dbc_corpus" / "multiplexing.dbc")
            .string();
    auto const escaped =
        run_capture({"mux-query", "--dbc", mux, "--mux", "Mode", "--value", "1", "--", "0x64"});
    CHECK(escaped.first == 0);
    CHECK(escaped ==
          run_capture({"mux-query", "--dbc", mux, "--mux", "Mode", "--value", "1", "0x64"}));
}

TEST_CASE("a token after -- spelled like a flag is a stray positional", "[cli]") {
    // The refusal comes before any DBC is read, so it needs no .so.
    auto const dbc = (repo_root() / "examples" / "example.dbc").string();
    const std::vector<std::pair<std::vector<std::string>, std::string>> rows{
        {{"validate", "--dbc", dbc, "--", "--json"}, "Error: unrecognized arguments: --json\n"},
        {{"validate", "--", "--dbc", dbc}, "Error: unrecognized arguments: --dbc " + dbc + "\n"},
    };
    for (auto const& [args, line] : rows) {
        CAPTURE(args);
        auto const [code, err] = run_capture_err(args);
        CHECK(code == 2);
        CHECK(err == line);
    }
}

TEST_CASE("CLI rejects unknown command, deferred check, and empty args", "[cli]") {
    // These fail before touching the FFI core, so they need no .so.
    CHECK(run({"check"}) == 2); // deferred — needs a verified CAN-log reader
    CHECK(run({"bogus"}) == 2);
    CHECK(run({}) == 2); // no subcommand
}

TEST_CASE("template writes the workbook the Excel loaders read", "[cli][template]") {
    // Writing the workbook goes through the binding's loader module, not the core.
    const TempPath out{"aletheia_cli_template.xlsx"};
    auto const [code, text] = run_capture({"template", out.string()});
    CHECK(code == 0);
    CHECK(text == "Template written to " + out.string() + "\n");
    auto const checks = aletheia::load_checks_from_excel(out.path);
    REQUIRE(checks.has_value());
    CHECK(checks->empty());
    // The DBC sheet is there with its header row and nothing under it.
    auto const dbc = aletheia::load_dbc_from_excel(out.path);
    REQUIRE_FALSE(dbc.has_value());
    CHECK(dbc.error().message() == "DBC sheet has no data rows");
}

TEST_CASE("template refuses a path that exists and leaves it as it was", "[cli][template]") {
    const TempPath existing{"aletheia_cli_template_existing.xlsx", "not a workbook\n"};
    auto const [code, err] = run_capture_err({"template", existing.string()});
    CHECK(code == 2);
    CHECK(err == "Error: File already exists: " + existing.string() + "\n");
    CHECK(read_text_file(existing.path) == "not a workbook\n");
}

TEST_CASE("template exits 2 on a missing parent and on a wrong argument count", "[cli][template]") {
    const TempPath parent{"aletheia_cli_template_missing_parent"};
    auto const target = parent.path / "checks.xlsx";
    CHECK(run({"template", target.string()}) == 2);
    CHECK_FALSE(std::filesystem::exists(parent.path));
    CHECK(run({"template"}) == 2);
    CHECK(run({"template", "--json", "a.xlsx"}) == 2);
    CHECK_FALSE(std::filesystem::exists("a.xlsx"));
}

TEST_CASE("template takes its path after --, which is not a positional itself", "[cli][template]") {
    const TempPath out{"aletheia_cli_template_escaped.xlsx"};
    auto const [code, text] = run_capture({"template", "--", out.string()});
    CHECK(code == 0);
    CHECK(text == "Template written to " + out.string() + "\n");
    CHECK(std::filesystem::exists(out.path));
}

TEST_CASE("template whose confirmation cannot be written exits 2 naming the reason",
          "[cli][template]") {
    for (auto const where : k_refusals) {
        CAPTURE(where == Refusal::AtWrite);
        const TempPath out{"aletheia_cli_template_unreported.xlsx"};
        auto const [code, err] = run_unwritable({"template", out.string()}, where);
        CHECK(code == 2);
        CHECK(err == unwritable_line());
    }
}

TEST_CASE("a report on a stream that failed before it names the stream's error",
          "[cli][template]") {
    // A stream already failed takes nothing and sets no errno, so the reason
    // is the stream's own, never an errno an earlier call left behind.
    const TempPath out{"aletheia_cli_template_failed_stream.xlsx"};
    std::cout.setstate(std::ios_base::badbit);
    errno = EACCES;
    auto const [code, err] = run_capture_err({"template", out.string()});
    std::cout.clear();
    CHECK(code == 2);
    CHECK(err == "Error: writing the report: " +
                     std::make_error_code(std::io_errc::stream).message() + "\n");
}

TEST_CASE("the CLI's logger writes WARNING-level events to its stream and nothing below",
          "[cli][log]") {
    std::ostringstream out;
    auto const logger = aletheia::cli_logger(out);
    logger.info("dbc.parsed", {{"messages", std::uint64_t{1}}});
    logger.warn("cache.full", {{"size", std::uint64_t{256}}});
    logger.warn("extraction.parse_failed",
                {{"canId", std::uint64_t{256}}, {"error", std::string_view{"bad frame"}}});
    CHECK(out.str() == "cache.full size=256\nextraction.parse_failed canId=256 error=bad frame\n");
}

// No Warn event carries a boolean, so a debug event's fields stand in.
TEST_CASE("the CLI's logger writes a boolean field as true or false", "[cli][log]") {
    std::ostringstream out;
    auto const logger = aletheia::cli_logger(out);
    logger.warn("frame.processed", {{"canId", std::uint64_t{256}}, {"extended", false}});
    logger.warn("frame.processed", {{"canId", std::uint64_t{0x1FFFFFFF}}, {"extended", true}});
    CHECK(out.str() == "frame.processed canId=256 extended=false\n"
                       "frame.processed canId=536870911 extended=true\n");
}
