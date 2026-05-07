// SPDX-License-Identifier: Apache-2.0
//
// Track D.1 doc-example harness — C++ Catch2 mirror of Python's
// `pytest --markdown-docs` (python/tests/test_doc_examples_harness.py +
// repo-root conftest.py) and Go's TestDocExamples
// (go/aletheia/doc_examples_test.go).
//
// Every ```cpp fence in the tracked user-facing markdown files is
// extracted, wrapped, compiled by ${CMAKE_CXX_COMPILER}, and executed
// end-to-end. A failing fence (compile or runtime) is a test failure
// reported with `file:Lline` precision. Non-runnable fences (signature
// sketches, illustrative pseudocode referencing undefined symbols)
// must use the `text` info string — TestNoNotestCppFences enforces
// the escape-hatch ban, paralleling the Go rule.
//
// Path substitutions (parallel python/conftest.py loader fakes):
//
//   "/opt/aletheia/lib/libaletheia-ffi.so" → resolved libaletheia-ffi.so
//   "checks.yaml"                          → testdata/doc_examples/checks.yaml
//   "checks.xlsx" / "tests.xlsx"           → examples/demo/demo_workbook.xlsx
//
// Wrapper shapes (head check on the first non-blank/non-comment line):
//
//   A. Already declares `int main(`              → use verbatim
//   B. Has #include or import-block decls only   → append stub `int main()`
//   C. Body fragment (statements/expressions)    → wrap in synthesized main
//      with predeclared globals (`backend`, `client`, `ts`, `can_id`, `dlc`,
//      `data_storage`, `data`, `frames`, `dbc`) under `using namespace aletheia;`.
//
// Skipped automatically when `libaletheia-ffi.so` is not findable.

#include <array>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <filesystem>
#include <fstream>
#include <regex>
#include <sstream>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include <unistd.h>

#include <catch2/catch_test_macros.hpp>

namespace fs = std::filesystem;

namespace {

// Tracked markdown files (mirror Go/Python lists).
constexpr std::array<std::string_view, 5> kDocFiles = {
    "README.md",
    "docs/PITCH.md",
    "docs/architecture/CANCELLATION.md",
    "docs/reference/INTERFACES.md",
    "docs/development/DISTRIBUTION.md",
};

struct CppFence {
    std::string file;    // repo-relative path
    int line;            // 1-based line number of opening ```cpp
    std::string content; // body between fences (no surrounding ``` lines)

    [[nodiscard]] auto display() const -> std::string { return file + ":L" + std::to_string(line); }
};

auto repo_root() -> fs::path {
    return fs::path{ALETHEIA_REPO_ROOT};
}

// findFFILib mirrors the Go harness's findFFILibForDocs.
auto find_ffi_lib() -> std::string {
    if (auto* env = std::getenv("ALETHEIA_LIB"); env != nullptr && env[0] != '\0') {
        if (fs::exists(env))
            return env;
    }
    constexpr std::array<std::string_view, 3> candidates = {
        "build/libaletheia-ffi.so",
        "../build/libaletheia-ffi.so",
        "../../build/libaletheia-ffi.so",
    };
    for (auto rel : candidates) {
        auto p = repo_root() / rel;
        if (fs::exists(p))
            return fs::weakly_canonical(p).string();
    }
    return {};
}

auto strip_left(std::string_view s) -> std::string_view {
    while (!s.empty() && (s.front() == ' ' || s.front() == '\t')) {
        s.remove_prefix(1);
    }
    return s;
}

auto strip_right(std::string_view s) -> std::string_view {
    while (!s.empty() && (s.back() == ' ' || s.back() == '\t' || s.back() == '\r')) {
        s.remove_suffix(1);
    }
    return s;
}

// Extracts every ```cpp fence from one markdown file.
auto extract_cpp_fences(const fs::path& abs_path, std::string_view rel_path)
    -> std::vector<CppFence> {
    std::ifstream in(abs_path);
    if (!in) {
        FAIL("read failed: " << abs_path);
    }
    std::vector<CppFence> fences;
    std::string line;
    int lineno = 0;
    bool in_fence = false;
    int fence_start = 0;
    std::string body;
    while (std::getline(in, line)) {
        ++lineno;
        auto trim = strip_left(line);
        if (!in_fence) {
            // Opening fence: ```cpp possibly followed by space/info-string.
            if (trim.starts_with("```cpp")) {
                auto rest = trim.substr(6);
                if (rest.empty() || rest.front() == ' ' || rest.front() == '\t') {
                    in_fence = true;
                    fence_start = lineno;
                    body.clear();
                }
            }
            continue;
        }
        // Inside a fence — closing line is exactly ``` after trim.
        if (strip_right(strip_left(line)) == "```") {
            fences.push_back({std::string{rel_path}, fence_start, body});
            in_fence = false;
            continue;
        }
        body.append(line).append("\n");
    }
    if (in_fence) {
        FAIL("unterminated ```cpp fence at " << rel_path << " line " << fence_start);
    }
    return fences;
}

// Substitute hardcoded doc paths to fixture paths (mirror the Go harness).
auto substitute_paths(std::string body, const std::string& lib_path, const std::string& yaml_fix,
                      const std::string& excel_fix) -> std::string {
    auto replace_all = [](std::string& s, std::string_view from, std::string_view to) {
        std::size_t pos = 0;
        while ((pos = s.find(from, pos)) != std::string::npos) {
            s.replace(pos, from.size(), to);
            pos += to.size();
        }
    };
    auto quote = [](std::string_view s) { return std::string("\"") + std::string(s) + "\""; };
    replace_all(body, R"("/opt/aletheia/lib/libaletheia-ffi.so")", quote(lib_path));
    replace_all(body, R"("checks.yaml")", quote(yaml_fix));
    replace_all(body, R"("checks.xlsx")", quote(excel_fix));
    replace_all(body, R"("tests.xlsx")", quote(excel_fix));
    return body;
}

// Heuristic: does the body contain a top-level `int main(` declaration?
auto has_main(std::string_view body) -> bool {
    static const std::regex main_re(
        R"((^|\n)\s*(?:\[\[[^\]]+\]\]\s*)?(?:static\s+|inline\s+|constexpr\s+)?int\s+main\s*\()");
    return std::regex_search(body.cbegin(), body.cend(), main_re);
}

// Heuristic: does the body contain a #include directive?
auto has_include(std::string_view body) -> bool {
    static const std::regex inc_re(R"((^|\n)\s*#\s*include\b)");
    return std::regex_search(body.cbegin(), body.cend(), inc_re);
}

// Body-fragment wrapper: matches the Go harness's _make_globals dict.
//
// Predeclared globals:
//   - libPath        : string, ALETHEIA_LIB env var
//   - backend        : std::unique_ptr<aletheia::IBackend> (FFI)
//   - client         : aletheia::AletheiaClient (parsed against an in-memory DBC)
//   - ts             : aletheia::Timestamp
//   - can_id, canID  : aletheia::CanId (StandardId{0x100})
//   - dlc            : aletheia::Dlc{8}
//   - data_storage   : std::vector<std::byte>(8)
//   - data           : std::span<const std::byte> over data_storage
//   - frames         : std::vector<aletheia::Frame>
//   - dbc            : aletheia::DbcDefinition (the in-memory DBC parsed into client)
//
// `using namespace aletheia;` keeps doc snippets idiomatic.
auto wrap_body_fragment(std::string body) -> std::string {
    constexpr std::string_view kPrologue =
        R"CPP(// Auto-generated wrapper — Track D.1 doc-example harness.
#include <chrono>
#include <cstddef>
#include <cstdlib>
#include <iostream>
#include <memory>
#include <span>
#include <stop_token>
#include <utility>
#include <variant>
#include <vector>

#include <aletheia/backend.hpp>
#include <aletheia/check.hpp>
#include <aletheia/client.hpp>
#include <aletheia/dbc.hpp>
#include <aletheia/error.hpp>
#include <aletheia/excel.hpp>
#include <aletheia/log.hpp>
#include <aletheia/ltl.hpp>
#include <aletheia/types.hpp>
#include <aletheia/yaml.hpp>

using namespace aletheia;

namespace doc_harness_detail {

inline auto build_doc_dbc() -> DbcDefinition {
    auto rat = [](std::int64_t n, std::int64_t d) {
        return Rational{n, d};
    };
    auto signal_def = [&](std::string_view name, std::uint16_t start_bit,
                          std::uint8_t bit_length, std::int64_t max_val) {
        return DbcSignal{
            .name = SignalName{std::string(name)},
            .start_bit = BitPosition{start_bit},
            .bit_length = BitLength{bit_length},
            .byte_order = ByteOrder::LittleEndian,
            .is_signed = false,
            .factor = RationalFactor{rat(1, 1)},
            .offset = RationalOffset{rat(0, 1)},
            .minimum = RationalBound{rat(0, 1)},
            .maximum = RationalBound{rat(max_val, 1)},
            .unit = Unit{""},
            .presence = AlwaysPresent{},
            .receivers = {},
        };
    };

    DbcMessage vehicle_state{
        .id = StandardId::create(0x100).value(),
        .name = MessageName{"VehicleState"},
        .dlc = Dlc::create(8).value(),
        .sender = NodeName{"ECU"},
        .senders = {},
        .signals = {
            signal_def("VehicleSpeed", 0, 16, 65535),
            signal_def("Speed", 16, 16, 65535),
            signal_def("BrakePedal", 32, 8, 255),
            signal_def("EngineRPM", 40, 8, 255),
            signal_def("FaultCode", 48, 8, 255),
            signal_def("ParkingBrake", 56, 1, 1),
        },
    };
    DbcMessage voltages{
        .id = StandardId::create(0x110).value(),
        .name = MessageName{"Voltages"},
        .dlc = Dlc::create(8).value(),
        .sender = NodeName{"BMS"},
        .senders = {},
        .signals = {
            signal_def("Voltage", 0, 16, 65535),
            signal_def("BatteryVoltage", 16, 16, 65535),
            signal_def("CoolantTemp", 32, 8, 255),
        },
    };
    return DbcDefinition{
        .version = "1.0",
        .messages = {std::move(vehicle_state), std::move(voltages)},
    };
}

} // namespace doc_harness_detail

int main() {
    auto* env_lib = std::getenv("ALETHEIA_LIB");
    std::string libPath = (env_lib != nullptr) ? env_lib : "";

    // Two backends: one consumed by the wrapper-scope `client`, one left
    // free for fences that construct their own client (INTERFACES.md L665).
    // GHC RTS init is idempotent in `make_ffi_backend`, so the second call
    // is cheap (dlopen handle + StablePtr only).
    auto initial_backend = make_ffi_backend(libPath);
    DbcDefinition dbc = doc_harness_detail::build_doc_dbc();
    AletheiaClient client{std::move(initial_backend)};
    [[maybe_unused]] auto _parse_result = client.parse_dbc(std::stop_token{}, dbc);

    [[maybe_unused]] auto backend = make_ffi_backend(libPath);
    [[maybe_unused]] Timestamp ts{0};
    [[maybe_unused]] CanId can_id = StandardId::create(0x100).value();
    [[maybe_unused]] CanId canID = can_id;
    [[maybe_unused]] Dlc dlc = Dlc::create(8).value();
    [[maybe_unused]] std::vector<std::byte> data_storage(8, std::byte{0});
    [[maybe_unused]] std::span<const std::byte> data{data_storage};
    [[maybe_unused]] std::vector<Frame> frames;

    // Fence body runs in a nested block so fences that redeclare backend /
    // client / ts / can_id / dlc / data via `auto x = ...` shadow the outer
    // scope's names cleanly. This matches the Go harness's nested-block
    // strategy for the body-fragment wrapper.
    {
)CPP";

    constexpr std::string_view kEpilogue = R"CPP(
    }

    return 0;
}
)CPP";

    std::string out;
    out.reserve(kPrologue.size() + body.size() + kEpilogue.size());
    out.append(kPrologue);
    out.append(body);
    out.append(kEpilogue);
    return out;
}

// Pick a wrapper shape based on body content.
auto wrap_fence(std::string body) -> std::string {
    if (has_main(body))
        return body;
    if (has_include(body)) {
        return body + "\n\nint main() { return 0; }\n";
    }
    return wrap_body_fragment(std::move(body));
}

auto write_file(const fs::path& path, std::string_view content) -> void {
    std::ofstream out(path, std::ios::binary);
    out.write(content.data(), static_cast<std::streamsize>(content.size()));
    out.close();
}

// Run a shell command, capturing stdout+stderr. Returns (exit_code, output).
auto run_capture(const std::string& cmd) -> std::pair<int, std::string> {
    std::string captured;
    auto* fp = popen((cmd + " 2>&1").c_str(), "r");
    if (fp == nullptr)
        return {-1, "popen failed"};
    std::array<char, 4096> buf{};
    while (auto n = std::fread(buf.data(), 1, buf.size(), fp)) {
        captured.append(buf.data(), n);
    }
    int rc = pclose(fp);
    if (WIFEXITED(rc))
        return {WEXITSTATUS(rc), captured};
    return {rc, captured};
}

// Quote a single shell argument (POSIX sh). Single-quote with embedded-quote
// escape — adequate for the paths we generate (no nested single quotes).
auto sh_quote(std::string_view s) -> std::string {
    std::string out;
    out.reserve(s.size() + 2);
    out.push_back('\'');
    for (char c : s) {
        if (c == '\'')
            out.append("'\\''");
        else
            out.push_back(c);
    }
    out.push_back('\'');
    return out;
}

// Cached fence list — extraction is idempotent so we read once and reuse
// across repeat entries (Catch2 SECTION re-enters the test case body for
// each section, which would otherwise re-parse the markdown N times).
auto fence_cache() -> const std::vector<CppFence>& {
    static const auto cached = []() {
        std::vector<CppFence> out;
        auto root = repo_root();
        for (auto rel : kDocFiles) {
            auto path = root / rel;
            if (!fs::exists(path))
                continue;
            auto fs_list = extract_cpp_fences(path, rel);
            out.insert(out.end(), fs_list.begin(), fs_list.end());
        }
        return out;
    }();
    return cached;
}

} // namespace

TEST_CASE("Track D.1 doc-example harness: every ```cpp fence compiles and runs", "[doc-examples]") {
    auto lib = find_ffi_lib();
    if (lib.empty()) {
        SKIP("libaletheia-ffi.so not found — run `cabal run shake -- build` first");
    }

    auto root = repo_root();
    auto yaml_fix = (root / "cpp" / "tests" / "testdata" / "doc_examples" / "checks.yaml").string();
    REQUIRE(fs::exists(yaml_fix));
    auto excel_fix = (root / "examples" / "demo" / "demo_workbook.xlsx").string();
    REQUIRE(fs::exists(excel_fix));

    const auto& fences = fence_cache();
    REQUIRE_FALSE(fences.empty());

    fs::path workdir =
        fs::temp_directory_path() / ("aletheia_doc_harness_" + std::to_string(::getpid()));
    fs::create_directories(workdir);

    for (std::size_t i = 0; i < fences.size(); ++i) {
        const auto& fence = fences[i];
        DYNAMIC_SECTION("Fence " << fence.display()) {
            auto body = substitute_paths(fence.content, lib, yaml_fix, excel_fix);
            auto src = wrap_fence(std::move(body));
            auto src_path = workdir / ("fence" + std::to_string(i) + ".cpp");
            auto out_path = workdir / ("fence" + std::to_string(i));
            write_file(src_path, src);

            // Compile.
            std::ostringstream cmd;
            cmd << sh_quote(ALETHEIA_DOC_CXX) << " -std=c++" << ALETHEIA_DOC_CXX_STD << " -I"
                << sh_quote(ALETHEIA_DOC_INCLUDE) << " -o " << sh_quote(out_path.string()) << " "
                << sh_quote(src_path.string()) << " " << sh_quote(ALETHEIA_DOC_LIB_FILE) << " "
                << sh_quote(ALETHEIA_DOC_YAML_LIB) << " " << sh_quote(ALETHEIA_DOC_OPENXLSX_LIB)
                << " -ldl -lpthread -lstdc++fs";
            auto compile_cmd = cmd.str();

            auto [compile_rc, compile_out] = run_capture(compile_cmd);
            INFO("Wrapper source: " << src_path);
            INFO("Compile command: " << compile_cmd);
            INFO("Compile output:\n" << compile_out);
            REQUIRE(compile_rc == 0);

            // Run.
            std::ostringstream run_cmd;
            run_cmd << "ALETHEIA_LIB=" << sh_quote(lib) << " " << sh_quote(out_path.string());
            auto [run_rc, run_out] = run_capture(run_cmd.str());
            INFO("Run output:\n" << run_out);
            REQUIRE(run_rc == 0);
        }
    }

    std::error_code ec;
    fs::remove_all(workdir, ec);
}

// ---------------------------------------------------------------------------
// Structural gates (mirror go/aletheia/doc_no_notest_test.go)
// ---------------------------------------------------------------------------

TEST_CASE("doc-example structural gate: no `<!-- cpp notest -->` annotations",
          "[doc-examples][gate]") {
    // Mirror of Go's TestNoNotestCppFences: a non-runnable fence must use
    // the `text` info string. The HTML-comment escape hatch silently hides
    // a fence from the harness while still rendering as cpp in prose.
    static const std::regex notest_re(R"(<!--\s*cpp\b[^>]*\bnotest\b[^>]*-->)");
    auto root = repo_root();
    for (auto rel : kDocFiles) {
        auto path = root / rel;
        if (!fs::exists(path))
            continue;
        std::ifstream in(path);
        std::stringstream ss;
        ss << in.rdbuf();
        auto body = ss.str();
        std::vector<int> offenders;
        auto begin = std::sregex_iterator(body.begin(), body.end(), notest_re);
        auto end = std::sregex_iterator{};
        for (auto it = begin; it != end; ++it) {
            int line =
                static_cast<int>(std::count(body.begin(), body.begin() + it->position(), '\n')) + 1;
            offenders.push_back(line);
        }
        if (!offenders.empty()) {
            std::ostringstream lines;
            lines << '[';
            for (std::size_t i = 0; i < offenders.size(); ++i) {
                if (i != 0)
                    lines << ", ";
                lines << "L" << offenders[i];
            }
            lines << ']';
            FAIL(rel << " has `<!-- cpp notest -->` annotations at " << lines.str()
                     << " — switch the fence info string from `cpp` to `text` (or"
                     << " drop the annotation so the harness runs the block).");
        }
    }
}

TEST_CASE("doc-example structural gate: at least one ```cpp fence collectively",
          "[doc-examples][gate]") {
    // Mirror of Go's TestEveryDocFileHasAtLeastOneGoFenceCollectively: guards
    // against a mass rename emptying the doc-example surface. We don't require
    // every individual file to ship a fence — some are prose-heavy — but the
    // collective set must exceed the floor.
    constexpr std::size_t kMinFences = 6;
    REQUIRE(fence_cache().size() >= kMinFences);
}
