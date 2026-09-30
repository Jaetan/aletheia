// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// Doc-example harness — C++ Catch2 mirror of Python's
// `pytest --markdown-docs` (python/tests/test_doc_examples_harness.py +
// repo-root conftest.py) and Go's TestDocExamples
// (go/aletheia/doc_examples_test.go).
//
// Every ```cpp fence of the documents k_doc_files lists is extracted,
// wrapped, compiled by ${CMAKE_CXX_COMPILER}, and executed end-to-end. A
// failing fence (compile or runtime) is a test failure reported with
// `file:Lline` precision. The C++ fences of a document k_path_docs lists are
// one program cut into steps, joined in order, compiled and run whole.
// Non-runnable fences (signature sketches, illustrative pseudocode referencing
// undefined symbols) open with tildes, which the extractor does not read. The
// structural gates at the foot of this file hold the list
// to the tree both ways, refuse a C++ fence hidden behind a suffixed info word
// as Go's TestNoGoFenceHidesBehindASuffix does, and keep a collective fence
// floor.
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
// The harness case skips when `libaletheia-ffi.so` is not findable; the
// structural gates need no library.

#include <algorithm>
#include <array>
#include <cctype>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <filesystem>
#include <fstream>
#include <ios>
#include <ranges>
#include <regex>
#include <sstream>
#include <stdexcept>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include <sys/wait.h>

#include <catch2/catch_message.hpp>
#include <catch2/catch_test_macros.hpp>

#include "repo_root.hpp"
#include "temp_path.hpp"
#include "text_file.hpp"

using aletheia::test::AsDirectory;
using aletheia::test::repo_root;
using aletheia::test::scratch_dir;
using aletheia::test::TempPath;

using aletheia::test::read_text_file;

namespace fs = std::filesystem;

// Every tracked Markdown file carrying a C++ fence, less those k_path_docs
// names; the structural gates below hold the lists to the tree both ways. Code
// no check runs opens with tildes, which the extractor does not read.
constexpr std::array<std::string_view, 5> k_doc_files = {
    "cpp/README.md",
    "docs/PITCH.md",
    "docs/reference/INTERFACES.md",
    "docs/reference/CPP_API.md",
    "docs/development/DISTRIBUTION.md",
};

// The tracked documents whose C++ fences, read in order, are one program cut
// into steps: the Tutorial's C++ path.
constexpr std::array<std::string_view, 1> k_path_docs = {
    "docs/guides/TUTORIAL.md",
};

namespace {
struct CppFence {
    std::string file;    // repo-relative path
    int line;            // 1-based line number of opening ```cpp
    std::string content; // body between fences (no surrounding ``` lines)

    [[nodiscard]] auto display() const -> std::string { return file + ":L" + std::to_string(line); }
};
} // namespace

// Repo root + include dir via env vars rather than compile-time defines, so
// the binary is bit-identical across build locations.  See
// cpp/tests/test_feature_matrix_parity.cpp.
static auto getenv_required(const char* name) -> std::string {
    if (const char* env = std::getenv(name); env != nullptr && *env != '\0') {
        return env;
    }
    throw std::runtime_error(
        std::string{name} +
        " env var not set; expected from ctest set_tests_properties(ENVIRONMENT ...) "
        "in cpp/CMakeLists.txt");
}

static auto doc_include_dir() -> std::string {
    return getenv_required("ALETHEIA_DOC_INCLUDE");
}

// findFFILib mirrors the Go harness's findFFILibForDocs.
static auto find_ffi_lib() -> std::string {
    if (auto* env = std::getenv("ALETHEIA_LIB"); env != nullptr && *env != '\0' && fs::exists(env))
        return env;

    constexpr std::array<std::string_view, 3> candidates = {
        "build/libaletheia-ffi.so",
        "../build/libaletheia-ffi.so",
        "../../build/libaletheia-ffi.so",
    };
    for (auto const rel : candidates) {
        auto const p = repo_root() / rel;
        if (fs::exists(p))
            return fs::weakly_canonical(p).string();
    }
    return {};
}

static auto strip_left(std::string_view s) -> std::string_view {
    while (!s.empty() && (s.front() == ' ' || s.front() == '\t')) {
        s.remove_prefix(1);
    }
    return s;
}

static auto strip_right(std::string_view s) -> std::string_view {
    while (!s.empty() && (s.back() == ' ' || s.back() == '\t' || s.back() == '\r')) {
        s.remove_suffix(1);
    }
    return s;
}

namespace {
// What a line opens, read by the first word of its info string. An info
// string holding a backtick opens nothing, CommonMark reading the line as
// inline code.
enum class FenceOpening : std::uint8_t {
    // any other line
    Other,
    // the harness's reading: leading blanks stripped, then a fence whose info
    // string's first word is exactly cpp
    Run,
    // cpp followed by ASCII punctuation (cpp,x): a reader still takes the
    // fence for C++, and the harness neither runs nor counts it
    Hidden,
};
} // namespace

static auto cpp_fence_opening(std::string_view line) -> FenceOpening {
    auto const trim = strip_left(line);
    if (!trim.starts_with("```cpp"))
        return FenceOpening::Other;
    auto const rest = trim.substr(6);
    if (rest.contains('`'))
        return FenceOpening::Other;
    if (rest.empty() || rest.front() == ' ' || rest.front() == '\t')
        return FenceOpening::Run;
    auto const next = static_cast<unsigned char>(rest.front());
    if (std::isalnum(next) != 0 || next == '_' || next >= 0x80)
        return FenceOpening::Other;
    return FenceOpening::Hidden;
}

// Extracts every ```cpp fence from one markdown file.
static auto extract_cpp_fences(const fs::path& abs_path, std::string_view rel_path)
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
        if (!in_fence) {
            if (cpp_fence_opening(line) == FenceOpening::Run) {
                in_fence = true;
                fence_start = lineno;
                body.clear();
            }
            continue;
        }
        // Inside a fence — closing line is exactly ``` after trim.
        if (strip_right(strip_left(line)) == "```") {
            fences.push_back({.file = std::string{rel_path}, .line = fence_start, .content = body});
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
static auto substitute_paths(std::string body, const std::string& lib_path,
                             const std::string& yaml_fix, const std::string& excel_fix)
    -> std::string {
    auto const replace_all = [](std::string& s, std::string_view from, std::string_view to) {
        std::size_t pos = 0;
        while ((pos = s.find(from, pos)) != std::string::npos) {
            s.replace(pos, from.size(), to);
            pos += to.size();
        }
    };
    auto const quote = [](std::string_view s) { return std::string("\"") + std::string(s) + "\""; };
    replace_all(body, R"("/opt/aletheia/lib/libaletheia-ffi.so")", quote(lib_path));
    replace_all(body, R"("checks.yaml")", quote(yaml_fix));
    replace_all(body, R"("checks.xlsx")", quote(excel_fix));
    replace_all(body, R"("tests.xlsx")", quote(excel_fix));
    return body;
}

// Heuristic: does the body contain a top-level `int main(` declaration?
static auto has_main(std::string_view body) -> bool {
    static const std::regex main_re(
        R"((^|\n)\s*(?:\[\[[^\]]+\]\]\s*)?(?:static\s+|inline\s+|constexpr\s+)?int\s+main\s*\()");
    return std::regex_search(body.cbegin(), body.cend(), main_re);
}

// Heuristic: does the body contain a #include directive?
static auto has_include(std::string_view body) -> bool {
    static const std::regex inc_re(R"((^|\n)\s*#\s*include\b)");
    return std::regex_search(body.cbegin(), body.cend(), inc_re);
}

// Body-fragment wrapper: matches the globals the Python harness predeclares
// in the repository's conftest.py.
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
constexpr std::string_view k_prologue =
    R"CPP(// Auto-generated wrapper: doc-example harness.
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
#include <ranges>

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

// Two backends: one consumed by the wrapper-scope `client`, one left free
// for a fence that constructs its own. GHC RTS init is idempotent in
// `make_ffi_backend`, so the second call is cheap (dlopen handle and
// StablePtr only).
auto initial_backend = make_ffi_backend(libPath);
DbcDefinition dbc = doc_harness_detail::build_doc_dbc();
AletheiaClient client{std::move(initial_backend)};
if (auto parsed = client.parse_dbc(std::stop_token{}, dbc); !parsed) {
    std::cerr << "the harness's DBC does not parse: " << parsed.error().message() << '\n';
    return 1;
}

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

constexpr std::string_view k_epilogue = R"CPP(
}

return 0;
}
)CPP";

static auto wrap_body_fragment(std::string body) -> std::string {
    std::string out;
    out.reserve(k_prologue.size() + body.size() + k_epilogue.size());
    out.append(k_prologue);
    out.append(body);
    out.append(k_epilogue);
    return out;
}

// Pick a wrapper shape based on body content.
static auto wrap_fence(std::string body) -> std::string {
    if (has_main(body))
        return body;
    if (has_include(body)) {
        return body + "\n\nint main() { return 0; }\n";
    }
    return wrap_body_fragment(std::move(body));
}

static auto write_file(const fs::path& path, std::string_view content) -> void {
    std::ofstream out(path, std::ios::binary);
    out.write(content.data(), static_cast<std::streamsize>(content.size()));
    out.close();
}

// Run a shell command, capturing stdout+stderr. Returns (exit_code, output).
static auto run_capture(const std::string& cmd) -> std::pair<int, std::string> {
    std::string captured;
    auto* fp = popen((cmd + " 2>&1").c_str(), "r");
    if (fp == nullptr)
        return {-1, "popen failed"};
    std::array<char, 4096> buf{};
    while (auto const n = std::fread(buf.data(), 1, buf.size(), fp)) {
        captured.append(buf.data(), n);
    }
    auto const rc = pclose(fp);
    if (WIFEXITED(rc))
        return {WEXITSTATUS(rc), captured};
    return {rc, captured};
}

// Quote a single shell argument (POSIX sh). Single-quote with embedded-quote
// escape — adequate for the paths we generate (no nested single quotes).
static auto sh_quote(std::string_view s) -> std::string {
    std::string out;
    out.reserve(s.size() + 2);
    out.push_back('\'');
    for (auto const c : s) {
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
static auto fence_cache() -> const std::vector<CppFence>& {
    static auto const cached = [] {
        std::vector<CppFence> out;
        auto const root = repo_root();
        for (auto const rel : k_doc_files) {
            auto fs_list = extract_cpp_fences(root / rel, rel);
            out.insert(out.end(), fs_list.begin(), fs_list.end());
        }
        return out;
    }();
    return cached;
}

namespace {
// The fixtures the path substitutions name.
struct Fixtures {
    std::string yaml;
    std::string excel;
};
} // namespace

static auto doc_fixtures(const fs::path& root) -> Fixtures {
    Fixtures fixtures{
        .yaml = (root / "cpp" / "tests" / "testdata" / "doc_examples" / "checks.yaml").string(),
        .excel = (root / "examples" / "demo" / "demo_workbook.xlsx").string(),
    };
    REQUIRE(fs::exists(fixtures.yaml));
    REQUIRE(fs::exists(fixtures.excel));
    return fixtures;
}

// Compiles one program against the binding and runs it, failing the calling
// test case on either step.
static auto compile_and_run(const fs::path& src_path, const fs::path& out_path,
                            const std::string& lib) -> void {
    // The library is shared and carries its own dependencies, so a program
    // links it alone and needs its directory on the run-time search path;
    // linking by file name gives the linker the path but not the loader.
    // ALETHEIA_DOC_SANITIZER_FLAG is set by CMake to the active sanitizer flag
    // (e.g. "-fsanitize=undefined") when the parent build was configured with
    // -DALETHEIA_SANITIZER=..., so the program's link to the library (which
    // carries sanitizer-runtime symbols) resolves; it is empty when no
    // sanitizer is active.
    auto const lib_dir = std::filesystem::path{ALETHEIA_DOC_LIB_FILE}.parent_path();
    std::ostringstream cmd;
    cmd << sh_quote(ALETHEIA_DOC_CXX) << " -std=c++" << ALETHEIA_DOC_CXX_STD << " -I"
        << sh_quote(doc_include_dir()) << " -o " << sh_quote(out_path.string()) << " "
        << sh_quote(src_path.string()) << " " << sh_quote(ALETHEIA_DOC_LIB_FILE) << " -Wl,-rpath,"
        << sh_quote(lib_dir.string()) << " -ldl -lpthread -lstdc++fs "
        << ALETHEIA_DOC_SANITIZER_FLAG;
    auto const compile_cmd = cmd.str();

    auto [compile_rc, compile_out] = run_capture(compile_cmd);
    INFO("Wrapper source: " << src_path);
    INFO("Compile command: " << compile_cmd);
    INFO("Compile output:\n" << compile_out);
    REQUIRE(compile_rc == 0);

    std::ostringstream run_cmd;
    run_cmd << "ALETHEIA_LIB=" << sh_quote(lib) << " " << sh_quote(out_path.string());
    auto [run_rc, run_out] = run_capture(run_cmd.str());
    INFO("Run output:\n" << run_out);
    REQUIRE(run_rc == 0);
}

TEST_CASE("doc-example harness: every ```cpp fence compiles and runs", "[doc-examples]") {
    auto const lib = find_ffi_lib();
    if (lib.empty()) {
        SKIP("libaletheia-ffi.so not found — run `cabal run shake -- build` first");
    }
    auto const fixtures = doc_fixtures(repo_root());

    auto const& fences = fence_cache();
    REQUIRE_FALSE(fences.empty());

    // A scratch directory that removes itself, so a failing fence (whose
    // assertion throws out of the loop) cannot leave its wrapper sources behind.
    const TempPath scratch{scratch_dir() / "aletheia_doc_harness", AsDirectory{}};
    auto const& workdir = scratch.path;

    for (auto const [i, fence] : std::views::enumerate(fences)) {
        DYNAMIC_SECTION("Fence " << fence.display()) {
            auto body = substitute_paths(fence.content, lib, fixtures.yaml, fixtures.excel);
            auto const src_path = workdir / ("fence" + std::to_string(i) + ".cpp");
            write_file(src_path, wrap_fence(std::move(body)));
            compile_and_run(src_path, workdir / ("fence" + std::to_string(i)), lib);
        }
    }
}

TEST_CASE("doc-example harness: every path document's ```cpp fences run as one program",
          "[doc-examples]") {
    auto const lib = find_ffi_lib();
    if (lib.empty()) {
        SKIP("libaletheia-ffi.so not found; run `cabal run shake -- build` first");
    }
    auto const root = repo_root();
    auto const fixtures = doc_fixtures(root);

    const TempPath scratch{scratch_dir() / "aletheia_doc_paths", AsDirectory{}};
    for (auto const [i, rel] : std::views::enumerate(k_path_docs)) {
        DYNAMIC_SECTION("Path " << rel) {
            std::string program;
            for (auto const& fence : extract_cpp_fences(root / rel, rel))
                program += fence.content;
            REQUIRE_FALSE(program.empty());
            auto const src_path = scratch.path / ("path" + std::to_string(i) + ".cpp");
            write_file(src_path,
                       substitute_paths(std::move(program), lib, fixtures.yaml, fixtures.excel));
            compile_and_run(src_path, scratch.path / ("path" + std::to_string(i)), lib);
        }
    }
}

// ---------------------------------------------------------------------------
// Structural gates (Go's: go/aletheia/doc_files_test.go)
// ---------------------------------------------------------------------------

// Every tracked Markdown file, as git lists it: the set a fresh checkout holds,
// so an untracked file in the working tree is never read.
static auto tracked_markdown(const fs::path& root) -> std::vector<std::string> {
    auto const [rc, out] =
        run_capture("git -C " + sh_quote(root.string()) + " ls-files -z -- '*.md' '*.mdx' '*.svx'");
    if (rc != 0) {
        FAIL("git ls-files exited " << rc << ": " << out);
    }
    std::vector<std::string> paths;
    for (auto const part : std::views::split(out, '\0')) {
        if (!part.empty())
            paths.emplace_back(std::string_view{part});
    }
    return paths;
}

TEST_CASE("doc-example structural gate: every tracked ```cpp fence is in a listed document",
          "[doc-examples][gate]") {
    auto const root = repo_root();
    std::vector<std::string> unlisted;
    for (auto const& doc : tracked_markdown(root)) {
        if (std::ranges::contains(k_doc_files, doc) || std::ranges::contains(k_path_docs, doc))
            continue;
        if (!extract_cpp_fences(root / doc, doc).empty())
            unlisted.push_back(doc);
    }
    CAPTURE(unlisted);
    CHECK(unlisted.empty());
}

TEST_CASE(
    "doc-example structural gate: every listed document is tracked and carries a ```cpp fence",
    "[doc-examples][gate]") {
    auto const root = repo_root();
    auto const tracked = tracked_markdown(root);
    auto const tracked_with_a_fence = [&](std::string_view doc) {
        INFO(doc << " is listed");
        CHECK(std::ranges::contains(tracked, doc));
        CHECK_FALSE(extract_cpp_fences(root / doc, doc).empty());
    };
    for (auto const [i, doc] : std::views::enumerate(k_doc_files)) {
        CHECK_FALSE(std::ranges::contains(k_doc_files | std::views::take(i), doc));
        tracked_with_a_fence(doc);
    }
    for (auto const [i, doc] : std::views::enumerate(k_path_docs)) {
        CHECK_FALSE(std::ranges::contains(k_path_docs | std::views::take(i), doc));
        CHECK_FALSE(std::ranges::contains(k_doc_files, doc));
        tracked_with_a_fence(doc);
    }
}

TEST_CASE("doc-example structural gate: no ```cpp fence hides behind a suffixed info word",
          "[doc-examples][gate]") {
    auto const root = repo_root();
    std::vector<std::string> hidden;
    for (auto const& doc : tracked_markdown(root)) {
        for (auto const [i, line] :
             std::views::enumerate(std::views::split(read_text_file(root / doc), '\n'))) {
            if (cpp_fence_opening(std::string_view{line}) == FenceOpening::Hidden)
                hidden.push_back(doc + ":" + std::to_string(i + 1));
        }
    }
    INFO("write cpp, or open a fence that cannot run with tildes");
    CAPTURE(hidden);
    CHECK(hidden.empty());
}

TEST_CASE("doc-example structural gate: a ```cpp fence is read by its first info word",
          "[doc-examples][gate]") {
    struct Row {
        std::string_view line;
        FenceOpening want;
    };
    for (auto const& [line, want] : std::array{
             Row{.line = "```cpp", .want = FenceOpening::Run},
             Row{.line = "   ```cpp", .want = FenceOpening::Run},
             Row{.line = "```cpp notest", .want = FenceOpening::Run},
             Row{.line = "```cpp\tx", .want = FenceOpening::Run},
             Row{.line = "```cpp,x", .want = FenceOpening::Hidden},
             Row{.line = "```cpp{.x}", .want = FenceOpening::Hidden},
             Row{.line = "```cpp:main.cpp", .want = FenceOpening::Hidden},
             Row{.line = "  ```cpp``` / ```go``` block", .want = FenceOpening::Other},
             Row{.line = "```cpp `x`", .want = FenceOpening::Other},
             Row{.line = "```cpp20", .want = FenceOpening::Other},
             Row{.line = "```cppfront", .want = FenceOpening::Other},
             Row{.line = "```", .want = FenceOpening::Other},
             Row{.line = "```text", .want = FenceOpening::Other},
         }) {
        INFO(line);
        CHECK(cpp_fence_opening(line) == want);
    }
}

TEST_CASE("doc-example structural gate: at least one ```cpp fence collectively",
          "[doc-examples][gate]") {
    // Mirror of Go's TestEveryDocFileHasAtLeastOneGoFenceCollectively: guards
    // against a mass rename emptying the doc-example surface, the listed files
    // together reaching the floor.
    constexpr std::size_t k_min_fences = 6;
    REQUIRE(fence_cache().size() >= k_min_fences);
}
