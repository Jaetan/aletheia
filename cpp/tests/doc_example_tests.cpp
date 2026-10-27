// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// Doc-example harness — C++ Catch2 mirror of Python's
// `pytest --markdown-docs` (python/tests/test_doc_examples_harness.py +
// repo-root conftest.py) and Go's TestDocExamples
// (go/aletheia/doc_examples_test.go).
//
// Every ```cpp fence of the documents k_doc_files lists, and of the `//`
// comments of the headers k_header_files lists, is extracted, wrapped,
// compiled by ${CMAKE_CXX_COMPILER}, and executed end-to-end. A failing fence
// (compile or runtime) is a test failure reported with `file:Lline`
// precision. The C++ fences of a document k_path_docs lists are one program
// cut into steps, joined in order, compiled and run whole, and every fence of
// a document k_whole_program_docs lists is also built as it stands, with
// nothing the harness adds, as a reader builds it. Non-runnable fences
// (signature sketches, illustrative pseudocode referencing undefined symbols)
// open with tildes, which the extractor does not read. The structural gates at the foot of this
// file hold the lists to the tree both ways, refuse a C++ fence hidden behind
// a suffixed info word as Go's TestNoGoFenceHidesBehindASuffix does, and keep
// a collective fence floor.
//
// Path substitutions (parallel python/conftest.py loader fakes):
//
//   "/opt/aletheia/lib/libaletheia-ffi.so" → the forwarding stand-in kernel
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
// Every program runs against the forwarding stand-in kernel, which hands each
// call to the library and logs each refusal it answers: a fence fails unless
// the kernel refused exactly the codes a `<!-- refuses: <code> ... -->` line
// directly above it names, so a fence that discards a refused call fails too.
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
#include <optional>
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

#include "doc_example_wrapping.hpp"
#include "repo_root.hpp"
#include "temp_path.hpp"
#include "text_file.hpp"

using aletheia::test::AsDirectory;
using aletheia::test::HarnessUse;
using aletheia::test::k_unread_check;
using aletheia::test::names_harness;
using aletheia::test::repo_root;
using aletheia::test::reported_harness_uses;
using aletheia::test::scratch_dir;
using aletheia::test::TempPath;
using aletheia::test::with_harness_client;
using aletheia::test::wrap_body_fragment;
using aletheia::test::wrap_unread_results;

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

// Every tracked C++ file whose `//` comments carry a ```cpp fence; the
// structural gates below hold the list to the tree both ways.
constexpr std::array<std::string_view, 3> k_header_files = {
    "cpp/include/aletheia/check.hpp",
    "cpp/include/aletheia/log.hpp",
    "cpp/include/aletheia/yaml.hpp",
};

// The listed documents whose fences are each a whole program, which a reader
// builds as it stands; the harness builds each as written too.
constexpr std::array<std::string_view, 1> k_whole_program_docs = {
    "cpp/README.md",
};

namespace {
struct CppFence {
    std::string file;                 // repo-relative path
    int line;                         // 1-based line number of opening ```cpp
    std::string content;              // body between fences (no surrounding ``` lines)
    std::vector<std::string> refuses; // the codes the line directly above names, in order

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
    auto const rest = strip_right(trim.substr(6));
    if (rest.contains('`'))
        return FenceOpening::Other;
    if (rest.empty() || rest.front() == ' ' || rest.front() == '\t')
        return FenceOpening::Run;
    auto const next = static_cast<unsigned char>(rest.front());
    if (std::isalnum(next) != 0 || next == '_' || next >= 0x80)
        return FenceOpening::Other;
    return FenceOpening::Hidden;
}

// The codes a line names when it is the mark directly above a fence that shows
// refusals, in the order the kernel answers them; none for any other line.
static auto stated_refusals(const std::string& line) -> std::vector<std::string> {
    static const std::regex mark(R"(<!-- refuses: ([a-z0-9_]+(?: [a-z0-9_]+)*) -->)");
    std::smatch m;
    if (!std::regex_match(line, m, mark))
        return {};
    std::vector<std::string> codes;
    for (auto const code : std::views::split(m[1].str(), ' '))
        codes.emplace_back(std::string_view{code});
    return codes;
}

namespace {
// Where a file carries its fences: on its own lines, as a Markdown document
// does, or in its `//` comments, as a header does.
enum class FenceHost : std::uint8_t { Lines, Comments };
} // namespace

// What a `//` comment line says past its slashes and one blank; none for a
// line that is no comment.
static auto comment_text(std::string_view line) -> std::optional<std::string> {
    auto text = strip_left(line);
    if (!text.starts_with("//"))
        return std::nullopt;
    text.remove_prefix(std::min(text.find_first_not_of('/'), text.size()));
    if (text.starts_with(' '))
        text.remove_prefix(1);
    return std::string{text};
}

// Extracts every ```cpp fence from one file, read where `host` says.
static auto extract_cpp_fences(const fs::path& abs_path, std::string_view rel_path,
                               FenceHost host = FenceHost::Lines) -> std::vector<CppFence> {
    std::ifstream in(abs_path);
    if (!in) {
        FAIL("read failed: " << abs_path);
    }
    std::vector<CppFence> fences;
    std::string raw;
    int lineno = 0;
    bool in_fence = false;
    int fence_start = 0;
    std::string body;
    std::vector<std::string> refuses;
    std::string previous;
    while (std::getline(in, raw)) {
        ++lineno;
        auto const read = host == FenceHost::Lines ? std::optional{raw} : comment_text(raw);
        if (!read) {
            if (in_fence) {
                FAIL("a ```cpp fence leaves its comment at " << rel_path << " line " << lineno);
            }
            previous.clear();
            continue;
        }
        auto const& line = *read;
        if (!in_fence) {
            if (cpp_fence_opening(line) == FenceOpening::Run) {
                in_fence = true;
                fence_start = lineno;
                body.clear();
                refuses = stated_refusals(previous);
            }
            previous = line;
            continue;
        }
        // Inside a fence — closing line is exactly ``` after trim.
        if (strip_right(strip_left(line)) == "```") {
            fences.push_back({.file = std::string{rel_path},
                              .line = fence_start,
                              .content = body,
                              .refuses = std::exchange(refuses, {})});
            in_fence = false;
            previous = line;
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
        R"((^|\n)\s*(?:\[\[[^\]]+\]\]\s*)?(?:static\s+|inline\s+|constexpr\s+)?)"
        R"((?:int\s+main\s*\(|auto\s+main\s*\([^)]*\)\s*->\s*int\b))");
    return std::regex_search(body.cbegin(), body.cend(), main_re);
}

// Heuristic: does the body contain a #include directive?
static auto has_include(std::string_view body) -> bool {
    static const std::regex inc_re(R"((^|\n)\s*#\s*include\b)");
    return std::regex_search(body.cbegin(), body.cend(), inc_re);
}

// The document line of each line of a fence's content.
static auto fence_lines(const CppFence& fence) -> std::vector<std::string> {
    auto const count = static_cast<int>(std::ranges::count(fence.content, '\n')) + 1;
    return std::views::iota(0, count) | std::views::transform([&](int k) {
               return fence.file + ":L" + std::to_string(fence.line + 1 + k);
           }) |
           std::ranges::to<std::vector>();
}

// Pick a wrapper shape based on body content, every shape's unread results
// handed to the check its program opens with.
static auto wrap_fence(std::string body, const CppFence& fence) -> std::string {
    body = wrap_unread_results(body, fence_lines(fence));
    if (has_main(body))
        return std::string{k_unread_check} + body;
    if (has_include(body)) {
        return std::string{k_unread_check} + body + "\n\nint main() { return 0; }\n";
    }
    return std::string{k_unread_check} + wrap_body_fragment(body);
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

// The fences, read once: Catch2 re-enters a test case for each of its sections.
static auto fence_cache() -> const std::vector<CppFence>& {
    static auto const cached = [] {
        std::vector<CppFence> out;
        auto const root = repo_root();
        auto const add = [&](std::string_view rel, FenceHost host) {
            auto const found = extract_cpp_fences(root / rel, rel, host);
            out.insert(out.end(), found.begin(), found.end());
        };
        for (auto const rel : k_doc_files)
            add(rel, FenceHost::Lines);
        for (auto const rel : k_header_files)
            add(rel, FenceHost::Comments);
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

// The code of each refusal the forwarding stand-in logged, in order: a line is
// the entry, a tab and the kernel's envelope. No file is no refusal.
static auto refusal_codes(const fs::path& log) -> std::vector<std::string> {
    static const std::regex code(R"re("code": "([a-z0-9_]+)")re");
    std::vector<std::string> codes;
    std::ifstream in(log);
    std::string line;
    while (std::getline(in, line)) {
        std::smatch m;
        if (!std::regex_search(line, m, code)) {
            FAIL("an unreadable refusal log line: " << line);
        }
        codes.push_back(m[1].str());
    }
    return codes;
}

// Compiles and links one program against the binding, failing the calling test
// case when it does not build.
static auto compile_program(const fs::path& src_path, const fs::path& out_path) -> void {
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
        << sh_quote(lib_dir.string()) << " -ldl -lpthread -lstdc++fs -Werror=unused-result "
        << ALETHEIA_DOC_SANITIZER_FLAG;
    auto const compile_cmd = cmd.str();

    auto const [compile_rc, compile_out] = run_capture(compile_cmd);
    INFO("Wrapper source: " << src_path);
    INFO("Compile command: " << compile_cmd);
    INFO("Compile output:\n" << compile_out);
    REQUIRE(compile_rc == 0);
}

// The uses of `client` and `backend` the compiler finds no declaration of in
// the program at `src_path`, from one pass of its front end: the uses the
// harness's client and backend stand behind, however the program declares its
// own names.
static auto harness_uses_of(const fs::path& src_path) -> std::vector<HarnessUse> {
    std::ostringstream cmd;
    cmd << sh_quote(ALETHEIA_DOC_CXX) << " -std=c++" << ALETHEIA_DOC_CXX_STD << " -I"
        << sh_quote(doc_include_dir()) << " -fsyntax-only -ferror-limit=0 -fno-spell-checking "
        << sh_quote(src_path.string());
    auto const [rc, diagnostics] = run_capture(cmd.str());
    INFO("Harness-name pass: " << cmd.str() << " (exit " << rc << ")\n" << diagnostics);
    return reported_harness_uses(diagnostics, src_path.string());
}

TEST_CASE("doc-example harness: the compiler names the uses the harness's client stands behind",
          "[doc-examples][gate]") {
    CHECK(reported_harness_uses("p.cpp:3:5: error: use of undeclared identifier 'client'\n"
                                "q.cpp:1:1: error: use of undeclared identifier 'client'\n"
                                "p.cpp:4:9: error: use of undeclared identifier 'backend'\n"
                                "p.cpp:5:1: error: use of undeclared identifier 'load'\n",
                                "p.cpp") ==
          std::vector<HarnessUse>{{.line = 3, .column = 5, .client = true},
                                  {.line = 4, .column = 9, .client = false}});
    CHECK(with_harness_client("a\n  client.x(backend);\n",
                              {{.line = 2, .column = 3, .client = true},
                               {.line = 2, .column = 12, .client = false},
                               {.line = 2, .column = 3, .client = true}}) ==
          "a\n  doc_harness_detail::harness_client().x(doc_harness_detail::harness_backend());\n");

    // A use in a loop after a read, and the forms a fragment declares the
    // names in itself: an own client over the harness's backend, a block's
    // own, a structured binding, a lambda's parameter, a member; a raw string
    // and a comment name them too.
    std::string const written =
        "auto const limit = 1;\n"
        "for (int i = 0; i < limit; ++i) {\n"
        "\t[[maybe_unused]] auto& used = client;\n"
        "}\n"
        "{\n"
        "    auto client = AletheiaClient::create(std::move(backend)).value();\n"
        "    [[maybe_unused]] auto& mine = client;\n"
        "}\n"
        "{\n"
        "    [[maybe_unused]] int const client = 1;\n"
        "}\n"
        "{\n"
        "    std::pair<int, int> const pair_value{3, 4};\n"
        "    auto [client, n] = pair_value;\n"
        "    auto f = [](int backend) { return backend + 1; };\n"
        "    struct Holder {\n"
        "        int client;\n"
        "    };\n"
        "    Holder const holder{f(n) + client};\n"
        "    [[maybe_unused]] auto const total = holder.client;\n"
        "}\n"
        "[[maybe_unused]] auto const* text = R\"x(say \"client\")x\"; // client\n"
        "[[maybe_unused]] auto& last = backend;\n";
    auto expected = written;
    for (auto const& [from, to] : std::to_array<std::pair<std::string_view, std::string_view>>({
             {"auto& used = client;", "auto& used = doc_harness_detail::harness_client();"},
             {"std::move(backend)", "std::move(doc_harness_detail::harness_backend())"},
             {"auto& last = backend;", "auto& last = doc_harness_detail::harness_backend();"},
         })) {
        expected.replace(expected.find(from), from.size(), to);
    }
    const TempPath scratch{scratch_dir() / "aletheia_doc_harness_names", AsDirectory{}};
    auto const src_path = scratch.path / "names.cpp";
    write_file(src_path, wrap_body_fragment(written));
    CHECK(with_harness_client(wrap_body_fragment(written), harness_uses_of(src_path)) ==
          wrap_body_fragment(expected));
}

// Compiles one program against the binding and runs it against the forwarding
// stand-in kernel, failing the calling test case on either step or on
// refusals other than the codes `refuses` names.
static auto compile_and_run(const fs::path& src_path, const fs::path& out_path,
                            const std::string& lib, const std::vector<std::string>& refuses)
    -> void {
    compile_program(src_path, out_path);
    auto const log = fs::path{out_path.string() + ".refusals"};
    std::ostringstream run_cmd;
    run_cmd << "ALETHEIA_LIB=" << sh_quote(ALETHEIA_DOC_FORWARDING_KERNEL)
            << " ALETHEIA_FORWARD_TO=" << sh_quote(lib)
            << " ALETHEIA_REFUSAL_LOG=" << sh_quote(log.string()) << " "
            << sh_quote(out_path.string());
    auto const [run_rc, run_out] = run_capture(run_cmd.str());
    INFO("Run output:\n" << run_out);
    REQUIRE(run_rc == 0);
    INFO("Refusal log:\n" << (fs::exists(log) ? read_text_file(log) : std::string{}));
    INFO("An example that shows a refusal names its codes on a `<!-- refuses: <code> ... -->` "
         "line directly above its fence");
    CHECK(refusal_codes(log) == refuses);
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
            auto body = substitute_paths(fence.content, ALETHEIA_DOC_FORWARDING_KERNEL,
                                         fixtures.yaml, fixtures.excel);
            auto const src_path = workdir / ("fence" + std::to_string(i) + ".cpp");
            auto program = wrap_fence(std::move(body), fence);
            if (names_harness(fence.content)) {
                write_file(src_path, program);
                program = with_harness_client(std::move(program), harness_uses_of(src_path));
            }
            write_file(src_path, program);
            compile_and_run(src_path, workdir / ("fence" + std::to_string(i)), lib, fence.refuses);
            if (std::ranges::contains(k_whole_program_docs, fence.file)) {
                // A reader builds it as it stands, with nothing the harness adds.
                auto const raw = workdir / ("fence" + std::to_string(i) + ".raw.cpp");
                write_file(raw, fence.content);
                compile_program(raw, workdir / ("fence" + std::to_string(i) + ".raw"));
            }
        }
    }
}

TEST_CASE("doc-example harness: an unread result is handed to the check, a read one is not",
          "[doc-examples][gate]") {
    std::vector<std::string> const where{"d.md:L1", "d.md:L2", "d.md:L3", "d.md:L4"};
    CHECK(wrap_unread_results("auto r = load(\"x\");\n", where) ==
          "auto r = docExampleUnread(\"d.md:L1\", load(\"x\"));\n");
    CHECK(wrap_unread_results("[[maybe_unused]] auto const _r =\n    load(1,\n         2);\n",
                              where) ==
          "[[maybe_unused]] auto const _r =\n    docExampleUnread(\"d.md:L1\", load(1,\n         "
          "2));\n");
    CHECK(wrap_unread_results("auto r = load();\nuse(r);\n", where) ==
          "auto r = load();\nuse(r);\n");
    CHECK(wrap_unread_results("auto n = 3;\n", where) == "auto n = 3;\n");
    CHECK(wrap_unread_results("auto s = f(\"a;b\"); // c;\n", where) ==
          "auto s = docExampleUnread(\"d.md:L1\", f(\"a;b\")); // c;\n");
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
            std::vector<std::string> refuses;
            std::vector<std::string> where;
            for (auto const& fence : extract_cpp_fences(root / rel, rel)) {
                program += fence.content;
                refuses.insert(refuses.end(), fence.refuses.begin(), fence.refuses.end());
                // A fence's content ends in a newline, so its last line is the next one's first.
                auto lines = fence_lines(fence);
                lines.pop_back();
                where.insert(where.end(), lines.begin(), lines.end());
            }
            REQUIRE_FALSE(program.empty());
            auto const src_path = scratch.path / ("path" + std::to_string(i) + ".cpp");
            write_file(src_path, std::string{k_unread_check} +
                                     substitute_paths(wrap_unread_results(program, where),
                                                      ALETHEIA_DOC_FORWARDING_KERNEL, fixtures.yaml,
                                                      fixtures.excel));
            compile_and_run(src_path, scratch.path / ("path" + std::to_string(i)), lib, refuses);
        }
    }
}

// ---------------------------------------------------------------------------
// Structural gates (Go's: go/aletheia/doc_files_test.go)
// ---------------------------------------------------------------------------

// Every tracked file the pathspecs name, as git lists it: the set a fresh
// checkout holds, so an untracked file in the working tree is never read.
static auto tracked_files(const fs::path& root, std::string_view pathspecs)
    -> std::vector<std::string> {
    auto const [rc, out] = run_capture("git -C " + sh_quote(root.string()) + " ls-files -z -- " +
                                       std::string{pathspecs});
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

static auto tracked_markdown(const fs::path& root) -> std::vector<std::string> {
    return tracked_files(root, "'*.md' '*.mdx' '*.svx'");
}

static auto tracked_cpp(const fs::path& root) -> std::vector<std::string> {
    return tracked_files(root, "'*.cpp' '*.hpp' '*.h'");
}

TEST_CASE("doc-example structural gate: every tracked ```cpp fence is in a listed file",
          "[doc-examples][gate]") {
    auto const root = repo_root();
    std::vector<std::string> unlisted;
    for (auto const& doc : tracked_markdown(root)) {
        if (std::ranges::contains(k_doc_files, doc) || std::ranges::contains(k_path_docs, doc))
            continue;
        if (!extract_cpp_fences(root / doc, doc).empty())
            unlisted.push_back(doc);
    }
    for (auto const& file : tracked_cpp(root)) {
        if (!std::ranges::contains(k_header_files, file) &&
            !extract_cpp_fences(root / file, file, FenceHost::Comments).empty())
            unlisted.push_back(file);
    }
    CAPTURE(unlisted);
    CHECK(unlisted.empty());
}

TEST_CASE("doc-example structural gate: every listed file is tracked and carries a ```cpp fence",
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
    for (auto const [i, doc] : std::views::enumerate(k_whole_program_docs)) {
        INFO(doc << " is a whole-program document");
        CHECK_FALSE(std::ranges::contains(k_whole_program_docs | std::views::take(i), doc));
        CHECK(std::ranges::contains(k_doc_files, doc));
    }
    auto const sources = tracked_cpp(root);
    for (auto const [i, header] : std::views::enumerate(k_header_files)) {
        INFO(header << " is listed");
        CHECK_FALSE(std::ranges::contains(k_header_files | std::views::take(i), header));
        CHECK(std::ranges::contains(sources, header));
        CHECK_FALSE(extract_cpp_fences(root / header, header, FenceHost::Comments).empty());
        CHECK(std::ranges::contains(fence_cache(), header, &CppFence::file));
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
    for (auto const& file : tracked_cpp(root)) {
        for (auto const [i, line] :
             std::views::enumerate(std::views::split(read_text_file(root / file), '\n'))) {
            auto const text = comment_text(std::string_view{line});
            if (text && cpp_fence_opening(*text) == FenceOpening::Hidden)
                hidden.push_back(file + ":" + std::to_string(i + 1));
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

TEST_CASE("doc-example structural gate: a comment line is read past its slashes and one blank",
          "[doc-examples][gate]") {
    struct Row {
        std::string_view line;
        std::optional<std::string_view> want;
    };
    for (auto const& [line, want] : std::array{
             Row{.line = "// ```cpp", .want = "```cpp"},
             Row{.line = "//   checks:", .want = "  checks:"},
             Row{.line = "  //x", .want = "x"},
             Row{.line = "/// ```cpp", .want = "```cpp"},
             Row{.line = "//", .want = ""},
             Row{.line = "int x; // ```cpp", .want = std::nullopt},
         }) {
        INFO(line);
        CHECK(comment_text(line) == want);
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
