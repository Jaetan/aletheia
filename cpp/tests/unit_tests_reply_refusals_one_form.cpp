// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// Every refusal of a reply place is built by reply_refusal, which writes the
// one form: a reader throws the refusal it builds, and the response parsers
// answer what a reader threw as a Protocol error carrying its text. A Protocol
// error the binding names anywhere else, or an exception a reader's file
// builds anywhere but there, is one the form leaves alone: the kernel's own
// message carried with its code, the binary extraction reply's layout, a
// library that answered no reply at all, or a fault no reply can cause. Each
// such site is listed by function with its count, so a refusal built by hand
// anywhere else is red, and so is a listed site that no longer builds one.
//
// The binding's sources are read as tokens, with comments, literals and
// preprocessor lines dropped. A function is a declaration whose parameter
// list a body follows, a member's name led by its classes; what a lambda or
// a local class builds is its enclosing function's.

#include <catch2/catch_message.hpp>
#include <catch2/catch_test_macros.hpp>

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <format>
#include <iterator>
#include <map>
#include <optional>
#include <ranges>
#include <regex>
#include <set>
#include <sstream>
#include <string>
#include <string_view>
#include <vector>

#include "repo_root.hpp"
#include "text_file.hpp"

namespace fs = std::filesystem;

namespace {

// A function of the binding building a Protocol error or a reader's
// exception: its file below cpp/, and its name, a member's led by its
// classes.
struct Site {
    std::string file;
    std::string function;

    auto operator<=>(Site const&) const = default;
};

} // namespace

// What each function outside the one form builds by hand, and why the form
// leaves it alone.
static auto left_alone() -> std::map<Site, int> {
    return {
        // The one form itself: the refusal a reader throws, and the Protocol
        // error each response parser answers for it.
        {{.file = "src/reply_shape.cpp", .function = "reply_refusal"}, 1},
        {{.file = "src/json_parse.cpp", .function = "wire_fault"}, 1},
        {{.file = "src/json_parse.cpp", .function = "binary_refusal"}, 1},
        // The kernel's own message, carried with its code: the kind an error
        // reply is typed when its code names none of its own.
        {{.file = "src/detail/json.hpp", .function = "binary_refusal"}, 1},
        {{.file = "src/json_parse.cpp", .function = "parse_success"}, 1},
        {{.file = "src/json_parse.cpp", .function = "parse_event_ack"}, 1},
        {{.file = "src/json_parse.cpp", .function = "parse_extraction"}, 1},
        {{.file = "src/json_parse.cpp", .function = "parse_frame_data"}, 1},
        {{.file = "src/json_parse.cpp", .function = "parse_frame_response"}, 1},
        {{.file = "src/json_parse.cpp", .function = "parse_stream_result"}, 1},
        {{.file = "src/json_parse.cpp", .function = "parse_dbc_response"}, 1},
        {{.file = "src/json_parse.cpp", .function = "parse_parsed_dbc"}, 1},
        {{.file = "src/json_parse.cpp", .function = "parse_dbc_text_response"}, 1},
        // The binary extraction reply's layout, which the reply proof does not
        // reach.
        {{.file = "src/client.cpp", .function = "wire_signal_errors"}, 4},
        {{.file = "src/client.cpp", .function = "parse_extraction_bin"}, 2},
        // A library that answered no reply: a null string, a refusal without
        // its envelope.
        {{.file = "src/ffi_backend.cpp", .function = "FfiBackend::wrap_str_result"}, 1},
        {{.file = "src/detail/ffi_logic.cpp", .function = "ffi_error_from_status"}, 1},
        {{.file = "src/property_check.cpp", .function = "entry_refusal"}, 1},
        {{.file = "src/rational_renderer.cpp", .function = "parse_decimal_ffi"}, 1},
        // A fault no reply can cause: a status no enumerator names, and text
        // nested past the depth bound, which read_reply carries as the reason
        // the text is refused as JSON text.
        {{.file = "src/reply_shape.cpp", .function = "status_word"}, 1},
        {{.file = "src/wide_json.cpp", .function = "WideBuilder::within_bound"}, 1},
    };
}

// The standard exceptions a reader's file may construct.
constexpr auto exception_types = std::to_array<std::string_view>({
    "exception",
    "runtime_error",
    "logic_error",
    "invalid_argument",
    "domain_error",
    "length_error",
    "out_of_range",
    "range_error",
    "overflow_error",
    "underflow_error",
    "system_error",
    "format_error",
});

static constexpr auto is_word_char(char c) -> bool {
    return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') || c == '_';
}

static constexpr auto is_space(char c) -> bool {
    return c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\f' || c == '\v';
}

// `rest` past the first `end` it holds, empty when it holds none.
static auto past(std::string_view rest, std::string_view end) -> std::string_view {
    auto const at = rest.find(end);
    return at == std::string_view::npos ? std::string_view{} : rest.substr(at + end.size());
}

// `rest`, which follows a literal's opening quote, past its closing one.
static auto past_quoted(std::string_view rest, char quote) -> std::string_view {
    auto const stops = std::to_array({quote, '\\'});
    for (;;) {
        auto const at = rest.find_first_of(std::string_view{stops.data(), stops.size()});
        if (at == std::string_view::npos)
            return {};
        if (rest.at(at) == quote)
            return rest.substr(at + 1);
        rest = rest.substr(std::min(at + 2, rest.size()));
    }
}

// `rest`, which opens a raw string at its quote, past the string.
static auto past_raw(std::string_view rest) -> std::string_view {
    auto const open = rest.find('(');
    if (open == std::string_view::npos)
        return {};
    auto const delimiter = rest.substr(1, open - 1);
    return past(rest.substr(open + 1), ")" + std::string{delimiter} + "\"");
}

// `rest`, which opens a preprocessor directive, past its last line.
static auto past_directive(std::string_view rest) -> std::string_view {
    for (;;) {
        auto const end = rest.find('\n');
        if (end == std::string_view::npos)
            return {};
        auto const continued = end > 0 && rest.at(end - 1) == '\\';
        rest = rest.substr(end + 1);
        if (!continued)
            return rest;
    }
}

// The length of the number `rest` opens: its digits, letters, points, digit
// separators and an exponent's sign.
static auto number_length(std::string_view rest) -> std::size_t {
    auto previous = '\0';
    auto const* const end = std::ranges::find_if(rest, [&previous](char c) {
        auto const exponent_sign =
            (c == '+' || c == '-') && std::string_view{"eEpP"}.contains(previous);
        previous = c;
        return !is_word_char(c) && c != '.' && c != '\'' && !exponent_sign;
    });
    return static_cast<std::size_t>(end - rest.begin());
}

// The width of the punctuation `rest` opens: "::", "->" and an operator
// followed by "=" are two characters, any other one.
static auto punctuation_width(std::string_view rest) -> std::size_t {
    if (rest.starts_with("::") || rest.starts_with("->"))
        return 2;
    if (rest.size() > 1 && rest.at(1) == '=' &&
        std::string_view{"<>!=+-*/%&|^"}.contains(rest.front()))
        return 2;
    return 1;
}

using Tokens = std::vector<std::string>;

// The tokens of C++ source text: identifiers, numbers (each read as "0") and
// punctuation, with comments, string and character literals and
// preprocessor directives dropped.
static auto tokens_of(std::string_view source) -> Tokens {
    constexpr auto raw_prefixes = std::to_array<std::string_view>({"R", "u8R", "uR", "UR", "LR"});
    constexpr auto literal_prefixes = std::to_array<std::string_view>({"u8", "u", "U", "L"});
    Tokens out;
    auto rest = source;
    auto line_start = true;
    while (!rest.empty()) {
        auto const c = rest.front();
        if (is_space(c)) {
            line_start = line_start || c == '\n';
            rest.remove_prefix(1);
        } else if (c == '#' && line_start) {
            rest = past_directive(rest);
        } else if (rest.starts_with("//")) {
            rest = past(rest, "\n");
            line_start = true;
        } else if (rest.starts_with("/*")) {
            rest = past(rest.substr(2), "*/");
        } else if (c == '"' || c == '\'') {
            rest = past_quoted(rest.substr(1), c);
            line_start = false;
        } else if (c >= '0' && c <= '9') {
            rest.remove_prefix(number_length(rest));
            out.emplace_back("0");
            line_start = false;
        } else if (is_word_char(c)) {
            auto const word =
                rest.substr(0, static_cast<std::size_t>(
                                   std::ranges::find_if_not(rest, is_word_char) - rest.begin()));
            rest.remove_prefix(word.size());
            line_start = false;
            if (rest.starts_with('"') && std::ranges::contains(raw_prefixes, word))
                rest = past_raw(rest);
            else if (!((rest.starts_with('"') || rest.starts_with('\'')) &&
                       std::ranges::contains(literal_prefixes, word)))
                out.emplace_back(word);
        } else {
            auto const width = punctuation_width(rest);
            out.emplace_back(rest.substr(0, width));
            rest.remove_prefix(width);
            line_start = false;
        }
    }
    return out;
}

namespace {

// What a brace opens: a namespace or a class, whose declarations are read; a
// function's body; or anything else, read only for its braces.
enum class Scope : std::uint8_t { Namespace, Type, Function, Opaque };

struct Frame {
    Scope scope;
    std::string name;
};

// A declaration being read at namespace or class scope, up to its `;` or the
// brace opening its body.
struct Declaration {
    // The name last read, qualified as it is written.
    std::string name;
    // The name read before its parameter list.
    std::optional<std::string> function;
    // namespace, class, struct, union, enum or extern, the first read.
    std::string keyword;
    // The name a class keyword introduces.
    std::string type;
    // The parentheses open around the token read.
    int parens = 0;
    // The angle brackets open in a template's parameters.
    int angles = 0;
    // An `=` read before any parameter list.
    bool assigned = false;
    // Its parameter list closed.
    bool closed = false;
    // A constructor's member initializers begun.
    bool initializers = false;
    // `template` read, its `<` next.
    bool templated = false;
    // An operator's symbol being read.
    bool operator_name = false;
};

} // namespace

// `name` led by the classes the walk is in, unless it is already qualified.
static auto qualified(std::vector<Frame> const& frames, std::string const& name) -> std::string {
    if (name.contains("::"))
        return name;
    std::string out;
    for (auto const& frame : frames)
        if (frame.scope == Scope::Type)
            out += frame.name + "::";
    return out + name;
}

// The function the walk is in: the one whose body it reads, else the one the
// declaration being read declares.
static auto site_name(std::vector<Frame> const& frames, Declaration const& declaration)
    -> std::string {
    auto const body = std::ranges::find(frames, Scope::Function, &Frame::scope);
    if (body != frames.end())
        return body->name;
    if (declaration.function)
        return qualified(frames, declaration.function.value());
    return "<namespace scope>";
}

// Whether the token at `index` builds a Protocol error, or, in a reader's
// file, an exception: an ErrorKind::Protocol not compared with, a standard
// exception constructed, or a throw of anything but reply_refusal's refusal, a
// standard exception or the exception being handled.
static auto builds(Tokens const& tokens, std::ptrdiff_t index, bool reader) -> bool {
    auto const at = [&tokens](std::ptrdiff_t k) -> std::string_view {
        return k >= 0 && k < std::ssize(tokens)
                   ? std::string_view{tokens.at(static_cast<std::size_t>(k))}
                   : std::string_view{};
    };
    if (at(index) == "Protocol" && at(index - 1) == "::" && at(index - 2) == "ErrorKind") {
        auto const before = at(index - 3) == "::" ? at(index - 5) : at(index - 3);
        return before != "==" && before != "!=" && before != "case";
    }
    if (!reader)
        return false;
    if (std::ranges::contains(exception_types, at(index)) && at(index - 1) == "::" &&
        at(index - 2) == "std")
        return (at(index + 1) == "(" || at(index + 1) == "{") && at(index - 3) != "->";
    if (at(index) != "throw")
        return false;
    auto const thrown = at(index + 1);
    if (thrown == ";" || (thrown == "reply_refusal" && at(index + 2) == "("))
        return false;
    return !(thrown == "std" && at(index + 2) == "::" &&
             std::ranges::contains(exception_types, at(index + 3)));
}

// Ends the scope a closing brace closes; the file's own scope is never
// closed, so a stray brace leaves the walk at namespace scope.
static auto close_brace(std::vector<Frame>& frames) -> void {
    if (frames.size() > 1)
        frames.pop_back();
}

// The scope the brace closing `declaration` opens, pushed onto `frames`; the
// declaration ends unless the brace opens an initializer within it.
static auto open_brace(std::vector<Frame>& frames, Declaration& declaration,
                       std::string_view previous) -> void {
    auto const& keyword = declaration.keyword;
    if (!declaration.function && (keyword == "namespace" || keyword == "extern")) {
        frames.push_back({.scope = Scope::Namespace, .name = ""});
        declaration = {};
        return;
    }
    if (!declaration.function &&
        (keyword == "class" || keyword == "struct" || keyword == "union")) {
        frames.push_back({.scope = Scope::Type, .name = declaration.type});
        declaration = {};
        return;
    }
    auto const member_initializer =
        declaration.initializers &&
        (previous == ">" || (!previous.empty() && is_word_char(previous.front())));
    if (declaration.function && !declaration.assigned && !member_initializer) {
        frames.push_back(
            {.scope = Scope::Function, .name = qualified(frames, declaration.function.value())});
        declaration = {};
        return;
    }
    frames.push_back({.scope = Scope::Opaque, .name = ""});
}

// Reads a token of a declaration at namespace or class scope.
static auto declare(std::vector<Frame>& frames, Declaration& declaration, std::string_view token,
                    std::string_view previous, std::string_view next, bool& skip_next) -> void {
    auto& d = declaration;
    if (d.angles > 0) {
        if (token == "<")
            ++d.angles;
        else if (token == ">")
            --d.angles;
        return;
    }
    if (token == "template") {
        d.templated = true;
        return;
    }
    if (d.templated && token == "<") {
        d.templated = false;
        d.angles = 1;
        return;
    }
    if (d.operator_name) {
        if (token != "(" || (d.name == "operator" && next == ")")) {
            d.name += token;
            if (token == "(") {
                d.name += ')';
                skip_next = true;
            }
            return;
        }
        d.operator_name = false;
    }
    if (d.parens > 0) {
        if (token == "(")
            ++d.parens;
        else if (token == ")")
            --d.parens;
        d.closed = d.parens == 0;
        return;
    }
    if (token == ";") {
        d = {};
    } else if (token == "}") {
        close_brace(frames);
        d = {};
    } else if (token == "{") {
        open_brace(frames, d, previous);
    } else if (token == "(") {
        if (!d.function && !d.assigned)
            d.function = d.name;
        d.parens = 1;
    } else if (token == "=") {
        d.assigned = d.assigned || !d.function;
    } else if (token == ":") {
        if (previous == "public" || previous == "private" || previous == "protected")
            d = {};
        else if (d.closed)
            d.initializers = true;
    } else if (token == "operator") {
        d.name = "operator";
        d.operator_name = true;
    } else if (is_word_char(token.front())) {
        constexpr auto keywords = std::to_array<std::string_view>(
            {"namespace", "class", "struct", "union", "enum", "extern"});
        if (d.keyword.empty() && !d.function && std::ranges::contains(keywords, token))
            d.keyword = token;
        else if (d.type.empty() && !d.keyword.empty())
            d.type = token;
        if (previous == "::" && !d.name.empty())
            d.name += "::" + std::string{token};
        else if (previous == "~")
            d.name = "~" + std::string{token};
        else
            d.name = token;
    }
}

// Adds each site's count in one file's tokens to `built`.
static auto count_sites(std::string const& file, Tokens const& tokens, bool reader,
                        std::map<Site, int>& built) -> void {
    std::vector<Frame> frames{{.scope = Scope::Namespace, .name = ""}};
    Declaration declaration;
    auto skip_next = false;
    auto const at = [&tokens](std::ptrdiff_t k) -> std::string_view {
        return k >= 0 && k < std::ssize(tokens)
                   ? std::string_view{tokens.at(static_cast<std::size_t>(k))}
                   : std::string_view{};
    };
    for (auto const [index, token] : std::views::enumerate(tokens)) {
        if (builds(tokens, index, reader))
            ++built[Site{.file = file, .function = site_name(frames, declaration)}];
        if (skip_next) {
            skip_next = false;
            continue;
        }
        auto const scope = frames.back().scope;
        if (scope == Scope::Function || scope == Scope::Opaque) {
            if (token == "{")
                frames.push_back({.scope = Scope::Opaque, .name = ""});
            else if (token == "}")
                close_brace(frames);
            continue;
        }
        declare(frames, declaration, token, at(index - 1), at(index + 1), skip_next);
    }
}

// Every source and header of the binding, below cpp/src and cpp/include.
static auto binding_files(fs::path const& cpp) -> std::vector<fs::path> {
    std::vector<fs::path> out;
    for (auto const* const tree : {"src", "include"})
        for (auto const& entry : fs::recursive_directory_iterator(cpp / tree))
            if (entry.is_regular_file() &&
                (entry.path().extension() == ".cpp" || entry.path().extension() == ".hpp"))
                out.push_back(entry.path().lexically_normal());
    std::ranges::sort(out);
    return out;
}

// The binding's headers `file` includes by a quoted name, found beside it or
// in cpp/src.
static auto local_includes(fs::path const& file, fs::path const& src) -> std::vector<fs::path> {
    static std::regex const include{R"re(^\s*#\s*include\s*"([^"]+)")re"};
    std::vector<fs::path> out;
    std::istringstream lines{aletheia::test::read_text_file(file)};
    for (std::string line; std::getline(lines, line);) {
        std::smatch match;
        if (!std::regex_search(line, match, include))
            continue;
        for (auto const& candidate : {file.parent_path() / match.str(1), src / match.str(1)})
            if (fs::exists(candidate)) {
                out.push_back(candidate.lexically_normal());
                break;
            }
    }
    return out;
}

// The readers' files: each json_parse*.cpp and reply_shape.cpp of cpp/src,
// every header of the binding they include, and the source of each such
// header, beside it or in cpp/src.
static auto reader_files(fs::path const& cpp) -> std::set<fs::path> {
    auto const src = (cpp / "src").lexically_normal();
    std::vector<fs::path> pending;
    for (auto const& entry : fs::directory_iterator(src)) {
        auto const name = entry.path().filename().string();
        if (name == "reply_shape.cpp" || (name.starts_with("json_parse") && name.ends_with(".cpp")))
            pending.push_back(entry.path().lexically_normal());
    }
    std::set<fs::path> out;
    while (!pending.empty()) {
        auto const file = pending.back();
        pending.pop_back();
        if (!out.insert(file).second)
            continue;
        std::ranges::copy(local_includes(file, src), std::back_inserter(pending));
        if (file.extension() != ".hpp")
            continue;
        auto beside = file;
        beside.replace_extension(".cpp");
        auto in_src = src / file.filename();
        in_src.replace_extension(".cpp");
        for (auto const& source : {beside, in_src})
            if (fs::exists(source))
                pending.push_back(source.lexically_normal());
    }
    return out;
}

// What each function of the binding builds: its Protocol errors across every
// file, and the exceptions of the readers' files.
static auto built_by_hand() -> std::map<Site, int> {
    auto const cpp = (aletheia::test::repo_root() / "cpp").lexically_normal();
    auto const readers = reader_files(cpp);
    std::map<Site, int> built;
    for (auto const& path : binding_files(cpp))
        count_sites(path.lexically_relative(cpp).generic_string(),
                    tokens_of(aletheia::test::read_text_file(path)), readers.contains(path), built);
    return built;
}

// No function builds a Protocol error, nor a reader's file an exception, but
// those the form leaves alone.
TEST_CASE("every refusal of a reply place is built by the one form", "[reply_shape]") {
    auto const built = built_by_hand();
    auto const listed = left_alone();
    std::vector<std::string> unlisted;
    std::vector<std::string> moved;
    for (auto const& [site, count] : built)
        if (!listed.contains(site))
            unlisted.push_back(std::format("{}:{} x{}", site.file, site.function, count));
    for (auto const& [site, count] : listed) {
        auto const found = built.find(site);
        auto const builds_now = found == built.end() ? 0 : found->second;
        if (builds_now != count)
            moved.push_back(std::format("{}:{} lists {}, builds {}", site.file, site.function,
                                        count, builds_now));
    }
    auto const lines = [](std::vector<std::string> const& rows) {
        std::string out;
        for (auto const& row : rows)
            out += "\n  " + row;
        return out;
    };
    INFO("refusals built outside the one form:\nunlisted:" << lines(unlisted)
                                                           << "\nmoved:" << lines(moved));
    CHECK(unlisted.empty());
    CHECK(moved.empty());
}
