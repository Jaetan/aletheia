// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// How the doc-example harness makes a program of a C++ fence: a body
// fragment's wrapper (its predeclared names, the client and backend it opens
// at the fragment's first use of one), and the check a result the fragment
// keeps unread is handed to.

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <ranges>
#include <regex>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

namespace aletheia::test {

// Body-fragment wrapper: matches the globals the Python harness predeclares
// in the repository's conftest.py.
//
// Predeclared globals:
//   - libPath        : string, ALETHEIA_LIB env var
//   - client         : aletheia::AletheiaClient (parsed against an in-memory DBC)
//   - backend        : std::unique_ptr<aletheia::IBackend> (FFI), each opened at
//                      the fragment's first evaluation of it (with_harness_client)
//   - ts             : aletheia::Timestamp
//   - can_id, canID  : aletheia::CanId (StandardId{0x100})
//   - dlc            : aletheia::Dlc{8}
//   - data_storage   : std::vector<std::byte>(8)
//   - data           : std::span<const std::byte> over data_storage
//   - frames         : std::vector<aletheia::Frame>
//   - dbc            : aletheia::DbcDefinition (the in-memory DBC parsed into client)
//
// `using namespace aletheia;` keeps doc snippets idiomatic.
inline constexpr std::string_view k_prologue =
    R"CPP(// Auto-generated wrapper: doc-example harness.
#include <chrono>
#include <cstddef>
#include <cstdlib>
#include <iostream>
#include <memory>
#include <optional>
#include <span>
#include <stop_token>
#include <string>
#include <string_view>
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
    return Rational::make(n, d).value();
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

// The harness's client, which parsed the DBC above, and a backend of its own,
// each opened at the fragment's first evaluation of its name, which the harness
// rewrites to these (with_harness_client).
inline std::optional<AletheiaClient> client_cell;
inline std::unique_ptr<IBackend> backend_cell;
inline bool backend_opened = false;

inline auto harness_lib() -> std::string {
    auto* env_lib = std::getenv("ALETHEIA_LIB");
    return env_lib != nullptr ? env_lib : "";
}

// The harness's own setup refused: the fragment cannot run, so the program
// ends naming why.
template<typename T>
inline auto harness_opened(Result<T> opened, std::string_view what) -> T {
    if (!opened) {
        std::cerr << "the harness's " << what << " does not open: " << opened.error().text()
                  << '\n';
        std::exit(1);
    }
    return std::move(opened).value();
}

inline auto harness_client() -> AletheiaClient& {
    if (!client_cell) {
        client_cell.emplace(
            harness_opened(AletheiaClient::open({.library = harness_lib()}), "client"));
        if (auto parsed = client_cell->parse_dbc(std::stop_token{}, build_doc_dbc()); !parsed) {
            std::cerr << "the harness's DBC does not parse: " << parsed.error().message() << '\n';
            std::exit(1);
        }
    }
    return *client_cell;
}

inline auto harness_backend() -> std::unique_ptr<IBackend>& {
    if (!backend_opened) {
        backend_cell = harness_opened(make_ffi_backend(harness_lib()), "backend");
        backend_opened = true;
    }
    return backend_cell;
}

// Closes what the fragment opened, after the fragment's own objects, wherever
// main returns.
struct HarnessClose {
    HarnessClose() = default;
    HarnessClose(const HarnessClose&) = delete;
    auto operator=(const HarnessClose&) -> HarnessClose& = delete;
    ~HarnessClose() {
        client_cell.reset();
        backend_cell.reset();
    }
};

} // namespace doc_harness_detail

int main() {
auto* env_lib = std::getenv("ALETHEIA_LIB");
[[maybe_unused]] std::string libPath = (env_lib != nullptr) ? env_lib : "";
[[maybe_unused]] DbcDefinition dbc = doc_harness_detail::build_doc_dbc();
[[maybe_unused]] doc_harness_detail::HarnessClose const doc_harness_close;
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

inline constexpr std::string_view k_epilogue = R"CPP(
}

return 0;
}
)CPP";

// The check a result the example keeps and never reads is handed to: the
// forwarding stand-in kernel sees only the kernel's refusals, and a binding
// refuses some inputs itself (an identifier out of range, a DLC above 15),
// so an example keeping such a refusal unread would pass on its exit status.
// It ends the run naming the line when the result holds an error, an
// AletheiaError or a factory's message alike; a type without one passes
// through, the branch reading it never instantiated.
inline constexpr std::string_view k_unread_check = R"CPP(#include <cstdlib>
#include <iostream>
#include <utility>

template <typename T>
auto docExampleUnread(const char* where, T&& kept) -> T&& {
    if constexpr (requires { kept.has_value(); kept.error(); }) {
        if (!kept.has_value()) {
            std::cerr << "the example discards an error at " << where;
            if constexpr (requires { kept.error().text(); })
                std::cerr << ": " << kept.error().text();
            else if constexpr (requires { std::cerr << kept.error(); })
                std::cerr << ": " << kept.error();
            std::cerr << '\n';
            std::exit(1);
        }
    }
    return std::forward<T>(kept);
}
)CPP";

// The offset of the `;` ending the statement whose text starts at `from`: the
// first outside brackets, string and character literals and line comments.
inline auto statement_end(std::string_view text, std::size_t from) -> std::size_t {
    enum class In : std::uint8_t { Code, Literal, Escape, Slash, Comment };
    auto in = In::Code;
    auto quote = '"';
    int depth = 0;
    for (auto const [k, c] : std::views::enumerate(text.substr(from))) {
        switch (in) {
        case In::Literal:
            if (c == '\\')
                in = In::Escape;
            else if (c == quote)
                in = In::Code;
            continue;
        case In::Escape:
            in = In::Literal;
            continue;
        case In::Comment:
            in = c == '\n' ? In::Code : In::Comment;
            continue;
        case In::Slash:
            in = In::Code;
            if (c == '/') {
                in = In::Comment;
                continue;
            }
            break;
        case In::Code:
            break;
        }
        if (c == '"' || c == '\'') {
            quote = c;
            in = In::Literal;
        } else if (c == '/') {
            in = In::Slash;
        } else if (c == '(' || c == '{' || c == '[') {
            ++depth;
        } else if (c == ')' || c == '}' || c == ']') {
            --depth;
        } else if (c == ';' && depth == 0) {
            return from + static_cast<std::size_t>(k);
        }
    }
    return std::string_view::npos;
}

// The program with each `auto name = ...;` declaration whose initialiser calls
// something and whose name the rest of the program never names handed to
// docExampleUnread, so the value is checked where it is kept, which is where
// it is last seen. `where[k]` names the document line of the program's line k.
inline auto wrap_unread_results(std::string_view program, std::vector<std::string> const& where)
    -> std::string {
    static std::regex const kept(
        R"(^(\s*(?:\[\[maybe_unused\]\]\s*)?auto\s+(?:const\s+)?(\w+)\s*=\s*).*)");
    static std::regex const calls(R"(\w\s*\()");
    std::vector<std::size_t> starts{0};
    for (auto const [i, c] : std::views::enumerate(program)) {
        if (c == '\n')
            starts.push_back(static_cast<std::size_t>(i) + 1);
    }
    std::string out;
    std::size_t done = 0;
    for (auto const [k, start] : std::views::enumerate(starts)) {
        if (start < done || static_cast<std::size_t>(k) >= where.size())
            continue;
        auto const line = std::string{program.substr(start, program.find('\n', start) - start)};
        std::smatch m;
        if (!std::regex_match(line, m, kept))
            continue;
        // The value starts at its first character, on the next line when the
        // declaration breaks after its `=`.
        auto const init =
            program.find_first_not_of(" \t\n", start + static_cast<std::size_t>(m.length(1)));
        auto const end = statement_end(program, init);
        if (end == std::string_view::npos)
            continue;
        auto const value = std::string{program.substr(init, end - init)};
        auto const rest = std::string{program.substr(end)};
        if (!std::regex_search(value, calls) ||
            std::regex_search(rest, std::regex{"\\b" + m[2].str() + "\\b"}))
            continue;
        out.append(program.substr(done, init - done));
        out.append("docExampleUnread(\"" + where[static_cast<std::size_t>(k)] + "\", ");
        out.append(value).append(")");
        done = end;
    }
    out.append(program.substr(done));
    return out;
}

// Whether a fragment spells `client` or `backend`, the names the harness's
// client and backend stand behind: only such a fragment needs the compiler's
// report of its undeclared uses before it runs.
inline auto names_harness(std::string_view body) -> bool {
    static std::regex const named(R"(\b(?:client|backend)\b)");
    return std::regex_search(body.begin(), body.end(), named);
}

// A use of `client` or `backend` the compiler found no declaration of: the
// line and the column, a byte's, it reports, and which of the two it names.
struct HarnessUse {
    std::size_t line = 0;
    std::size_t column = 0;
    bool client = false;

    friend auto operator==(HarnessUse const&, HarnessUse const&) -> bool = default;
};

// The uses clang's output on `file` reports undeclared, as `<file>:<line>:
// <column>: error: use of undeclared identifier 'client'`: the declarations
// a fragment writes itself, in any form, are the compiler's to tell apart.
inline auto reported_harness_uses(std::string_view diagnostics, std::string_view file)
    -> std::vector<HarnessUse> {
    static std::regex const reported(
        R"(^(.*):(\d+):(\d+): error: use of undeclared identifier '(client|backend)')");
    std::vector<HarnessUse> uses;
    for (auto const line : diagnostics | std::views::split('\n')) {
        std::string const text{std::string_view{line}};
        std::smatch m;
        if (std::regex_search(text, m, reported) && m.str(1) == file)
            uses.push_back({.line = std::stoul(m.str(2)),
                            .column = std::stoul(m.str(3)),
                            .client = m.str(4) == "client"});
    }
    return uses;
}

// The program with each of `uses` calling the harness's opener of its name,
// so the harness's client and backend, and the runtime with them, open at the
// fragment's first evaluation of one: until then the runtime is down, as a
// reader's program finds it until it starts the runtime or opens a client, so
// a fragment reading a number first fails here as it would there.
inline auto with_harness_client(std::string program, std::vector<HarnessUse> uses) -> std::string {
    std::vector<std::size_t> starts{0};
    for (auto const [i, c] : std::views::enumerate(program)) {
        if (c == '\n')
            starts.push_back(static_cast<std::size_t>(i) + 1);
    }
    auto const place = [](HarnessUse const& use) { return std::pair{use.line, use.column}; };
    std::ranges::sort(uses, std::ranges::greater{}, place);
    auto const repeated = std::ranges::unique(uses, {}, place);
    uses.erase(repeated.begin(), repeated.end());
    for (auto const& use : uses) {
        program.replace(starts.at(use.line - 1) + use.column - 1, use.client ? 6 : 7,
                        use.client ? "doc_harness_detail::harness_client()"
                                   : "doc_harness_detail::harness_backend()");
    }
    return program;
}

// The fragment inside the wrapper, its uses of the harness's names as it
// wrote them: with_harness_client gives them the harness's client.
inline auto wrap_body_fragment(std::string const& body) -> std::string {
    return std::string{k_prologue} + body + std::string{k_epilogue};
}

} // namespace aletheia::test
