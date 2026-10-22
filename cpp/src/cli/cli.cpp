// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// CLI implementation behind aletheia::run_cli (declared in <aletheia/cli.hpp>);
// the aletheia-cli binary (src/cli/main.cpp) is a thin argv wrapper over it,
// and the CLI tests call run_cli directly. It mirrors the Python
// `python -m aletheia` subcommand surface — validate, extract, signals,
// format-dbc, mux-query — by dispatching to the real verified Agda core
// through the dlopen client (no analysis logic is reimplemented here), and
// `template` writes the blank Excel workbook through the binding's own loader
// module, without the core.
//
// There is no `check` subcommand (LTL over a CAN log file): it needs a
// CAN-log reader the C++ binding does not provide. DBC sources are `.dbc`
// text files parsed by the verified text parser; canonical-JSON and `.xlsx`
// inputs are not accepted. Flags may appear before or after positionals, and
// a bare "--" ends them: every token after it is a positional.
//
// Output goes through std::cout and std::cerr so a host that embeds run_cli
// (the CLI tests do) can redirect it; a report that cannot be written is an
// error. The library path is $ALETHEIA_LIB when it names a file, else the
// repository's build/ as seen from the working directory. Exit codes: 0 ok,
// 1 validation failed, 2 error.

#include <aletheia/backend.hpp>
#include <aletheia/cli.hpp>
#include <aletheia/client.hpp>
#include <aletheia/dbc.hpp>
#include <aletheia/detail/checked.hpp>
#include <aletheia/detail/rational_renderer.hpp>
#include <aletheia/excel.hpp>
#include <aletheia/types.hpp>
#include <aletheia/validation.hpp>

#include "detail/loader_utils.hpp"

#include <nlohmann/json.hpp>

#include <algorithm>
#include <cctype>
#include <cerrno>
#include <charconv>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <exception>
#include <expected>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <map>
#include <memory>
#include <optional>
#include <ostream>
#include <ranges>
#include <set>
#include <span>
#include <sstream>
#include <stop_token>
#include <string>
#include <string_view>
#include <system_error>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

namespace {

using aletheia::AletheiaClient;
using aletheia::CanId;
using aletheia::cli_exit_error;
using aletheia::cli_exit_ok;
using aletheia::cli_exit_validation_failed;
using aletheia::DbcDefinition;
using aletheia::DbcMessage;
using aletheia::DbcSignal;
using aletheia::ExtendedId;
using aletheia::StandardId;
using Json = nlohmann::json;

constexpr std::uint32_t k_std_id_max = 0x7FF; // 11-bit standard CAN ID ceiling
constexpr int k_json_indent = 2;

struct Args {
    std::map<std::string, std::string> opts; // value flags (--dbc, --mux, --value)
    std::set<std::string> flags;             // bool flags (--json, --extended)
    std::vector<std::string> positionals;
};

// load_dbc_text failure: the human-readable message every subcommand dies
// with, plus the typed core error when the verified parser itself rejected
// the text (absent for file-level failures: missing path, unsupported
// extension, unreadable file). cmd_validate renders a rejected parse that
// carries validation issues as a normal validation report; every other
// subcommand prints `message` unchanged.
struct DbcLoadError {
    std::string message;
    std::optional<aletheia::AletheiaError> core;
};

} // namespace

// --- output helpers -------------------------------------------------------

static auto die(std::string_view msg) -> int {
    std::cerr << "Error: " << msg << '\n';
    return cli_exit_error;
}

// Refuses the positionals a subcommand does not take, in the words the Python
// CLI's argument parser uses for them.
static auto refuse_unrecognized(std::span<const std::string> extras) -> int {
    return die("unrecognized arguments: " +
               (extras | std::views::join_with(' ') | std::ranges::to<std::string>()));
}

// Writes a whole report to std::cout in one insertion and flushes it, answering
// `outcome` once the stream has taken it. A refusal, at the write or at the
// flush where a full device first fails, is read with the errno it set and
// outranks the outcome: the error exit names the system's reason, or the
// stream's own when the failure set none.
static auto emit_report(std::string_view report, int outcome) -> int {
    errno = 0;
    std::cout << report << std::flush;
    if (std::cout)
        return outcome;
    auto const err = errno;
    return die("writing the report: " +
               (err != 0 ? std::generic_category().message(err)
                         : std::make_error_code(std::io_errc::stream).message()));
}

static auto emit_json(const Json& j, int outcome = cli_exit_ok) -> int {
    return emit_report(j.dump(k_json_indent) + '\n', outcome);
}

// --- client / DBC loading -------------------------------------------------

static auto resolve_lib() -> std::optional<std::filesystem::path> {
    auto found = aletheia::find_ffi_library();
    if (found.empty())
        return std::nullopt;
    return found;
}

static auto make_client() -> std::expected<AletheiaClient, std::string> {
    auto const lib = resolve_lib();
    if (!lib)
        return std::unexpected<std::string>(
            "libaletheia-ffi.so not found; set $ALETHEIA_LIB or run 'cabal run shake -- build'");
    try {
        return AletheiaClient(aletheia::make_ffi_backend(lib.value()),
                              aletheia::cli_logger(std::cerr));
    } catch (const std::exception& e) {
        return std::unexpected<std::string>(std::string{"loading FFI backend: "} + e.what());
    }
}

// Reads a `.dbc` text file and parses it through the verified Agda text
// parser, returning the parse result (DBC + warnings). The kernel's parse
// epilogue IS full DBC validation, so the warnings are the complete
// validation issue list for the parsed DBC (a parse carrying errors is
// rejected by the kernel and surfaces as a DbcLoadError with core issues).
// Canonical-JSON and `.xlsx` inputs are not accepted. The file's size is
// checked against the DBC text bound before it is read, as the loaders do.
// Every byte becomes the character of the same number, encoded as UTF-8 for
// the JSON command, so the kernel decides the file's characters whatever its
// encoding: a byte above 0x7E is refused with its position.
static auto latin1_to_utf8(std::string_view bytes) -> std::string {
    std::string out;
    out.reserve(bytes.size());
    for (const unsigned char byte : bytes) {
        const unsigned value = byte;
        if (value < 0x80U) {
            out.push_back(static_cast<char>(value));
        } else {
            out.push_back(static_cast<char>(0xC0U | (value >> 6U)));
            out.push_back(static_cast<char>(0x80U | (value & 0x3FU)));
        }
    }
    return out;
}

static auto load_dbc_text(AletheiaClient& client, const std::string& path)
    -> std::expected<aletheia::ParsedDBC, DbcLoadError> {
    if (path.empty())
        return std::unexpected(DbcLoadError{.message = "no DBC source (use --dbc <file>.dbc)"});
    if (path.ends_with(".json") || path.ends_with(".xlsx"))
        return std::unexpected(DbcLoadError{
            .message = path + ": the C++ CLI accepts .dbc text input only (not JSON or .xlsx)"});
    if (auto const bound = aletheia::detail::check_file_size_bound(path); !bound)
        return std::unexpected(DbcLoadError{
            .message =
                "reading " + path + ": " + std::string{aletheia::detail::error_of(bound).message()},
            .core = aletheia::detail::error_of(bound),
        });
    const std::ifstream in{path};
    if (!in)
        return std::unexpected(DbcLoadError{.message = "reading " + path});
    std::ostringstream buf;
    buf << in.rdbuf();
    auto parsed = client.parse_dbc_text(std::stop_token{}, latin1_to_utf8(buf.str()));
    if (!parsed)
        return std::unexpected(DbcLoadError{
            .message = "parsing " + path + ": " +
                       std::string{aletheia::detail::error_of(parsed).message()},
            .core = aletheia::detail::error_of(parsed),
        });
    return std::move(parsed).value();
}

// --- value parsing --------------------------------------------------------

static auto parse_can_id(std::string_view s) -> std::optional<std::uint32_t> {
    int base = 10;
    if (s.starts_with("0x") || s.starts_with("0X")) {
        s = s.substr(2);
        base = 16;
    }
    // Materialize a std::string so from_chars reads null-terminated data()
    // (string_view::data() trips bugprone-suspicious-stringview-data-usage).
    // std::to_address(end()) is the arithmetic-free [last) bound — well-defined
    // on a past-the-end iterator ([pointer.conversion] requires no dereference),
    // and data()+size() would trip cppcoreguidelines-pro-bounds-pointer-arithmetic.
    // Cold path.
    const std::string str{s};
    std::uint32_t value = 0;
    auto const* const end = std::to_address(str.end());
    auto const [ptr, ec] = std::from_chars(str.data(), end, value, base);
    if (ec != std::errc{} || ptr != end)
        return std::nullopt;
    return value;
}

static auto make_can_id(std::uint32_t n, bool extended) -> std::optional<CanId> {
    if (extended) {
        if (auto const id = ExtendedId::create(n))
            return CanId{id.value()};
        return std::nullopt;
    }
    if (n > k_std_id_max)
        return std::nullopt;
    if (auto const id = StandardId::create(static_cast<std::uint16_t>(n)))
        return CanId{id.value()};
    return std::nullopt;
}

static auto parse_hex_data(std::string_view s) -> std::optional<std::vector<std::byte>> {
    std::string cleaned;
    for (auto const c : s)
        if (c != ' ' && c != ':')
            cleaned.push_back(c);
    std::string_view view{cleaned};
    if (view.starts_with("0x") || view.starts_with("0X"))
        view = view.substr(2);
    if (view.size() % 2 != 0)
        return std::nullopt;
    std::vector<std::byte> out;
    out.reserve(view.size() / 2);
    for (auto const octet_chars : view | std::views::chunk(2)) {
        const std::string octet{octet_chars.begin(), octet_chars.end()};
        std::uint8_t byte = 0;
        auto const* const end = std::to_address(octet.end());
        auto const [ptr, ec] = std::from_chars(octet.data(), end, byte, 16);
        if (ec != std::errc{} || ptr != end)
            return std::nullopt;
        out.push_back(std::byte{byte});
    }
    return out;
}

// --- argument parsing -----------------------------------------------------

// Classifies argv into value-flags, bool-flags, and positionals. Flags may
// appear in any position (matching the Python argparse UX); "--flag value"
// and "--flag=value" are both accepted. The first bare "--" ends the flags:
// it is neither a flag nor a positional, and every token after it is a
// positional, one spelled like a flag included.
static auto parse_args(std::span<const std::string> args, const std::set<std::string>& value_flags,
                       const std::set<std::string>& bool_flags)
    -> std::expected<Args, std::string> {
    Args out;
    // A cursor rather than a counter: a value flag consumes the argument after
    // it, so the step is a variable number of elements and the consumption is
    // what the loop says.
    while (!args.empty()) {
        const std::string& a = args.front();
        args = aletheia::detail::subspan_at(args, 1);
        if (a == "--") {
            out.positionals.append_range(args);
            break;
        }
        if (!a.starts_with("--")) {
            out.positionals.push_back(a);
            continue;
        }
        auto name = a.substr(2);
        std::optional<std::string> inline_val;
        if (auto const eq = name.find('='); eq != std::string::npos) {
            inline_val = name.substr(eq + 1);
            name = name.substr(0, eq);
        }
        if (bool_flags.contains(name)) {
            out.flags.insert(name);
        } else if (value_flags.contains(name)) {
            if (inline_val) {
                out.opts[name] = inline_val.value();
            } else if (!args.empty()) {
                out.opts[name] = args.front();
                args = aletheia::detail::subspan_at(args, 1);
            } else {
                return std::unexpected<std::string>("flag --" + name + " requires a value");
            }
        } else {
            return std::unexpected<std::string>("unknown flag: " + a);
        }
    }
    return out;
}

static auto opt_or(const Args& a, const std::string& key) -> std::string {
    auto const it = a.opts.find(key);
    return it == a.opts.end() ? std::string{} : it->second;
}

// --- subcommands ----------------------------------------------------------

// The human-readable validation report: a one-line verdict, then the
// numbered issue list when there is one.
static auto validation_text(bool has_errors, const std::vector<aletheia::ValidationIssue>& issues)
    -> std::string {
    if (issues.empty())
        return "Validation passed: no issues found\n";
    std::ostringstream out;
    out << (has_errors ? "Validation FAILED" : "Validation passed with warnings") << " ("
        << issues.size() << " issues)\n\n";
    int n = 1;
    for (auto const& i : issues) {
        std::string sev{aletheia::to_string(i.severity)};
        std::ranges::transform(sev, sev.begin(),
                               [](unsigned char c) { return static_cast<char>(std::toupper(c)); });
        out << "  " << n++ << ". [" << sev << "] " << aletheia::issue_code_label(i) << ": "
            << i.detail << '\n';
    }
    return std::move(out).str();
}

// Renders a validation outcome in both the --json and human-readable forms;
// shared by the parse-success path (the parse warnings, has_errors=false)
// and the rejected-parse path (a handler_validation_failed error carrying
// issues), so both print the identical report shape. The exit code reflects
// the validation outcome in both output modes: a pipeline running --json
// still needs exit 1 on failure.
static auto render_validation(bool has_errors, const std::vector<aletheia::ValidationIssue>& issues,
                              bool as_json) -> int {
    auto const outcome = has_errors ? cli_exit_validation_failed : cli_exit_ok;
    if (!as_json)
        return emit_report(validation_text(has_errors, issues), outcome);
    auto arr = Json::array();
    for (auto const& i : issues)
        arr.push_back({{"severity", std::string{aletheia::to_string(i.severity)}},
                       {"code", std::string{aletheia::issue_code_label(i)}},
                       {"detail", i.detail}});
    return emit_json({{"status", has_errors ? "fail" : "pass"},
                      {"has_errors", has_errors},
                      {"total_issues", issues.size()},
                      {"issues", arr}},
                     outcome);
}

// `has_errors` for a rejected parse is derived from the decoded issue
// severities (the kernel only rejects when at least one error is present;
// the wire flag was already required well-typed by the decoder's lift).
static auto has_error_issue(const std::vector<aletheia::ValidationIssue>& issues) -> bool {
    return std::ranges::any_of(issues, [](const aletheia::ValidationIssue& i) {
        return i.severity == aletheia::IssueSeverity::Error;
    });
}

static auto cmd_validate(const Args& a) -> int {
    auto client = make_client();
    if (!client)
        return die(aletheia::detail::error_of(client));
    auto const def = load_dbc_text(client.value(), opt_or(a, "dbc"));
    if (!def) {
        // A parse rejected with validation issues renders as a normal
        // validation report; any other load failure stays fatal.
        auto const& core = aletheia::detail::error_of(def).core;
        if (core.has_value()) {
            auto const& issues = core.value().issues();
            if (issues.has_value())
                return render_validation(has_error_issue(issues.value()), issues.value(),
                                         a.flags.contains("json"));
        }
        return die(aletheia::detail::error_of(def).message);
    }
    // The kernel's parse epilogue IS full DBC validation: on parse success
    // has_errors is structurally false and the parse warnings are the
    // complete issue list — no second kernel round-trip needed.
    return render_validation(false, def.value().warnings, a.flags.contains("json"));
}

// Exact rational -> JSON for `extract --json`: a bare integer when the
// denominator is 1, else the `{"numerator","denominator"}` object — the same
// wire SHAPE as Python's FractionJSONEncoder and the binding's own DBC canonical
// JSON (`json_serialize.cpp::rational_to_json`).  The parsed value is identical
// across bindings; the byte order is not (nlohmann's default object is a sorted
// map, so keys emit alphabetically — `denominator` before `numerator` — whereas
// Python emits insertion order).  The float principle bars a lossy conversion to
// double here (this is machine-readable output a consumer parses), and the type
// offers none.  Extraction values
// are kernel-canonical (reduced, positive denominator), so no gcd / INT64_MIN
// normalisation is needed (unlike `rational_to_json`, which guards arbitrary
// caller-built rationals on the DBC-serialize path).
static auto extract_value_to_json(const aletheia::Rational& r) -> Json {
    if (r.denominator() == 1)
        return r.numerator();
    return Json{{"numerator", r.numerator()}, {"denominator", r.denominator()}};
}

// Exact rational -> human-readable string for CLI text output, via the verified
// kernel renderer (Agda `formatℚ`): a terminating decimal (`1/4` -> "0.25") or an
// exact fraction (`1/3` -> "1/3"), never a lossy conversion to double.  Byte-identical
// with Go's FormatRational and Python's format_rational (same kernel FFI).  The
// CLI always has a live client here, so the RTS is up (format_rational_ffi throws
// only when it is not).
static auto render_rational(const aletheia::Rational& r) -> std::string {
    return aletheia::detail::format_rational_ffi(r.numerator(), r.denominator());
}

static auto cmd_extract(const Args& a) -> int {
    if (a.positionals.size() < 2)
        return die("extract requires <can_id> <data> positional arguments");
    if (a.positionals.size() > 2)
        return refuse_unrecognized(a.positionals | std::views::drop(2));
    auto const can_id = parse_can_id(a.positionals.at(0));
    if (!can_id)
        return die("invalid CAN ID: " + a.positionals.at(0));
    auto const data = parse_hex_data(a.positionals.at(1));
    if (!data)
        return die("invalid hex data: " + a.positionals.at(1));
    auto const extended = a.flags.contains("extended");
    auto client = make_client();
    if (!client)
        return die(aletheia::detail::error_of(client));
    auto const def = load_dbc_text(client.value(), opt_or(a, "dbc"));
    if (!def)
        return die(aletheia::detail::error_of(def).message);
    auto const id = make_can_id(can_id.value(), extended);
    if (!id)
        return die("invalid CAN ID for the selected width");
    auto const* msg = def.value().dbc.message_by_id(id.value());
    if (msg == nullptr)
        return die("CAN ID not found in DBC");
    auto const res =
        client.value().extract_signals(std::stop_token{}, id.value(), msg->dlc, data.value());
    if (!res)
        return die(aletheia::detail::error_of(res).message());

    if (a.flags.contains("json")) {
        auto values = Json::object();
        for (auto const& v : res.value().values)
            values[v.name.get()] = extract_value_to_json(v.value.get());
        auto errors = Json::object();
        for (auto const& e : res.value().errors)
            errors[e.name.get()] = e.reason;
        auto absent = Json::array();
        for (auto const& s : res.value().absent)
            absent.push_back(s.get());
        return emit_json({{"can_id", can_id.value()},
                          {"extended", extended},
                          {"values", values},
                          {"errors", errors},
                          {"absent", absent}});
    }
    std::ostringstream out;
    out << "CAN ID 0x" << std::hex << can_id.value() << std::dec << " (" << msg->name.get()
        << "):\n\n";
    if (res.value().values.empty())
        out << "  (no signals)\n";
    for (auto const& v : res.value().values)
        out << "  " << v.name.get() << " = " << render_rational(v.value.get()) << '\n';
    for (auto const& e : res.value().errors)
        out << "  error " << e.name.get() << ": " << e.reason << '\n';
    return emit_report(std::move(out).str(), cli_exit_ok);
}

static void print_signal_line(std::ostream& out, const aletheia::DbcSignal& sig) {
    const std::string_view order =
        sig.byte_order == aletheia::ByteOrder::LittleEndian ? "LE" : "BE";
    const std::string_view sign = sig.is_signed ? "signed" : "unsigned";
    out << "  " << sig.name.get() << " bits[" << sig.start_bit.get() << ":"
        << static_cast<unsigned>(sig.bit_length.get()) << "] " << order << " " << sign << " x"
        << render_rational(sig.factor.get()) << " " << render_rational(sig.offset.get()) << " "
        << sig.unit.get() << '\n';
}

static auto cmd_signals(const Args& a) -> int {
    auto client = make_client();
    if (!client)
        return die(aletheia::detail::error_of(client));
    auto const def = load_dbc_text(client.value(), opt_or(a, "dbc"));
    if (!def)
        return die(aletheia::detail::error_of(def).message);
    if (a.flags.contains("json"))
        return emit_report(aletheia::to_canonical_json(def.value().dbc) + '\n', cli_exit_ok);
    std::ostringstream out;
    std::size_t total = 0;
    for (auto const& msg : def.value().dbc.messages) {
        out << "Message 0x" << std::hex << aletheia::can_id_value(msg.id) << std::dec << " "
            << msg.name.get() << '\n';
        for (auto const& sig : msg.signals) {
            ++total;
            print_signal_line(out, sig);
        }
    }
    out << '\n' << def.value().dbc.messages.size() << " messages, " << total << " signals\n";
    return emit_report(std::move(out).str(), cli_exit_ok);
}

static auto cmd_format_dbc(const Args& a) -> int {
    auto client = make_client();
    if (!client)
        return die(aletheia::detail::error_of(client));
    auto const def = load_dbc_text(client.value(), opt_or(a, "dbc"));
    if (!def)
        return die(aletheia::detail::error_of(def).message);
    auto const canonical = client.value().format_dbc(std::stop_token{});
    if (!canonical)
        return die(aletheia::detail::error_of(canonical).message());
    return emit_report(aletheia::to_canonical_json(canonical.value()) + '\n', cli_exit_ok);
}

static auto resolve_mux_message(const DbcDefinition& def, const std::string& ident, bool extended)
    -> const DbcMessage* {
    if (auto const can_id = parse_can_id(ident))
        if (auto const id = make_can_id(can_id.value(), extended))
            if (auto const* msg = def.message_by_id(id.value()))
                return msg;
    return def.message_by_name(aletheia::MessageName{ident});
}

// The line both mux-query modes open with, and the one the Go and Python
// interfaces print: the identifier, the name and the payload length.
static void print_message_header(std::ostream& out, const DbcMessage& msg) {
    out << "Message 0x" << std::hex << aletheia::can_id_value(msg.id) << std::dec << " "
        << msg.name.get() << " (DLC " << aletheia::dlc_to_bytes(msg.dlc) << ")\n";
}

// The signal names of one mux value, comma-separated, as the other two
// interfaces print them.
static auto join_signal_names(std::span<const DbcSignal> sigs) -> std::string {
    std::string out;
    for (auto const& s : sigs) {
        if (!out.empty())
            out += ", ";
        out += s.name.get();
    }
    return out;
}

// mux-query selector mode: the signals present for one (multiplexor, value).
static auto mux_selector(const DbcMessage& msg, const std::string& mux, std::uint32_t value,
                         bool as_json) -> int {
    auto const sigs =
        msg.signals_for_mux_value(aletheia::SignalName{mux}, aletheia::MultiplexValue{value});
    if (as_json) {
        auto names = Json::array();
        for (auto const& s : sigs)
            names.push_back(s.name.get());
        return emit_json({{"message_id", aletheia::can_id_value(msg.id)},
                          {"message_name", msg.name.get()},
                          {"multiplexor", mux},
                          {"value", value},
                          {"signals", names}});
    }
    std::ostringstream out;
    print_message_header(out, msg);
    out << "Multiplexor " << mux << " = " << value << ": " << sigs.size() << " signals present\n";
    for (auto const& s : sigs)
        out << "  " << s.name.get() << '\n';
    return emit_report(std::move(out).str(), cli_exit_ok);
}

// mux-query summary mode: every multiplexor, its values, and their signals.
static auto mux_summary(const DbcMessage& msg, bool as_json) -> int {
    if (as_json) {
        auto muxes = Json::array();
        for (auto const& name : msg.multiplexor_names()) {
            auto vals = Json::array();
            for (auto const v : msg.multiplex_values(name)) {
                auto sigs = Json::array();
                for (auto const& s : msg.signals_for_mux_value(name, v))
                    sigs.push_back(s.name.get());
                vals.push_back({{"value", v.get()}, {"signals", sigs}});
            }
            muxes.push_back({{"name", name.get()}, {"values", vals}});
        }
        return emit_json({{"message_id", aletheia::can_id_value(msg.id)},
                          {"message_name", msg.name.get()},
                          {"is_multiplexed", msg.is_multiplexed()},
                          {"multiplexors", muxes}});
    }
    std::ostringstream out;
    print_message_header(out, msg);
    // A message that is not multiplexed names no multiplexor, so the loop
    // adds nothing after its line.
    if (!msg.is_multiplexed())
        out << "  Not multiplexed: all " << msg.signals.size() << " signals are always present.\n";
    for (auto const& name : msg.multiplexor_names()) {
        out << "  " << name.get() << ":\n";
        for (auto const v : msg.multiplex_values(name)) {
            auto const sigs = msg.signals_for_mux_value(name, v);
            out << "    value " << v.get() << ": " << sigs.size() << " signals ("
                << join_signal_names(sigs) << ")\n";
        }
    }
    return emit_report(std::move(out).str(), cli_exit_ok);
}

static auto cmd_mux_query(const Args& a) -> int {
    if (a.positionals.empty())
        return die("mux-query requires a <message> positional argument (CAN ID or name)");
    if (a.positionals.size() > 1)
        return refuse_unrecognized(a.positionals | std::views::drop(1));
    auto client = make_client();
    if (!client)
        return die(aletheia::detail::error_of(client));
    auto const def = load_dbc_text(client.value(), opt_or(a, "dbc"));
    if (!def)
        return die(aletheia::detail::error_of(def).message);
    auto const* msg =
        resolve_mux_message(def.value().dbc, a.positionals.at(0), a.flags.contains("extended"));
    if (msg == nullptr)
        return die("message not found by id or name: " + a.positionals.at(0));

    // `--mux NAME --value N` (both or neither) selects one multiplexor value;
    // otherwise print the full summary. Mirrors the Python/Go CLIs.
    auto const has_mux = a.opts.contains("mux");
    auto const has_value = a.opts.contains("value");
    if (has_mux != has_value)
        return die("--mux and --value must be provided together");
    if (!has_mux)
        return mux_summary(*msg, a.flags.contains("json"));

    const std::string& vstr = a.opts.at("value");
    std::uint32_t value = 0;
    auto const* const vend = std::to_address(vstr.end());
    if (auto const [ptr, ec] = std::from_chars(vstr.data(), vend, value);
        ec != std::errc{} || ptr != vend) {
        return die("invalid --value: " + vstr);
    }
    return mux_selector(*msg, a.opts.at("mux"), value, a.flags.contains("json"));
}

// Writes the blank workbook the Excel loaders read; a path that exists is
// refused and left as it was.
static auto cmd_template(const Args& a) -> int {
    if (a.positionals.empty())
        return die("template requires one <path> positional argument");
    if (a.positionals.size() > 1)
        return refuse_unrecognized(a.positionals | std::views::drop(1));
    auto const& path = a.positionals.at(0);
    if (auto const made = aletheia::create_excel_template(path); !made)
        return die(aletheia::detail::error_of(made).message());
    return emit_report("Template written to " + path + '\n', cli_exit_ok);
}

constexpr std::string_view k_usage =
    "aletheia: formally verified CAN signal analysis (C++ CLI)\n\n"
    "Usage: aletheia-cli <command> [flags] [args]\n\n"
    "Commands:\n"
    "  validate    validate a DBC definition for structural issues\n"
    "  extract     decode signals from a single CAN frame\n"
    "  signals     list signals defined in a DBC file\n"
    "  format-dbc  re-export a DBC as canonical JSON via the Agda core\n"
    "  mux-query   inspect multiplexor structure of a DBC message\n"
    "  template    write a blank Excel workbook to fill in with a DBC and checks\n\n"
    "DBC source: --dbc <file>.dbc (verified text parser). Flags may go before or after "
    "positionals.\n"
    "Library path: $ALETHEIA_LIB or a default location.";

// Dispatch the parsed command; separated from run_cli so run_cli stays
// exception-free (bugprone-exception-escape) via a single try/catch.
static auto dispatch(const std::string& cmd, std::span<const std::string> rest) -> int {
    const std::set<std::string> bool_flags{"json", "extended"};
    if (cmd == "validate" || cmd == "signals" || cmd == "format-dbc") {
        auto const parsed = parse_args(rest, {"dbc"}, bool_flags);
        if (!parsed)
            return die(aletheia::detail::error_of(parsed));
        // None of the three takes a positional: one given is refused before
        // any DBC is read.
        if (auto const& extra = parsed.value().positionals; !extra.empty())
            return refuse_unrecognized(extra);
        if (cmd == "validate")
            return cmd_validate(parsed.value());
        if (cmd == "signals")
            return cmd_signals(parsed.value());
        return cmd_format_dbc(parsed.value());
    }
    if (cmd == "extract") {
        auto const parsed = parse_args(rest, {"dbc"}, bool_flags);
        if (!parsed)
            return die(aletheia::detail::error_of(parsed));
        return cmd_extract(parsed.value());
    }
    if (cmd == "mux-query") {
        auto const parsed = parse_args(rest, {"dbc", "mux", "value"}, bool_flags);
        if (!parsed)
            return die(aletheia::detail::error_of(parsed));
        return cmd_mux_query(parsed.value());
    }
    if (cmd == "template") {
        auto const parsed = parse_args(rest, {}, {});
        if (!parsed)
            return die(aletheia::detail::error_of(parsed));
        return cmd_template(parsed.value());
    }
    if (cmd == "check") {
        std::cerr << "Error: 'check' is not available in the C++ CLI: it needs a CAN-log reader "
                     "the binding does not provide. Use the Python CLI for log-file checking.\n";
        return cli_exit_error;
    }
    if (cmd == "-h" || cmd == "--help" || cmd == "help") {
        std::cout << k_usage << '\n';
        return cli_exit_ok;
    }
    std::cerr << "Error: unknown command '" << cmd << "'\n\n" << k_usage << '\n';
    return cli_exit_error;
}

namespace aletheia {

auto cli_logger(std::ostream& out) -> Logger {
    return Logger(
        [&out](const LogRecord& r) {
            out << r.event;
            for (auto const& [key, value] : r.fields) {
                out << ' ' << key << '=';
                std::visit(
                    [&out](auto const& v) {
                        if constexpr (std::is_same_v<std::decay_t<decltype(v)>, bool>)
                            out << (v ? "true" : "false");
                        else
                            out << v;
                    },
                    value);
            }
            out << '\n';
        },
        LogLevel::Warn);
}

auto run_cli(std::span<const std::string> args) noexcept -> int {
    try {
        if (args.empty()) {
            std::cerr << k_usage << '\n';
            return cli_exit_error;
        }
        return dispatch(args.front(), aletheia::detail::subspan_at(args, 1));
    } catch (const std::exception& e) {
        return die(std::string{"unexpected error: "} + e.what());
    } catch (...) {
        return die("unexpected error");
    }
}

} // namespace aletheia
