// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// CLI implementation behind aletheia::run_cli (declared in <aletheia/cli.hpp>);
// the aletheia-cli binary (src/cli/main.cpp) is a thin argv wrapper over it,
// and the CLI tests call run_cli directly. It mirrors the Python
// `python -m aletheia` subcommand surface — validate, extract, signals,
// format-dbc, mux-query — by dispatching to the real verified Agda core
// through the dlopen client (no analysis logic is reimplemented here).
//
// The `check` subcommand (LTL over a CAN log file) is intentionally absent:
// it needs a verified CAN-log reader the C++ binding does not yet provide
// (Phase 6 item — the python-can replacement). DBC sources are `.dbc` text
// files parsed by the verified text parser; canonical-JSON and `.xlsx`
// inputs are not yet wired. Flags may appear before or after positionals.
//
// The library path is resolved from $ALETHEIA_LIB, else common build/install
// locations. Exit codes: 0 ok, 1 violations / validation failed, 2 error.

#include <aletheia/backend.hpp>
#include <aletheia/cli.hpp>
#include <aletheia/client.hpp>
#include <aletheia/dbc.hpp>
#include <aletheia/detail/rational_renderer.hpp>
#include <aletheia/types.hpp>
#include <aletheia/validation.hpp>

#include <nlohmann/json.hpp>

#include <cctype>
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
#include <set>
#include <span>
#include <sstream>
#include <stop_token>
#include <string>
#include <string_view>
#include <system_error>
#include <vector>

namespace {

using aletheia::AletheiaClient;
using aletheia::CanId;
using aletheia::DbcDefinition;
using aletheia::DbcMessage;
using aletheia::ExtendedId;
using aletheia::StandardId;
using Json = nlohmann::json;

constexpr int k_exit_ok = 0;
constexpr int k_exit_violations = 1;
constexpr int k_exit_error = 2;
constexpr std::uint32_t k_std_id_max = 0x7FF; // 11-bit standard CAN ID ceiling
constexpr int k_json_indent = 2;

struct Args {
    std::map<std::string, std::string> opts; // value flags (--dbc, --mux, --value)
    std::set<std::string> flags;             // bool flags (--json, --extended)
    std::vector<std::string> positionals;
};

} // namespace

// --- output helpers -------------------------------------------------------

static auto die(std::string_view msg) -> int {
    std::cerr << "Error: " << msg << '\n';
    return k_exit_error;
}

static auto emit_json(const Json& j) -> int {
    std::cout << j.dump(k_json_indent) << '\n';
    return k_exit_ok;
}

// --- client / DBC loading -------------------------------------------------

static auto resolve_lib() -> std::optional<std::filesystem::path> {
    if (const char* env = std::getenv("ALETHEIA_LIB"); env != nullptr && *env != '\0')
        return std::filesystem::path{env};
    for (const auto* cand :
         {"build/libaletheia-ffi.so", "../build/libaletheia-ffi.so",
          "../../build/libaletheia-ffi.so", "/usr/local/lib/libaletheia-ffi.so"}) {
        std::error_code ec;
        if (std::filesystem::exists(cand, ec))
            return std::filesystem::path{cand};
    }
    return std::nullopt;
}

static auto make_client() -> std::expected<AletheiaClient, std::string> {
    auto lib = resolve_lib();
    if (!lib)
        return std::unexpected<std::string>(
            "libaletheia-ffi.so not found; set $ALETHEIA_LIB or run 'cabal run shake -- build'");
    try {
        return AletheiaClient(aletheia::make_ffi_backend(*lib));
    } catch (const std::exception& e) {
        return std::unexpected<std::string>(std::string{"loading FFI backend: "} + e.what());
    }
}

// Reads a `.dbc` text file and parses it through the verified Agda text parser.
// Canonical-JSON and `.xlsx` inputs are not yet wired.
static auto load_dbc_text(AletheiaClient& client, const std::string& path)
    -> std::expected<DbcDefinition, std::string> {
    if (path.empty())
        return std::unexpected<std::string>("no DBC source (use --dbc <file>.dbc)");
    if (path.ends_with(".json") || path.ends_with(".xlsx"))
        return std::unexpected<std::string>(
            path + ": only .dbc text input is supported by the C++ CLI yet "
                   "(JSON / .xlsx input not wired)");
    const std::ifstream in{path};
    if (!in)
        return std::unexpected<std::string>("reading " + path);
    std::ostringstream buf;
    buf << in.rdbuf();
    auto parsed = client.parse_dbc_text(std::stop_token{}, buf.str());
    if (!parsed)
        return std::unexpected<std::string>("parsing " + path + ": " +
                                            std::string{parsed.error().message()});
    return parsed->dbc;
}

// --- value parsing --------------------------------------------------------

static auto parse_can_id(std::string_view s) -> std::optional<std::uint32_t> {
    int base = 10;
    if (s.starts_with("0x") || s.starts_with("0X")) {
        s.remove_prefix(2);
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
    const auto* const end = std::to_address(str.end());
    auto [ptr, ec] = std::from_chars(str.data(), end, value, base);
    if (ec != std::errc{} || ptr != end)
        return std::nullopt;
    return value;
}

static auto make_can_id(std::uint32_t n, bool extended) -> std::optional<CanId> {
    if (extended) {
        if (auto id = ExtendedId::create(n))
            return CanId{*id};
        return std::nullopt;
    }
    if (n > k_std_id_max)
        return std::nullopt;
    if (auto id = StandardId::create(static_cast<std::uint16_t>(n)))
        return CanId{*id};
    return std::nullopt;
}

static auto parse_hex_data(std::string_view s) -> std::optional<std::vector<std::byte>> {
    std::string cleaned;
    for (const char c : s)
        if (c != ' ' && c != ':')
            cleaned.push_back(c);
    std::string_view view{cleaned};
    if (view.starts_with("0x") || view.starts_with("0X"))
        view.remove_prefix(2);
    if (view.size() % 2 != 0)
        return std::nullopt;
    std::vector<std::byte> out;
    out.reserve(view.size() / 2);
    for (std::size_t i = 0; i < view.size(); i += 2) {
        const std::string octet{view.substr(i, 2)};
        std::uint8_t byte = 0;
        const auto* const end = std::to_address(octet.end());
        auto [ptr, ec] = std::from_chars(octet.data(), end, byte, 16);
        if (ec != std::errc{} || ptr != end)
            return std::nullopt;
        out.push_back(std::byte{byte});
    }
    return out;
}

// --- argument parsing -----------------------------------------------------

// Classifies argv into value-flags, bool-flags, and positionals. Flags may
// appear in any position (matching the Python argparse UX); "--flag value"
// and "--flag=value" are both accepted.
static auto parse_args(std::span<const std::string> args, const std::set<std::string>& value_flags,
                       const std::set<std::string>& bool_flags)
    -> std::expected<Args, std::string> {
    Args out;
    for (std::size_t i = 0; i < args.size(); ++i) {
        const std::string& a = args[i];
        if (!a.starts_with("--")) {
            out.positionals.push_back(a);
            continue;
        }
        std::string name = a.substr(2);
        std::optional<std::string> inline_val;
        if (auto eq = name.find('='); eq != std::string::npos) {
            inline_val = name.substr(eq + 1);
            name = name.substr(0, eq);
        }
        if (bool_flags.contains(name)) {
            out.flags.insert(name);
        } else if (value_flags.contains(name)) {
            if (inline_val)
                out.opts[name] = *inline_val;
            else if (i + 1 < args.size())
                out.opts[name] = args[++i];
            else
                return std::unexpected<std::string>("flag --" + name + " requires a value");
        } else {
            return std::unexpected<std::string>("unknown flag: " + a);
        }
    }
    return out;
}

static auto opt_or(const Args& a, const std::string& key) -> std::string {
    auto it = a.opts.find(key);
    return it == a.opts.end() ? std::string{} : it->second;
}

// --- subcommands ----------------------------------------------------------

static auto cmd_validate(const Args& a) -> int {
    auto client = make_client();
    if (!client)
        return die(client.error());
    auto def = load_dbc_text(*client, opt_or(a, "dbc"));
    if (!def)
        return die(def.error());
    auto res = client->validate_dbc(std::stop_token{}, *def);
    if (!res)
        return die(std::string{res.error().message()});

    if (a.flags.contains("json")) {
        Json issues = Json::array();
        for (const auto& i : res->issues)
            issues.push_back({{"severity", std::string{aletheia::to_string(i.severity)}},
                              {"code", std::string{aletheia::issue_code_label(i)}},
                              {"detail", i.detail}});
        return emit_json({{"status", res->has_errors ? "fail" : "pass"},
                          {"has_errors", res->has_errors},
                          {"total_issues", res->issues.size()},
                          {"issues", issues}});
    }
    if (res->issues.empty()) {
        std::cout << "Validation passed: no issues found\n";
        return k_exit_ok;
    }
    std::cout << (res->has_errors ? "Validation FAILED" : "Validation passed with warnings") << " ("
              << res->issues.size() << " issues)\n\n";
    int n = 1;
    for (const auto& i : res->issues) {
        std::string sev{aletheia::to_string(i.severity)};
        for (char& c : sev)
            c = static_cast<char>(std::toupper(static_cast<unsigned char>(c)));
        std::cout << "  " << n++ << ". [" << sev << "] " << aletheia::issue_code_label(i) << ": "
                  << i.detail << '\n';
    }
    return res->has_errors ? k_exit_violations : k_exit_ok;
}

// Exact rational -> JSON for `extract --json`: a bare integer when the
// denominator is 1, else the `{"numerator","denominator"}` object — the same
// wire SHAPE as Python's FractionJSONEncoder and the binding's own DBC canonical
// JSON (`json_serialize.cpp::rational_to_json`).  The parsed value is identical
// across bindings; the byte order is not (nlohmann's default object is a sorted
// map, so keys emit alphabetically — `denominator` before `numerator` — whereas
// Python emits insertion order).  The float principle bars a lossy `to_double()`
// here (this is machine-readable output a consumer parses).  Extraction values
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
// exact fraction (`1/3` -> "1/3"), never a lossy `to_double()`.  Byte-identical
// with Go's FormatRational and Python's format_rational (same kernel FFI).  The
// CLI always has a live client here, so the RTS is up (format_rational_ffi throws
// only when it is not).
static auto render_rational(const aletheia::Rational& r) -> std::string {
    return aletheia::detail::format_rational_ffi(r.numerator(), r.denominator());
}

static auto cmd_extract(const Args& a) -> int {
    if (a.positionals.size() != 2)
        return die("extract requires <can_id> <data> positional arguments");
    auto can_id = parse_can_id(a.positionals[0]);
    if (!can_id)
        return die("invalid CAN ID: " + a.positionals[0]);
    auto data = parse_hex_data(a.positionals[1]);
    if (!data)
        return die("invalid hex data: " + a.positionals[1]);
    const bool extended = a.flags.contains("extended");
    auto client = make_client();
    if (!client)
        return die(client.error());
    auto def = load_dbc_text(*client, opt_or(a, "dbc"));
    if (!def)
        return die(def.error());
    auto id = make_can_id(*can_id, extended);
    if (!id)
        return die("invalid CAN ID for the selected width");
    const DbcMessage* msg = def->message_by_id(*id);
    if (msg == nullptr)
        return die("CAN ID not found in DBC");
    auto res = client->extract_signals(std::stop_token{}, *id, msg->dlc, *data);
    if (!res)
        return die(std::string{res.error().message()});

    if (a.flags.contains("json")) {
        Json values = Json::object();
        for (const auto& v : res->values)
            values[v.name.get()] = extract_value_to_json(v.value.get());
        Json errors = Json::object();
        for (const auto& e : res->errors)
            errors[e.name.get()] = e.reason;
        Json absent = Json::array();
        for (const auto& s : res->absent)
            absent.push_back(s.get());
        return emit_json({{"can_id", *can_id},
                          {"extended", extended},
                          {"values", values},
                          {"errors", errors},
                          {"absent", absent}});
    }
    std::cout << "CAN ID 0x" << std::hex << *can_id << std::dec << " (" << msg->name.get()
              << "):\n\n";
    if (res->values.empty())
        std::cout << "  (no signals)\n";
    for (const auto& v : res->values)
        std::cout << "  " << v.name.get() << " = " << render_rational(v.value.get()) << '\n';
    for (const auto& e : res->errors)
        std::cout << "  error " << e.name.get() << ": " << e.reason << '\n';
    return k_exit_ok;
}

static void print_signal_line(const aletheia::DbcSignal& sig) {
    const std::string_view order =
        sig.byte_order == aletheia::ByteOrder::LittleEndian ? "LE" : "BE";
    const std::string_view sign = sig.is_signed ? "signed" : "unsigned";
    std::cout << "  " << sig.name.get() << " bits[" << sig.start_bit.get() << ":"
              << static_cast<unsigned>(sig.bit_length.get()) << "] " << order << " " << sign << " x"
              << render_rational(sig.factor.get()) << " " << render_rational(sig.offset.get())
              << " " << sig.unit.get() << '\n';
}

static auto cmd_signals(const Args& a) -> int {
    auto client = make_client();
    if (!client)
        return die(client.error());
    auto def = load_dbc_text(*client, opt_or(a, "dbc"));
    if (!def)
        return die(def.error());
    if (a.flags.contains("json")) {
        std::cout << aletheia::to_canonical_json(*def) << '\n';
        return k_exit_ok;
    }
    std::size_t total = 0;
    for (const auto& msg : def->messages) {
        std::cout << "Message 0x" << std::hex << aletheia::can_id_value(msg.id) << std::dec << " "
                  << msg.name.get() << '\n';
        for (const auto& sig : msg.signals) {
            ++total;
            print_signal_line(sig);
        }
    }
    std::cout << '\n' << def->messages.size() << " messages, " << total << " signals\n";
    return k_exit_ok;
}

static auto cmd_format_dbc(const Args& a) -> int {
    auto client = make_client();
    if (!client)
        return die(client.error());
    auto def = load_dbc_text(*client, opt_or(a, "dbc"));
    if (!def)
        return die(def.error());
    auto canonical = client->format_dbc(std::stop_token{});
    if (!canonical)
        return die(std::string{canonical.error().message()});
    std::cout << aletheia::to_canonical_json(*canonical) << '\n';
    return k_exit_ok;
}

static auto resolve_mux_message(const DbcDefinition& def, const std::string& ident, bool extended)
    -> const DbcMessage* {
    if (auto can_id = parse_can_id(ident))
        if (auto id = make_can_id(*can_id, extended))
            if (const DbcMessage* msg = def.message_by_id(*id))
                return msg;
    return def.message_by_name(aletheia::MessageName{ident});
}

// mux-query selector mode: the signals present for one (multiplexor, value).
static auto mux_selector(const DbcMessage& msg, const std::string& mux, std::uint32_t value,
                         bool as_json) -> int {
    const auto sigs =
        msg.signals_for_mux_value(aletheia::SignalName{mux}, aletheia::MultiplexValue{value});
    if (as_json) {
        Json names = Json::array();
        for (const auto& s : sigs)
            names.push_back(s.name.get());
        return emit_json({{"message_id", aletheia::can_id_value(msg.id)},
                          {"message_name", msg.name.get()},
                          {"multiplexor", mux},
                          {"value", value},
                          {"signals", names}});
    }
    std::cout << "Message 0x" << std::hex << aletheia::can_id_value(msg.id) << std::dec << " "
              << msg.name.get() << " — " << mux << " = " << value << ": " << sigs.size()
              << " signals\n";
    for (const auto& s : sigs)
        std::cout << "  " << s.name.get() << '\n';
    return k_exit_ok;
}

// mux-query summary mode: every multiplexor, its values, and their signals.
static auto mux_summary(const DbcMessage& msg, bool as_json) -> int {
    if (as_json) {
        Json muxes = Json::array();
        for (const auto& name : msg.multiplexor_names()) {
            Json vals = Json::array();
            for (auto v : msg.multiplex_values(name)) {
                Json sigs = Json::array();
                for (const auto& s : msg.signals_for_mux_value(name, v))
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
    std::cout << "Message 0x" << std::hex << aletheia::can_id_value(msg.id) << std::dec << " "
              << msg.name.get() << '\n';
    if (!msg.is_multiplexed()) {
        std::cout << "  Not multiplexed — " << msg.signals.size() << " signals always present.\n";
        return k_exit_ok;
    }
    for (const auto& name : msg.multiplexor_names()) {
        std::cout << "  " << name.get() << ":\n";
        for (auto v : msg.multiplex_values(name)) {
            auto sigs = msg.signals_for_mux_value(name, v);
            std::cout << "    value " << v.get() << ": " << sigs.size() << " signals\n";
        }
    }
    return k_exit_ok;
}

static auto cmd_mux_query(const Args& a) -> int {
    if (a.positionals.size() != 1)
        return die("mux-query requires a <message> positional argument (CAN ID or name)");
    auto client = make_client();
    if (!client)
        return die(client.error());
    auto def = load_dbc_text(*client, opt_or(a, "dbc"));
    if (!def)
        return die(def.error());
    const DbcMessage* msg =
        resolve_mux_message(*def, a.positionals[0], a.flags.contains("extended"));
    if (msg == nullptr)
        return die("message not found by id or name: " + a.positionals[0]);

    // `--mux NAME --value N` (both or neither) selects one multiplexor value;
    // otherwise print the full summary. Mirrors the Python/Go CLIs.
    const bool has_mux = a.opts.contains("mux");
    const bool has_value = a.opts.contains("value");
    if (has_mux != has_value)
        return die("--mux and --value must be provided together");
    if (!has_mux)
        return mux_summary(*msg, a.flags.contains("json"));

    const std::string& vstr = a.opts.at("value");
    std::uint32_t value = 0;
    const auto* const vend = std::to_address(vstr.end());
    if (auto [ptr, ec] = std::from_chars(vstr.data(), vend, value);
        ec != std::errc{} || ptr != vend) {
        return die("invalid --value: " + vstr);
    }
    return mux_selector(*msg, a.opts.at("mux"), value, a.flags.contains("json"));
}

constexpr std::string_view k_usage =
    "aletheia — formally verified CAN signal analysis (C++ CLI)\n\n"
    "Usage: aletheia-cli <command> [flags] [args]\n\n"
    "Commands:\n"
    "  validate    validate a DBC definition for structural issues\n"
    "  extract     decode signals from a single CAN frame\n"
    "  signals     list signals defined in a DBC file\n"
    "  format-dbc  re-export a DBC as canonical JSON via the Agda core\n"
    "  mux-query   inspect multiplexor structure of a DBC message\n\n"
    "DBC source: --dbc <file>.dbc (verified text parser).\n"
    "Library path: $ALETHEIA_LIB or a build/install default.";

// Dispatch the parsed command; separated from main() so main() stays
// exception-free (bugprone-exception-escape) via a single try/catch.
static auto dispatch(const std::string& cmd, std::span<const std::string> rest) -> int {
    const std::set<std::string> bool_flags{"json", "extended"};
    if (cmd == "validate" || cmd == "signals" || cmd == "format-dbc") {
        auto parsed = parse_args(rest, {"dbc"}, bool_flags);
        if (!parsed)
            return die(parsed.error());
        if (cmd == "validate")
            return cmd_validate(*parsed);
        if (cmd == "signals")
            return cmd_signals(*parsed);
        return cmd_format_dbc(*parsed);
    }
    if (cmd == "extract") {
        auto parsed = parse_args(rest, {"dbc"}, bool_flags);
        if (!parsed)
            return die(parsed.error());
        return cmd_extract(*parsed);
    }
    if (cmd == "mux-query") {
        auto parsed = parse_args(rest, {"dbc", "mux", "value"}, bool_flags);
        if (!parsed)
            return die(parsed.error());
        return cmd_mux_query(*parsed);
    }
    if (cmd == "check") {
        std::cerr << "Error: 'check' is not available in the C++ CLI yet — it needs a verified "
                     "CAN-log reader (Phase 6: python-can replacement). Use the Python CLI for "
                     "log-file checking.\n";
        return k_exit_error;
    }
    if (cmd == "-h" || cmd == "--help" || cmd == "help") {
        std::cout << k_usage << '\n';
        return k_exit_ok;
    }
    std::cerr << "Error: unknown command '" << cmd << "'\n\n" << k_usage << '\n';
    return k_exit_error;
}

namespace aletheia {

auto run_cli(std::span<const std::string> args) noexcept -> int {
    try {
        if (args.empty()) {
            std::cerr << k_usage << '\n';
            return k_exit_error;
        }
        return dispatch(args.front(), args.subspan(1));
    } catch (const std::exception& e) {
        return die(std::string{"unexpected error: "} + e.what());
    }
}

} // namespace aletheia
