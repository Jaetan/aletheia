// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// Excel check and DBC loader implementation.
//
#include <aletheia/excel.hpp>

#include "detail/loader_utils.hpp"

#include <OpenXLSX.hpp>

#include <algorithm>
#include <cctype>
#include <charconv>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <exception>
#include <expected>
#include <filesystem>
#include <format>
#include <iterator>
#include <limits>
#include <map>
#include <memory>
#include <sstream>
#include <stdexcept>
#include <string>
#include <string_view>
#include <system_error>
#include <tuple>
#include <utility>
#include <vector>

namespace aletheia {

// std::from_chars takes a raw pointer pair [first, last). The canonical idiom
// `sv.data() + sv.size()` trips cppcoreguidelines-pro-bounds-pointer-arithmetic;
// `std::to_address(sv.end())` is arithmetic-free and equivalent since C++20
// string_view::iterator is a contiguous iterator.
static auto sv_end_ptr(std::string_view sv) -> const char* {
    return std::to_address(sv.end());
}

// ---------------------------------------------------------------------------
// Sheet headers
// ---------------------------------------------------------------------------

// Construct-on-first-use: function-local statics make any (vector-allocation)
// throw happen lazily on first call — catchable — rather than during static
// initialization before main() (bugprone-throwing-static-initialization).
static auto dbc_headers() -> const std::vector<std::string>& {
    static const std::vector<std::string> h = {
        "Message ID",  "Message Name",    "Extended", "DLC",    "Signal", "Start Bit", "Length",
        "Byte Order",  "Signed",          "Factor",   "Offset", "Min",    "Max",       "Unit",
        "Multiplexor", "Multiplex Value",
    };
    return h;
}

static auto checks_headers() -> const std::vector<std::string>& {
    static const std::vector<std::string> h = {
        "Check Name", "Signal", "Condition", "Value", "Min", "Max", "Time (ms)", "Severity",
    };
    return h;
}

static auto when_then_headers() -> const std::vector<std::string>& {
    static const std::vector<std::string> h = {
        "Check Name",  "When Signal",    "When Condition", "When Value",
        "Then Signal", "Then Condition", "Then Value",     "Then Min",
        "Then Max",    "Within (ms)",    "Severity",
    };
    return h;
}

// ---------------------------------------------------------------------------
// Cell value conversion helper
// ---------------------------------------------------------------------------

static auto row_ctx(int row_num) -> std::string {
    return "Row " + std::to_string(row_num);
}

/// Extract the literal text of a cell's <v> element from the cell's own XML
/// (XLCell::print). OpenXLSX's public API exposes only the PARSED value, and
/// for an Integer-classified cell that parse is a prefix-read — it silently
/// turns dot-free scientific notation ("1e16") into 1 and an empty <v/> into
/// 0 — so the raw stored text must come from the XML itself. XML entities are
/// left encoded (they cannot form a digit run, so the strictness check treats
/// them as the garbage they are). Returns "" for a missing or empty <v>: the
/// element carries no attributes, so its opening tag is the three bytes
/// searched for, and a self-closing <v/> is not found, which reads as empty.
static auto raw_stored_v_text(const OpenXLSX::XLCell& cell) -> std::string {
    std::ostringstream os;
    cell.print(os);
    const std::string xml = os.str();
    constexpr std::string_view open_tag = "<v>";
    const std::size_t open = xml.find(open_tag);
    if (open == std::string::npos)
        return "";
    const std::size_t text = open + open_tag.size();
    const std::size_t close = xml.find("</v>", text);
    if (close == std::string::npos)
        return "";
    return xml.substr(text, close - text);
}

/// True when s is a non-empty ASCII digit run with an optional leading minus,
/// which is every shape a stored integer takes and the only one whose Integer
/// parse is exact rather than a prefix-read.
static auto is_signed_digit_run(std::string_view s) -> bool {
    if (s.starts_with('-'))
        s.remove_prefix(1);
    if (s.empty())
        return false;
    return std::ranges::all_of(s, [](char ch) { return ch >= '0' && ch <= '9'; });
}

/// Convert a cell to its loader-string form, returning empty for empty cells.
/// The Integer branch trusts the parsed value only after verifying the raw
/// stored <v> text is a digit run with an optional minus (see raw_stored_v_text);
/// anything else — dot-free scientific notation, an empty <v/> — is refused
/// truthfully, naming the stored text. Float values render shortest
/// round-trip: they are only ever echoed in rejection messages, and a
/// fixed-precision rendering would misstate the stored value.
static auto cell_to_string(const OpenXLSX::XLCell& cell, const std::string& header, int row_num)
    -> std::string {
    const OpenXLSX::XLCellValue val = cell.value();
    switch (val.type()) {
    case OpenXLSX::XLValueType::String:
        return val.get<std::string>();
    case OpenXLSX::XLValueType::Integer: {
        const std::string raw = raw_stored_v_text(cell);
        if (!is_signed_digit_run(raw))
            throw std::runtime_error(row_ctx(row_num) + ": '" + header + "' number cell stores \"" +
                                     raw +
                                     "\", which is not a plain integer (store the digits "
                                     "verbatim, or format the cell as text)");
        return std::to_string(val.get<std::int64_t>());
    }
    case OpenXLSX::XLValueType::Float:
        return std::format("{}", val.get<double>());
    case OpenXLSX::XLValueType::Boolean:
        return val.get<bool>() ? "TRUE" : "FALSE";
    default:
        return "";
    }
}

// ---------------------------------------------------------------------------
// Cell map type and builder
// ---------------------------------------------------------------------------

/// A cell's stringified value plus whether it is stored as text (an XLValueType
/// of String). Strict coercion needs that distinction: a number stored as text
/// is rejected for a numeric field, matching the Python reference.
namespace {
struct CellVal {
    std::string value;
    bool is_text = false;
};
} // namespace

using CellMap = std::map<std::string, CellVal>;

/// One data row of a sheet: its 1-based row number (for error messages) and
/// its header-keyed cells.
namespace {
struct DataRow {
    int number;
    CellMap cells;
};
} // namespace

/// Build a header->cell map from a worksheet row, keeping only present
/// (non-empty) cells; a column with no header name is keyed by that empty
/// name, which no field reads.
static auto row_to_map(OpenXLSX::XLWorksheet const& ws, int row,
                       const std::vector<std::string>& headers) -> CellMap {
    CellMap result;
    for (std::size_t i = 0; i < headers.size(); ++i) {
        auto const cell = ws.cell(row, static_cast<std::uint16_t>(i + 1));
        auto const str_val = cell_to_string(cell, headers[i], row);
        if (str_val.empty())
            continue;
        result[headers[i]] = CellVal{
            .value = str_val, .is_text = cell.value().type() == OpenXLSX::XLValueType::String};
    }
    return result;
}

// ---------------------------------------------------------------------------
// Typed field extractors with error context
// ---------------------------------------------------------------------------

// get_str requires a text cell — strict, matching the Python reference: a
// number or boolean cell is rejected rather than silently stringified.
static auto get_str(const CellMap& cells, const std::string& key, const std::string& ctx_str)
    -> std::string {
    auto const it = cells.find(key);
    if (it == cells.end())
        throw std::runtime_error(ctx_str + ": missing or invalid '" + key + "' (expected string)");
    if (!it->second.is_text)
        throw std::runtime_error(ctx_str + ": '" + key + "' must be text, got a non-text value " +
                                 it->second.value);
    return it->second.value;
}

// get_any returns a present cell's value regardless of type — used only for
// Message ID, which legitimately accepts a hex string or a native number.
static auto get_any(const CellMap& cells, const std::string& key, const std::string& ctx_str)
    -> std::string {
    auto const it = cells.find(key);
    if (it == cells.end())
        throw std::runtime_error(ctx_str + ": missing or invalid '" + key + "'");
    return it->second.value;
}

// get_decimal requires a TEXT cell holding a decimal literal.  The float
// principle refuses a number-typed cell: a float64 has already lost the
// authored precision, so numeric fields are authored as text-formatted cells
// and parsed exactly by the kernel decimal SSOT (Rational::from_decimal).
// RTS-gated: an FfiBackend must be live first.  A kernel decimal refusal is
// re-thrown with the row and field prefixed, because the kernel knows the
// literal and not the workbook position, and the loader answers Validation;
// any other kernel throw passes through unchanged and the loader answers with
// its own kind.
static auto get_decimal(const CellMap& cells, const std::string& key, const std::string& ctx_str)
    -> Rational {
    auto const it = cells.find(key);
    if (it == cells.end())
        throw std::runtime_error(ctx_str + ": missing or invalid '" + key + "' (expected number)");
    if (!it->second.is_text)
        throw std::runtime_error(ctx_str + ": '" + key + "' is a number cell (got " +
                                 it->second.value +
                                 "); format it as TEXT so the exact value is preserved "
                                 "(a number cell stores a lossy float)");
    try {
        return Rational::from_decimal(it->second.value);
    } catch (const AletheiaException& ex) {
        if (ex.kind() != ErrorKind::Validation)
            throw; // runtime-down / ABI faults are not properties of the cell
        throw std::runtime_error(ctx_str + ": invalid '" + key + "': " + ex.what());
    }
}

// get_int is get_decimal plus a whole-number requirement (DLC / Start Bit /
// Length / Multiplex Value / Time), so it inherits the text-cell contract and
// the kernel refusal handling.
static auto get_int(const CellMap& cells, const std::string& key, const std::string& ctx_str)
    -> std::int64_t {
    auto const value = get_decimal(cells, key, ctx_str);
    if (value.denominator() != 1)
        throw std::runtime_error(ctx_str + ": '" + key + "' value " +
                                 cells.find(key)->second.value + " is not a whole number");
    return value.numerator();
}

// Refuse a whole-number cell that does not fit the field's type, naming the
// field and the bound it crossed.
template<typename T>
static auto checked_cast(std::int64_t value, std::string_view field, const std::string& ctx_str)
    -> T {
    if (value < 0 || std::cmp_greater(value, std::numeric_limits<T>::max()))
        throw std::runtime_error(std::format("{}: '{}' out of range [0, {}]: {}", ctx_str, field,
                                             std::numeric_limits<T>::max(), value));
    return static_cast<T>(value);
}

// get_bool accepts the multi-form boolean the peer bindings accept: a native
// boolean, an integral 1/0, or TRUE/FALSE/1/0 text (case-insensitive). Booleans
// are exempt from the all-text contract (which governs only numeric cells).
static auto get_bool(const CellMap& cells, const std::string& key, const std::string& ctx_str)
    -> bool {
    auto const it = cells.find(key);
    if (it == cells.end())
        throw std::runtime_error(ctx_str + ": missing or invalid '" + key +
                                 "' (expected TRUE/FALSE)");
    auto upper = it->second.value;
    std::ranges::transform(upper, upper.begin(), [](unsigned char ch) -> char {
        return static_cast<char>(std::toupper(ch));
    });
    if (upper == "TRUE" || upper == "1")
        return true;
    if (upper == "FALSE" || upper == "0")
        return false;
    throw std::runtime_error(ctx_str + ": missing or invalid '" + key + "' (expected TRUE/FALSE)");
}

static auto has_key(const CellMap& cells, const std::string& key) -> bool {
    return cells.contains(key);
}

// ---------------------------------------------------------------------------
// Header extraction from first row
// ---------------------------------------------------------------------------

static auto headers_from_row(OpenXLSX::XLWorksheet const& ws, std::uint16_t count)
    -> std::vector<std::string> {
    std::vector<std::string> result;
    result.reserve(count);
    // The counter is wider than the bound it is compared against: at a count of
    // the bound type's maximum, a counter of that same type wraps on the
    // increment that should end the loop and the loop never ends.  The library
    // clamps a column reference to its own maximum today, so nothing reaches
    // that count, but the termination of this loop is not that library's to
    // decide.
    for (std::uint32_t col = 1; col <= count; ++col) {
        // Lossless: the counter never exceeds the bound, which is of the
        // narrower type the cell accessor takes.
        const OpenXLSX::XLCellValue val = ws.cell(1, static_cast<std::uint16_t>(col)).value();
        if (val.type() == OpenXLSX::XLValueType::String)
            result.push_back(val.get<std::string>());
        else
            result.emplace_back();
    }
    return result;
}

// ---------------------------------------------------------------------------
// Message ID parsing
// ---------------------------------------------------------------------------

static auto parse_message_id(const std::string& val, const std::string& ctx_str) -> std::uint32_t {
    // std::from_chars is locale-independent (unlike std::stoul).
    auto lower = val;
    std::ranges::transform(lower, lower.begin(), [](unsigned char ch) -> char {
        return static_cast<char>(std::tolower(ch));
    });
    const bool is_hex = lower.starts_with("0x");
    const std::string digits = is_hex ? val.substr(2) : val;
    std::uint32_t result = 0;
    auto const* const end = sv_end_ptr(digits);
    auto [ptr, ec] = std::from_chars(digits.data(), end, result, is_hex ? 16 : 10);
    if (ec != std::errc{} || ptr != end)
        throw std::runtime_error(
            ctx_str +
            ": invalid 'Message ID' \xe2\x80\x94 expected integer or hex string (e.g. 0x100)");
    return result;
}

// ---------------------------------------------------------------------------
// Checks sheet parser
// ---------------------------------------------------------------------------

// The optional Check Name / Severity columns, applied to a built check.
static void apply_row_metadata(CheckResult& result, const CellMap& cells,
                               const std::string& ctx_str) {
    if (has_key(cells, "Check Name"))
        result.named(get_str(cells, "Check Name", ctx_str));
    if (has_key(cells, "Severity"))
        result.severity(get_str(cells, "Severity", ctx_str));
}

static auto parse_simple_row(const CellMap& cells, int row_num) -> CheckResult {
    auto const ctx_str = row_ctx(row_num);
    auto signal = get_str(cells, "Signal", ctx_str);
    auto condition = get_str(cells, "Condition", ctx_str);

    if (!detail::is_simple_condition(condition))
        throw std::runtime_error(ctx_str + ": unknown condition '" + condition + "'");

    CheckResult result = [&] -> CheckResult {
        if (detail::is_simple_value_condition(condition)) {
            auto const value = PhysicalValue{get_decimal(cells, "Value", ctx_str)};
            return detail::dispatch_simple(signal, condition, value);
        }
        if (detail::is_simple_range_condition(condition)) {
            if (!has_key(cells, "Min") || !has_key(cells, "Max"))
                throw std::runtime_error(ctx_str + ": condition '" + condition +
                                         "' requires 'Min' and 'Max'");
            auto const lo = PhysicalValue{get_decimal(cells, "Min", ctx_str)};
            auto const hi = PhysicalValue{get_decimal(cells, "Max", ctx_str)};
            return check::signal(signal).stays_between(lo, hi);
        }
        if (detail::is_simple_settles_condition(condition)) {
            if (!has_key(cells, "Min") || !has_key(cells, "Max"))
                throw std::runtime_error(ctx_str +
                                         ": condition 'settles_between' requires 'Min' and 'Max'");
            if (!has_key(cells, "Time (ms)"))
                throw std::runtime_error(ctx_str +
                                         ": condition 'settles_between' requires 'Time (ms)'");
            auto const lo = PhysicalValue{get_decimal(cells, "Min", ctx_str)};
            auto const hi = PhysicalValue{get_decimal(cells, "Max", ctx_str)};
            auto const ms = std::chrono::milliseconds{get_int(cells, "Time (ms)", ctx_str)};
            return check::signal(signal).settles_between(lo, hi).within(ms);
        }
        auto const value = PhysicalValue{get_decimal(cells, "Value", ctx_str)};
        return check::signal(signal).equals(value).always();
    }();

    apply_row_metadata(result, cells, ctx_str);
    return result;
}

// ---------------------------------------------------------------------------
// When-Then sheet parser
// ---------------------------------------------------------------------------

static auto parse_when_then_row(const CellMap& cells, int row_num) -> CheckResult {
    auto const ctx_str = row_ctx(row_num);
    auto const when_signal = get_str(cells, "When Signal", ctx_str);
    auto const when_cond = get_str(cells, "When Condition", ctx_str);
    auto const when_value = PhysicalValue{get_decimal(cells, "When Value", ctx_str)};

    if (!detail::is_when_condition(when_cond))
        throw std::runtime_error(ctx_str + ": unknown when condition '" + when_cond + "'");

    auto const when_builder = check::when(when_signal);
    auto const when_result = detail::dispatch_when(when_builder, when_cond, when_value);

    auto const then_signal = get_str(cells, "Then Signal", ctx_str);
    auto then_cond = get_str(cells, "Then Condition", ctx_str);

    // The word is held to the vocabulary by taking its slots: one lookup
    // answers both whether the obligation is known and what it reads.
    auto const slots = detail::then_slots(then_cond);
    if (!slots)
        throw std::runtime_error(ctx_str + ": unknown then condition '" + then_cond + "'");

    auto then_builder = when_result.then(then_signal);
    auto within_ms = std::chrono::milliseconds{get_int(cells, "Within (ms)", ctx_str)};

    // Which columns the obligation reads is the vocabulary's business, not
    // this loader's; which columns they are, and what to say when one is
    // missing, is this loader's. Only the slots the obligation reads are
    // handed over.
    CheckResult result = [&] -> CheckResult {
        detail::ThenSlotValues read;
        switch (*slots) {
        case detail::ThenSlots::Value:
            read.emplace("value", PhysicalValue{get_decimal(cells, "Then Value", ctx_str)});
            break;
        case detail::ThenSlots::Range:
            if (!has_key(cells, "Then Min") || !has_key(cells, "Then Max"))
                throw std::runtime_error(ctx_str + ": then condition '" + then_cond +
                                         "' requires 'Then Min' and 'Then Max'");
            read.emplace("lo", PhysicalValue{get_decimal(cells, "Then Min", ctx_str)});
            read.emplace("hi", PhysicalValue{get_decimal(cells, "Then Max", ctx_str)});
            break;
        }
        return detail::dispatch_then(then_builder, then_cond, read, within_ms);
    }();

    apply_row_metadata(result, cells, ctx_str);
    return result;
}

// ---------------------------------------------------------------------------
// DBC signal parser
// ---------------------------------------------------------------------------

static auto parse_dbc_signal(const CellMap& cells, int row_num) -> DbcSignal {
    auto const ctx_str = row_ctx(row_num);

    auto const byte_order_str = get_str(cells, "Byte Order", ctx_str);
    ByteOrder byte_order{};
    if (byte_order_str == "little_endian")
        byte_order = ByteOrder::LittleEndian;
    else if (byte_order_str == "big_endian")
        byte_order = ByteOrder::BigEndian;
    else
        throw std::runtime_error(ctx_str +
                                 ": 'Byte Order' must be 'little_endian' or 'big_endian'");

    // Unit is optional text; a non-text cell defaults to empty (matching the
    // Python reference's is_str check) rather than erroring.
    std::string unit_str;
    if (auto const it = cells.find("Unit"); it != cells.end() && it->second.is_text)
        unit_str = it->second.value;

    // Multiplexing
    const bool has_muxor = has_key(cells, "Multiplexor");
    const bool has_mux_val = has_key(cells, "Multiplex Value");

    if (has_muxor != has_mux_val)
        throw std::runtime_error(ctx_str + ": 'Multiplexor' and 'Multiplex Value' "
                                           "must both be provided or both be empty");

    SignalPresence presence;
    if (has_muxor) {
        auto const mux_val = checked_cast<std::uint32_t>(get_int(cells, "Multiplex Value", ctx_str),
                                                         "Multiplex Value", ctx_str);
        presence = Multiplexed{.multiplexor = SignalName{get_str(cells, "Multiplexor", ctx_str)},
                               .multiplex_values = {MultiplexValue{mux_val}}};
    } else {
        presence = AlwaysPresent{};
    }

    auto const start_bit_val =
        checked_cast<std::uint16_t>(get_int(cells, "Start Bit", ctx_str), "Start Bit", ctx_str);
    auto const bit_length_val =
        checked_cast<std::uint16_t>(get_int(cells, "Length", ctx_str), "Length", ctx_str);

    return DbcSignal{
        .name = SignalName{get_str(cells, "Signal", ctx_str)},
        .start_bit = BitPosition{start_bit_val},
        .bit_length = BitLength{bit_length_val},
        .byte_order = byte_order,
        .is_signed = get_bool(cells, "Signed", ctx_str),
        .factor = RationalFactor{get_decimal(cells, "Factor", ctx_str)},
        .offset = RationalOffset{get_decimal(cells, "Offset", ctx_str)},
        .minimum = RationalBound{get_decimal(cells, "Min", ctx_str)},
        .maximum = RationalBound{get_decimal(cells, "Max", ctx_str)},
        .unit = Unit{unit_str},
        .presence = presence,
    };
}

// ---------------------------------------------------------------------------
// Sheet existence check
// ---------------------------------------------------------------------------

static auto worksheet_exists(OpenXLSX::XLDocument const& doc, std::string_view name) -> bool {
    return std::ranges::contains(doc.workbook().worksheetNames(), std::string(name));
}

// A sheet's data rows: every non-empty row below the header, each paired with
// its 1-based sheet row number for error messages.
static auto collect_data_rows(OpenXLSX::XLWorksheet const& ws) -> std::vector<DataRow> {
    auto const headers = headers_from_row(ws, ws.columnCount());
    std::vector<DataRow> rows;
    auto const total_rows = ws.rowCount();
    for (std::uint32_t r = 2; r <= total_rows; ++r) {
        auto cells = row_to_map(ws, static_cast<int>(r), headers);
        if (!cells.empty())
            rows.push_back(DataRow{.number = static_cast<int>(r), .cells = std::move(cells)});
    }
    return rows;
}

// The entry guards every Excel reader runs before handing the path to
// OpenXLSX: no symlink, raw size, uncompressed size (see loader_utils.hpp).
static auto harden_excel_path(const std::filesystem::path& path) -> Result<void> {
    if (auto v = detail::validate_loader_path(path, "Excel"); !v)
        return std::unexpected(v.error());
    if (auto v = detail::check_file_size_bound(path); !v)
        return std::unexpected(v.error());
    return detail::check_xlsx_uncompressed_bound(path);
}

// ---------------------------------------------------------------------------
// Write header row helper
// ---------------------------------------------------------------------------

static void write_header_row(OpenXLSX::XLWorksheet const& ws,
                             const std::vector<std::string>& headers,
                             OpenXLSX::XLStyleIndex header_fmt) {
    for (std::size_t i = 0; i < headers.size(); ++i) {
        auto cell = ws.cell(1, static_cast<std::uint16_t>(i + 1));
        cell.value() = headers[i];
        cell.setCellFormat(header_fmt);
    }
}

// ===========================================================================
// Public API: Checks from Excel
// ===========================================================================

auto load_checks_from_excel(const std::filesystem::path& path, std::string_view checks_sheet,
                            std::string_view when_then_sheet) -> Result<std::vector<CheckResult>> {
    if (auto v = harden_excel_path(path); !v)
        return std::unexpected(v.error());

    try {
        OpenXLSX::XLDocument doc;
        doc.open(path.string());

        const bool has_checks = worksheet_exists(doc, checks_sheet);
        const bool has_when_then = worksheet_exists(doc, when_then_sheet);

        if (!has_checks && !has_when_then)
            return std::unexpected(AletheiaError{
                ErrorKind::Validation, "Workbook has no '" + std::string(checks_sheet) + "' or '" +
                                           std::string(when_then_sheet) + "' sheet"});

        std::vector<CheckResult> results;

        if (has_checks) {
            auto const ws = doc.workbook().worksheet(std::string(checks_sheet));
            for (auto const& row : collect_data_rows(ws))
                results.push_back(parse_simple_row(row.cells, row.number));
        }

        if (has_when_then) {
            auto const ws = doc.workbook().worksheet(std::string(when_then_sheet));
            for (auto const& row : collect_data_rows(ws))
                results.push_back(parse_when_then_row(row.cells, row.number));
        }

        return results;

    } catch (const AletheiaException& ex) {
        // A kernel or runtime failure keeps its kind; only a cell's own defect
        // is a Validation error.
        return std::unexpected(ex.error());
    } catch (const std::exception& ex) {
        return std::unexpected(AletheiaError{ErrorKind::Validation, ex.what()});
    }
}

// ===========================================================================
// Public API: DBC from Excel
// ===========================================================================

// (msg_id, msg_name, dlc, is_extended) — the row-level identity of a message.
using MessageKeyExt = std::tuple<std::uint32_t, std::string, std::int64_t, bool>;

// Group data rows by message key, in first-seen order. Each row becomes one
// signal in its parent message. The transient position map exists only so
// grouping stays a single pass; the returned vector needs no key re-lookup.
static auto group_rows_by_message(const std::vector<DataRow>& data_rows)
    -> std::vector<std::pair<MessageKeyExt, std::vector<std::size_t>>> {
    std::vector<std::pair<MessageKeyExt, std::vector<std::size_t>>> groups;
    std::map<MessageKeyExt, std::size_t> positions;
    for (std::size_t i = 0; i < data_rows.size(); ++i) {
        auto const& cells = data_rows[i].cells;
        auto const ctx_str = row_ctx(data_rows[i].number);
        auto msg_id = parse_message_id(get_any(cells, "Message ID", ctx_str), ctx_str);
        auto const msg_name = get_str(cells, "Message Name", ctx_str);
        auto dlc = get_int(cells, "DLC", ctx_str);
        const bool extended = has_key(cells, "Extended") && get_bool(cells, "Extended", ctx_str);
        MessageKeyExt key{msg_id, msg_name, dlc, extended};
        auto [it, inserted] = positions.try_emplace(key, groups.size());
        if (inserted)
            groups.emplace_back(std::move(key), std::vector<std::size_t>{});
        groups[it->second].second.push_back(i);
    }
    return groups;
}

// Build one DbcMessage from its group of rows; surfaces validation errors as
// an unexpected Result so the top-level loop stays linear.
static auto build_message_from_group(const MessageKeyExt& key,
                                     const std::vector<std::size_t>& indices,
                                     const std::vector<DataRow>& data_rows) -> Result<DbcMessage> {
    std::vector<DbcSignal> signals;
    std::ranges::transform(indices, std::back_inserter(signals), [&](std::size_t idx) {
        return parse_dbc_signal(data_rows[idx].cells, data_rows[idx].number);
    });
    auto [msg_id, msg_name, dlc, extended] = key;
    auto can_id_result =
        extended
            ? ExtendedId::create(msg_id).transform([](auto eid) -> CanId { return CanId{eid}; })
            : StandardId::create(static_cast<std::uint16_t>(msg_id))
                  .transform([](auto sid) -> CanId { return CanId{sid}; });
    if (!can_id_result.has_value())
        return std::unexpected(
            AletheiaError{ErrorKind::Validation, "Invalid CAN ID: " + std::to_string(msg_id)});
    if (dlc < 0 || dlc > 15)
        return std::unexpected(AletheiaError{
            ErrorKind::Validation, row_ctx(data_rows[indices[0]].number) +
                                       ": DLC out of range [0, 15]: " + std::to_string(dlc)});
    auto dlc_result = Dlc::create(static_cast<std::uint8_t>(dlc));
    if (!dlc_result.has_value())
        return std::unexpected(
            AletheiaError{ErrorKind::Validation, "Invalid DLC: " + std::to_string(dlc)});
    return DbcMessage{
        .id = can_id_result.value(),
        .name = MessageName{msg_name},
        .dlc = dlc_result.value(),
        .sender = NodeName{""},
        .signals = std::move(signals),
    };
}

auto load_dbc_from_excel(const std::filesystem::path& path, std::string_view sheet)
    -> Result<DbcDefinition> {
    if (auto v = harden_excel_path(path); !v)
        return std::unexpected(v.error());

    try {
        OpenXLSX::XLDocument doc;
        doc.open(path.string());

        if (!worksheet_exists(doc, sheet))
            return std::unexpected(AletheiaError{
                ErrorKind::Validation, "Workbook has no '" + std::string(sheet) + "' sheet"});

        auto const ws = doc.workbook().worksheet(std::string(sheet));
        auto const data_rows = collect_data_rows(ws);
        if (data_rows.empty())
            return std::unexpected(
                AletheiaError{ErrorKind::Validation, "DBC sheet has no data rows"});

        std::vector<DbcMessage> messages;
        for (auto const& [key, rows] : group_rows_by_message(data_rows)) {
            auto msg = build_message_from_group(key, rows, data_rows);
            if (!msg.has_value())
                return std::unexpected(msg.error());
            messages.push_back(std::move(msg.value()));
        }

        return DbcDefinition{.version = "", .messages = std::move(messages)};

    } catch (const AletheiaException& ex) {
        return std::unexpected(ex.error());
    } catch (const std::exception& ex) {
        return std::unexpected(AletheiaError{ErrorKind::Validation, ex.what()});
    }
}

// ===========================================================================
// Public API: Template creation
// ===========================================================================

auto create_excel_template(const std::filesystem::path& path) -> Result<void> {
    // Validate the destination's parent dir
    // before letting OpenXLSX raise an opaque exception inside `doc.create`.
    if (auto v = detail::validate_output_parent_dir(path); !v)
        return std::unexpected(v.error());
    if (std::filesystem::exists(path))
        return std::unexpected(
            AletheiaError{ErrorKind::Validation, "File already exists: " + path.string()});

    try {
        OpenXLSX::XLDocument doc;
        doc.create(path.string(), OpenXLSX::XLForceOverwrite);

        // Bold cell format for the header rows, created once and applied to every
        // header cell.  Python (openpyxl Font(bold=True)) and Go (excelize
        // Font{Bold: true}) bold their template headers; match them.
        auto const& styles = doc.styles();
        auto const bold_font = styles.fonts().create();
        styles.fonts()[bold_font].setBold(true);
        auto const header_fmt = styles.cellFormats().create();
        styles.cellFormats()[header_fmt].setFontIndex(bold_font);

        // The workbook starts with one default sheet; it becomes the DBC sheet.
        doc.workbook().worksheet("Sheet1").setName("DBC");
        auto const ws_dbc = doc.workbook().worksheet("DBC");
        write_header_row(ws_dbc, dbc_headers(), header_fmt);

        // Checks sheet
        doc.workbook().addWorksheet("Checks");
        auto const ws_checks = doc.workbook().worksheet("Checks");
        write_header_row(ws_checks, checks_headers(), header_fmt);

        // When-Then sheet
        doc.workbook().addWorksheet("When-Then");
        auto const ws_wt = doc.workbook().worksheet("When-Then");
        write_header_row(ws_wt, when_then_headers(), header_fmt);

        doc.save();
        return {};

    } catch (const std::exception& ex) {
        return std::unexpected(AletheiaError{ErrorKind::Validation, ex.what()});
    }
}

} // namespace aletheia
