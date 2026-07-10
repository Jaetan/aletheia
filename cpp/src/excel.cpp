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
#include <limits>
#include <map>
#include <memory>
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

/// Convert an XLCellValue to a string, returning empty for empty cells.
static auto cell_to_string(const OpenXLSX::XLCellValue& val) -> std::string {
    switch (val.type()) {
    case OpenXLSX::XLValueType::String:
        return val.get<std::string>();
    case OpenXLSX::XLValueType::Integer:
        return std::to_string(val.get<std::int64_t>());
    case OpenXLSX::XLValueType::Float:
        return std::to_string(val.get<double>());
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

/// Build a header->cell map from a worksheet row, keeping only present
/// (non-empty) cells and dropping any column with an empty header name.
static auto row_to_map(OpenXLSX::XLWorksheet& ws, int row, const std::vector<std::string>& headers)
    -> CellMap {
    CellMap result;
    for (std::size_t i = 0; i < headers.size(); ++i) {
        if (headers[i].empty())
            continue; // a column with no header name is ignored
        const OpenXLSX::XLCellValue val = ws.cell(row, static_cast<std::uint16_t>(i + 1)).value();
        auto str_val = cell_to_string(val);
        if (str_val.empty())
            continue;
        result[headers[i]] =
            CellVal{.value = str_val, .is_text = val.type() == OpenXLSX::XLValueType::String};
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
    auto it = cells.find(key);
    if (it == cells.end() || it->second.value.empty())
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
    auto it = cells.find(key);
    if (it == cells.end() || it->second.value.empty())
        throw std::runtime_error(ctx_str + ": missing or invalid '" + key + "'");
    return it->second.value;
}

// get_decimal requires a TEXT cell holding a decimal literal.  The float
// principle INVERTS the old contract: a number-typed cell is rejected (a
// float64 has already lost the authored precision), so numeric fields must be
// authored as text-formatted cells and parsed exactly by the kernel decimal
// SSOT (Rational::from_decimal).  RTS-gated: an FfiBackend must be live first;
// the loader's outer `catch (const std::runtime_error&)` converts both the
// runtime-down and the malformed-literal throws into a Validation Result.
static auto get_decimal(const CellMap& cells, const std::string& key, const std::string& ctx_str)
    -> Rational {
    auto it = cells.find(key);
    if (it == cells.end() || it->second.value.empty())
        throw std::runtime_error(ctx_str + ": missing or invalid '" + key + "' (expected number)");
    if (!it->second.is_text)
        throw std::runtime_error(ctx_str + ": '" + key + "' is a number cell (got " +
                                 it->second.value +
                                 "); format it as TEXT so the exact value is preserved "
                                 "(a number cell stores a lossy float)");
    return Rational::from_decimal(it->second.value);
}

// get_int requires a TEXT cell holding a whole number (DLC / Start Bit / Length
// / Multiplex Value / Time).  Same inverted contract as get_decimal: a numeric
// cell is rejected; the text is parsed exactly via the kernel decimal SSOT and
// must reduce to denominator 1.
static auto get_int(const CellMap& cells, const std::string& key, const std::string& ctx_str)
    -> std::int64_t {
    auto it = cells.find(key);
    if (it == cells.end() || it->second.value.empty())
        throw std::runtime_error(ctx_str + ": missing or invalid '" + key + "' (expected integer)");
    if (!it->second.is_text)
        throw std::runtime_error(ctx_str + ": '" + key + "' is a number cell (got " +
                                 it->second.value +
                                 "); format it as TEXT so the exact value is preserved "
                                 "(a number cell stores a lossy float)");
    auto value = Rational::from_decimal(it->second.value);
    if (value.denominator() != 1)
        throw std::runtime_error(ctx_str + ": '" + key + "' value " + it->second.value +
                                 " is not a whole number");
    return value.numerator();
}

// get_bool accepts the multi-form boolean the peer bindings accept: a native
// boolean, an integral 1/0, or TRUE/FALSE/1/0 text (case-insensitive). Booleans
// are exempt from the all-text contract (which governs only numeric cells).
static auto get_bool(const CellMap& cells, const std::string& key, const std::string& ctx_str)
    -> bool {
    auto it = cells.find(key);
    if (it == cells.end() || it->second.value.empty())
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

static auto row_ctx(int row_num) -> std::string {
    return "Row " + std::to_string(row_num);
}

static auto has_key(const CellMap& cells, const std::string& key) -> bool {
    auto it = cells.find(key);
    return it != cells.end() && !it->second.value.empty();
}

// ---------------------------------------------------------------------------
// Header extraction from first row
// ---------------------------------------------------------------------------

static auto headers_from_row(OpenXLSX::XLWorksheet& ws, std::size_t count)
    -> std::vector<std::string> {
    std::vector<std::string> result;
    result.reserve(count);
    for (std::size_t i = 0; i < count; ++i) {
        const OpenXLSX::XLCellValue val = ws.cell(1, static_cast<std::uint16_t>(i + 1)).value();
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
    if (val.empty())
        throw std::runtime_error(
            ctx_str +
            ": invalid 'Message ID' \xe2\x80\x94 expected integer or hex string (e.g. 0x100)");
    // std::from_chars is locale-independent (unlike std::stoul).
    auto lower = val;
    std::ranges::transform(lower, lower.begin(), [](unsigned char ch) -> char {
        return static_cast<char>(std::tolower(ch));
    });
    const bool is_hex = lower.starts_with("0x");
    const std::string digits = is_hex ? val.substr(2) : val;
    std::uint32_t result = 0;
    const auto* const end = sv_end_ptr(digits);
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

static auto parse_simple_row(const CellMap& cells, int row_num) -> CheckResult {
    auto signal = get_str(cells, "Signal", row_ctx(row_num));
    auto condition = get_str(cells, "Condition", row_ctx(row_num));

    if (!detail::is_simple_condition(condition))
        throw std::runtime_error(row_ctx(row_num) + ": unknown condition '" + condition + "'");

    CheckResult result = [&]() -> CheckResult {
        if (detail::is_simple_value_condition(condition)) {
            auto value = PhysicalValue{get_decimal(cells, "Value", row_ctx(row_num))};
            return detail::dispatch_simple(signal, condition, value);
        }
        if (detail::is_simple_range_condition(condition)) {
            if (!has_key(cells, "Min") || !has_key(cells, "Max"))
                throw std::runtime_error(row_ctx(row_num) + ": condition '" + condition +
                                         "' requires 'Min' and 'Max'");
            auto lo = PhysicalValue{get_decimal(cells, "Min", row_ctx(row_num))};
            auto hi = PhysicalValue{get_decimal(cells, "Max", row_ctx(row_num))};
            return check::signal(signal).stays_between(lo, hi);
        }
        if (detail::is_simple_settles_condition(condition)) {
            if (!has_key(cells, "Min") || !has_key(cells, "Max"))
                throw std::runtime_error(row_ctx(row_num) +
                                         ": condition 'settles_between' requires 'Min' and 'Max'");
            if (!has_key(cells, "Time (ms)"))
                throw std::runtime_error(row_ctx(row_num) +
                                         ": condition 'settles_between' requires 'Time (ms)'");
            auto lo = PhysicalValue{get_decimal(cells, "Min", row_ctx(row_num))};
            auto hi = PhysicalValue{get_decimal(cells, "Max", row_ctx(row_num))};
            auto ms = std::chrono::milliseconds{get_int(cells, "Time (ms)", row_ctx(row_num))};
            return check::signal(signal).settles_between(lo, hi).within(ms);
        }
        // equals
        auto value = PhysicalValue{get_decimal(cells, "Value", row_ctx(row_num))};
        return check::signal(signal).equals(value).always();
    }();

    // Metadata
    if (has_key(cells, "Check Name"))
        result.named(get_str(cells, "Check Name", row_ctx(row_num)));
    if (has_key(cells, "Severity"))
        result.severity(get_str(cells, "Severity", row_ctx(row_num)));

    return result;
}

// ---------------------------------------------------------------------------
// When-Then sheet parser
// ---------------------------------------------------------------------------

static auto parse_when_then_row(const CellMap& cells, int row_num) -> CheckResult {
    auto when_signal = get_str(cells, "When Signal", row_ctx(row_num));
    auto when_cond = get_str(cells, "When Condition", row_ctx(row_num));
    auto when_value = PhysicalValue{get_decimal(cells, "When Value", row_ctx(row_num))};

    if (!detail::is_when_condition(when_cond))
        throw std::runtime_error(row_ctx(row_num) + ": unknown when condition '" + when_cond + "'");

    auto when_builder = check::when(when_signal);
    auto when_result = detail::dispatch_when(when_builder, when_cond, when_value);

    auto then_signal = get_str(cells, "Then Signal", row_ctx(row_num));
    auto then_cond = get_str(cells, "Then Condition", row_ctx(row_num));

    if (!detail::is_then_condition(then_cond))
        throw std::runtime_error(row_ctx(row_num) + ": unknown then condition '" + then_cond + "'");

    auto then_builder = when_result.then(then_signal);
    auto within_ms = std::chrono::milliseconds{get_int(cells, "Within (ms)", row_ctx(row_num))};

    CheckResult result = [&]() -> CheckResult {
        if (then_cond == "equals") {
            auto val = PhysicalValue{get_decimal(cells, "Then Value", row_ctx(row_num))};
            return then_builder.equals(val).within(within_ms);
        }
        if (then_cond == "exceeds") {
            auto val = PhysicalValue{get_decimal(cells, "Then Value", row_ctx(row_num))};
            return then_builder.exceeds(val).within(within_ms);
        }
        // stays_between
        if (!has_key(cells, "Then Min") || !has_key(cells, "Then Max"))
            throw std::runtime_error(
                row_ctx(row_num) +
                ": then condition 'stays_between' requires 'Then Min' and 'Then Max'");
        auto lo = PhysicalValue{get_decimal(cells, "Then Min", row_ctx(row_num))};
        auto hi = PhysicalValue{get_decimal(cells, "Then Max", row_ctx(row_num))};
        return then_builder.stays_between(lo, hi).within(within_ms);
    }();

    // Metadata
    if (has_key(cells, "Check Name"))
        result.named(get_str(cells, "Check Name", row_ctx(row_num)));
    if (has_key(cells, "Severity"))
        result.severity(get_str(cells, "Severity", row_ctx(row_num)));

    return result;
}

// ---------------------------------------------------------------------------
// DBC signal parser
// ---------------------------------------------------------------------------

static auto parse_dbc_signal(const CellMap& cells, int row_num) -> DbcSignal {
    auto ctx_str = row_ctx(row_num);

    auto byte_order_str = get_str(cells, "Byte Order", ctx_str);
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
    if (auto it = cells.find("Unit"); it != cells.end() && it->second.is_text)
        unit_str = it->second.value;

    // Multiplexing
    const bool has_muxor = has_key(cells, "Multiplexor");
    const bool has_mux_val = has_key(cells, "Multiplex Value");

    if (has_muxor != has_mux_val)
        throw std::runtime_error(ctx_str + ": 'Multiplexor' and 'Multiplex Value' "
                                           "must both be provided or both be empty");

    SignalPresence presence;
    if (has_muxor) {
        auto mux_val = get_int(cells, "Multiplex Value", ctx_str);
        if (mux_val < 0 || std::cmp_greater(mux_val, std::numeric_limits<std::uint32_t>::max()))
            throw std::runtime_error(ctx_str + ": 'Multiplex Value' out of range [0, " +
                                     std::to_string(std::numeric_limits<std::uint32_t>::max()) +
                                     "]: " + std::to_string(mux_val));
        presence =
            Multiplexed{.multiplexor = SignalName{get_str(cells, "Multiplexor", ctx_str)},
                        .multiplex_values = {MultiplexValue{static_cast<std::uint32_t>(mux_val)}}};
    } else {
        presence = AlwaysPresent{};
    }

    auto start_bit_val = get_int(cells, "Start Bit", ctx_str);
    if (start_bit_val < 0 ||
        std::cmp_greater(start_bit_val, std::numeric_limits<std::uint16_t>::max()))
        throw std::runtime_error(ctx_str + ": 'Start Bit' out of range [0, " +
                                 std::to_string(std::numeric_limits<std::uint16_t>::max()) +
                                 "]: " + std::to_string(start_bit_val));
    auto bit_length_val = get_int(cells, "Length", ctx_str);
    if (bit_length_val < 0 ||
        std::cmp_greater(bit_length_val, std::numeric_limits<std::uint8_t>::max()))
        throw std::runtime_error(ctx_str + ": 'Length' out of range [0, " +
                                 std::to_string(std::numeric_limits<std::uint8_t>::max()) +
                                 "]: " + std::to_string(bit_length_val));

    return DbcSignal{
        .name = SignalName{get_str(cells, "Signal", ctx_str)},
        .start_bit = BitPosition{static_cast<std::uint16_t>(start_bit_val)},
        .bit_length = BitLength{static_cast<std::uint8_t>(bit_length_val)},
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

static auto worksheet_exists(OpenXLSX::XLDocument& doc, std::string_view name) -> bool {
    auto names = doc.workbook().worksheetNames();
    return std::ranges::find(names, std::string(name)) != names.end();
}

// ---------------------------------------------------------------------------
// Write header row helper
// ---------------------------------------------------------------------------

static void write_header_row(OpenXLSX::XLWorksheet& ws, const std::vector<std::string>& headers,
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
    // Reject symlinks, raw-size cap,
    // ZIP-uncompressed cap before handing the path to OpenXLSX.  See
    // `cpp/src/detail/loader_utils.hpp` for rationale + TOCTOU note.
    if (auto v = detail::validate_loader_path(path, "Excel"); !v)
        return std::unexpected(v.error());
    if (auto v = detail::check_file_size_bound(path); !v)
        return std::unexpected(v.error());
    if (auto v = detail::check_xlsx_uncompressed_bound(path); !v)
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
            auto ws = doc.workbook().worksheet(std::string(checks_sheet));
            auto headers = headers_from_row(ws, static_cast<std::size_t>(ws.columnCount()));
            auto total_rows = ws.rowCount();
            for (std::uint32_t r = 2; r <= total_rows; ++r) {
                auto cells = row_to_map(ws, static_cast<int>(r), headers);
                if (cells.empty())
                    continue;
                results.push_back(parse_simple_row(cells, static_cast<int>(r)));
            }
        }

        if (has_when_then) {
            auto ws = doc.workbook().worksheet(std::string(when_then_sheet));
            auto headers = headers_from_row(ws, static_cast<std::size_t>(ws.columnCount()));
            auto total_rows = ws.rowCount();
            for (std::uint32_t r = 2; r <= total_rows; ++r) {
                auto cells = row_to_map(ws, static_cast<int>(r), headers);
                if (cells.empty())
                    continue;
                results.push_back(parse_when_then_row(cells, static_cast<int>(r)));
            }
        }

        doc.close();
        return results;

    } catch (const std::runtime_error& ex) {
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
static auto group_rows_by_message(const std::vector<CellMap>& data_rows,
                                  const std::vector<int>& row_numbers)
    -> std::vector<std::pair<MessageKeyExt, std::vector<std::size_t>>> {
    std::vector<std::pair<MessageKeyExt, std::vector<std::size_t>>> groups;
    std::map<MessageKeyExt, std::size_t> positions;
    for (std::size_t i = 0; i < data_rows.size(); ++i) {
        const auto& cells = data_rows[i];
        auto rn = row_numbers[i];
        auto msg_id_str = get_any(cells, "Message ID", row_ctx(rn));
        auto msg_id = parse_message_id(msg_id_str, row_ctx(rn));
        auto msg_name = get_str(cells, "Message Name", row_ctx(rn));
        auto dlc = get_int(cells, "DLC", row_ctx(rn));
        const bool extended =
            has_key(cells, "Extended") && get_bool(cells, "Extended", row_ctx(rn));
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
                                     const std::vector<CellMap>& data_rows,
                                     const std::vector<int>& row_numbers) -> Result<DbcMessage> {
    std::vector<DbcSignal> signals;
    signals.reserve(indices.size());
    for (auto idx : indices)
        signals.push_back(parse_dbc_signal(data_rows[idx], row_numbers[idx]));
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
            ErrorKind::Validation, row_ctx(row_numbers[indices[0]]) +
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
    // Same hardening as load_checks_from_excel.
    if (auto v = detail::validate_loader_path(path, "Excel"); !v)
        return std::unexpected(v.error());
    if (auto v = detail::check_file_size_bound(path); !v)
        return std::unexpected(v.error());
    if (auto v = detail::check_xlsx_uncompressed_bound(path); !v)
        return std::unexpected(v.error());

    try {
        OpenXLSX::XLDocument doc;
        doc.open(path.string());

        if (!worksheet_exists(doc, sheet))
            return std::unexpected(AletheiaError{
                ErrorKind::Validation, "Workbook has no '" + std::string(sheet) + "' sheet"});

        auto ws = doc.workbook().worksheet(std::string(sheet));
        auto headers = headers_from_row(ws, static_cast<std::size_t>(ws.columnCount()));
        auto total_rows = ws.rowCount();

        std::vector<CellMap> data_rows;
        std::vector<int> row_numbers;
        for (std::uint32_t r = 2; r <= total_rows; ++r) {
            auto cells = row_to_map(ws, static_cast<int>(r), headers);
            if (cells.empty())
                continue;
            data_rows.push_back(std::move(cells));
            row_numbers.push_back(static_cast<int>(r));
        }
        if (data_rows.empty())
            return std::unexpected(
                AletheiaError{ErrorKind::Validation, "DBC sheet has no data rows"});

        auto groups = group_rows_by_message(data_rows, row_numbers);

        std::vector<DbcMessage> messages;
        for (const auto& [key, rows] : groups) {
            auto msg = build_message_from_group(key, rows, data_rows, row_numbers);
            if (!msg.has_value())
                return std::unexpected(msg.error());
            messages.push_back(std::move(msg.value()));
        }

        doc.close();
        return DbcDefinition{.version = "", .messages = std::move(messages)};

    } catch (const std::runtime_error& ex) {
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

        // Rename default sheet to DBC
        // Bold cell format for the header rows, created once and applied to every
        // header cell.  Python (openpyxl Font(bold=True)) and Go (excelize
        // Font{Bold: true}) bold their template headers; match them.
        auto& styles = doc.styles();
        const auto bold_font = styles.fonts().create();
        styles.fonts()[bold_font].setBold(true);
        const auto header_fmt = styles.cellFormats().create();
        styles.cellFormats()[header_fmt].setFontIndex(bold_font);

        doc.workbook().worksheet("Sheet1").setName("DBC");
        auto ws_dbc = doc.workbook().worksheet("DBC");
        write_header_row(ws_dbc, dbc_headers(), header_fmt);

        // Checks sheet
        doc.workbook().addWorksheet("Checks");
        auto ws_checks = doc.workbook().worksheet("Checks");
        write_header_row(ws_checks, checks_headers(), header_fmt);

        // When-Then sheet
        doc.workbook().addWorksheet("When-Then");
        auto ws_wt = doc.workbook().worksheet("When-Then");
        write_header_row(ws_wt, when_then_headers(), header_fmt);

        doc.save();
        doc.close();
        return {};

    } catch (const std::exception& ex) {
        return std::unexpected(AletheiaError{ErrorKind::Validation, ex.what()});
    }
}

} // namespace aletheia
