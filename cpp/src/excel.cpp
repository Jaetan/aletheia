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
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <exception>
#include <expected>
#include <filesystem>
#include <limits>
#include <map>
#include <stdexcept>
#include <string>
#include <string_view>
#include <system_error>
#include <tuple>
#include <utility>
#include <vector>

namespace aletheia {

namespace {

// ---------------------------------------------------------------------------
// Sheet headers
// ---------------------------------------------------------------------------

const std::vector<std::string> dbc_headers = {
    "Message ID",  "Message Name",    "Extended", "DLC",    "Signal", "Start Bit", "Length",
    "Byte Order",  "Signed",          "Factor",   "Offset", "Min",    "Max",       "Unit",
    "Multiplexor", "Multiplex Value",
};

const std::vector<std::string> checks_headers = {
    "Check Name", "Signal", "Condition", "Value", "Min", "Max", "Time (ms)", "Severity",
};

const std::vector<std::string> when_then_headers = {
    "Check Name", "When Signal", "When Condition", "When Value",  "Then Signal", "Then Condition",
    "Then Value", "Then Min",    "Then Max",       "Within (ms)", "Severity",
};

// ---------------------------------------------------------------------------
// Cell value conversion helper
// ---------------------------------------------------------------------------

/// Convert an XLCellValue to a string, returning empty for empty cells.
auto cell_to_string(const OpenXLSX::XLCellValue& val) -> std::string {
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

using CellMap = std::map<std::string, std::string>;

/// Build a header->value map from a worksheet row, skipping empty values.
auto row_to_map(OpenXLSX::XLWorksheet& ws, int row, const std::vector<std::string>& headers)
    -> CellMap {
    CellMap result;
    for (std::size_t i = 0; i < headers.size(); ++i) {
        const OpenXLSX::XLCellValue val = ws.cell(row, static_cast<std::uint16_t>(i + 1)).value();
        auto str_val = cell_to_string(val);
        if (str_val.empty())
            continue;
        result[headers[i]] = str_val;
    }
    return result;
}

// ---------------------------------------------------------------------------
// Typed field extractors with error context
// ---------------------------------------------------------------------------

auto get_str(const CellMap& cells, const std::string& key, const std::string& ctx_str)
    -> std::string {
    auto it = cells.find(key);
    if (it == cells.end() || it->second.empty())
        throw std::runtime_error(ctx_str + ": missing or invalid '" + key + "' (expected string)");
    return it->second;
}

auto get_number(const CellMap& cells, const std::string& key, const std::string& ctx_str)
    -> double {
    auto it = cells.find(key);
    if (it == cells.end() || it->second.empty())
        throw std::runtime_error(ctx_str + ": missing or invalid '" + key + "' (expected number)");
    // Reject booleans
    auto upper = it->second;
    std::ranges::transform(upper, upper.begin(), [](unsigned char ch) -> char {
        return static_cast<char>(std::toupper(ch));
    });
    if (upper == "TRUE" || upper == "FALSE")
        throw std::runtime_error(ctx_str + ": missing or invalid '" + key + "' (expected number)");
    // std::from_chars is locale-independent (unlike std::stod).
    const auto& sv = it->second;
    double result = 0.0;
    auto [ptr, ec] = std::from_chars(sv.data(), sv.data() + sv.size(), result);
    if (ec != std::errc{} || ptr != sv.data() + sv.size())
        throw std::runtime_error(ctx_str + ": missing or invalid '" + key + "' (expected number)");
    return result;
}

auto get_int(const CellMap& cells, const std::string& key, const std::string& ctx_str)
    -> std::int64_t {
    auto it = cells.find(key);
    if (it == cells.end() || it->second.empty())
        throw std::runtime_error(ctx_str + ": missing or invalid '" + key + "' (expected integer)");
    // Reject booleans (cell_to_string converts Excel booleans to "TRUE"/"FALSE")
    auto upper = it->second;
    std::ranges::transform(upper, upper.begin(), [](unsigned char ch) -> char {
        return static_cast<char>(std::toupper(ch));
    });
    if (upper == "TRUE" || upper == "FALSE")
        throw std::runtime_error(ctx_str + ": missing or invalid '" + key + "' (expected integer)");
    // Detect float truncation: parse as double first and reject non-integral values.
    // std::from_chars is locale-independent (unlike std::stod/std::stoll).
    const auto& sv = it->second;
    double dval = 0.0;
    auto [dptr, dec] = std::from_chars(sv.data(), sv.data() + sv.size(), dval);
    if (dec != std::errc{} || dptr != sv.data() + sv.size())
        throw std::runtime_error(ctx_str + ": missing or invalid '" + key + "' (expected integer)");
    if (dval != std::floor(dval))
        throw std::runtime_error(ctx_str + ": '" + key + "' value " + it->second +
                                 " is not an integer (would be silently truncated)");
    std::int64_t result = 0;
    auto [iptr, iec] = std::from_chars(sv.data(), sv.data() + sv.size(), result);
    if (iec != std::errc{} || iptr != sv.data() + sv.size())
        throw std::runtime_error(ctx_str + ": missing or invalid '" + key + "' (expected integer)");
    return result;
}

auto get_bool(const CellMap& cells, const std::string& key, const std::string& ctx_str) -> bool {
    auto it = cells.find(key);
    if (it == cells.end() || it->second.empty())
        throw std::runtime_error(ctx_str + ": missing or invalid '" + key +
                                 "' (expected TRUE/FALSE)");
    auto upper = it->second;
    std::ranges::transform(upper, upper.begin(), [](unsigned char ch) -> char {
        return static_cast<char>(std::toupper(ch));
    });
    if (upper == "TRUE" || upper == "1")
        return true;
    if (upper == "FALSE" || upper == "0")
        return false;
    throw std::runtime_error(ctx_str + ": missing or invalid '" + key + "' (expected TRUE/FALSE)");
}

auto row_ctx(int row_num) -> std::string {
    return "Row " + std::to_string(row_num);
}

auto has_key(const CellMap& cells, const std::string& key) -> bool {
    auto it = cells.find(key);
    return it != cells.end() && !it->second.empty();
}

// ---------------------------------------------------------------------------
// Header extraction from first row
// ---------------------------------------------------------------------------

auto headers_from_row(OpenXLSX::XLWorksheet& ws, std::size_t count) -> std::vector<std::string> {
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

auto parse_message_id(const std::string& val, const std::string& ctx_str) -> std::uint32_t {
    if (val.empty())
        throw std::runtime_error(
            ctx_str +
            ": invalid 'Message ID' \xe2\x80\x94 expected integer or hex string (e.g. 0x100)");
    // std::from_chars is locale-independent (unlike std::stoul).
    auto lower = val;
    std::ranges::transform(lower, lower.begin(), [](unsigned char ch) -> char {
        return static_cast<char>(std::tolower(ch));
    });
    std::uint32_t result = 0;
    const char* begin = val.data();
    const char* end = val.data() + val.size();
    std::errc ec{};
    const char* ptr = nullptr;
    if (lower.starts_with("0x")) {
        auto [p, e] = std::from_chars(begin + 2, end, result, 16);
        ptr = p;
        ec = e;
    } else {
        auto [p, e] = std::from_chars(begin, end, result);
        ptr = p;
        ec = e;
    }
    if (ec != std::errc{} || ptr != end)
        throw std::runtime_error(
            ctx_str +
            ": invalid 'Message ID' \xe2\x80\x94 expected integer or hex string (e.g. 0x100)");
    return result;
}

// ---------------------------------------------------------------------------
// Checks sheet parser
// ---------------------------------------------------------------------------

auto parse_simple_row(const CellMap& cells, int row_num) -> CheckResult {
    auto signal = get_str(cells, "Signal", row_ctx(row_num));
    auto condition = get_str(cells, "Condition", row_ctx(row_num));

    if (!detail::is_simple_condition(condition))
        throw std::runtime_error(row_ctx(row_num) + ": unknown condition '" + condition + "'");

    CheckResult result = [&]() -> CheckResult {
        if (detail::is_simple_value_condition(condition)) {
            auto value =
                PhysicalValue{Rational::from_double(get_number(cells, "Value", row_ctx(row_num)))};
            return detail::dispatch_simple(signal, condition, value);
        }
        if (detail::is_simple_range_condition(condition)) {
            if (!has_key(cells, "Min") || !has_key(cells, "Max"))
                throw std::runtime_error(row_ctx(row_num) + ": condition '" + condition +
                                         "' requires 'Min' and 'Max'");
            auto lo =
                PhysicalValue{Rational::from_double(get_number(cells, "Min", row_ctx(row_num)))};
            auto hi =
                PhysicalValue{Rational::from_double(get_number(cells, "Max", row_ctx(row_num)))};
            return Check::signal(signal).stays_between(lo, hi);
        }
        if (detail::is_simple_settles_condition(condition)) {
            if (!has_key(cells, "Min") || !has_key(cells, "Max"))
                throw std::runtime_error(row_ctx(row_num) +
                                         ": condition 'settles_between' requires 'Min' and 'Max'");
            if (!has_key(cells, "Time (ms)"))
                throw std::runtime_error(row_ctx(row_num) +
                                         ": condition 'settles_between' requires 'Time (ms)'");
            auto lo =
                PhysicalValue{Rational::from_double(get_number(cells, "Min", row_ctx(row_num)))};
            auto hi =
                PhysicalValue{Rational::from_double(get_number(cells, "Max", row_ctx(row_num)))};
            auto ms = std::chrono::milliseconds{get_int(cells, "Time (ms)", row_ctx(row_num))};
            return Check::signal(signal).settles_between(lo, hi).within(ms);
        }
        // equals
        auto value =
            PhysicalValue{Rational::from_double(get_number(cells, "Value", row_ctx(row_num)))};
        return Check::signal(signal).equals(value).always();
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

auto parse_when_then_row(const CellMap& cells, int row_num) -> CheckResult {
    auto when_signal = get_str(cells, "When Signal", row_ctx(row_num));
    auto when_cond = get_str(cells, "When Condition", row_ctx(row_num));
    auto when_value =
        PhysicalValue{Rational::from_double(get_number(cells, "When Value", row_ctx(row_num)))};

    if (!detail::is_when_condition(when_cond))
        throw std::runtime_error(row_ctx(row_num) + ": unknown when condition '" + when_cond + "'");

    auto when_builder = Check::when(when_signal);
    auto when_result = detail::dispatch_when(when_builder, when_cond, when_value);

    auto then_signal = get_str(cells, "Then Signal", row_ctx(row_num));
    auto then_cond = get_str(cells, "Then Condition", row_ctx(row_num));

    if (!detail::is_then_condition(then_cond))
        throw std::runtime_error(row_ctx(row_num) + ": unknown then condition '" + then_cond + "'");

    auto then_builder = when_result.then(then_signal);
    auto within_ms = std::chrono::milliseconds{get_int(cells, "Within (ms)", row_ctx(row_num))};

    CheckResult result = [&]() -> CheckResult {
        if (then_cond == "equals") {
            auto val = PhysicalValue{
                Rational::from_double(get_number(cells, "Then Value", row_ctx(row_num)))};
            return then_builder.equals(val).within(within_ms);
        }
        if (then_cond == "exceeds") {
            auto val = PhysicalValue{
                Rational::from_double(get_number(cells, "Then Value", row_ctx(row_num)))};
            return then_builder.exceeds(val).within(within_ms);
        }
        // stays_between
        if (!has_key(cells, "Then Min") || !has_key(cells, "Then Max"))
            throw std::runtime_error(
                row_ctx(row_num) +
                ": then condition 'stays_between' requires 'Then Min' and 'Then Max'");
        auto lo =
            PhysicalValue{Rational::from_double(get_number(cells, "Then Min", row_ctx(row_num)))};
        auto hi =
            PhysicalValue{Rational::from_double(get_number(cells, "Then Max", row_ctx(row_num)))};
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

auto parse_dbc_signal(const CellMap& cells, int row_num) -> DbcSignal {
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

    // Unit defaults to empty if missing
    std::string unit_str;
    if (has_key(cells, "Unit"))
        unit_str = get_str(cells, "Unit", ctx_str);

    // Multiplexing
    const bool has_muxor = has_key(cells, "Multiplexor");
    const bool has_mux_val = has_key(cells, "Multiplex Value");

    if (has_muxor != has_mux_val)
        throw std::runtime_error(ctx_str + ": 'Multiplexor' and 'Multiplex Value' "
                                           "must both be provided or both be empty");

    SignalPresence presence;
    if (has_muxor) {
        auto mux_val = get_int(cells, "Multiplex Value", ctx_str);
        if (mux_val < 0 ||
            mux_val > static_cast<std::int64_t>(std::numeric_limits<std::uint32_t>::max()))
            throw std::runtime_error(ctx_str + ": 'Multiplex Value' out of range [0, " +
                                     std::to_string(std::numeric_limits<std::uint32_t>::max()) +
                                     "]: " + std::to_string(mux_val));
        presence = Multiplexed{.multiplexor = SignalName{get_str(cells, "Multiplexor", ctx_str)},
                               .mux_values = {MultiplexValue{static_cast<std::uint32_t>(mux_val)}}};
    } else {
        presence = AlwaysPresent{};
    }

    auto start_bit_val = get_int(cells, "Start Bit", ctx_str);
    if (start_bit_val < 0 || start_bit_val > std::numeric_limits<std::uint16_t>::max())
        throw std::runtime_error(ctx_str + ": 'Start Bit' out of range [0, " +
                                 std::to_string(std::numeric_limits<std::uint16_t>::max()) +
                                 "]: " + std::to_string(start_bit_val));
    auto bit_length_val = get_int(cells, "Length", ctx_str);
    if (bit_length_val < 0 || bit_length_val > std::numeric_limits<std::uint8_t>::max())
        throw std::runtime_error(ctx_str + ": 'Length' out of range [0, " +
                                 std::to_string(std::numeric_limits<std::uint8_t>::max()) +
                                 "]: " + std::to_string(bit_length_val));

    return DbcSignal{
        .name = SignalName{get_str(cells, "Signal", ctx_str)},
        .start_bit = BitPosition{static_cast<std::uint16_t>(start_bit_val)},
        .bit_length = BitLength{static_cast<std::uint8_t>(bit_length_val)},
        .byte_order = byte_order,
        .is_signed = get_bool(cells, "Signed", ctx_str),
        .factor = RationalFactor{Rational::from_double(get_number(cells, "Factor", ctx_str))},
        .offset = RationalOffset{Rational::from_double(get_number(cells, "Offset", ctx_str))},
        .minimum = RationalBound{Rational::from_double(get_number(cells, "Min", ctx_str))},
        .maximum = RationalBound{Rational::from_double(get_number(cells, "Max", ctx_str))},
        .unit = Unit{unit_str},
        .presence = presence,
    };
}

// ---------------------------------------------------------------------------
// Sheet existence check
// ---------------------------------------------------------------------------

auto worksheet_exists(OpenXLSX::XLDocument& doc, std::string_view name) -> bool {
    auto names = doc.workbook().worksheetNames();
    return std::ranges::find(names, std::string(name)) != names.end();
}

// ---------------------------------------------------------------------------
// Write header row helper
// ---------------------------------------------------------------------------

void write_header_row(OpenXLSX::XLWorksheet& ws, const std::vector<std::string>& headers) {
    for (std::size_t i = 0; i < headers.size(); ++i)
        ws.cell(1, static_cast<std::uint16_t>(i + 1)).value() = headers[i];
}

} // namespace

// ===========================================================================
// Public API: Checks from Excel
// ===========================================================================

auto load_checks_from_excel(const std::filesystem::path& path, std::string_view checks_sheet,
                            std::string_view when_then_sheet) -> Result<std::vector<CheckResult>> {
    if (!std::filesystem::exists(path))
        return std::unexpected(
            AletheiaError{ErrorKind::Validation, "Excel file not found: " + path.string()});

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
            auto headers = headers_from_row(ws, checks_headers.size());
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
            auto headers = headers_from_row(ws, when_then_headers.size());
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

namespace {

// (msg_id, msg_name, dlc, is_extended) — the row-level identity of a message.
using MessageKeyExt = std::tuple<std::uint32_t, std::string, std::int64_t, bool>;

// Group data rows by message key, preserving first-seen order. Each row
// becomes one signal in its parent message.
auto group_rows_by_message(const std::vector<CellMap>& data_rows,
                           const std::vector<int>& row_numbers)
    -> std::pair<std::map<MessageKeyExt, std::vector<std::size_t>>, std::vector<MessageKeyExt>> {
    std::map<MessageKeyExt, std::vector<std::size_t>> groups;
    std::vector<MessageKeyExt> insertion_order;
    for (std::size_t i = 0; i < data_rows.size(); ++i) {
        const auto& cells = data_rows[i];
        auto rn = row_numbers[i];
        auto msg_id_str = get_str(cells, "Message ID", row_ctx(rn));
        auto msg_id = parse_message_id(msg_id_str, row_ctx(rn));
        auto msg_name = get_str(cells, "Message Name", row_ctx(rn));
        auto dlc = get_int(cells, "DLC", row_ctx(rn));
        const bool extended =
            has_key(cells, "Extended") && get_bool(cells, "Extended", row_ctx(rn));
        const MessageKeyExt key{msg_id, msg_name, dlc, extended};
        if (!groups.contains(key))
            insertion_order.push_back(key);
        groups[key].push_back(i);
    }
    return {std::move(groups), std::move(insertion_order)};
}

// Build one DbcMessage from its group of rows; surfaces validation errors as
// an unexpected Result so the top-level loop stays linear.
auto build_message_from_group(const MessageKeyExt& key, const std::vector<std::size_t>& indices,
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

} // namespace

auto load_dbc_from_excel(const std::filesystem::path& path, std::string_view sheet)
    -> Result<DbcDefinition> {
    if (!std::filesystem::exists(path))
        return std::unexpected(
            AletheiaError{ErrorKind::Validation, "Excel file not found: " + path.string()});

    try {
        OpenXLSX::XLDocument doc;
        doc.open(path.string());

        if (!worksheet_exists(doc, sheet))
            return std::unexpected(AletheiaError{
                ErrorKind::Validation, "Workbook has no '" + std::string(sheet) + "' sheet"});

        auto ws = doc.workbook().worksheet(std::string(sheet));
        auto headers = headers_from_row(ws, dbc_headers.size());
        auto total_rows = ws.rowCount();

        std::vector<CellMap> data_rows;
        std::vector<int> row_numbers;
        for (std::uint32_t r = 2; r <= total_rows; ++r) {
            auto cells = row_to_map(ws, static_cast<int>(r), headers);
            if (cells.empty())
                continue;
            data_rows.push_back(cells);
            row_numbers.push_back(static_cast<int>(r));
        }
        if (data_rows.empty())
            return std::unexpected(
                AletheiaError{ErrorKind::Validation, "DBC sheet has no data rows"});

        auto [groups, insertion_order] = group_rows_by_message(data_rows, row_numbers);

        std::vector<DbcMessage> messages;
        for (const auto& key : insertion_order) {
            auto msg = build_message_from_group(key, groups[key], data_rows, row_numbers);
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
    if (std::filesystem::exists(path))
        return std::unexpected(
            AletheiaError{ErrorKind::Validation, "File already exists: " + path.string()});

    try {
        OpenXLSX::XLDocument doc;
        doc.create(path.string(), OpenXLSX::XLForceOverwrite);

        // Rename default sheet to DBC
        doc.workbook().worksheet("Sheet1").setName("DBC");
        auto ws_dbc = doc.workbook().worksheet("DBC");
        write_header_row(ws_dbc, dbc_headers);

        // Checks sheet
        doc.workbook().addWorksheet("Checks");
        auto ws_checks = doc.workbook().worksheet("Checks");
        write_header_row(ws_checks, checks_headers);

        // When-Then sheet
        doc.workbook().addWorksheet("When-Then");
        auto ws_wt = doc.workbook().worksheet("When-Then");
        write_header_row(ws_wt, when_then_headers);

        doc.save();
        doc.close();
        return {};

    } catch (const std::exception& ex) {
        return std::unexpected(AletheiaError{ErrorKind::Validation, ex.what()});
    }
}

} // namespace aletheia
