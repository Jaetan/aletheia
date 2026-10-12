// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// The workbooks the Excel loader tests author: the header row of each sheet
// kind, a data row written under the all-text contract, and a one-sheet
// workbook of each kind.

#include <OpenXLSX.hpp>

#include <algorithm>
#include <array>
#include <cctype>
#include <cstdint>
#include <filesystem>
#include <ranges>
#include <span>
#include <string>
#include <string_view>
#include <vector>

namespace aletheia::test {

// The header row each sheet kind carries. Held as views over string literals
// so nothing runs a constructor before main.
inline constexpr std::array<std::string_view, 8> checks_hdr = {
    "Check Name", "Signal", "Condition", "Value", "Min", "Max", "Time (ms)", "Severity"};

inline constexpr std::array<std::string_view, 11> wt_hdr = {
    "Check Name", "When Signal", "When Condition", "When Value",  "Then Signal", "Then Condition",
    "Then Value", "Then Min",    "Then Max",       "Within (ms)", "Severity"};

inline constexpr std::array<std::string_view, 16> dbc_hdr = {
    "Message ID",      "Message Name", "DLC",    "Signal", "Start Bit", "Length", "Byte Order",
    "Signed",          "Factor",       "Offset", "Min",    "Max",       "Unit",   "Multiplexor",
    "Multiplex Value", "Extended",
};

inline void write_header(OpenXLSX::XLWorksheet const& ws,
                         std::span<const std::string_view> headers) {
    for (auto const [i, header] : std::views::enumerate(headers))
        ws.cell(1, static_cast<std::uint16_t>(i + 1)).value() = std::string{header};
}

/// Write a data row (2-indexed) under the float-principle all-text contract: a
/// boolean fixture string ("TRUE"/"FALSE") becomes a native bool cell, and
/// EVERYTHING ELSE, numbers (e.g. "220", "0.1") AND text (e.g. a hex id like
/// "0x100"), is written as a TEXT cell. The loader requires numeric fields to
/// be text-formatted so the exact decimal is parsed by the kernel SSOT
/// (Rational::from_decimal); a number stored natively is rejected. To author a
/// number deliberately stored as a *native number* cell (the strict-rejection
/// tests), write it directly with an int64/double value.
inline void write_row(OpenXLSX::XLWorksheet const& ws, int row,
                      const std::vector<std::string>& values) {
    for (auto const [i, value] : std::views::enumerate(values)) {
        const std::string& s = value;
        if (s.empty())
            continue;
        auto const col = static_cast<std::uint16_t>(i + 1);
        auto upper = s;
        std::ranges::transform(upper, upper.begin(), [](unsigned char ch) -> char {
            return static_cast<char>(std::toupper(ch));
        });
        if (upper == "TRUE")
            ws.cell(row, col).value() = true;
        else if (upper == "FALSE")
            ws.cell(row, col).value() = false;
        else
            ws.cell(row, col).value() = s; // numbers AND text → TEXT cell
    }
}

/// Create a one-sheet workbook: the sheet renamed, its header row written and
/// one data row per entry from row 2 down.
inline void make_workbook(const std::filesystem::path& path, const std::string& sheet,
                          std::span<const std::string_view> headers,
                          const std::vector<std::vector<std::string>>& rows) {
    OpenXLSX::XLDocument doc;
    doc.create(path.string(), OpenXLSX::XLForceOverwrite);
    doc.workbook().worksheet("Sheet1").setName(sheet);
    auto const ws = doc.workbook().worksheet(sheet);
    write_header(ws, headers);
    for (auto const [r, row] : std::views::enumerate(rows))
        write_row(ws, static_cast<int>(r + 2), row);
    doc.save();
    doc.close();
}

inline void make_checks_workbook(const std::filesystem::path& path,
                                 const std::vector<std::vector<std::string>>& rows) {
    make_workbook(path, "Checks", checks_hdr, rows);
}

inline void make_wt_workbook(const std::filesystem::path& path,
                             const std::vector<std::vector<std::string>>& rows) {
    make_workbook(path, "When-Then", wt_hdr, rows);
}

inline void make_dbc_workbook(const std::filesystem::path& path,
                              const std::vector<std::vector<std::string>>& rows) {
    make_workbook(path, "DBC", dbc_hdr, rows);
}

} // namespace aletheia::test
