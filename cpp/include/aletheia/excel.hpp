// SPDX-License-Identifier: BSD-2-Clause
//
// Excel loader for CAN signal checks and DBC definitions.
//
// Loads check definitions and DBC signal tables from Excel workbooks
// (.xlsx) and compiles them through the Check API into LTL properties.
//
// Designed for automotive technicians who define checks in spreadsheet
// templates -- no code, no YAML, just fill in cells.
//
#pragma once

// load_checks_from_excel returns Result<vector<CheckResult>> and load_dbc_from_excel
// returns Result<DbcDefinition> — callers need CheckResult, DbcDefinition, and the
// Result/AletheiaError vocabulary without a separate direct include.
#include <aletheia/check.hpp> // IWYU pragma: export
#include <aletheia/dbc.hpp>   // IWYU pragma: export
#include <aletheia/error.hpp> // IWYU pragma: export

#include <filesystem>
#include <string_view>
#include <vector>

namespace aletheia {

/// Load signal checks from an Excel workbook.
///
/// Reads the Checks and When-Then sheets. Either or both may be present.
auto load_checks_from_excel(const std::filesystem::path& path,
                            std::string_view checks_sheet = "Checks",
                            std::string_view when_then_sheet = "When-Then")
    -> Result<std::vector<CheckResult>>;

/// Load a DBC definition from the DBC sheet of an Excel workbook.
auto load_dbc_from_excel(const std::filesystem::path& path, std::string_view sheet = "DBC")
    -> Result<DbcDefinition>;

/// Create a blank Excel template with headers and column formatting.
///
/// Writes a .xlsx file with three sheets (DBC, Checks, When-Then),
/// each with correct headers in bold. Does not overwrite existing files.
auto create_excel_template(const std::filesystem::path& path) -> Result<void>;

} // namespace aletheia
