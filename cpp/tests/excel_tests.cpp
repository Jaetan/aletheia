// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// Excel loader tests.
// Tests Excel check and DBC parsing with programmatically-created workbooks.
#include <catch2/catch_test_macros.hpp>
#include <catch2/generators/catch_generators.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>

#include <aletheia/enrich.hpp>
#include <aletheia/error.hpp>
#include <aletheia/excel.hpp>

#include <OpenXLSX.hpp>

#include <algorithm>
#include <array>
#include <cctype>
#include <cstdint>
#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <ios>
#include <ranges>
#include <span>
#include <string>
#include <string_view>
#include <system_error>
#include <variant>
#include <vector>

#include "temp_path.hpp"
#ifdef ALETHEIA_ALLOC_FAULT
#include "alloc_fault.hpp"
#endif
#include <catch2/matchers/catch_matchers.hpp>
#include <dlfcn.h>
#include <unistd.h>

#include "repo_root.hpp"

using aletheia::test::repo_root;

using aletheia::test::AsDirectory;
using aletheia::test::scratch_dir;
using aletheia::test::TempPath;

using namespace aletheia;
using Catch::Matchers::ContainsSubstring;

// ===========================================================================
// Test helpers
// ===========================================================================

// The header row each sheet kind carries. Held as views over string literals
// so nothing runs a constructor before main.
constexpr std::array<std::string_view, 8> checks_hdr = {
    "Check Name", "Signal", "Condition", "Value", "Min", "Max", "Time (ms)", "Severity"};

constexpr std::array<std::string_view, 11> wt_hdr = {
    "Check Name", "When Signal", "When Condition", "When Value",  "Then Signal", "Then Condition",
    "Then Value", "Then Min",    "Then Max",       "Within (ms)", "Severity"};

constexpr std::array<std::string_view, 16> dbc_hdr = {
    "Message ID",      "Message Name", "DLC",    "Signal", "Start Bit", "Length", "Byte Order",
    "Signed",          "Factor",       "Offset", "Min",    "Max",       "Unit",   "Multiplexor",
    "Multiplex Value", "Extended",
};

// Write raw bytes to a binary stream. The stream takes char and the archive
// fixtures below read as unsigned, so each byte crosses as a value rather than
// through a cast of the buffer's type.
static void write_bytes(std::ofstream& ofs, std::span<const unsigned char> bytes) {
    for (const unsigned char b : bytes)
        ofs.put(static_cast<char>(b));
}

static void write_header(OpenXLSX::XLWorksheet const& ws,
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
static void write_row(OpenXLSX::XLWorksheet const& ws, int row,
                      const std::vector<std::string>& values) {
    for (auto const [i, value] : std::views::enumerate(values)) {
        const std::string& s = value;
        if (s.empty())
            continue;
        auto const col = static_cast<std::uint16_t>(i + 1);
        std::string upper = s;
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
static void make_workbook(const std::filesystem::path& path, const std::string& sheet,
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

static void make_checks_workbook(const std::filesystem::path& path,
                                 const std::vector<std::vector<std::string>>& rows) {
    make_workbook(path, "Checks", checks_hdr, rows);
}

static void make_wt_workbook(const std::filesystem::path& path,
                             const std::vector<std::vector<std::string>>& rows) {
    make_workbook(path, "When-Then", wt_hdr, rows);
}

static void make_dbc_workbook(const std::filesystem::path& path,
                              const std::vector<std::vector<std::string>>& rows) {
    make_workbook(path, "DBC", dbc_hdr, rows);
}

/// Build a one-row DBC workbook whose Message ID cell is a native number cell,
/// then (when raw_override is non-null) rewrite that cell's raw stored <v>
/// text by patching the sheet XML inside the saved archive through OpenXLSX's
/// public XLZipArchive — the typed setters cannot author a dot-free scientific
/// literal or an empty <v/>. Every other field is text per the all-text
/// contract. id_value doubles as the patch anchor, so surgery callers pass a
/// sentinel unique within the sheet XML.
static void make_dbc_workbook_with_raw_id(const std::filesystem::path& path, std::int64_t id_value,
                                          const char* raw_override) {
    OpenXLSX::XLDocument doc;
    doc.create(path.string(), OpenXLSX::XLForceOverwrite);
    doc.workbook().worksheet("Sheet1").setName("DBC");
    auto const ws = doc.workbook().worksheet("DBC");
    write_header(ws, dbc_hdr);
    write_row(ws, 2,
              {"", "Msg", "8", "Sig", "0", "8", "little_endian", "FALSE", "1", "0", "0", "255", "",
               "", "", ""});
    ws.cell(2, 1).value() = id_value; // native number cell
    doc.save();
    doc.close();
    if (raw_override == nullptr)
        return;
    const std::string sheet_name = "xl/worksheets/sheet1.xml";
    const std::string needle = "<v>" + std::to_string(id_value) + "</v>";
    const std::string replacement =
        (*raw_override == '\0') ? std::string{"<v/>"} : "<v>" + std::string{raw_override} + "</v>";
    OpenXLSX::XLZipArchive zip;
    zip.open(path.string());
    std::string xml = zip.getEntry(sheet_name);
    auto const pos = xml.find(needle);
    REQUIRE(pos != std::string::npos);
    xml.replace(pos, needle.size(), replacement);
    zip.addEntry(sheet_name, xml);
    zip.save();
    zip.close();
}

// ===========================================================================
// Simple check conditions
// ===========================================================================

TEST_CASE("excel: never_exceeds", "[excel][simple]") {
    TempPath tf("excel_never_exceeds.xlsx");
    // Check Name, Signal, Condition, Value, Min, Max, Time (ms), Severity
    make_checks_workbook(tf.path, {{"", "Speed", "never_exceeds", "220", "", "", "", ""}});
    auto result = load_checks_from_excel(tf.path);
    REQUIRE(result.has_value());
    REQUIRE(result->size() == 1);
    REQUIRE((*result)[0].to_formula().has_value());
    CHECK((*result)[0].condition_desc() == "<= 220");
}

TEST_CASE("excel: never_below", "[excel][simple]") {
    TempPath tf("excel_never_below.xlsx");
    make_checks_workbook(tf.path, {{"", "Voltage", "never_below", "11.5", "", "", "", ""}});
    auto result = load_checks_from_excel(tf.path);
    REQUIRE(result.has_value());
    REQUIRE(result->size() == 1);
    CHECK((*result)[0].condition_desc() == ">= 11.5");
}

TEST_CASE("excel: stays_between", "[excel][simple]") {
    TempPath tf("excel_stays_between.xlsx");
    make_checks_workbook(tf.path, {{"", "Voltage", "stays_between", "", "11.5", "14.5", "", ""}});
    auto result = load_checks_from_excel(tf.path);
    REQUIRE(result.has_value());
    REQUIRE(result->size() == 1);
    CHECK((*result)[0].condition_desc() == "between 11.5 and 14.5");
}

TEST_CASE("excel: never_equals", "[excel][simple]") {
    TempPath tf("excel_never_equals.xlsx");
    make_checks_workbook(tf.path, {{"", "ErrorCode", "never_equals", "99", "", "", "", ""}});
    auto result = load_checks_from_excel(tf.path);
    REQUIRE(result.has_value());
    REQUIRE(result->size() == 1);
    CHECK((*result)[0].condition_desc() == "!= 99");
}

TEST_CASE("excel: equals always", "[excel][simple]") {
    TempPath tf("excel_equals.xlsx");
    make_checks_workbook(tf.path, {{"", "ParkingBrake", "equals", "0", "", "", "", ""}});
    auto result = load_checks_from_excel(tf.path);
    REQUIRE(result.has_value());
    REQUIRE(result->size() == 1);
    CHECK((*result)[0].condition_desc() == "= 0");
}

TEST_CASE("excel: settles_between", "[excel][simple]") {
    TempPath tf("excel_settles.xlsx");
    make_checks_workbook(tf.path, {{"", "Coolant", "settles_between", "", "85", "95", "5000", ""}});
    auto result = load_checks_from_excel(tf.path);
    REQUIRE(result.has_value());
    REQUIRE(result->size() == 1);
    CHECK((*result)[0].condition_desc() == "between 85 and 95 within 5000ms");
}

// ===========================================================================
// When/Then conditions
// ===========================================================================

TEST_CASE("excel: when exceeds then equals", "[excel][when-then]") {
    TempPath tf("excel_wt_exc_eq.xlsx");
    // Check Name, When Signal, When Condition, When Value,
    // Then Signal, Then Condition, Then Value, Then Min, Then Max,
    // Within (ms), Severity
    make_wt_workbook(tf.path, {{"", "BrakePedal", "exceeds", "50", "BrakeLight", "equals", "1", "",
                                "", "100", ""}});
    auto result = load_checks_from_excel(tf.path);
    REQUIRE(result.has_value());
    REQUIRE(result->size() == 1);
    REQUIRE((*result)[0].to_formula().has_value());
    CHECK(format_formula(*(*result)[0].to_formula()) ==
          "always(not(BrakePedal > 50) or eventually within 100ms (BrakeLight = 1))");
}

TEST_CASE("excel: when equals then exceeds", "[excel][when-then]") {
    TempPath tf("excel_wt_eq_exc.xlsx");
    make_wt_workbook(
        tf.path, {{"", "Gear", "equals", "1", "ReverseLight", "exceeds", "0", "", "", "200", ""}});
    auto result = load_checks_from_excel(tf.path);
    REQUIRE(result.has_value());
    REQUIRE(result->size() == 1);
    REQUIRE((*result)[0].to_formula().has_value());
    CHECK(format_formula(*(*result)[0].to_formula()) ==
          "always(not(Gear = 1) or eventually within 200ms (ReverseLight > 0))");
}

TEST_CASE("excel: when drops_below then stays_between", "[excel][when-then]") {
    TempPath tf("excel_wt_drop_sb.xlsx");
    make_wt_workbook(tf.path, {{"", "FuelLevel", "drops_below", "10", "FuelWarning",
                                "stays_between", "", "1", "1", "500", ""}});
    auto result = load_checks_from_excel(tf.path);
    REQUIRE(result.has_value());
    REQUIRE(result->size() == 1);
    REQUIRE((*result)[0].to_formula().has_value());
    CHECK(format_formula(*(*result)[0].to_formula()) ==
          "always(not(FuelLevel < 10) or eventually within 500ms (1 <= FuelWarning <= 1))");
}

// ===========================================================================
// Metadata
// ===========================================================================

TEST_CASE("excel: check name applied", "[excel][metadata]") {
    TempPath tf("excel_meta_name.xlsx");
    make_checks_workbook(tf.path,
                         {{"Speed limit", "Speed", "never_exceeds", "220", "", "", "", ""}});
    auto result = load_checks_from_excel(tf.path);
    REQUIRE(result.has_value());
    CHECK((*result)[0].name() == "Speed limit");
}

TEST_CASE("excel: severity applied", "[excel][metadata]") {
    TempPath tf("excel_meta_sev.xlsx");
    make_checks_workbook(tf.path, {{"", "Speed", "never_exceeds", "220", "", "", "", "critical"}});
    auto result = load_checks_from_excel(tf.path);
    REQUIRE(result.has_value());
    CHECK((*result)[0].check_severity() == "critical");
}

TEST_CASE("excel: name and severity together", "[excel][metadata]") {
    TempPath tf("excel_meta_both.xlsx");
    make_checks_workbook(
        tf.path, {{"Speed limit", "Speed", "never_exceeds", "220", "", "", "", "critical"}});
    auto result = load_checks_from_excel(tf.path);
    REQUIRE(result.has_value());
    CHECK((*result)[0].name() == "Speed limit");
    CHECK((*result)[0].check_severity() == "critical");
}

TEST_CASE("excel: defaults when no name or severity", "[excel][metadata]") {
    TempPath tf("excel_meta_defaults.xlsx");
    make_checks_workbook(tf.path, {{"", "Speed", "never_exceeds", "200", "", "", "", ""}});
    auto result = load_checks_from_excel(tf.path);
    REQUIRE(result.has_value());
    CHECK((*result)[0].name().empty());
    CHECK((*result)[0].check_severity().empty());
}

TEST_CASE("excel: when-then with metadata", "[excel][metadata]") {
    TempPath tf("excel_meta_wt.xlsx");
    make_wt_workbook(tf.path, {{"Brake response", "BrakePedal", "exceeds", "50", "BrakeLight",
                                "equals", "1", "", "", "100", "safety"}});
    auto result = load_checks_from_excel(tf.path);
    REQUIRE(result.has_value());
    CHECK((*result)[0].name() == "Brake response");
    CHECK((*result)[0].check_severity() == "safety");
}

// ===========================================================================
// DBC parsing
// ===========================================================================

TEST_CASE("excel: DBC single signal", "[excel][dbc]") {
    TempPath tf("excel_dbc_single.xlsx");
    // Message ID, Message Name, DLC, Signal, Start Bit, Length,
    // Byte Order, Signed, Factor, Offset, Min, Max, Unit,
    // Multiplexor, Multiplex Value
    make_dbc_workbook(tf.path, {{"256", "VehicleSpeed", "8", "Speed", "0", "16", "little_endian",
                                 "FALSE", "0.1", "0", "0", "300", "km/h", "", "", ""}});
    auto result = load_dbc_from_excel(tf.path);
    REQUIRE(result.has_value());
    REQUIRE(result->messages.size() == 1);

    auto& msg = result->messages[0];
    CHECK(msg.name.get() == "VehicleSpeed");
    CHECK(msg.signals.size() == 1);

    auto const& sig = msg.signals[0];
    CHECK(sig.name.get() == "Speed");
    CHECK(sig.start_bit.get() == 0);
    CHECK(sig.bit_length.get() == 16);
    CHECK(sig.byte_order == ByteOrder::LittleEndian);
    CHECK(!sig.is_signed);
    CHECK(sig.unit.get() == "km/h");
    CHECK(std::holds_alternative<AlwaysPresent>(sig.presence));
    // Standard ID (256 <= 2047, not extended)
    CHECK(std::holds_alternative<StandardId>(msg.id));
}

TEST_CASE("excel: DBC message grouping", "[excel][dbc]") {
    TempPath tf("excel_dbc_group.xlsx");
    make_dbc_workbook(tf.path, {
                                   {"256", "Msg1", "8", "Sig1", "0", "8", "little_endian", "FALSE",
                                    "1", "0", "0", "255", "", "", "", ""},
                                   {"256", "Msg1", "8", "Sig2", "8", "8", "little_endian", "FALSE",
                                    "1", "0", "0", "255", "", "", "", ""},
                                   {"512", "Msg2", "4", "Sig3", "0", "16", "big_endian", "TRUE",
                                    "0.5", "10", "-100", "100", "C", "", "", ""},
                               });
    auto result = load_dbc_from_excel(tf.path);
    REQUIRE(result.has_value());
    REQUIRE(result->messages.size() == 2);
    CHECK(result->messages[0].signals.size() == 2);
    CHECK(result->messages[1].signals.size() == 1);
    CHECK(result->messages[1].signals[0].byte_order == ByteOrder::BigEndian);
    CHECK(result->messages[1].signals[0].is_signed);
}

TEST_CASE("excel: DBC hex message ID", "[excel][dbc]") {
    TempPath tf("excel_dbc_hex.xlsx");
    make_dbc_workbook(tf.path, {{"0x100", "HexMsg", "8", "Sig", "0", "8", "little_endian", "FALSE",
                                 "1", "0", "0", "255", "", "", "", ""}});
    auto result = load_dbc_from_excel(tf.path);
    REQUIRE(result.has_value());
    auto& msg = result->messages[0];
    auto* std_id = std::get_if<StandardId>(&msg.id);
    REQUIRE(std_id != nullptr);
    CHECK(std_id->value() == 0x100);
}

TEST_CASE("excel: DBC signed variants", "[excel][dbc]") {
    TempPath tf("excel_dbc_signed.xlsx");
    make_dbc_workbook(tf.path, {
                                   {"256", "M1", "8", "S1", "0", "8", "little_endian", "TRUE", "1",
                                    "0", "-128", "127", "", "", "", ""},
                                   {"256", "M1", "8", "S2", "8", "8", "little_endian", "1", "1",
                                    "0", "0", "255", "", "", "", ""},
                                   {"256", "M1", "8", "S3", "16", "8", "little_endian", "0", "1",
                                    "0", "0", "255", "", "", "", ""},
                               });
    auto result = load_dbc_from_excel(tf.path);
    REQUIRE(result.has_value());
    auto& sigs = result->messages[0].signals;
    CHECK(sigs[0].is_signed);
    CHECK(sigs[1].is_signed);
    CHECK(!sigs[2].is_signed);
}

TEST_CASE("excel: DBC missing unit defaults to empty", "[excel][dbc]") {
    TempPath tf("excel_dbc_no_unit.xlsx");
    make_dbc_workbook(tf.path, {{"256", "Msg", "8", "Sig", "0", "8", "little_endian", "FALSE", "1",
                                 "0", "0", "255", "", "", "", ""}});
    auto result = load_dbc_from_excel(tf.path);
    REQUIRE(result.has_value());
    CHECK(result->messages[0].signals[0].unit.get().empty());
}

// ===========================================================================
// Multiplexing
// ===========================================================================

TEST_CASE("excel: DBC always present signal", "[excel][mux]") {
    TempPath tf("excel_mux_always.xlsx");
    make_dbc_workbook(tf.path, {{"256", "Msg", "8", "Sig", "0", "8", "little_endian", "FALSE", "1",
                                 "0", "0", "255", "", "", "", ""}});
    auto result = load_dbc_from_excel(tf.path);
    REQUIRE(result.has_value());
    CHECK(std::holds_alternative<AlwaysPresent>(result->messages[0].signals[0].presence));
}

TEST_CASE("excel: DBC multiplexed signal", "[excel][mux]") {
    TempPath tf("excel_mux_muxed.xlsx");
    make_dbc_workbook(tf.path, {{"256", "Msg", "8", "MuxSig", "0", "8", "little_endian", "FALSE",
                                 "1", "0", "0", "255", "", "Selector", "3", ""}});
    auto result = load_dbc_from_excel(tf.path);
    REQUIRE(result.has_value());
    auto& pres = result->messages[0].signals[0].presence;
    REQUIRE(std::holds_alternative<Multiplexed>(pres));
    auto& mux = std::get<Multiplexed>(pres);
    CHECK(mux.multiplexor.get() == "Selector");
    REQUIRE(mux.multiplex_values.size() == 1);
    CHECK(mux.multiplex_values[0].get() == 3);
}

TEST_CASE("excel: DBC mixed always and mux", "[excel][mux]") {
    TempPath tf("excel_mux_mixed.xlsx");
    make_dbc_workbook(tf.path, {
                                   {"256", "Msg", "8", "AlwaysSig", "0", "8", "little_endian",
                                    "FALSE", "1", "0", "0", "255", "", "", "", ""},
                                   {"256", "Msg", "8", "MuxSig", "8", "8", "little_endian", "FALSE",
                                    "1", "0", "0", "255", "", "Selector", "1", ""},
                               });
    auto result = load_dbc_from_excel(tf.path);
    REQUIRE(result.has_value());
    auto& sigs = result->messages[0].signals;
    CHECK(std::holds_alternative<AlwaysPresent>(sigs[0].presence));
    CHECK(std::holds_alternative<Multiplexed>(sigs[1].presence));
}

TEST_CASE("excel: DBC partial mux error", "[excel][mux]") {
    TempPath tf("excel_mux_partial.xlsx");
    // Only Multiplexor provided, no Multiplex Value
    make_dbc_workbook(tf.path, {{"256", "Msg", "8", "Sig", "0", "8", "little_endian", "FALSE", "1",
                                 "0", "0", "255", "", "Selector", "", ""}});
    auto result = load_dbc_from_excel(tf.path);
    REQUIRE(!result.has_value());
    CHECK_THAT(std::string(result.error().message()),
               ContainsSubstring("must both be provided or both be empty"));
}

// ===========================================================================
// Template creation
// ===========================================================================

TEST_CASE("excel: create template", "[excel][template]") {
    TempPath tf("excel_template_test.xlsx");
    auto const result = create_excel_template(tf.path);
    REQUIRE(result.has_value());
    CHECK(std::filesystem::exists(tf.path));
}

TEST_CASE("excel: template has 3 sheets", "[excel][template]") {
    TempPath tf("excel_template_sheets.xlsx");
    auto const result = create_excel_template(tf.path);
    REQUIRE(result.has_value());

    OpenXLSX::XLDocument doc;
    doc.open(tf.path.string());
    auto names = doc.workbook().worksheetNames();
    doc.close();

    CHECK(std::ranges::contains(names, "DBC"));
    CHECK(std::ranges::contains(names, "Checks"));
    CHECK(std::ranges::contains(names, "When-Then"));
}

TEST_CASE("excel: template DBC headers correct", "[excel][template]") {
    TempPath tf("excel_template_hdr.xlsx");
    auto const result = create_excel_template(tf.path);
    REQUIRE(result.has_value());

    OpenXLSX::XLDocument doc;
    doc.open(tf.path.string());
    auto const ws = doc.workbook().worksheet("DBC");
    const OpenXLSX::XLCellValue v1 = ws.cell(1, 1).value();
    const OpenXLSX::XLCellValue v3 = ws.cell(1, 3).value();
    const OpenXLSX::XLCellValue v5 = ws.cell(1, 5).value();
    const OpenXLSX::XLCellValue v16 = ws.cell(1, 16).value();
    doc.close();

    CHECK(v1.get<std::string>() == "Message ID");
    CHECK(v3.get<std::string>() == "Extended");
    CHECK(v5.get<std::string>() == "Signal");
    CHECK(v16.get<std::string>() == "Multiplex Value");
}

TEST_CASE("excel: template headers are bold", "[excel][template]") {
    TempPath tf("excel_template_bold.xlsx");
    auto const result = create_excel_template(tf.path);
    REQUIRE(result.has_value());

    // Reopen and verify the header cell's font is bold — round-trips through the
    // save. Python (openpyxl Font(bold=True)) and Go (excelize Font{Bold:true})
    // bold their template headers; this pins C++ parity.
    OpenXLSX::XLDocument doc;
    doc.open(tf.path.string());
    auto const& styles = doc.styles();
    auto const ws = doc.workbook().worksheet("DBC");
    auto const fmt_idx = ws.cell(1, 1).cellFormat();
    auto const font_idx = styles.cellFormats()[fmt_idx].fontIndex();
    const bool is_bold = styles.fonts()[font_idx].bold();
    doc.close();

    CHECK(is_bold);
}

TEST_CASE("excel: template Checks headers correct", "[excel][template]") {
    TempPath tf("excel_template_checks_hdr.xlsx");
    auto const result = create_excel_template(tf.path);
    REQUIRE(result.has_value());

    OpenXLSX::XLDocument doc;
    doc.open(tf.path.string());
    auto const ws = doc.workbook().worksheet("Checks");
    const OpenXLSX::XLCellValue v1 = ws.cell(1, 1).value();
    const OpenXLSX::XLCellValue v3 = ws.cell(1, 3).value();
    const OpenXLSX::XLCellValue v8 = ws.cell(1, 8).value();
    doc.close();

    CHECK(v1.get<std::string>() == "Check Name");
    CHECK(v3.get<std::string>() == "Condition");
    CHECK(v8.get<std::string>() == "Severity");
}

TEST_CASE("excel: template When-Then headers correct", "[excel][template]") {
    TempPath tf("excel_template_wt_hdr.xlsx");
    auto const result = create_excel_template(tf.path);
    REQUIRE(result.has_value());

    OpenXLSX::XLDocument doc;
    doc.open(tf.path.string());
    auto const ws = doc.workbook().worksheet("When-Then");
    const OpenXLSX::XLCellValue v1 = ws.cell(1, 1).value();
    const OpenXLSX::XLCellValue v10 = ws.cell(1, 10).value();
    const OpenXLSX::XLCellValue v11 = ws.cell(1, 11).value();
    doc.close();

    CHECK(v1.get<std::string>() == "Check Name");
    CHECK(v10.get<std::string>() == "Within (ms)");
    CHECK(v11.get<std::string>() == "Severity");
}

TEST_CASE("excel: template no overwrite", "[excel][template]") {
    TempPath tf("excel_template_nooverwrite.xlsx");
    auto const first = create_excel_template(tf.path);
    REQUIRE(first.has_value());
    auto second = create_excel_template(tf.path);
    REQUIRE(!second.has_value());
    CHECK_THAT(std::string(second.error().message()), ContainsSubstring("already exists"));
}

// ===========================================================================
// Error cases
// ===========================================================================

TEST_CASE("excel: file not found", "[excel][error]") {
    auto result = load_checks_from_excel("/nonexistent/path/checks.xlsx");
    REQUIRE(!result.has_value());
    CHECK_THAT(std::string(result.error().message()), ContainsSubstring("not found"));
}

TEST_CASE("excel: no checks or when-then sheet", "[excel][error]") {
    TempPath tf("excel_no_sheets.xlsx");
    OpenXLSX::XLDocument doc;
    doc.create(tf.path.string(), OpenXLSX::XLForceOverwrite);
    // Default sheet is Sheet1, not Checks or When-Then
    doc.save();
    doc.close();
    auto result = load_checks_from_excel(tf.path);
    REQUIRE(!result.has_value());
    CHECK_THAT(std::string(result.error().message()), ContainsSubstring("has no"));
}

TEST_CASE("excel: unknown simple condition", "[excel][error]") {
    TempPath tf("excel_err_cond.xlsx");
    make_checks_workbook(tf.path, {{"", "Speed", "bogus_cond", "100", "", "", "", ""}});
    auto result = load_checks_from_excel(tf.path);
    REQUIRE(!result.has_value());
    CHECK_THAT(std::string(result.error().message()),
               ContainsSubstring("unknown condition 'bogus_cond'"));
}

TEST_CASE("excel: missing min for stays_between", "[excel][error]") {
    TempPath tf("excel_err_min.xlsx");
    make_checks_workbook(tf.path, {{"", "Voltage", "stays_between", "", "", "14.5", "", ""}});
    auto result = load_checks_from_excel(tf.path);
    REQUIRE(!result.has_value());
    CHECK_THAT(std::string(result.error().message()),
               ContainsSubstring("requires 'Min' and 'Max'"));
}

TEST_CASE("excel: missing time for settles_between", "[excel][error]") {
    TempPath tf("excel_err_time.xlsx");
    make_checks_workbook(tf.path, {{"", "Coolant", "settles_between", "", "85", "95", "", ""}});
    auto result = load_checks_from_excel(tf.path);
    REQUIRE(!result.has_value());
    CHECK_THAT(std::string(result.error().message()), ContainsSubstring("requires 'Time (ms)'"));
}

TEST_CASE("excel: unknown when condition", "[excel][error]") {
    TempPath tf("excel_err_when.xlsx");
    make_wt_workbook(
        tf.path, {{"", "Brake", "bogus_when", "50", "Light", "equals", "1", "", "", "100", ""}});
    auto result = load_checks_from_excel(tf.path);
    REQUIRE(!result.has_value());
    CHECK_THAT(std::string(result.error().message()),
               ContainsSubstring("unknown when condition 'bogus_when'"));
}

TEST_CASE("excel: unknown then condition", "[excel][error]") {
    TempPath tf("excel_err_then.xlsx");
    make_wt_workbook(
        tf.path, {{"", "Brake", "exceeds", "50", "Light", "bogus_then", "1", "", "", "100", ""}});
    auto result = load_checks_from_excel(tf.path);
    REQUIRE(!result.has_value());
    CHECK_THAT(std::string(result.error().message()),
               ContainsSubstring("unknown then condition 'bogus_then'"));
}

TEST_CASE("excel: DBC invalid byte order", "[excel][error]") {
    TempPath tf("excel_err_byte_order.xlsx");
    make_dbc_workbook(tf.path, {{"256", "Msg", "8", "Sig", "0", "8", "wrong_order", "FALSE", "1",
                                 "0", "0", "255", "", "", "", ""}});
    auto result = load_dbc_from_excel(tf.path);
    REQUIRE(!result.has_value());
    CHECK_THAT(std::string(result.error().message()),
               ContainsSubstring("'little_endian' or 'big_endian'"));
}

TEST_CASE("excel: DBC invalid message ID", "[excel][error]") {
    TempPath tf("excel_err_msgid.xlsx");
    make_dbc_workbook(tf.path, {{"not_a_number", "Msg", "8", "Sig", "0", "8", "little_endian",
                                 "FALSE", "1", "0", "0", "255", "", "", "", ""}});
    auto result = load_dbc_from_excel(tf.path);
    REQUIRE(!result.has_value());
    CHECK_THAT(std::string(result.error().message()), ContainsSubstring("invalid 'Message ID'"));
}

TEST_CASE("excel: DBC file not found", "[excel][error]") {
    auto result = load_dbc_from_excel("/nonexistent/path/dbc.xlsx");
    REQUIRE(!result.has_value());
    CHECK_THAT(std::string(result.error().message()), ContainsSubstring("not found"));
}

TEST_CASE("excel: DBC no sheet", "[excel][error]") {
    TempPath tf("excel_dbc_no_sheet.xlsx");
    OpenXLSX::XLDocument doc;
    doc.create(tf.path.string(), OpenXLSX::XLForceOverwrite);
    doc.save();
    doc.close();
    auto result = load_dbc_from_excel(tf.path);
    REQUIRE(!result.has_value());
    CHECK_THAT(std::string(result.error().message()), ContainsSubstring("has no"));
}

// ===========================================================================
// Empty row skip
// ===========================================================================

TEST_CASE("excel: empty rows are skipped", "[excel][simple]") {
    TempPath tf("excel_empty_rows.xlsx");
    OpenXLSX::XLDocument doc;
    doc.create(tf.path.string(), OpenXLSX::XLForceOverwrite);
    doc.workbook().worksheet("Sheet1").setName("Checks");
    auto const ws = doc.workbook().worksheet("Checks");
    write_header(ws, checks_hdr);
    // Row 2: data (numeric Value written as TEXT per the all-text contract)
    ws.cell(2, 2).value() = std::string("Speed");
    ws.cell(2, 3).value() = std::string("never_exceeds");
    ws.cell(2, 4).value() = std::string("220");
    // Row 3: empty (no cells set — skipped)
    // Row 4: data
    ws.cell(4, 2).value() = std::string("Voltage");
    ws.cell(4, 3).value() = std::string("never_below");
    ws.cell(4, 4).value() = std::string("11.5");
    doc.save();
    doc.close();

    auto result = load_checks_from_excel(tf.path);
    REQUIRE(result.has_value());
    CHECK(result->size() == 2);
}

// ===========================================================================
// DBC rational factor conversion
// ===========================================================================

TEST_CASE("excel: DBC factor as integer rational", "[excel][dbc]") {
    TempPath tf("excel_dbc_int_factor.xlsx");
    make_dbc_workbook(tf.path, {{"256", "Msg", "8", "Sig", "0", "8", "little_endian", "FALSE", "1",
                                 "0", "0", "255", "", "", "", ""}});
    auto result = load_dbc_from_excel(tf.path);
    REQUIRE(result.has_value());
    auto const& factor = result->messages[0].signals[0].factor.get();
    // Integer 1 should be represented as 1/1
    CHECK(factor.numerator() == 1);
    CHECK(factor.denominator() == 1);
}

TEST_CASE("excel: DBC factor as fractional rational", "[excel][dbc]") {
    TempPath tf("excel_dbc_frac_factor.xlsx");
    make_dbc_workbook(tf.path, {{"256", "Msg", "8", "Sig", "0", "8", "little_endian", "FALSE",
                                 "0.1", "0", "0", "300", "km/h", "", "", ""}});
    auto result = load_dbc_from_excel(tf.path);
    REQUIRE(result.has_value());
    auto const& factor = result->messages[0].signals[0].factor.get();
    // 0.1 should be represented as 1/10 (after GCD simplification)
    CHECK(factor.numerator() == 1);
    CHECK(factor.denominator() == 10);
}

// ===========================================================================
// Extended CAN ID via "Extended" column
// ===========================================================================

TEST_CASE("excel: DBC extended CAN ID via Extended column", "[excel][dbc]") {
    TempPath tf("excel_dbc_extended_id.xlsx");
    // ID 0x10000 (65536) with Extended=TRUE — must produce ExtendedId
    make_dbc_workbook(tf.path, {{"65536", "ExtMsg", "8", "Sig1", "0", "16", "little_endian",
                                 "FALSE", "1", "0", "0", "65535", "", "", "", "TRUE"}});
    auto result = load_dbc_from_excel(tf.path);
    REQUIRE(result.has_value());
    REQUIRE(result->messages.size() == 1);

    auto& msg = result->messages[0];
    CHECK(msg.name.get() == "ExtMsg");
    REQUIRE(std::holds_alternative<ExtendedId>(msg.id));
    CHECK(std::get<ExtendedId>(msg.id).value() == 65536);
}

TEST_CASE("excel: DBC standard ID with Extended=FALSE", "[excel][dbc]") {
    TempPath tf("excel_dbc_std_explicit.xlsx");
    // ID 256 with Extended=FALSE — must produce StandardId
    make_dbc_workbook(tf.path, {{"256", "StdMsg", "8", "Sig1", "0", "8", "little_endian", "FALSE",
                                 "1", "0", "0", "255", "", "", "", "FALSE"}});
    auto result = load_dbc_from_excel(tf.path);
    REQUIRE(result.has_value());
    REQUIRE(result->messages.size() == 1);
    CHECK(std::holds_alternative<StandardId>(result->messages[0].id));
    CHECK(std::get<StandardId>(result->messages[0].id).value() == 256);
}

TEST_CASE("excel: DBC standard ID without Extended column", "[excel][dbc]") {
    TempPath tf("excel_dbc_std_empty.xlsx");
    // Extended column empty — defaults to standard
    make_dbc_workbook(tf.path, {{"256", "StdMsg2", "8", "Sig1", "0", "8", "little_endian", "FALSE",
                                 "1", "0", "0", "255", "", "", "", ""}});
    auto result = load_dbc_from_excel(tf.path);
    REQUIRE(result.has_value());
    REQUIRE(result->messages.size() == 1);
    CHECK(std::holds_alternative<StandardId>(result->messages[0].id));
}

// ===========================================================================
// Template creation roundtrip
// ===========================================================================

TEST_CASE("excel: template roundtrip — load checks from empty template", "[excel][template]") {
    TempPath tf("excel_template_roundtrip.xlsx");
    auto const create_result = create_excel_template(tf.path);
    REQUIRE(create_result.has_value());

    // Load checks from the empty template — should return empty valid result
    auto checks = load_checks_from_excel(tf.path);
    REQUIRE(checks.has_value());
    CHECK(checks->empty());

    // Load DBC from the empty template — should fail (no data rows)
    auto dbc = load_dbc_from_excel(tf.path);
    REQUIRE(!dbc.has_value());
    CHECK_THAT(std::string(dbc.error().message()), ContainsSubstring("no data rows"));
}

// ===========================================================================
// Adversarial-input hardening
// ===========================================================================

TEST_CASE("excel: symlink rejected", "[excel][hardening]") {
    TempPath real("excel_real_target.xlsx");
    make_checks_workbook(real.path, {{"", "Speed", "never_exceeds", "220", "", "", "", ""}});
    TempPath link("excel_symlink.xlsx");
    std::error_code ec;
    std::filesystem::create_symlink(real.path, link.path, ec);
    if (ec) {
        SUCCEED("Skipping symlink test — symlink creation not permitted on this filesystem");
        return;
    }

    auto result = load_checks_from_excel(link.path);
    REQUIRE(!result.has_value());
    CHECK(result.error().kind() == ErrorKind::Validation);
    CHECK_THAT(std::string(result.error().message()), ContainsSubstring("symbolic link"));
}

TEST_CASE("excel: file size cap rejected", "[excel][hardening]") {
    // Build a non-archive plain file > 64 MiB.  load_checks_from_excel
    // rejects it on size BEFORE attempting OpenXLSX open.
    TempPath tf("excel_oversize.xlsx");
    {
        std::ofstream ofs(tf.path, std::ios::binary);
        std::vector<char> chunk(std::size_t{1024} * 1024, '\xAA');
        // 65 MiB, one mebibyte at a time: the count is the point, not a position.
        for ([[maybe_unused]] auto const mebibyte : std::views::repeat(0, 65))
            ofs.write(chunk.data(), static_cast<std::streamsize>(chunk.size()));
    }
    auto result = load_checks_from_excel(tf.path);
    REQUIRE(!result.has_value());
    CHECK(result.error().kind() == ErrorKind::InputBoundExceeded);
    REQUIRE(result.error().bound_info().has_value());
    CHECK(result.error().bound_info()->bound_kind == "input_length_bytes");
    CHECK(result.error().bound_info()->limit == 64ULL * 1024 * 1024);
}

TEST_CASE("excel: ZIP central-directory bomb rejected", "[excel][hardening]") {
    // Forge a tiny "ZIP" with a single CD entry whose uncompressed_size
    // claims to be 1 GiB.  The walker should reject without unpacking.
    TempPath tf("excel_zip_bomb.xlsx");
    {
        std::ofstream ofs(tf.path, std::ios::binary);
        // -- One CD entry header, signature 0x02014b50, uncompressed_size = 1 GiB --
        std::array<unsigned char, 46> cd{
            0x50, 0x4b, 0x01, 0x02, // signature
            0x00, 0x00,             // version made by
            0x00, 0x00,             // version needed
            0x00, 0x00,             // flags
            0x00, 0x00,             // method (stored)
            0x00, 0x00, 0x00, 0x00, // mod time / date
            0x00, 0x00, 0x00, 0x00, // CRC-32
            0x00, 0x00, 0x00, 0x00, // compressed size
            0x00, 0x00, 0x00, 0x40, // uncompressed size = 0x40000000 = 1 GiB
            0x00, 0x00,             // file name length
            0x00, 0x00,             // extra field length
            0x00, 0x00,             // file comment length
            0x00, 0x00,             // disk number start
            0x00, 0x00,             // internal attrs
            0x00, 0x00, 0x00, 0x00, // external attrs
            0x00, 0x00, 0x00, 0x00, // relative offset
        };
        write_bytes(ofs, cd);
        // -- EOCD record at file tail --
        std::array<unsigned char, 22> eocd{
            0x50, 0x4b, 0x05, 0x06, // signature
            0x00, 0x00, 0x00, 0x00, // disk numbers
            0x01, 0x00, 0x01, 0x00, // entries
            0x2e, 0x00, 0x00, 0x00, // CD size = 46
            0x00, 0x00, 0x00, 0x00, // CD offset = 0
            0x00, 0x00,             // comment length
        };
        write_bytes(ofs, eocd);
    }
    auto result = load_checks_from_excel(tf.path);
    REQUIRE(!result.has_value());
    CHECK(result.error().kind() == ErrorKind::InputBoundExceeded);
    REQUIRE(result.error().bound_info().has_value());
    CHECK(result.error().bound_info()->bound_kind == "input_length_bytes");
    CHECK(result.error().bound_info()->observed == 0x40000000ULL);
    CHECK_THAT(std::string(result.error().message()), ContainsSubstring("ZIP-bomb defence"));
}

TEST_CASE("excel: create_template parent dir missing rejected", "[excel][hardening]") {
    auto const bad =
        std::filesystem::temp_directory_path() / "aletheia_does_not_exist_12345" / "template.xlsx";
    auto result = create_excel_template(bad);
    REQUIRE(!result.has_value());
    CHECK(result.error().kind() == ErrorKind::Validation);
    CHECK_THAT(std::string(result.error().message()),
               ContainsSubstring("Parent directory does not exist"));
}

TEST_CASE("excel: create_template stat failure is distinguished from a missing parent",
          "[excel][hardening]") {
    // A parent whose component is longer than a name may be makes the stat
    // itself fail with ENAMETOOLONG, which is not the directory being absent.
    // Reporting it as absent sends a reader to create a directory that may
    // well be there, and hides a machine out of descriptors under load. The
    // input path is held to the same distinction by the yaml suite's "stat
    // failure is distinguished from a missing file", and Go's
    // TestCreateTemplate_StatFailureNotMislabeled holds this one.
    // ENAMETOOLONG is deterministic and needs no permissions.
    auto const bad =
        std::filesystem::temp_directory_path() / std::string(5000, 'a') / "template.xlsx";
    auto result = create_excel_template(bad);
    REQUIRE(!result.has_value());
    CHECK(result.error().kind() == ErrorKind::Validation);
    CHECK_THAT(std::string(result.error().message()), ContainsSubstring("Could not stat"));
    CHECK_THAT(std::string(result.error().message()),
               !ContainsSubstring("Parent directory does not exist"));
}

// ===========================================================================
// Strict coercion and cross-binding portability locks
// ===========================================================================

// The float principle INVERTS the coercion contract: a numeric field stored as a
// native NUMBER cell must be rejected (a float64 has already lost the authored
// precision), so numbers must be text-formatted and parsed exactly by the kernel
// SSOT. The demo workbook can't exercise this (it stores numbers as text). The
// Value cell is written directly as a native int to force a number cell,
// bypassing the all-text write_row helper.
TEST_CASE("excel: strict rejects a Value stored as a native number", "[excel][strict]") {
    TempPath tf("excel_strict_number_value.xlsx");
    OpenXLSX::XLDocument doc;
    doc.create(tf.path.string(), OpenXLSX::XLForceOverwrite);
    doc.workbook().worksheet("Sheet1").setName("Checks");
    auto const ws = doc.workbook().worksheet("Checks");
    write_header(ws, checks_hdr);
    ws.cell(2, 2).value() = std::string("Speed");
    ws.cell(2, 3).value() = std::string("never_exceeds");
    ws.cell(2, 4).value() = std::int64_t{220}; // Value as a native NUMBER cell
    doc.save();
    doc.close();

    auto result = load_checks_from_excel(tf.path);
    REQUIRE_FALSE(result.has_value());
    CHECK_THAT(std::string(result.error().message()), ContainsSubstring("format it as TEXT"));
}

TEST_CASE("excel: DBC strict rejects a Factor stored as a native number", "[excel][strict][dbc]") {
    TempPath tf("excel_strict_number_factor.xlsx");
    OpenXLSX::XLDocument doc;
    doc.create(tf.path.string(), OpenXLSX::XLForceOverwrite);
    doc.workbook().worksheet("Sheet1").setName("DBC");
    auto const ws = doc.workbook().worksheet("DBC");
    write_header(ws, dbc_hdr);
    // dbc_hdr: ID, Name, DLC, Signal, Start Bit, Length, Byte Order, Signed,
    //          Factor(9), Offset(10), Min(11), Max(12), ...
    // Every numeric field is text (the all-text contract) EXCEPT Factor, which is
    // a native number cell — so the loader reaches the Factor parse and rejects
    // it (DLC / Start Bit / Length are read before Factor and would otherwise
    // trip "format it as TEXT" on the wrong field).
    ws.cell(2, 1).value() = std::string("256");
    ws.cell(2, 2).value() = std::string("Msg");
    ws.cell(2, 3).value() = std::string("8");
    ws.cell(2, 4).value() = std::string("Sig");
    ws.cell(2, 5).value() = std::string("0");
    ws.cell(2, 6).value() = std::string("8");
    ws.cell(2, 7).value() = std::string("little_endian");
    ws.cell(2, 8).value() = false;
    ws.cell(2, 9).value() = 0.25; // Factor as a native NUMBER cell
    ws.cell(2, 10).value() = std::string("0");
    ws.cell(2, 11).value() = std::string("0");
    ws.cell(2, 12).value() = std::string("1");
    doc.save();
    doc.close();

    auto result = load_dbc_from_excel(tf.path);
    REQUIRE_FALSE(result.has_value());
    CHECK_THAT(std::string(result.error().message()), ContainsSubstring("format it as TEXT"));
    // The echo must be the shortest round-trip rendering of the stored double —
    // a fixed-six-decimal rendering ("0.250000") would misstate the cell.
    CHECK_THAT(std::string(result.error().message()), ContainsSubstring("(got 0.25)"));
}

// ===========================================================================
// Raw-stored-value discipline (native number cells)
// ===========================================================================

// OpenXLSX classifies a number cell (no `t` attribute) whose stored text has
// no '.' and no negative exponent as Integer, and the underlying XML read
// prefix-parses that text — so a stored "1e16" would silently load as Message
// ID 1 and an empty <v/> as ID 0. The loader must trust the integer read only
// after verifying the raw stored text is a digit run with an optional minus, and
// refuse truthfully otherwise.

TEST_CASE("excel: DBC Message ID storing dot-free scientific notation is refused",
          "[excel][dbc][strict]") {
    TempPath tf("excel_dbc_msgid_sci.xlsx");
    make_dbc_workbook_with_raw_id(tf.path, 31337421, "1e16");
    auto result = load_dbc_from_excel(tf.path);
    REQUIRE_FALSE(result.has_value()); // a prefix-parse would load Message ID 1
    CHECK_THAT(std::string(result.error().message()), ContainsSubstring("1e16"));
    CHECK_THAT(std::string(result.error().message()), ContainsSubstring("Message ID"));
}

TEST_CASE("excel: DBC Message ID with an empty stored <v/> is refused", "[excel][dbc][strict]") {
    TempPath tf("excel_dbc_msgid_empty_v.xlsx");
    make_dbc_workbook_with_raw_id(tf.path, 31337421, "");
    auto result = load_dbc_from_excel(tf.path);
    REQUIRE_FALSE(result.has_value()); // a prefix-parse would load Message ID 0
    CHECK_THAT(std::string(result.error().message()), ContainsSubstring("Message ID"));
}

// Positive lock guarding the raw check from over-rejecting: a native number
// cell whose stored text is a plain digit run is a legitimate Message ID.
TEST_CASE("excel: DBC Message ID as a native integer cell loads", "[excel][dbc]") {
    TempPath tf("excel_dbc_msgid_native.xlsx");
    make_dbc_workbook_with_raw_id(tf.path, 256, nullptr);
    auto result = load_dbc_from_excel(tf.path);
    REQUIRE(result.has_value());
    REQUIRE(result->messages.size() == 1);
    CHECK(std::holds_alternative<StandardId>(result->messages[0].id));
}

// A kernel decimal refusal surfaced through get_decimal/get_int must carry the
// loader's own "Row N: invalid 'Field'" prefix — the kernel knows the literal,
// not the workbook position.
TEST_CASE("excel: kernel decimal refusal carries row and field context", "[excel][dbc]") {
    TempPath tf("excel_decimal_ctx.xlsx");
    make_dbc_workbook(tf.path, {{"256", "Msg", "8", "Sig", "0", "8", "little_endian", "FALSE",
                                 "abc", "0", "0", "255", "", "", "", ""}});
    auto result = load_dbc_from_excel(tf.path);
    REQUIRE_FALSE(result.has_value());
    CHECK_THAT(std::string(result.error().message()), ContainsSubstring("Row 2: invalid 'Factor'"));
}

// Cross-binding portability lock: the shared demo workbook's DBC sheet omits the
// Extended column, so every binding must load it as standard 11-bit messages
// (matching Python / Go / Rust).
TEST_CASE("excel: demo workbook DBC loads as standard messages", "[excel][dbc][portability]") {
    auto const path = repo_root() / "examples" / "demo" / "demo_workbook.xlsx";
    auto result = load_dbc_from_excel(path);
    REQUIRE(result.has_value());
    CHECK(result->messages.size() == 2);
    for (auto const& msg : result->messages)
        CHECK(std::holds_alternative<StandardId>(msg.id));
}

TEST_CASE("temp path: every shape is removed when its scope ends", "[excel][temp]") {
    // The three suites that share this type rely on the removal, and nothing
    // else asserts it: a destructor that stopped removing would leave scratch
    // files behind for every run without failing a single case.
    std::filesystem::path reserved;
    std::filesystem::path written;
    std::filesystem::path made;
    {
        const TempPath bare{"aletheia_temp_path_bare.bin"};
        reserved = bare.path;
        std::ofstream{bare.path} << "x";
        REQUIRE(std::filesystem::exists(reserved));

        const TempPath with_content{"aletheia_temp_path_content.txt", "hello"};
        written = with_content.path;
        REQUIRE(std::filesystem::exists(written));
        std::ifstream in{written};
        std::string body;
        in >> body;
        CHECK(body == "hello");

        const TempPath dir{scratch_dir() / "aletheia_temp_path_dir", AsDirectory{}};
        made = dir.path;
        std::ofstream{made / "inside.txt"} << "y";
        REQUIRE(std::filesystem::is_directory(made));
    }
    CHECK_FALSE(std::filesystem::exists(reserved));
    CHECK_FALSE(std::filesystem::exists(written));
    CHECK_FALSE(std::filesystem::exists(made));
}

// ===========================================================================
// Edges of the sheet readers
// ===========================================================================

TEST_CASE("excel: a native integer Message ID carrying a nine and a minus is read exactly",
          "[excel][dbc][strict]") {
    // The digit run check admits every digit and a leading minus; the minus
    // then fails as a CAN ID, by the ID's own wording and not the strict one.
    SECTION("nineteen loads as 19") {
        TempPath tf("excel_dbc_msgid_19.xlsx");
        make_dbc_workbook_with_raw_id(tf.path, 19, nullptr);
        auto result = load_dbc_from_excel(tf.path);
        REQUIRE(result.has_value());
        REQUIRE(result->messages.size() == 1);
        CHECK(std::get<StandardId>(result->messages[0].id).value() == 19);
    }
    SECTION("minus nine is refused as an ID, not as a stored shape") {
        TempPath tf("excel_dbc_msgid_minus.xlsx");
        make_dbc_workbook_with_raw_id(tf.path, 31337421, "-9");
        auto result = load_dbc_from_excel(tf.path);
        REQUIRE_FALSE(result.has_value());
        CHECK_THAT(std::string(result.error().message()),
                   ContainsSubstring("invalid 'Message ID'"));
        CHECK_THAT(std::string(result.error().message()),
                   !ContainsSubstring("not a plain integer"));
    }
}

TEST_CASE("excel: a missing required cell is refused by its field's name", "[excel][error]") {
    SECTION("a text field") {
        TempPath tf("excel_missing_signal.xlsx");
        make_checks_workbook(tf.path, {{"", "", "never_exceeds", "220", "", "", "", ""}});
        auto result = load_checks_from_excel(tf.path);
        REQUIRE_FALSE(result.has_value());
        CHECK_THAT(std::string(result.error().message()),
                   ContainsSubstring("missing or invalid 'Signal' (expected string)"));
    }
    SECTION("a number field") {
        TempPath tf("excel_missing_value.xlsx");
        make_checks_workbook(tf.path, {{"", "Speed", "never_exceeds", "", "", "", "", ""}});
        auto result = load_checks_from_excel(tf.path);
        REQUIRE_FALSE(result.has_value());
        CHECK_THAT(std::string(result.error().message()),
                   ContainsSubstring("missing or invalid 'Value' (expected number)"));
    }
    SECTION("the message id") {
        TempPath tf("excel_missing_id.xlsx");
        make_dbc_workbook(tf.path, {{"", "Msg", "8", "Sig", "0", "8", "little_endian", "FALSE", "1",
                                     "0", "0", "255", "", "", "", ""}});
        auto result = load_dbc_from_excel(tf.path);
        REQUIRE_FALSE(result.has_value());
        CHECK_THAT(std::string(result.error().message()),
                   ContainsSubstring("missing or invalid 'Message ID'"));
    }
    SECTION("a boolean field") {
        TempPath tf("excel_missing_signed.xlsx");
        make_dbc_workbook(tf.path, {{"256", "Msg", "8", "Sig", "0", "8", "little_endian", "", "1",
                                     "0", "0", "255", "", "", "", ""}});
        auto result = load_dbc_from_excel(tf.path);
        REQUIRE_FALSE(result.has_value());
        CHECK_THAT(std::string(result.error().message()),
                   ContainsSubstring("missing or invalid 'Signed' (expected TRUE/FALSE)"));
    }
}

TEST_CASE("excel: DBC DLC is accepted at both ends of its range and refused past them",
          "[excel][dbc]") {
    auto const row = [](const char* dlc) -> std::vector<std::string> {
        return {"256", "Msg", dlc, "Sig", "0", "8", "little_endian", "FALSE", "1", "0",
                "0",   "255", "",  "",    "",  ""};
    };
    SECTION("0 and 15 load") {
        auto const dlc = GENERATE(0, 15);
        TempPath tf("excel_dbc_dlc_edge.xlsx");
        make_dbc_workbook(tf.path, {row(std::to_string(dlc).c_str())});
        auto result = load_dbc_from_excel(tf.path);
        REQUIRE(result.has_value());
        REQUIRE(result->messages.size() == 1);
        CHECK(result->messages[0].dlc.value() == static_cast<std::uint8_t>(dlc));
    }
    SECTION("16 and -1 are refused") {
        auto const dlc = GENERATE(16, -1);
        TempPath tf("excel_dbc_dlc_past.xlsx");
        make_dbc_workbook(tf.path, {row(std::to_string(dlc).c_str())});
        auto result = load_dbc_from_excel(tf.path);
        REQUIRE_FALSE(result.has_value());
        CHECK_THAT(std::string(result.error().message()), ContainsSubstring("DLC out of range"));
    }
}

TEST_CASE("excel: every data row of a long sheet is loaded", "[excel][simple]") {
    TempPath tf("excel_fifty_rows.xlsx");
    std::vector<std::vector<std::string>> rows;
    rows.reserve(50);
    for (auto const i : std::views::iota(0, 50))
        rows.push_back({"", "Sig" + std::to_string(i), "never_exceeds", "1", "", "", "", ""});
    make_checks_workbook(tf.path, rows);
    auto result = load_checks_from_excel(tf.path);
    REQUIRE(result.has_value());
    CHECK(result->size() == 50);
}

TEST_CASE("excel: a header far to the right of the others is still read", "[excel][metadata]") {
    // The header row is read to the sheet's own column count, wherever the
    // last named column sits.
    TempPath tf("excel_wide_header.xlsx");
    {
        OpenXLSX::XLDocument doc;
        doc.create(tf.path.string(), OpenXLSX::XLForceOverwrite);
        doc.workbook().worksheet("Sheet1").setName("Checks");
        auto const ws = doc.workbook().worksheet("Checks");
        write_header(ws, std::span{checks_hdr}.first(7));
        ws.cell(1, 50).value() = std::string{"Severity"};
        write_row(ws, 2, {"", "Speed", "never_exceeds", "220"});
        ws.cell(2, 50).value() = std::string{"critical"};
        doc.save();
        doc.close();
    }
    auto result = load_checks_from_excel(tf.path);
    REQUIRE(result.has_value());
    REQUIRE(result->size() == 1);
    CHECK((*result)[0].check_severity() == "critical");
}

TEST_CASE("excel: DBC multiplex value zero is a value, not an absence", "[excel][mux]") {
    TempPath tf("excel_dbc_mux_zero.xlsx");
    make_dbc_workbook(tf.path, {{"256", "Msg", "8", "MuxSig", "0", "8", "little_endian", "FALSE",
                                 "1", "0", "0", "255", "", "Selector", "0", ""}});
    auto result = load_dbc_from_excel(tf.path);
    REQUIRE(result.has_value());
    REQUIRE(result->messages.size() == 1);
    auto const& sig = result->messages[0].signals[0];
    auto const* mux = std::get_if<Multiplexed>(&sig.presence);
    REQUIRE(mux != nullptr);
    REQUIRE(mux->multiplex_values.size() == 1);
    CHECK(mux->multiplex_values[0] == MultiplexValue{0});
}

// ===========================================================================
// The paths the library throws on
// ===========================================================================

TEST_CASE("excel: a ZIP archive that is not a workbook is refused by the library's own word",
          "[excel][hardening]") {
    // The archive walker admits any well-formed ZIP, so a ZIP with no workbook
    // inside reaches the library's open, which throws; the loader answers with
    // the library's message and leaves nothing of the attempt behind.
    TempPath tf("excel_not_a_workbook.xlsx");
    make_checks_workbook(tf.path, {});
    {
        OpenXLSX::XLZipArchive zip;
        zip.open(tf.path.string());
        zip.deleteEntry("xl/workbook.xml");
        zip.save();
        zip.close();
    }
    auto const checks = load_checks_from_excel(tf.path);
    REQUIRE_FALSE(checks.has_value());
    CHECK(checks.error().kind() == ErrorKind::Validation);
    auto const dbc = load_dbc_from_excel(tf.path);
    REQUIRE_FALSE(dbc.has_value());
    CHECK(dbc.error().kind() == ErrorKind::Validation);
}

TEST_CASE("excel: a template into a directory that cannot be written is refused with the reason",
          "[excel][hardening]") {
    if (::geteuid() == 0)
        SKIP("root writes anywhere");
    const TempPath dir("excel_unwritable_dir");
    std::filesystem::create_directories(dir.path);
    std::filesystem::permissions(dir.path, std::filesystem::perms::owner_read |
                                               std::filesystem::perms::owner_exec);
    auto const result = create_excel_template(dir.path / "template.xlsx");
    std::filesystem::permissions(dir.path, std::filesystem::perms::owner_all);
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::Validation);
}

#ifdef ALETHEIA_ALLOC_FAULT
// Each loader fills its result one row at a time, with a parsed row in hand
// while the container grows; a growth that throws destroys that row on the
// way out, and a cleanup that dropped it would leave its blocks behind.
TEST_CASE("excel: the loaders release their temporaries when an allocation fails",
          "[excel][alloc_fault]") {
    using aletheia::test::alloc_fault::expect_balanced;
    // The harness spares the library's own allocations by the names of the
    // frames on the stack, and the library hides its symbols in the shipped
    // build; a build that cannot name them would end the program on the first
    // failed allocation inside the library.
    if (dlsym(RTLD_DEFAULT, "_ZN8OpenXLSX10XLDocument4openERKNSt7__cxx1112basic_stringIcSt11char_"
                            "traitsIcESaIcEEE") == nullptr)
        SKIP("the spreadsheet library's frames cannot be named in this build");
    SECTION("the checks loader, over a checks sheet") {
        TempPath tf("excel_alloc_checks.xlsx");
        make_checks_workbook(
            tf.path,
            {{"the engine speed stays under its redline", "EngineSpeedInRevolutionsPerMinute",
              "never_exceeds", "6000", "", "", "", ""},
             {"the coolant settles into its band", "CoolantTemperatureInDegreesCelsius",
              "settles_between", "", "80", "95", "30000", ""}});
        REQUIRE(load_checks_from_excel(tf.path).has_value());
        expect_balanced([&] { return load_checks_from_excel(tf.path); });
    }
    SECTION("the checks loader, over a when-then sheet") {
        TempPath tf("excel_alloc_when_then.xlsx");
        make_wt_workbook(tf.path,
                         {{"braking dims the lamp", "BrakePedalPositionAsAPercentage", "exceeds",
                           "50", "BrakeLampIlluminationState", "equals", "1", "", "", "100", ""}});
        REQUIRE(load_checks_from_excel(tf.path).has_value());
        expect_balanced([&] { return load_checks_from_excel(tf.path); });
    }
    SECTION("the DBC loader") {
        TempPath tf("excel_alloc_dbc.xlsx");
        make_dbc_workbook(tf.path, {{"256", "VehicleSpeedInKilometresPerHour", "8",
                                     "VehicleSpeedSignalName", "0", "16", "little_endian", "FALSE",
                                     "0.1", "0", "0", "300", "kilometres per hour", "", "", ""},
                                    {"256", "VehicleSpeedInKilometresPerHour", "8",
                                     "EngineSpeedSignalName", "16", "16", "little_endian", "FALSE",
                                     "1", "0", "0", "8000", "revolutions per minute", "", "", ""}});
        REQUIRE(load_dbc_from_excel(tf.path).has_value());
        expect_balanced([&] { return load_dbc_from_excel(tf.path); });
    }
    SECTION("the template writer") {
        TempPath tf("excel_alloc_template.xlsx");
        expect_balanced([&] {
            std::filesystem::remove(tf.path);
            return create_excel_template(tf.path);
        });
    }
}
#endif
