// Excel loader tests.
// Tests Excel check and DBC parsing with programmatically-created workbooks.
#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>

#include <aletheia/excel.hpp>

#include <OpenXLSX.hpp>

#include <cstdint>
#include <filesystem>
#include <string>
#include <variant>
#include <vector>

using namespace aletheia;
using Catch::Matchers::ContainsSubstring;

// ===========================================================================
// Test helpers
// ===========================================================================

namespace {

/// RAII temp file that removes on destruction.
struct TempFile {
    std::filesystem::path path;

    explicit TempFile(const std::string& name)
        : path(std::filesystem::temp_directory_path() / name) {
        if (std::filesystem::exists(path))
            std::filesystem::remove(path);
    }
    ~TempFile() {
        if (std::filesystem::exists(path))
            std::filesystem::remove(path);
    }
    TempFile(const TempFile&) = delete;
    auto operator=(const TempFile&) -> TempFile& = delete;
    TempFile(TempFile&&) = delete;
    auto operator=(TempFile&&) -> TempFile& = delete;
};

// Header constants
const std::vector<std::string> checks_hdr = {"Check Name", "Signal", "Condition", "Value",
                                             "Min",        "Max",    "Time (ms)", "Severity"};

const std::vector<std::string> wt_hdr = {
    "Check Name", "When Signal", "When Condition", "When Value",  "Then Signal", "Then Condition",
    "Then Value", "Then Min",    "Then Max",       "Within (ms)", "Severity"};

const std::vector<std::string> dbc_hdr = {
    "Message ID",      "Message Name", "DLC",    "Signal", "Start Bit", "Length", "Byte Order",
    "Signed",          "Factor",       "Offset", "Min",    "Max",       "Unit",   "Multiplexor",
    "Multiplex Value", "Extended",
};

void write_header(OpenXLSX::XLWorksheet& ws, const std::vector<std::string>& headers) {
    for (std::size_t i = 0; i < headers.size(); ++i)
        ws.cell(1, static_cast<std::uint16_t>(i + 1)).value() = headers[i];
}

/// Write a data row (2-indexed) to a worksheet from string values.
/// Empty strings are skipped (leave cell empty).
void write_row(OpenXLSX::XLWorksheet& ws, int row, const std::vector<std::string>& values) {
    for (std::size_t i = 0; i < values.size(); ++i)
        if (!values[i].empty())
            ws.cell(row, static_cast<std::uint16_t>(i + 1)).value() = values[i];
}

/// Create a workbook with a Checks sheet containing header + data rows.
void make_checks_workbook(const std::filesystem::path& path,
                          const std::vector<std::vector<std::string>>& rows) {
    OpenXLSX::XLDocument doc;
    doc.create(path.string(), OpenXLSX::XLForceOverwrite);
    doc.workbook().worksheet("Sheet1").setName("Checks");
    auto ws = doc.workbook().worksheet("Checks");
    write_header(ws, checks_hdr);
    for (std::size_t r = 0; r < rows.size(); ++r)
        write_row(ws, static_cast<int>(r + 2), rows[r]);
    doc.save();
    doc.close();
}

/// Create a workbook with a When-Then sheet.
void make_wt_workbook(const std::filesystem::path& path,
                      const std::vector<std::vector<std::string>>& rows) {
    OpenXLSX::XLDocument doc;
    doc.create(path.string(), OpenXLSX::XLForceOverwrite);
    doc.workbook().worksheet("Sheet1").setName("When-Then");
    auto ws = doc.workbook().worksheet("When-Then");
    write_header(ws, wt_hdr);
    for (std::size_t r = 0; r < rows.size(); ++r)
        write_row(ws, static_cast<int>(r + 2), rows[r]);
    doc.save();
    doc.close();
}

/// Create a workbook with a DBC sheet.
void make_dbc_workbook(const std::filesystem::path& path,
                       const std::vector<std::vector<std::string>>& rows) {
    OpenXLSX::XLDocument doc;
    doc.create(path.string(), OpenXLSX::XLForceOverwrite);
    doc.workbook().worksheet("Sheet1").setName("DBC");
    auto ws = doc.workbook().worksheet("DBC");
    write_header(ws, dbc_hdr);
    for (std::size_t r = 0; r < rows.size(); ++r)
        write_row(ws, static_cast<int>(r + 2), rows[r]);
    doc.save();
    doc.close();
}

} // namespace

// ===========================================================================
// Simple check conditions
// ===========================================================================

TEST_CASE("excel: never_exceeds", "[excel][simple]") {
    TempFile tf("excel_never_exceeds.xlsx");
    // Check Name, Signal, Condition, Value, Min, Max, Time (ms), Severity
    make_checks_workbook(tf.path, {{"", "Speed", "never_exceeds", "220", "", "", "", ""}});
    auto result = load_checks_from_excel(tf.path);
    REQUIRE(result.has_value());
    REQUIRE(result->size() == 1);
    auto formula = (*result)[0].to_formula();
    REQUIRE(formula.has_value());
}

TEST_CASE("excel: never_below", "[excel][simple]") {
    TempFile tf("excel_never_below.xlsx");
    make_checks_workbook(tf.path, {{"", "Voltage", "never_below", "11.5", "", "", "", ""}});
    auto result = load_checks_from_excel(tf.path);
    REQUIRE(result.has_value());
    REQUIRE(result->size() == 1);
}

TEST_CASE("excel: stays_between", "[excel][simple]") {
    TempFile tf("excel_stays_between.xlsx");
    make_checks_workbook(tf.path, {{"", "Voltage", "stays_between", "", "11.5", "14.5", "", ""}});
    auto result = load_checks_from_excel(tf.path);
    REQUIRE(result.has_value());
    REQUIRE(result->size() == 1);
}

TEST_CASE("excel: never_equals", "[excel][simple]") {
    TempFile tf("excel_never_equals.xlsx");
    make_checks_workbook(tf.path, {{"", "ErrorCode", "never_equals", "99", "", "", "", ""}});
    auto result = load_checks_from_excel(tf.path);
    REQUIRE(result.has_value());
    REQUIRE(result->size() == 1);
}

TEST_CASE("excel: equals always", "[excel][simple]") {
    TempFile tf("excel_equals.xlsx");
    make_checks_workbook(tf.path, {{"", "ParkingBrake", "equals", "0", "", "", "", ""}});
    auto result = load_checks_from_excel(tf.path);
    REQUIRE(result.has_value());
    REQUIRE(result->size() == 1);
}

TEST_CASE("excel: settles_between", "[excel][simple]") {
    TempFile tf("excel_settles.xlsx");
    make_checks_workbook(tf.path, {{"", "Coolant", "settles_between", "", "85", "95", "5000", ""}});
    auto result = load_checks_from_excel(tf.path);
    REQUIRE(result.has_value());
    REQUIRE(result->size() == 1);
}

// ===========================================================================
// When/Then conditions
// ===========================================================================

TEST_CASE("excel: when exceeds then equals", "[excel][when-then]") {
    TempFile tf("excel_wt_exc_eq.xlsx");
    // Check Name, When Signal, When Condition, When Value,
    // Then Signal, Then Condition, Then Value, Then Min, Then Max,
    // Within (ms), Severity
    make_wt_workbook(tf.path, {{"", "BrakePedal", "exceeds", "50", "BrakeLight", "equals", "1", "",
                                "", "100", ""}});
    auto result = load_checks_from_excel(tf.path);
    REQUIRE(result.has_value());
    REQUIRE(result->size() == 1);
}

TEST_CASE("excel: when equals then exceeds", "[excel][when-then]") {
    TempFile tf("excel_wt_eq_exc.xlsx");
    make_wt_workbook(
        tf.path, {{"", "Gear", "equals", "1", "ReverseLight", "exceeds", "0", "", "", "200", ""}});
    auto result = load_checks_from_excel(tf.path);
    REQUIRE(result.has_value());
    REQUIRE(result->size() == 1);
}

TEST_CASE("excel: when drops_below then stays_between", "[excel][when-then]") {
    TempFile tf("excel_wt_drop_sb.xlsx");
    make_wt_workbook(tf.path, {{"", "FuelLevel", "drops_below", "10", "FuelWarning",
                                "stays_between", "", "1", "1", "500", ""}});
    auto result = load_checks_from_excel(tf.path);
    REQUIRE(result.has_value());
    REQUIRE(result->size() == 1);
}

// ===========================================================================
// Metadata
// ===========================================================================

TEST_CASE("excel: check name applied", "[excel][metadata]") {
    TempFile tf("excel_meta_name.xlsx");
    make_checks_workbook(tf.path,
                         {{"Speed limit", "Speed", "never_exceeds", "220", "", "", "", ""}});
    auto result = load_checks_from_excel(tf.path);
    REQUIRE(result.has_value());
    CHECK((*result)[0].name() == "Speed limit");
}

TEST_CASE("excel: severity applied", "[excel][metadata]") {
    TempFile tf("excel_meta_sev.xlsx");
    make_checks_workbook(tf.path, {{"", "Speed", "never_exceeds", "220", "", "", "", "critical"}});
    auto result = load_checks_from_excel(tf.path);
    REQUIRE(result.has_value());
    CHECK((*result)[0].check_severity() == "critical");
}

TEST_CASE("excel: name and severity together", "[excel][metadata]") {
    TempFile tf("excel_meta_both.xlsx");
    make_checks_workbook(
        tf.path, {{"Speed limit", "Speed", "never_exceeds", "220", "", "", "", "critical"}});
    auto result = load_checks_from_excel(tf.path);
    REQUIRE(result.has_value());
    CHECK((*result)[0].name() == "Speed limit");
    CHECK((*result)[0].check_severity() == "critical");
}

TEST_CASE("excel: defaults when no name or severity", "[excel][metadata]") {
    TempFile tf("excel_meta_defaults.xlsx");
    make_checks_workbook(tf.path, {{"", "Speed", "never_exceeds", "200", "", "", "", ""}});
    auto result = load_checks_from_excel(tf.path);
    REQUIRE(result.has_value());
    CHECK((*result)[0].name().empty());
    CHECK((*result)[0].check_severity().empty());
}

TEST_CASE("excel: when-then with metadata", "[excel][metadata]") {
    TempFile tf("excel_meta_wt.xlsx");
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
    TempFile tf("excel_dbc_single.xlsx");
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

    auto& sig = msg.signals[0];
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
    TempFile tf("excel_dbc_group.xlsx");
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
    TempFile tf("excel_dbc_hex.xlsx");
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
    TempFile tf("excel_dbc_signed.xlsx");
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
    TempFile tf("excel_dbc_no_unit.xlsx");
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
    TempFile tf("excel_mux_always.xlsx");
    make_dbc_workbook(tf.path, {{"256", "Msg", "8", "Sig", "0", "8", "little_endian", "FALSE", "1",
                                 "0", "0", "255", "", "", "", ""}});
    auto result = load_dbc_from_excel(tf.path);
    REQUIRE(result.has_value());
    CHECK(std::holds_alternative<AlwaysPresent>(result->messages[0].signals[0].presence));
}

TEST_CASE("excel: DBC multiplexed signal", "[excel][mux]") {
    TempFile tf("excel_mux_muxed.xlsx");
    make_dbc_workbook(tf.path, {{"256", "Msg", "8", "MuxSig", "0", "8", "little_endian", "FALSE",
                                 "1", "0", "0", "255", "", "Selector", "3", ""}});
    auto result = load_dbc_from_excel(tf.path);
    REQUIRE(result.has_value());
    auto& pres = result->messages[0].signals[0].presence;
    REQUIRE(std::holds_alternative<Multiplexed>(pres));
    auto& mux = std::get<Multiplexed>(pres);
    CHECK(mux.multiplexor.get() == "Selector");
    REQUIRE(mux.mux_values.size() == 1);
    CHECK(mux.mux_values[0].get() == 3);
}

TEST_CASE("excel: DBC mixed always and mux", "[excel][mux]") {
    TempFile tf("excel_mux_mixed.xlsx");
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
    TempFile tf("excel_mux_partial.xlsx");
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
    TempFile tf("excel_template_test.xlsx");
    auto result = create_excel_template(tf.path);
    REQUIRE(result.has_value());
    CHECK(std::filesystem::exists(tf.path));
}

TEST_CASE("excel: template has 3 sheets", "[excel][template]") {
    TempFile tf("excel_template_sheets.xlsx");
    auto result = create_excel_template(tf.path);
    REQUIRE(result.has_value());

    OpenXLSX::XLDocument doc;
    doc.open(tf.path.string());
    auto names = doc.workbook().worksheetNames();
    doc.close();

    CHECK(std::find(names.begin(), names.end(), "DBC") != names.end());
    CHECK(std::find(names.begin(), names.end(), "Checks") != names.end());
    CHECK(std::find(names.begin(), names.end(), "When-Then") != names.end());
}

TEST_CASE("excel: template DBC headers correct", "[excel][template]") {
    TempFile tf("excel_template_hdr.xlsx");
    auto result = create_excel_template(tf.path);
    REQUIRE(result.has_value());

    OpenXLSX::XLDocument doc;
    doc.open(tf.path.string());
    auto ws = doc.workbook().worksheet("DBC");
    OpenXLSX::XLCellValue v1 = ws.cell(1, 1).value();
    OpenXLSX::XLCellValue v3 = ws.cell(1, 3).value();
    OpenXLSX::XLCellValue v5 = ws.cell(1, 5).value();
    OpenXLSX::XLCellValue v16 = ws.cell(1, 16).value();
    doc.close();

    CHECK(v1.get<std::string>() == "Message ID");
    CHECK(v3.get<std::string>() == "Extended");
    CHECK(v5.get<std::string>() == "Signal");
    CHECK(v16.get<std::string>() == "Multiplex Value");
}

TEST_CASE("excel: template Checks headers correct", "[excel][template]") {
    TempFile tf("excel_template_checks_hdr.xlsx");
    auto result = create_excel_template(tf.path);
    REQUIRE(result.has_value());

    OpenXLSX::XLDocument doc;
    doc.open(tf.path.string());
    auto ws = doc.workbook().worksheet("Checks");
    OpenXLSX::XLCellValue v1 = ws.cell(1, 1).value();
    OpenXLSX::XLCellValue v3 = ws.cell(1, 3).value();
    OpenXLSX::XLCellValue v8 = ws.cell(1, 8).value();
    doc.close();

    CHECK(v1.get<std::string>() == "Check Name");
    CHECK(v3.get<std::string>() == "Condition");
    CHECK(v8.get<std::string>() == "Severity");
}

TEST_CASE("excel: template When-Then headers correct", "[excel][template]") {
    TempFile tf("excel_template_wt_hdr.xlsx");
    auto result = create_excel_template(tf.path);
    REQUIRE(result.has_value());

    OpenXLSX::XLDocument doc;
    doc.open(tf.path.string());
    auto ws = doc.workbook().worksheet("When-Then");
    OpenXLSX::XLCellValue v1 = ws.cell(1, 1).value();
    OpenXLSX::XLCellValue v10 = ws.cell(1, 10).value();
    OpenXLSX::XLCellValue v11 = ws.cell(1, 11).value();
    doc.close();

    CHECK(v1.get<std::string>() == "Check Name");
    CHECK(v10.get<std::string>() == "Within (ms)");
    CHECK(v11.get<std::string>() == "Severity");
}

TEST_CASE("excel: template no overwrite", "[excel][template]") {
    TempFile tf("excel_template_nooverwrite.xlsx");
    auto first = create_excel_template(tf.path);
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
    TempFile tf("excel_no_sheets.xlsx");
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
    TempFile tf("excel_err_cond.xlsx");
    make_checks_workbook(tf.path, {{"", "Speed", "bogus_cond", "100", "", "", "", ""}});
    auto result = load_checks_from_excel(tf.path);
    REQUIRE(!result.has_value());
    CHECK_THAT(std::string(result.error().message()),
               ContainsSubstring("unknown condition 'bogus_cond'"));
}

TEST_CASE("excel: missing min for stays_between", "[excel][error]") {
    TempFile tf("excel_err_min.xlsx");
    make_checks_workbook(tf.path, {{"", "Voltage", "stays_between", "", "", "14.5", "", ""}});
    auto result = load_checks_from_excel(tf.path);
    REQUIRE(!result.has_value());
    CHECK_THAT(std::string(result.error().message()),
               ContainsSubstring("requires 'Min' and 'Max'"));
}

TEST_CASE("excel: missing time for settles_between", "[excel][error]") {
    TempFile tf("excel_err_time.xlsx");
    make_checks_workbook(tf.path, {{"", "Coolant", "settles_between", "", "85", "95", "", ""}});
    auto result = load_checks_from_excel(tf.path);
    REQUIRE(!result.has_value());
    CHECK_THAT(std::string(result.error().message()), ContainsSubstring("requires 'Time (ms)'"));
}

TEST_CASE("excel: unknown when condition", "[excel][error]") {
    TempFile tf("excel_err_when.xlsx");
    make_wt_workbook(
        tf.path, {{"", "Brake", "bogus_when", "50", "Light", "equals", "1", "", "", "100", ""}});
    auto result = load_checks_from_excel(tf.path);
    REQUIRE(!result.has_value());
    CHECK_THAT(std::string(result.error().message()),
               ContainsSubstring("unknown when condition 'bogus_when'"));
}

TEST_CASE("excel: unknown then condition", "[excel][error]") {
    TempFile tf("excel_err_then.xlsx");
    make_wt_workbook(
        tf.path, {{"", "Brake", "exceeds", "50", "Light", "bogus_then", "1", "", "", "100", ""}});
    auto result = load_checks_from_excel(tf.path);
    REQUIRE(!result.has_value());
    CHECK_THAT(std::string(result.error().message()),
               ContainsSubstring("unknown then condition 'bogus_then'"));
}

TEST_CASE("excel: DBC invalid byte order", "[excel][error]") {
    TempFile tf("excel_err_byte_order.xlsx");
    make_dbc_workbook(tf.path, {{"256", "Msg", "8", "Sig", "0", "8", "wrong_order", "FALSE", "1",
                                 "0", "0", "255", "", "", "", ""}});
    auto result = load_dbc_from_excel(tf.path);
    REQUIRE(!result.has_value());
    CHECK_THAT(std::string(result.error().message()),
               ContainsSubstring("'little_endian' or 'big_endian'"));
}

TEST_CASE("excel: DBC invalid message ID", "[excel][error]") {
    TempFile tf("excel_err_msgid.xlsx");
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
    TempFile tf("excel_dbc_no_sheet.xlsx");
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
    TempFile tf("excel_empty_rows.xlsx");
    OpenXLSX::XLDocument doc;
    doc.create(tf.path.string(), OpenXLSX::XLForceOverwrite);
    doc.workbook().worksheet("Sheet1").setName("Checks");
    auto ws = doc.workbook().worksheet("Checks");
    write_header(ws, checks_hdr);
    // Row 2: data
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
    TempFile tf("excel_dbc_int_factor.xlsx");
    make_dbc_workbook(tf.path, {{"256", "Msg", "8", "Sig", "0", "8", "little_endian", "FALSE", "1",
                                 "0", "0", "255", "", "", "", ""}});
    auto result = load_dbc_from_excel(tf.path);
    REQUIRE(result.has_value());
    auto& factor = result->messages[0].signals[0].factor.get();
    // Integer 1 should be represented as 1/1
    CHECK(factor.numerator == 1);
    CHECK(factor.denominator == 1);
}

TEST_CASE("excel: DBC factor as fractional rational", "[excel][dbc]") {
    TempFile tf("excel_dbc_frac_factor.xlsx");
    make_dbc_workbook(tf.path, {{"256", "Msg", "8", "Sig", "0", "8", "little_endian", "FALSE",
                                 "0.1", "0", "0", "300", "km/h", "", "", ""}});
    auto result = load_dbc_from_excel(tf.path);
    REQUIRE(result.has_value());
    auto& factor = result->messages[0].signals[0].factor.get();
    // 0.1 should be represented as 1/10 (after GCD simplification)
    CHECK(factor.numerator == 1);
    CHECK(factor.denominator == 10);
}

// ===========================================================================
// Extended CAN ID via "Extended" column
// ===========================================================================

TEST_CASE("excel: DBC extended CAN ID via Extended column", "[excel][dbc]") {
    TempFile tf("excel_dbc_extended_id.xlsx");
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
    TempFile tf("excel_dbc_std_explicit.xlsx");
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
    TempFile tf("excel_dbc_std_empty.xlsx");
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
    TempFile tf("excel_template_roundtrip.xlsx");
    auto create_result = create_excel_template(tf.path);
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
