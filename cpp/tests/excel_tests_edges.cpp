// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// Excel loader tests at the edges of what it accepts: adversarial files, numbers
// stored as native cells, the sheet readers' bounds and the library's throw
// paths; and the tests of the scratch paths the suites share.
#include <catch2/catch_test_macros.hpp>
#include <catch2/generators/catch_generators.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>

#include <aletheia/error.hpp>
#include <aletheia/excel.hpp>

#include <OpenXLSX.hpp>

#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <ios>
#include <optional>
#include <ranges>
#include <span>
#include <string>
#include <string_view>
#include <system_error>
#include <variant>
#include <vector>

#include "excel_workbooks.hpp"
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

using aletheia::test::checks_hdr;
using aletheia::test::dbc_hdr;
using aletheia::test::make_checks_workbook;
using aletheia::test::make_dbc_workbook;
using aletheia::test::make_wt_workbook;
using aletheia::test::write_header;
using aletheia::test::write_row;

using namespace aletheia;
using Catch::Matchers::ContainsSubstring;

// ===========================================================================
// Test helpers
// ===========================================================================

// Write raw bytes to a binary stream. The stream takes char and the archive
// fixtures below read as unsigned, so each byte crosses as a value rather than
// through a cast of the buffer's type.
static void write_bytes(std::ofstream& ofs, std::span<const unsigned char> bytes) {
    for (auto const b : bytes)
        ofs.put(static_cast<char>(b));
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
    auto const needle = "<v>" + std::to_string(id_value) + "</v>";
    auto const replacement =
        (*raw_override == '\0') ? std::string{"<v/>"} : "<v>" + std::string{raw_override} + "</v>";
    OpenXLSX::XLZipArchive zip;
    zip.open(path.string());
    auto xml = zip.getEntry(sheet_name);
    auto const pos = xml.find(needle);
    REQUIRE(pos != std::string::npos);
    xml.replace(pos, needle.size(), replacement);
    zip.addEntry(sheet_name, xml);
    zip.save();
    zip.close();
}

// ===========================================================================
// Adversarial-input hardening
// ===========================================================================

TEST_CASE("excel: symlink rejected", "[excel][hardening]") {
    const TempPath real("excel_real_target.xlsx");
    make_checks_workbook(real.path, {{"", "Speed", "never_exceeds", "220", "", "", "", ""}});
    const TempPath link("excel_symlink.xlsx");
    std::error_code ec;
    std::filesystem::create_symlink(real.path, link.path, ec);
    if (ec) {
        SUCCEED("Skipping symlink test — symlink creation not permitted on this filesystem");
        return;
    }

    auto const result = load_checks_from_excel(link.path);
    REQUIRE(!result.has_value());
    CHECK(result.error().kind() == ErrorKind::Validation);
    CHECK_THAT(std::string(result.error().message()), ContainsSubstring("symbolic link"));
}

TEST_CASE("excel: file size cap rejected", "[excel][hardening]") {
    // Build a non-archive plain file > 64 MiB.  load_checks_from_excel
    // rejects it on size BEFORE attempting OpenXLSX open.
    const TempPath tf("excel_oversize.xlsx");
    {
        std::ofstream ofs(tf.path, std::ios::binary);
        const std::vector<char> chunk(std::size_t{1024} * 1024, '\xAA');
        // 65 MiB, one mebibyte at a time: the count is the point, not a position.
        std::ranges::for_each(std::views::repeat(0, 65), [&](auto) {
            ofs.write(chunk.data(), static_cast<std::streamsize>(chunk.size()));
        });
    }
    auto const result = load_checks_from_excel(tf.path);
    REQUIRE(!result.has_value());
    CHECK(result.error().kind() == ErrorKind::InputBoundExceeded);
    REQUIRE(result.error().bound_info().has_value());
    CHECK(result.error().bound_info()->bound_kind == "input_length_bytes");
    CHECK(result.error().bound_info()->limit == 64ULL * 1024 * 1024);
}

TEST_CASE("excel: ZIP central-directory bomb rejected", "[excel][hardening]") {
    // Forge a tiny "ZIP" with a single CD entry whose uncompressed_size
    // claims to be 1 GiB.  The walker should reject without unpacking.
    const TempPath tf("excel_zip_bomb.xlsx");
    {
        std::ofstream ofs(tf.path, std::ios::binary);
        // -- One CD entry header, signature 0x02014b50, uncompressed_size = 1 GiB --
        const std::array<unsigned char, 46> cd{
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
        const std::array<unsigned char, 22> eocd{
            0x50, 0x4b, 0x05, 0x06, // signature
            0x00, 0x00, 0x00, 0x00, // disk numbers
            0x01, 0x00, 0x01, 0x00, // entries
            0x2e, 0x00, 0x00, 0x00, // CD size = 46
            0x00, 0x00, 0x00, 0x00, // CD offset = 0
            0x00, 0x00,             // comment length
        };
        write_bytes(ofs, eocd);
    }
    auto const result = load_checks_from_excel(tf.path);
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
    auto const result = create_excel_template(bad);
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
    auto const result = create_excel_template(bad);
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
    const TempPath tf("excel_strict_number_value.xlsx");
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

    auto const result = load_checks_from_excel(tf.path);
    REQUIRE_FALSE(result.has_value());
    CHECK_THAT(std::string(result.error().message()), ContainsSubstring("format it as TEXT"));
}

TEST_CASE("excel: DBC strict rejects a Factor stored as a native number", "[excel][strict][dbc]") {
    const TempPath tf("excel_strict_number_factor.xlsx");
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

    auto const result = load_dbc_from_excel(tf.path);
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
    const TempPath tf("excel_dbc_msgid_sci.xlsx");
    make_dbc_workbook_with_raw_id(tf.path, 31337421, "1e16");
    auto const result = load_dbc_from_excel(tf.path);
    REQUIRE_FALSE(result.has_value()); // a prefix-parse would load Message ID 1
    CHECK_THAT(std::string(result.error().message()), ContainsSubstring("1e16"));
    CHECK_THAT(std::string(result.error().message()), ContainsSubstring("Message ID"));
}

TEST_CASE("excel: DBC Message ID with an empty stored <v/> is refused", "[excel][dbc][strict]") {
    const TempPath tf("excel_dbc_msgid_empty_v.xlsx");
    make_dbc_workbook_with_raw_id(tf.path, 31337421, "");
    auto const result = load_dbc_from_excel(tf.path);
    REQUIRE_FALSE(result.has_value()); // a prefix-parse would load Message ID 0
    CHECK_THAT(std::string(result.error().message()), ContainsSubstring("Message ID"));
}

// Positive lock guarding the raw check from over-rejecting: a native number
// cell whose stored text is a plain digit run is a legitimate Message ID.
TEST_CASE("excel: DBC Message ID as a native integer cell loads", "[excel][dbc]") {
    const TempPath tf("excel_dbc_msgid_native.xlsx");
    make_dbc_workbook_with_raw_id(tf.path, 256, nullptr);
    auto const result = load_dbc_from_excel(tf.path);
    REQUIRE(result.has_value());
    REQUIRE(result->messages.size() == 1);
    CHECK(std::holds_alternative<StandardId>(result->messages[0].id));
}

// A kernel decimal refusal surfaced through get_decimal/get_int must carry the
// loader's own "Row N: invalid 'Field'" prefix — the kernel knows the literal,
// not the workbook position.
TEST_CASE("excel: kernel decimal refusal carries row and field context", "[excel][dbc]") {
    const TempPath tf("excel_decimal_ctx.xlsx");
    make_dbc_workbook(tf.path, {{"256", "Msg", "8", "Sig", "0", "8", "little_endian", "FALSE",
                                 "abc", "0", "0", "255", "", "", "", ""}});
    auto const result = load_dbc_from_excel(tf.path);
    REQUIRE_FALSE(result.has_value());
    CHECK_THAT(std::string(result.error().message()), ContainsSubstring("Row 2: invalid 'Factor'"));
}

// Cross-binding portability lock: the shared demo workbook's DBC sheet omits the
// Extended column, so every binding must load it as standard 11-bit messages
// (matching Python / Go / Rust).
TEST_CASE("excel: demo workbook DBC loads as standard messages", "[excel][dbc][portability]") {
    auto const path = repo_root() / "examples" / "demo" / "demo_workbook.xlsx";
    auto const result = load_dbc_from_excel(path);
    REQUIRE(result.has_value());
    CHECK(result->messages.size() == 2);
    for (auto const& msg : result->messages)
        CHECK(std::holds_alternative<StandardId>(msg.id));
}

// A directory name of the scratch shape under this process id, which no run
// makes and the sweep reads as any other, so a case can plant one.
static auto planted(std::string_view fate) -> std::filesystem::path {
    return std::filesystem::temp_directory_path() /
           (std::string(aletheia::test::scratch_prefix) + std::to_string(::getpid()) + "-" +
            std::string(fate));
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

TEST_CASE("temp path: a scratch directory outlives its owner only while the owner runs",
          "[excel][temp]") {
    // Removal at exit cannot be the whole answer: a run a signal ends never
    // reaches static destruction and keeps its directory, which about one run
    // in eight of a sweep does.  What the next run clears is every
    // directory whose lock it can take, the lock being the liveness test a
    // process id is not, since an id is reused, and a timestamp is not.
    auto const root = std::filesystem::temp_directory_path();

    SECTION("one whose lock is free is removed, contents and all") {
        auto const dead = planted("dead");
        std::filesystem::create_directories(dead);
        std::ofstream{dead / "left_behind.bin"} << "x";
        REQUIRE(std::filesystem::exists(dead / "left_behind.bin"));
        aletheia::test::reap_dead_scratch_dirs();
        CHECK_FALSE(std::filesystem::exists(dead));
    }

    SECTION("one whose owner holds its lock is kept, and goes once the lock does") {
        auto const live = planted("live");
        {
            std::optional<aletheia::test::ScratchLock> holder;
            aletheia::test::hold_scratch_dir(live, holder);
            REQUIRE(holder->owns(live));
            aletheia::test::reap_dead_scratch_dirs();
            CHECK(std::filesystem::is_directory(live));
        }
        aletheia::test::reap_dead_scratch_dirs();
        CHECK_FALSE(std::filesystem::exists(live));
    }

    SECTION("a link planted under the name is refused rather than followed") {
        // The system temp directory is world writable, so a link is the one
        // entry whose name says scratch and whose contents are someone else's.
        auto const target = root / ("aletheia-link-target-" + std::to_string(::getpid()));
        std::filesystem::create_directories(target);
        auto const link = planted("link");
        std::filesystem::create_directory_symlink(target, link);
        aletheia::test::reap_dead_scratch_dirs();
        CHECK(std::filesystem::is_symlink(link));
        CHECK(std::filesystem::is_directory(target));
        std::error_code ec;
        std::filesystem::remove(link, ec);
        std::filesystem::remove(target, ec);
    }

    SECTION("the sweeping process keeps its own scratch directory") {
        const TempPath keeper{"aletheia_temp_path_keeper.bin", "still here"};
        aletheia::test::reap_dead_scratch_dirs();
        CHECK(std::filesystem::is_directory(scratch_dir()));
        CHECK(std::filesystem::exists(keeper.path));
    }
}

TEST_CASE("temp path: a lock outlived by its directory's removal owns nothing at that path",
          "[excel][temp]") {
    // Ownership is the lock and the inode together: a lock taken on a
    // directory a sweep then removed is held on an inode no path reaches, and
    // a directory created under the same name afterwards is another inode.
    // Both are the false arm of the comparison, which nothing else drives.
    auto const dir = planted("orphan");
    std::optional<aletheia::test::ScratchLock> lock;
    aletheia::test::hold_scratch_dir(dir, lock);
    REQUIRE(lock->owns(dir));
    std::filesystem::remove_all(dir);
    CHECK_FALSE(lock->owns(dir));
    std::filesystem::create_directories(dir);
    CHECK_FALSE(lock->owns(dir));
    std::error_code ec;
    std::filesystem::remove_all(dir, ec);
}

TEST_CASE("temp path: a scratch directory a peer is sweeping is held once the peer is done",
          "[excel][temp]") {
    // A run whose process id a killed run's directory carries can find a peer
    // removing that directory between its own creation of it and its lock, the
    // peer holding the lock for the whole removal. The peer here is a second
    // lock in this process, since flock is per open file description, and it
    // removes the directory and lets go only inside the try's wait: a try that
    // slept and retried instead of waiting on the lock would find the peer
    // still holding it on every try and run out of tries.
    auto const dir = planted("contested");
    std::optional<aletheia::test::ScratchLock> peer_lock;
    aletheia::test::hold_scratch_dir(dir, peer_lock);
    REQUIRE(peer_lock->owns(dir));
    bool peer_let_go = false;
    auto const peer_sweeps = [&](const std::filesystem::path& contested) {
        std::error_code ec;
        std::filesystem::remove_all(contested, ec);
        peer_lock.reset();
        peer_let_go = true;
        aletheia::test::wait_until_free(contested);
    };
    std::optional<aletheia::test::ScratchLock> lock;
    aletheia::test::hold_scratch_dir(dir, lock, peer_sweeps);
    REQUIRE(peer_let_go);
    REQUIRE(lock.has_value());
    CHECK(lock->owns(dir));
    CHECK(std::filesystem::is_directory(dir));
    std::error_code ec;
    std::filesystem::remove_all(dir, ec);
}

// ===========================================================================
// Edges of the sheet readers
// ===========================================================================

TEST_CASE("excel: a native integer Message ID carrying a nine and a minus is read exactly",
          "[excel][dbc][strict]") {
    // The digit run check admits every digit and a leading minus; the minus
    // then fails as a CAN ID, by the ID's own wording and not the strict one.
    SECTION("nineteen loads as 19") {
        const TempPath tf("excel_dbc_msgid_19.xlsx");
        make_dbc_workbook_with_raw_id(tf.path, 19, nullptr);
        auto const result = load_dbc_from_excel(tf.path);
        REQUIRE(result.has_value());
        REQUIRE(result->messages.size() == 1);
        CHECK(std::get<StandardId>(result->messages[0].id).value() == 19);
    }
    SECTION("minus nine is refused as an ID, not as a stored shape") {
        const TempPath tf("excel_dbc_msgid_minus.xlsx");
        make_dbc_workbook_with_raw_id(tf.path, 31337421, "-9");
        auto const result = load_dbc_from_excel(tf.path);
        REQUIRE_FALSE(result.has_value());
        CHECK_THAT(std::string(result.error().message()),
                   ContainsSubstring("invalid 'Message ID'"));
        CHECK_THAT(std::string(result.error().message()),
                   !ContainsSubstring("not a plain integer"));
    }
}

TEST_CASE("excel: a missing required cell is refused by its field's name", "[excel][error]") {
    SECTION("a text field") {
        const TempPath tf("excel_missing_signal.xlsx");
        make_checks_workbook(tf.path, {{"", "", "never_exceeds", "220", "", "", "", ""}});
        auto const result = load_checks_from_excel(tf.path);
        REQUIRE_FALSE(result.has_value());
        CHECK_THAT(std::string(result.error().message()),
                   ContainsSubstring("missing or invalid 'Signal' (expected string)"));
    }
    SECTION("a number field") {
        const TempPath tf("excel_missing_value.xlsx");
        make_checks_workbook(tf.path, {{"", "Speed", "never_exceeds", "", "", "", "", ""}});
        auto const result = load_checks_from_excel(tf.path);
        REQUIRE_FALSE(result.has_value());
        CHECK_THAT(std::string(result.error().message()),
                   ContainsSubstring("missing or invalid 'Value' (expected number)"));
    }
    SECTION("the message id") {
        const TempPath tf("excel_missing_id.xlsx");
        make_dbc_workbook(tf.path, {{"", "Msg", "8", "Sig", "0", "8", "little_endian", "FALSE", "1",
                                     "0", "0", "255", "", "", "", ""}});
        auto const result = load_dbc_from_excel(tf.path);
        REQUIRE_FALSE(result.has_value());
        CHECK_THAT(std::string(result.error().message()),
                   ContainsSubstring("missing or invalid 'Message ID'"));
    }
    SECTION("a boolean field") {
        const TempPath tf("excel_missing_signed.xlsx");
        make_dbc_workbook(tf.path, {{"256", "Msg", "8", "Sig", "0", "8", "little_endian", "", "1",
                                     "0", "0", "255", "", "", "", ""}});
        auto const result = load_dbc_from_excel(tf.path);
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
        const TempPath tf("excel_dbc_dlc_edge.xlsx");
        make_dbc_workbook(tf.path, {row(std::to_string(dlc).c_str())});
        auto const result = load_dbc_from_excel(tf.path);
        REQUIRE(result.has_value());
        REQUIRE(result->messages.size() == 1);
        CHECK(result->messages[0].dlc.value() == static_cast<std::uint8_t>(dlc));
    }
    SECTION("16 and -1 are refused") {
        // 256 truncates to 0 in a byte, a valid DLC: the refusal must come
        // before the narrowing, not from the factory after it.
        auto const dlc = GENERATE(16, -1, 256);
        const TempPath tf("excel_dbc_dlc_past.xlsx");
        make_dbc_workbook(tf.path, {row(std::to_string(dlc).c_str())});
        auto const result = load_dbc_from_excel(tf.path);
        REQUIRE_FALSE(result.has_value());
        CHECK_THAT(std::string(result.error().message()), ContainsSubstring("DLC out of range"));
    }
}

TEST_CASE("excel: every data row of a long sheet is loaded", "[excel][simple]") {
    const TempPath tf("excel_fifty_rows.xlsx");
    std::vector<std::vector<std::string>> rows;
    rows.reserve(50);
    for (auto const i : std::views::iota(0, 50))
        rows.push_back({"", "Sig" + std::to_string(i), "never_exceeds", "1", "", "", "", ""});
    make_checks_workbook(tf.path, rows);
    auto const result = load_checks_from_excel(tf.path);
    REQUIRE(result.has_value());
    CHECK(result->size() == 50);
}

TEST_CASE("excel: a header far to the right of the others is still read", "[excel][metadata]") {
    // The header row is read to the sheet's own column count, wherever the
    // last named column sits.
    const TempPath tf("excel_wide_header.xlsx");
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
    auto const result = load_checks_from_excel(tf.path);
    REQUIRE(result.has_value());
    REQUIRE(result->size() == 1);
    CHECK((*result)[0].check_severity() == "critical");
}

TEST_CASE("excel: DBC multiplex value zero is a value, not an absence", "[excel][mux]") {
    const TempPath tf("excel_dbc_mux_zero.xlsx");
    make_dbc_workbook(tf.path, {{"256", "Msg", "8", "MuxSig", "0", "8", "little_endian", "FALSE",
                                 "1", "0", "0", "255", "", "Selector", "0", ""}});
    auto const result = load_dbc_from_excel(tf.path);
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
    const TempPath tf("excel_not_a_workbook.xlsx");
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
        const TempPath tf("excel_alloc_checks.xlsx");
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
        const TempPath tf("excel_alloc_when_then.xlsx");
        make_wt_workbook(tf.path,
                         {{"braking dims the lamp", "BrakePedalPositionAsAPercentage", "exceeds",
                           "50", "BrakeLampIlluminationState", "equals", "1", "", "", "100", ""}});
        REQUIRE(load_checks_from_excel(tf.path).has_value());
        expect_balanced([&] { return load_checks_from_excel(tf.path); });
    }
    SECTION("the DBC loader") {
        const TempPath tf("excel_alloc_dbc.xlsx");
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
        const TempPath tf("excel_alloc_template.xlsx");
        expect_balanced([&] {
            std::filesystem::remove(tf.path);
            return create_excel_template(tf.path);
        });
    }
}
#endif

TEST_CASE("excel: a boolean cell that is neither TRUE nor FALSE is refused, by name",
          "[excel][error]") {
    const TempPath tf("excel_dbc_bool_maybe.xlsx");
    make_dbc_workbook(tf.path, {{"256", "M", "8", "S", "0", "8", "little_endian", "MAYBE", "1", "0",
                                 "0", "255", "", "", "", ""}});
    auto const result = load_dbc_from_excel(tf.path);
    REQUIRE_FALSE(result.has_value());
    CHECK_THAT(std::string(result.error().message()), ContainsSubstring("expected TRUE/FALSE"));
}

TEST_CASE("excel: a range condition missing a bound is refused, by name", "[excel][error]") {
    SECTION("stays_between without Max") {
        const TempPath tf("excel_range_no_max.xlsx");
        make_checks_workbook(tf.path, {{"", "V", "stays_between", "", "11.5", "", "", ""}});
        auto const result = load_checks_from_excel(tf.path);
        REQUIRE_FALSE(result.has_value());
        CHECK_THAT(std::string(result.error().message()),
                   ContainsSubstring("requires 'Min' and 'Max'"));
    }
    SECTION("settles_between without Min") {
        const TempPath tf("excel_settles_no_min.xlsx");
        make_checks_workbook(tf.path,
                             {{"", "Coolant", "settles_between", "", "", "95", "5000", ""}});
        auto const result = load_checks_from_excel(tf.path);
        REQUIRE_FALSE(result.has_value());
        CHECK_THAT(std::string(result.error().message()),
                   ContainsSubstring("requires 'Min' and 'Max'"));
    }
    SECTION("a then range without Then Max") {
        const TempPath tf("excel_then_range_no_max.xlsx");
        make_wt_workbook(tf.path, {{"", "BrakePedal", "exceeds", "50", "Coolant", "stays_between",
                                    "", "85", "", "100", ""}});
        auto const result = load_checks_from_excel(tf.path);
        REQUIRE_FALSE(result.has_value());
        CHECK_THAT(std::string(result.error().message()),
                   ContainsSubstring("requires 'Then Min' and 'Then Max'"));
    }
}

TEST_CASE("excel: a standard CAN ID past its range is refused, by name", "[excel][dbc][error]") {
    // 65792 truncates to 256 in 16 bits, a valid id: the refusal must come
    // before the narrowing, not from the factory after it.
    auto const* const id = GENERATE("2048", "65792");
    const TempPath tf("excel_dbc_id_past.xlsx");
    make_dbc_workbook(tf.path, {{id, "M", "8", "S", "0", "8", "little_endian", "FALSE", "1", "0",
                                 "0", "255", "", "", "", ""}});
    auto const result = load_dbc_from_excel(tf.path);
    REQUIRE_FALSE(result.has_value());
    CHECK_THAT(std::string(result.error().message()), ContainsSubstring("Invalid CAN ID"));
}

TEST_CASE("excel: a range condition missing its other bound is refused, by name",
          "[excel][error]") {
    SECTION("settles_between without Max") {
        const TempPath tf("excel_settles_no_max.xlsx");
        make_checks_workbook(tf.path,
                             {{"", "Coolant", "settles_between", "", "85", "", "5000", ""}});
        auto const result = load_checks_from_excel(tf.path);
        REQUIRE_FALSE(result.has_value());
        CHECK_THAT(std::string(result.error().message()),
                   ContainsSubstring("requires 'Min' and 'Max'"));
    }
    SECTION("a then range without Then Min") {
        const TempPath tf("excel_then_range_no_min.xlsx");
        make_wt_workbook(tf.path, {{"", "BrakePedal", "exceeds", "50", "Coolant", "stays_between",
                                    "", "", "95", "100", ""}});
        auto const result = load_checks_from_excel(tf.path);
        REQUIRE_FALSE(result.has_value());
        CHECK_THAT(std::string(result.error().message()),
                   ContainsSubstring("requires 'Then Min' and 'Then Max'"));
    }
}
