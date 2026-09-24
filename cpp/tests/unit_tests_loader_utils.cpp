// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// The shared then-dispatcher of the YAML and Excel loaders: it reads the slots
// its word names from what the loader passed, and refuses a slot the loader
// did not pass by name rather than reading a filler.

#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>

#include "detail/loader_utils.hpp"
#include "temp_path.hpp"

#include <aletheia/check.hpp>
#include <aletheia/enrich.hpp>
#include <aletheia/error.hpp>
#include <aletheia/limits.hpp>
#include <aletheia/types.hpp>

#include <algorithm>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <ios>
#include <ranges>
#include <sstream>
#include <string>
#include <unistd.h>
#include <vector>

using aletheia::detail::ThenSlotValues;
using aletheia::PhysicalValue;
using aletheia::Rational;
using Catch::Matchers::ContainsSubstring;

static auto then_builder() -> aletheia::ThenSignal {
    return aletheia::check::when("Brake").drops_below(PhysicalValue{Rational{10, 1}}).then("Speed");
}

static constexpr auto k_within = std::chrono::milliseconds{100};

TEST_CASE("dispatch_then reads the slot its word names", "[loader_utils]") {
    auto const builder = then_builder();
    auto const five = PhysicalValue{Rational{5, 1}};
    auto const nine = PhysicalValue{Rational{9, 1}};

    auto const rendered = [](aletheia::CheckResult const& result) {
        return aletheia::format_formula(result.to_formula());
    };
    CHECK(
        rendered(aletheia::detail::dispatch_then(builder, "equals", {{"value", five}}, k_within)) ==
        "always(not(Brake < 10) or eventually within 100ms (Speed = 5))");
    CHECK(rendered(
              aletheia::detail::dispatch_then(builder, "exceeds", {{"value", five}}, k_within)) ==
          "always(not(Brake < 10) or eventually within 100ms (Speed > 5))");
    CHECK(rendered(aletheia::detail::dispatch_then(builder, "stays_between",
                                                   {{"lo", five}, {"hi", nine}}, k_within)) ==
          "always(not(Brake < 10) or eventually within 100ms (5 <= Speed <= 9))");
}

TEST_CASE("dispatch_then refuses a slot the loader did not pass, by name", "[loader_utils]") {
    auto const builder = then_builder();
    auto const five = PhysicalValue{Rational{5, 1}};
    ThenSlotValues const range_only{{"lo", five}, {"hi", five}};
    ThenSlotValues const value_only{{"value", five}};

    CHECK_THROWS_WITH(aletheia::detail::dispatch_then(builder, "equals", range_only, k_within),
                      ContainsSubstring("'equals' reads slot 'value'"));
    CHECK_THROWS_WITH(aletheia::detail::dispatch_then(builder, "exceeds", range_only, k_within),
                      ContainsSubstring("'exceeds' reads slot 'value'"));
    CHECK_THROWS_WITH(
        aletheia::detail::dispatch_then(builder, "stays_between", value_only, k_within),
        ContainsSubstring("'stays_between' reads slot 'lo'"));
    CHECK_THROWS_WITH(aletheia::detail::dispatch_then(builder, "stays_between",
                                                      ThenSlotValues{{"lo", five}}, k_within),
                      ContainsSubstring("'stays_between' reads slot 'hi'"));
}

TEST_CASE("dispatch_then refuses a word outside the vocabulary, by name", "[loader_utils]") {
    CHECK_THROWS_WITH(aletheia::detail::dispatch_then(then_builder(), "flickers", {}, k_within),
                      ContainsSubstring("flickers"));
}

// ===========================================================================
// Path and size bounds
// ===========================================================================

using aletheia::detail::check_file_size_bound;
using aletheia::detail::check_input_size_bound;
using aletheia::detail::check_xlsx_uncompressed_bound;
using aletheia::detail::validate_loader_path;
using aletheia::detail::validate_output_parent_dir;
using aletheia::max_dbc_text_bytes;
using aletheia::test::scratch_dir;
using aletheia::test::TempPath;

// A file of exactly `size` bytes, sparse, so a bound at the size of the
// text cap costs no writing.
static void make_sparse_file(const std::filesystem::path& path, std::uintmax_t size) {
    { const std::ofstream touch{path, std::ios::binary}; }
    std::filesystem::resize_file(path, size);
}

namespace {
// Little-endian bytes appended to a ZIP image under construction.
struct ZipImage {
    std::vector<unsigned char> bytes;
    void u16(std::uint16_t v) {
        bytes.push_back(static_cast<unsigned char>(v & 0xFFU));
        bytes.push_back(static_cast<unsigned char>(v >> 8U));
    }
    void u32(std::uint32_t v) {
        u16(static_cast<std::uint16_t>(v & 0xFFFFU));
        u16(static_cast<std::uint16_t>(v >> 16U));
    }
    // One central-directory entry: signature, then the fields the walker
    // reads, then name, extra and comment bytes of the lengths given.
    void cd_entry(std::uint32_t uncompressed, std::uint16_t name_len, std::uint16_t extra_len,
                  std::uint16_t comment_len) {
        u32(0x02014b50);
        // version made by, version needed, flags, method, mod time
        std::ranges::for_each(std::views::repeat(0, 5), [this](auto) { u16(0); });
        u16(0); // mod date
        u32(0); // CRC-32
        u32(0); // compressed size
        u32(uncompressed);
        u16(name_len);
        u16(extra_len);
        u16(comment_len);
        u16(0); // disk number start
        u16(0); // internal attributes
        u32(0); // external attributes
        u32(0); // relative offset
        bytes.insert(bytes.end(), std::size_t{name_len} + extra_len + comment_len, 'x');
    }
    void eocd(std::uint16_t entries, std::uint32_t cd_size, std::uint32_t cd_offset) {
        u32(0x06054b50);
        u16(0); // this disk
        u16(0); // disk with the central directory
        u16(entries);
        u16(entries);
        u32(cd_size);
        u32(cd_offset);
        u16(0); // comment length
    }
    void write(const std::filesystem::path& path) const {
        std::ofstream out{path, std::ios::binary};
        for (auto const b : bytes)
            out.put(static_cast<char>(b));
    }
};
} // namespace

TEST_CASE("the text cap admits the cap itself and refuses one byte more", "[loader][bounds]") {
    SECTION("on a size") {
        CHECK(check_input_size_bound(max_dbc_text_bytes).has_value());
        auto const past = check_input_size_bound(max_dbc_text_bytes + 1);
        REQUIRE_FALSE(past.has_value());
        CHECK(past.error().kind() == aletheia::ErrorKind::InputBoundExceeded);
    }
    SECTION("on a file") {
        TempPath at_cap("loader_at_cap.dbc");
        make_sparse_file(at_cap.path, max_dbc_text_bytes);
        CHECK(check_file_size_bound(at_cap.path).has_value());
        TempPath past_cap("loader_past_cap.dbc");
        make_sparse_file(past_cap.path, max_dbc_text_bytes + 1);
        auto const past = check_file_size_bound(past_cap.path);
        REQUIRE_FALSE(past.has_value());
        CHECK(past.error().kind() == aletheia::ErrorKind::InputBoundExceeded);
    }
}

TEST_CASE("a file that cannot be sized is reported as such, not as oversize", "[loader][bounds]") {
    auto const missing = scratch_dir() / "loader_never_written.dbc";
    auto const sized = check_file_size_bound(missing);
    REQUIRE_FALSE(sized.has_value());
    CHECK_THAT(std::string{sized.error().message()}, ContainsSubstring("Could not stat file"));
    auto const walked = check_xlsx_uncompressed_bound(missing);
    REQUIRE_FALSE(walked.has_value());
    CHECK_THAT(std::string{walked.error().message()},
               ContainsSubstring("Could not stat .xlsx archive"));
}

TEST_CASE("a path through a regular file is absence, on both loader path checks",
          "[loader][path]") {
    // ENOTDIR: a component that exists but is not a directory. Go's loader
    // answers absence for it, and so do both checks here. The output path's
    // parent is itself below the file, so its own status fails the same way.
    const TempPath file("loader_not_a_dir.txt", "x");
    auto const through = file.path / "sub" / "inner.yaml";
    auto const loader = validate_loader_path(through, "YAML");
    REQUIRE_FALSE(loader.has_value());
    CHECK_THAT(std::string{loader.error().message()}, ContainsSubstring("file not found"));
    auto const parent = validate_output_parent_dir(through);
    REQUIRE_FALSE(parent.has_value());
    CHECK_THAT(std::string{parent.error().message()},
               ContainsSubstring("Parent directory does not exist"));
}

TEST_CASE("a bare file name has no parent directory to check", "[loader][path]") {
    CHECK(validate_output_parent_dir("template.xlsx").has_value());
}

TEST_CASE("a positioned read fills its buffer whole or says it could not", "[loader][zip]") {
    using aletheia::detail::read_exactly;
    std::istringstream in{"abcdef"};
    std::string out(3, '\0');
    CHECK(read_exactly(in, 2, out));
    CHECK(out == "cde");
    SECTION("a read the stream cuts short") {
        std::string four(4, '\0');
        CHECK_FALSE(read_exactly(in, 4, four));
    }
    SECTION("a read past the end") {
        std::string two(2, '\0');
        CHECK_FALSE(read_exactly(in, 10, two));
    }
    SECTION("a stream already failed") {
        std::string one(1, '\0');
        in.setstate(std::ios::failbit);
        CHECK_FALSE(read_exactly(in, 0, one));
    }
}

TEST_CASE("an archive that cannot be opened is reported as such, not as malformed",
          "[loader][zip]") {
    // A file that stats but does not open: its size is known and its record
    // is not, and the refusal has to say the first and not the second. Root
    // opens anything, so under root there is no such file to make.
    if (::geteuid() == 0)
        SKIP("root opens a file whatever its mode");
    TempPath f("loader_unreadable.xlsx");
    make_sparse_file(f.path, 4096);
    std::filesystem::permissions(f.path, std::filesystem::perms::none);
    auto const r = check_xlsx_uncompressed_bound(f.path);
    std::filesystem::permissions(f.path, std::filesystem::perms::owner_read |
                                             std::filesystem::perms::owner_write);
    REQUIRE_FALSE(r.has_value());
    CHECK_THAT(std::string{r.error().message()}, ContainsSubstring("Could not open .xlsx archive"));
}

TEST_CASE("the archive walker finds the end-of-directory record at every size it can",
          "[loader][zip]") {
    SECTION("one byte short of a record is not an archive") {
        TempPath f("loader_short.xlsx");
        make_sparse_file(f.path, 21);
        auto const r = check_xlsx_uncompressed_bound(f.path);
        REQUIRE_FALSE(r.has_value());
        CHECK_THAT(std::string{r.error().message()}, ContainsSubstring("Not a valid .xlsx"));
    }
    SECTION("an empty archive is exactly one record, and holds nothing") {
        TempPath f("loader_empty.xlsx");
        ZipImage z;
        z.eocd(0, 0, 0);
        z.write(f.path);
        CHECK(check_xlsx_uncompressed_bound(f.path).has_value());
    }
    SECTION("a file with no record anywhere in its tail is not an archive") {
        TempPath f("loader_no_record.xlsx");
        make_sparse_file(f.path, 4096);
        auto const r = check_xlsx_uncompressed_bound(f.path);
        REQUIRE_FALSE(r.has_value());
        CHECK_THAT(std::string{r.error().message()}, ContainsSubstring("Not a valid .xlsx"));
    }
}

TEST_CASE("the archive walker bounds the central directory by the file's own size",
          "[loader][zip]") {
    // Each forged record puts the directory exactly at the file's edge, which
    // is where a bound drawn one byte off would refuse a well-formed archive
    // or read past a malformed one.
    TempPath f("loader_cd_edge.xlsx");
    SECTION("a directory that starts at the end of the file is empty, and allowed") {
        ZipImage z;
        z.eocd(0, 0, 22);
        z.write(f.path);
        CHECK(check_xlsx_uncompressed_bound(f.path).has_value());
    }
    SECTION("a directory as large as the file is read, and found malformed") {
        ZipImage z;
        z.eocd(1, 22, 0);
        z.write(f.path);
        auto const r = check_xlsx_uncompressed_bound(f.path);
        REQUIRE_FALSE(r.has_value());
        CHECK_THAT(std::string{r.error().message()},
                   ContainsSubstring("Malformed central directory in"));
    }
    SECTION("a directory ending exactly at the file's end is read, and found malformed") {
        ZipImage z;
        z.eocd(1, 12, 10);
        z.write(f.path);
        auto const r = check_xlsx_uncompressed_bound(f.path);
        REQUIRE_FALSE(r.has_value());
        CHECK_THAT(std::string{r.error().message()},
                   ContainsSubstring("Malformed central directory in"));
    }
    SECTION("a directory reaching past the file's end is refused before it is read") {
        ZipImage z;
        z.eocd(1, 13, 10);
        z.write(f.path);
        auto const r = check_xlsx_uncompressed_bound(f.path);
        REQUIRE_FALSE(r.has_value());
        CHECK_THAT(std::string{r.error().message()},
                   ContainsSubstring("Malformed central directory location"));
    }
}

TEST_CASE("the archive walker sums every entry, stepping over each entry's variable fields",
          "[loader][zip]") {
    // Two entries whose sizes together pass the cap while each alone does
    // not, the first carrying a name, an extra field and a comment the walker
    // must step over to find the second.
    TempPath f("loader_two_entries.xlsx");
    ZipImage z;
    constexpr auto half = static_cast<std::uint32_t>(max_dbc_text_bytes / 2);
    z.cd_entry(half + 1, 3, 4, 5);
    z.cd_entry(half, 0, 0, 0);
    auto const cd_size = static_cast<std::uint32_t>(z.bytes.size());
    z.eocd(2, cd_size, 0);
    z.write(f.path);
    auto const r = check_xlsx_uncompressed_bound(f.path);
    REQUIRE_FALSE(r.has_value());
    CHECK(r.error().kind() == aletheia::ErrorKind::InputBoundExceeded);
    REQUIRE(r.error().bound_info().has_value());
    CHECK(r.error().bound_info()->observed == (std::uint64_t{half} * 2) + 1);
}

TEST_CASE("the archive walker admits an uncompressed total at the cap", "[loader][zip]") {
    TempPath f("loader_at_cap.xlsx");
    ZipImage z;
    z.cd_entry(static_cast<std::uint32_t>(max_dbc_text_bytes), 0, 0, 0);
    auto const cd_size = static_cast<std::uint32_t>(z.bytes.size());
    z.eocd(1, cd_size, 0);
    z.write(f.path);
    CHECK(check_xlsx_uncompressed_bound(f.path).has_value());
}

TEST_CASE("a directory is refused as a loader path, and a file as an output parent, by name",
          "[loader][path]") {
    auto const loader = validate_loader_path(std::filesystem::temp_directory_path(), "YAML");
    REQUIRE_FALSE(loader.has_value());
    CHECK_THAT(std::string{loader.error().message()}, ContainsSubstring("not a regular file"));
    const TempPath file("loader_parent_is_a_file.txt", "x");
    auto const parent = validate_output_parent_dir(file.path / "out.xlsx");
    REQUIRE_FALSE(parent.has_value());
    CHECK_THAT(std::string{parent.error().message()},
               ContainsSubstring("Parent path is not a directory"));
}

TEST_CASE("the archive walker steps over a name longer than a byte holds", "[loader][zip]") {
    // A name length past 255 sets the high byte of its 16-bit field, which a
    // reader assembling the field from the low byte alone would misplace the
    // entry after it by.
    TempPath f("loader_long_name.xlsx");
    ZipImage z;
    constexpr auto half = static_cast<std::uint32_t>(max_dbc_text_bytes / 2);
    z.cd_entry(half + 1, 300, 0, 0);
    z.cd_entry(half, 0, 0, 0);
    auto const cd_size = static_cast<std::uint32_t>(z.bytes.size());
    z.eocd(2, cd_size, 0);
    z.write(f.path);
    auto const r = check_xlsx_uncompressed_bound(f.path);
    REQUIRE_FALSE(r.has_value());
    REQUIRE(r.error().bound_info().has_value());
    CHECK(r.error().bound_info()->observed == (std::uint64_t{half} * 2) + 1);
}
