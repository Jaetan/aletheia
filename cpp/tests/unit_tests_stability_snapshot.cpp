// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// Unit tests: the stability harness's reads answer a count or why they could
// not, and a zero only when zero is what they read. Each read but
// malloc_info_bytes's default calls, which one case leaves on glibc's own to
// read this process's report, is pointed at files and text planted here, so no
// case depends on what the host's /proc holds.
#include "stability_snapshot.hpp"
#include "temp_path.hpp"

#include <aletheia/detail/checked.hpp>

#include <catch2/catch_test_macros.hpp>
#include <catch2/generators/catch_generators.hpp>

#include <cerrno>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <filesystem>
#include <format>
#include <fstream>
#include <string>
#include <system_error>

using aletheia::bench::count_setting;
using aletheia::bench::fd_count;
using aletheia::bench::malloc_info_bytes;
using aletheia::bench::malloc_info_total;
using aletheia::bench::status_field;
using aletheia::bench::take_snapshot;
using aletheia::test::AsDirectory;
using aletheia::test::scratch_dir;
using aletheia::test::TempPath;

namespace {

// /proc/self/status's shape, trimmed to a line around the two that are read.
constexpr auto status_text = "Name:\tstability\nVmRSS:\t    7564 kB\nThreads:\t3\n";

// malloc_info's shape: an arena's own totals, then the aggregate after the
// last </heap>, which sums to 135200.
constexpr auto malloc_xml = R"(<malloc version="1">
<heap nr="0">
<total type="rest" count="1" size="1000"/>
</heap>
<total type="fast" count="0" size="0"/>
<total type="rest" count="1" size="135152"/>
<total type="mmap" count="2" size="48"/>
<system type="current" size="139264"/>
</malloc>
)";

} // namespace

// Stands in for malloc_info, writing the planted text, and refuses a stream
// that is not there, as a read that wrote through one would end the process.
static auto write_planted(int /*options*/, FILE* stream) -> int {
    if (stream == nullptr) {
        errno = EBADF;
        return -1;
    }
    return std::fputs(malloc_xml, stream) < 0 ? -1 : 0;
}

// Stands in for an open_memstream that cannot allocate its stream.
static auto open_fails(char** /*text*/, std::size_t* /*size*/) -> FILE* {
    errno = ENOMEM;
    return nullptr;
}

// Stands in for a malloc_info that refuses after writing part of its text.
static auto write_fails(int /*options*/, FILE* stream) -> int {
    static_cast<void>(std::fputs("<malloc", stream));
    errno = EINVAL;
    return -1;
}

// A descriptor directory as /proc/self/fd lists one: two links naming a
// resource, one naming runtime machinery, and an entry that does not read as
// a link, as a descriptor closed after the listing does not.
static void plant_descriptors(std::filesystem::path const& dir) {
    std::filesystem::create_symlink("/dev/null", dir / "0");
    std::filesystem::create_symlink("pipe:[4242]", dir / "1");
    std::filesystem::create_symlink("anon_inode:[eventfd]", dir / "2");
    std::ofstream{dir / "3"}.close();
}

TEST_CASE("count_setting reads a whole number from 1 to the top of an int",
          "[benchmark][stability]") {
    auto const [text, count] = GENERATE(
        table<std::string, int>({{"1", 1}, {"100000", 100000}, {"2147483647", 2147483647}}));
    CHECK(count_setting("ALETHEIA_STABILITY_CYCLES", text) == count);
}

TEST_CASE("count_setting refuses anything else, naming the variable and the bound",
          "[benchmark][stability]") {
    auto const text = GENERATE(as<std::string>{}, "0", "-0", "-3", "+5", " 5", "5 ", "5x", "",
                               "abc", "2147483648", "99999999999999999999");
    auto const count = count_setting("ALETHEIA_STABILITY_FRAMES", text);
    REQUIRE_FALSE(count.has_value());
    CHECK(aletheia::detail::error_of(count) ==
          std::format(
              "ALETHEIA_STABILITY_FRAMES must be a whole number from 1 to 2147483647, got '{}'",
              text));
}

TEST_CASE("status_field reads the whole number after its field, before the unit",
          "[benchmark][stability]") {
    TempPath const status("stability_status", status_text);
    CHECK(status_field(status.path, "VmRSS:") == 7564);
    CHECK(status_field(status.path, "Threads:") == 3);
}

TEST_CASE("status_field reads a zero as the count it is", "[benchmark][stability]") {
    TempPath const status("stability_status", "Threads:\t0\n");
    CHECK(status_field(status.path, "Threads:") == 0);
}

TEST_CASE("status_field refuses a file that does not open, naming it", "[benchmark][stability]") {
    TempPath const missing("stability_no_status");
    auto const read = status_field(missing.path, "VmRSS:");
    REQUIRE_FALSE(read.has_value());
    CHECK(read.error() == std::format("reading {}: the file does not open", missing.string()));
}

TEST_CASE("status_field refuses a file without the field", "[benchmark][stability]") {
    TempPath const status("stability_status", "Name:\tstability\nThreads:\t3\n");
    auto const read = status_field(status.path, "VmRSS:");
    REQUIRE_FALSE(read.has_value());
    CHECK(read.error() == std::format("reading {}: no VmRSS: line", status.string()));
}

TEST_CASE("status_field refuses a value that is not a whole number", "[benchmark][stability]") {
    auto const value = GENERATE(as<std::string>{}, "abc", "", "-3", "12x", "99999999999999999999");
    TempPath const status("stability_status", std::format("Threads:\t{}\n", value));
    auto const read = status_field(status.path, "Threads:");
    REQUIRE_FALSE(read.has_value());
    CHECK(read.error() == std::format("reading {}: Threads: reads '{}', not a whole number",
                                      status.string(), value));
}

TEST_CASE("fd_count counts the links that name a resource", "[benchmark][stability]") {
    TempPath const dir(scratch_dir() / "stability_fd", AsDirectory{});
    plant_descriptors(dir.path);
    CHECK(fd_count(dir.path) == 2);
}

TEST_CASE("fd_count reads an empty listing as zero descriptors", "[benchmark][stability]") {
    TempPath const dir(scratch_dir() / "stability_fd", AsDirectory{});
    CHECK(fd_count(dir.path) == 0);
}

TEST_CASE("fd_count refuses a directory that does not list, naming it", "[benchmark][stability]") {
    TempPath const missing("stability_no_fd");
    auto const read = fd_count(missing.path);
    REQUIRE_FALSE(read.has_value());
    CHECK(read.error() ==
          std::format("reading {}: {}", missing.string(),
                      std::make_error_code(std::errc::no_such_file_or_directory).message()));
}

TEST_CASE("malloc_info_total sums the aggregate after the last heap", "[benchmark][stability]") {
    CHECK(malloc_info_total(malloc_xml) == 135200);
}

TEST_CASE("malloc_info_total sums from the start of a text with no heap",
          "[benchmark][stability]") {
    CHECK(malloc_info_total(R"(<total type="rest" size="5"/><total type="mmap" size="7"/>)") == 12);
}

TEST_CASE("malloc_info_total sums only the elements named total", "[benchmark][stability]") {
    CHECK(malloc_info_total(
              R"(</heap><total type="rest" size="5"/><totals type="rest" size="7"/>)") == 5);
}

TEST_CASE("malloc_info_total reads zero sizes as the count they are", "[benchmark][stability]") {
    CHECK(malloc_info_total(R"(</heap><total type="rest" size="0"/>)") == 0);
}

TEST_CASE("malloc_info_total accepts a total at the top of the range", "[benchmark][stability]") {
    CHECK(malloc_info_total(R"(</heap><total type="rest" size="9223372036854775807"/>)") ==
          9223372036854775807);
}

TEST_CASE("malloc_info_total refuses a text with no aggregate", "[benchmark][stability]") {
    auto const read = malloc_info_total(R"(<heap><total type="rest" size="5"/></heap>)");
    REQUIRE_FALSE(read.has_value());
    CHECK(read.error() == "reading malloc_info: no <total> after the last </heap>");
}

TEST_CASE("malloc_info_total refuses a total without a size", "[benchmark][stability]") {
    auto const read = malloc_info_total(
        R"(</heap><total type="rest" count="1"/><system type="current" size="9"/>)");
    REQUIRE_FALSE(read.has_value());
    CHECK(read.error() ==
          R"(reading malloc_info: '<total type="rest" count="1"/' carries no size)");
}

TEST_CASE("malloc_info_total refuses a size that is not a whole number", "[benchmark][stability]") {
    auto const element = GENERATE(
        as<std::string>{}, R"(<total type="rest" size="12x"/)", R"(<total type="rest" size=""/)",
        R"(<total type="rest" size="-3"/)", R"(<total type="rest" size="5/)");
    auto const read = malloc_info_total(std::format("</heap>{}>", element));
    REQUIRE_FALSE(read.has_value());
    CHECK(read.error() == std::format("reading malloc_info: '{}' carries a size that is not a "
                                      "whole number",
                                      element));
}

TEST_CASE("malloc_info_total refuses totals that add up past the count's range",
          "[benchmark][stability]") {
    auto const read = malloc_info_total(R"(</heap><total type="rest" size="9223372036854775807"/>)"
                                        R"(<total type="mmap" size="1"/>)");
    REQUIRE_FALSE(read.has_value());
    CHECK(read.error() == "reading malloc_info: the <total> sizes add up past a 64-bit count");
}

TEST_CASE("malloc_info_bytes reads the text the stream was given", "[benchmark][stability]") {
    CHECK(malloc_info_bytes(&open_memstream, &write_planted) == 135200);
}

TEST_CASE("malloc_info_bytes reads this process's own report", "[benchmark][stability]") {
    CHECK(malloc_info_bytes().has_value());
}

TEST_CASE("malloc_info_bytes refuses a stream that does not open", "[benchmark][stability]") {
    auto const read = malloc_info_bytes(&open_fails, &write_planted);
    REQUIRE_FALSE(read.has_value());
    CHECK(read.error() == std::format("reading malloc_info: open_memstream failed: {}",
                                      std::generic_category().message(ENOMEM)));
}

TEST_CASE("malloc_info_bytes refuses a report that fails", "[benchmark][stability]") {
    auto const read = malloc_info_bytes(&open_memstream, &write_fails);
    REQUIRE_FALSE(read.has_value());
    CHECK(read.error() == std::format("reading malloc_info: malloc_info failed: {}",
                                      std::generic_category().message(EINVAL)));
}

TEST_CASE("take_snapshot holds each read, the resident set in bytes", "[benchmark][stability]") {
    TempPath const status("stability_status", status_text);
    TempPath const fds(scratch_dir() / "stability_fd", AsDirectory{});
    plant_descriptors(fds.path);
    auto const snapshot = take_snapshot(status.path, fds.path, &open_memstream, &write_planted);
    REQUIRE(snapshot.has_value());
    CHECK(snapshot->rss_bytes == std::int64_t{7564} * 1024);
    CHECK(snapshot->fd_count == 2);
    CHECK(snapshot->active_thread_count == 3);
    CHECK(snapshot->malloc_info_bytes == 135200);
}

TEST_CASE("take_snapshot holds a resident set at the top of a 64-bit count of bytes",
          "[benchmark][stability]") {
    TempPath const status("stability_status", "VmRSS:\t9007199254740991 kB\nThreads:\t3\n");
    TempPath const fds(scratch_dir() / "stability_fd", AsDirectory{});
    auto const snapshot = take_snapshot(status.path, fds.path, &open_memstream, &write_planted);
    REQUIRE(snapshot.has_value());
    CHECK(snapshot.value().rss_bytes == std::int64_t{9007199254740991} * 1024);
}

TEST_CASE("take_snapshot refuses a resident set past a 64-bit count of bytes",
          "[benchmark][stability]") {
    TempPath const status("stability_status", "VmRSS:\t9007199254740992 kB\nThreads:\t3\n");
    TempPath const fds(scratch_dir() / "stability_fd", AsDirectory{});
    auto const snapshot = take_snapshot(status.path, fds.path, &open_memstream, &write_planted);
    REQUIRE_FALSE(snapshot.has_value());
    CHECK(aletheia::detail::error_of(snapshot) ==
          std::format("reading {}: VmRSS: in bytes is past a 64-bit count", status.string()));
}

TEST_CASE("take_snapshot refuses with the first read that answers no count",
          "[benchmark][stability]") {
    TempPath const status("stability_status", "VmRSS:\t7564 kB\n");
    TempPath const fds(scratch_dir() / "stability_fd", AsDirectory{});
    TempPath const missing("stability_no_status");
    TempPath const no_fds("stability_no_fd");
    auto const message = std::make_error_code(std::errc::no_such_file_or_directory).message();

    SECTION("the status file") {
        auto const snapshot = take_snapshot(missing.path, no_fds.path);
        REQUIRE_FALSE(snapshot.has_value());
        CHECK(snapshot.error() ==
              std::format("reading {}: the file does not open", missing.string()));
    }
    SECTION("the descriptor directory") {
        auto const snapshot = take_snapshot(status.path, no_fds.path);
        REQUIRE_FALSE(snapshot.has_value());
        CHECK(snapshot.error() == std::format("reading {}: {}", no_fds.string(), message));
    }
    SECTION("the thread count") {
        auto const snapshot = take_snapshot(status.path, fds.path);
        REQUIRE_FALSE(snapshot.has_value());
        CHECK(snapshot.error() == std::format("reading {}: no Threads: line", status.string()));
    }
    SECTION("the malloc_info report") {
        TempPath const complete("stability_complete_status", status_text);
        auto const snapshot = take_snapshot(complete.path, fds.path, &open_fails, &write_planted);
        REQUIRE_FALSE(snapshot.has_value());
        CHECK(snapshot.error() == std::format("reading malloc_info: open_memstream failed: {}",
                                              std::generic_category().message(ENOMEM)));
    }
}
