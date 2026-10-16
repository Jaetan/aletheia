// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// The stability harness's reads: the run's size from its count variables, and
// the snapshot of the process's resources with the reads it is made of. A read
// that cannot answer a count, because its file or directory does not open, its
// field is missing or its value is not a whole number in range, answers why
// instead: a zero read at both snapshots is a drift of zero, which every gate
// passes, and a count read as its default sizes a run nobody asked for. Each
// read takes what it reads, a path, a text or the calls it makes, so a test
// plants its own.
#pragma once

#include "aletheia/detail/checked.hpp"

#include <algorithm>
#include <cerrno>
#include <charconv>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <expected>
#include <filesystem>
#include <format>
#include <fstream>
#include <iterator>
#include <limits>
#include <malloc.h>
#include <memory>
#include <optional>
#include <ranges>
#include <string>
#include <string_view>
#include <system_error>

namespace aletheia::bench {

// A count, or why the read could not answer one.
using Reading = std::expected<std::int64_t, std::string>;

// What one snapshot holds; the harness judges the drift between two.
struct Snapshot {
    std::int64_t rss_bytes;
    std::int64_t fd_count;
    std::int64_t active_thread_count;
    std::int64_t malloc_info_bytes;
};

// The refusal of a read of `source`, in the shape every read's takes.
inline auto refused(std::string_view source, std::string_view reason)
    -> std::unexpected<std::string> {
    return std::unexpected(std::format("reading {}: {}", source, reason));
}

// The value `text` spells when the whole of it is a whole number that fits.
inline auto whole_number(std::string_view text) -> std::optional<std::int64_t> {
    std::int64_t value = 0;
    auto const* const last = std::to_address(text.end());
    auto const [end, ec] = std::from_chars(std::to_address(text.begin()), last, value);
    if (ec != std::errc{} || end != last || value < 0)
        return std::nullopt;
    return value;
}

// The largest count a count variable sets: the harness holds its counts in an
// int.
inline constexpr auto k_count_max = std::numeric_limits<int>::max();

// The count `text`, the value of the variable `name`, sets: ASCII digits only,
// from 1 to k_count_max. Anything else answers why it sets none.
inline auto count_setting(std::string_view name, std::string_view text)
    -> std::expected<int, std::string> {
    if (auto const value = whole_number(text);
        value && value.value() >= 1 && value.value() <= k_count_max)
        return static_cast<int>(value.value());
    return std::unexpected(
        std::format("{} must be a whole number from 1 to {}, got '{}'", name, k_count_max, text));
}

// The number after `field` ("VmRSS:" or "Threads:") on its line of the status
// file at `status`, up to the blank before its unit.
inline auto status_field(const std::filesystem::path& status, std::string_view field) -> Reading {
    std::ifstream in(status);
    if (!in)
        return refused(status.string(), "the file does not open");
    const std::string text{std::istreambuf_iterator<char>{in}, std::istreambuf_iterator<char>{}};
    auto lines = text | std::views::split('\n') |
                 std::views::transform([](auto const line) { return std::string_view{line}; });
    auto const line = std::ranges::find_if(
        lines, [field](std::string_view candidate) { return candidate.starts_with(field); });
    if (line == lines.end())
        return refused(status.string(), std::format("no {} line", field));
    auto value = (*line).substr(field.size());
    value = value.substr(std::min(value.find_first_not_of(" \t"), value.size()));
    if (auto const number = whole_number(value.substr(0, value.find_first_of(" \t"))))
        return number.value();
    return refused(status.string(), std::format("{} reads '{}', not a whole number", field, value));
}

// The entries of the descriptor directory `dir` that name a real resource (a
// regular file, a pipe, a socket): the things a forgotten close leaks. An
// anon_inode target (eventfd, eventpoll, timerfd, signalfd) is I/O multiplexer
// machinery the GHC RTS and glibc allocate lazily as the workload grows, and
// counting it defeats a hard-zero gate.
inline auto fd_count(const std::filesystem::path& dir) -> Reading {
    std::error_code ec;
    std::int64_t count = 0;
    for (std::filesystem::directory_iterator it(dir, ec);
         it != std::filesystem::directory_iterator{}; it.increment(ec)) {
        // An entry that no longer reads as a link is a descriptor closed
        // between the listing and the read.
        std::error_code link_ec;
        auto const target = std::filesystem::read_symlink(it->path(), link_ec);
        if (link_ec || target.string().starts_with("anon_inode:"))
            continue;
        ++count;
    }
    // A listing that fails, at its start or part way, ends the loop with `ec`
    // set.
    if (ec)
        return refused(dir.string(), ec.message());
    return count;
}

// The bytes glibc's malloc_info reports in `xml`: one <heap> element per
// arena, each with its own <total> entries, followed by the process-wide
// aggregate after the last </heap>, or from the start when there is none. Only
// the aggregate is summed; summing every <total> would count the arena bytes
// twice. Imperfect but stable enough to gate fragmentation drift.
inline auto malloc_info_total(std::string_view xml) -> Reading {
    constexpr std::string_view source = "malloc_info";
    constexpr std::string_view size_attribute = R"(size=")";
    auto const last_heap = xml.rfind("</heap>");
    auto const aggregate = xml.substr(last_heap == std::string_view::npos ? 0 : last_heap);
    std::int64_t total = 0;
    bool counted = false;
    // Each tag of the aggregate, as the text after its '<'.
    for (auto const piece : aggregate | std::views::split('<')) {
        const std::string_view tag(piece.begin(), piece.end());
        if (!tag.starts_with("total type="))
            continue;
        // The element up to its closing '>', or up to the next tag.
        auto const element = tag.substr(0, tag.find('>'));
        auto const size_at = element.find(size_attribute);
        if (size_at == std::string_view::npos)
            return refused(source, std::format("'<{}' carries no size", element));
        auto const digits = element.substr(size_at + size_attribute.size());
        auto const size = whole_number(digits.substr(0, digits.find('"')));
        if (!size)
            return refused(source,
                           std::format("'<{}' carries a size that is not a whole number", element));
        if (size.value() > std::numeric_limits<std::int64_t>::max() - total)
            return refused(source, "the <total> sizes add up past a 64-bit count");
        total += size.value();
        counted = true;
    }
    if (!counted)
        return refused(source, "no <total> after the last </heap>");
    return total;
}

// The two glibc calls malloc_info_bytes makes, open_memstream's and
// malloc_info's, as pointers a test replaces.
using OpenStream = FILE* (*)(char**, std::size_t*);
using WriteMallocInfo = int (*)(int, FILE*);

// The process's malloc_info total, written through a memory stream.
inline auto malloc_info_bytes(OpenStream open = &open_memstream,
                              WriteMallocInfo write = &malloc_info) -> Reading {
    constexpr std::string_view source = "malloc_info";
    char* text = nullptr;
    std::size_t size = 0;
    std::unique_ptr<FILE, decltype(&std::fclose)> stream(open(&text, &size), &std::fclose);
    if (stream == nullptr)
        return refused(source, std::format("open_memstream failed: {}",
                                           std::generic_category().message(errno)));
    auto const written = write(0, stream.get());
    auto const write_error = errno;
    // Closing the stream publishes its buffer into `text` and `size`, whether
    // or not the write succeeded, so the buffer is owned from here on.
    stream.reset();
    const std::unique_ptr<char, decltype(&std::free)> text_owner(text, &std::free);
    if (written != 0)
        return refused(source, std::format("malloc_info failed: {}",
                                           std::generic_category().message(write_error)));
    return malloc_info_total({text, size});
}

// One snapshot: the resident set and the thread count from the status file at
// `status`, the descriptors listed in `fds` and malloc_info's total, read
// through `open` and `write` as malloc_info_bytes reads it. VmRSS counts kB and
// the snapshot holds bytes, so a VmRSS past a 64-bit count of bytes answers no
// count. The first of those reads that answers no count is the snapshot's
// refusal.
inline auto take_snapshot(const std::filesystem::path& status, const std::filesystem::path& fds,
                          OpenStream open = &open_memstream, WriteMallocInfo write = &malloc_info)
    -> std::expected<Snapshot, std::string> {
    constexpr std::int64_t bytes_per_kib = 1024;
    auto const rss =
        status_field(status, "VmRSS:").and_then([&status](std::int64_t kib) -> Reading {
            if (kib > std::numeric_limits<std::int64_t>::max() / bytes_per_kib)
                return refused(status.string(), "VmRSS: in bytes is past a 64-bit count");
            return kib * bytes_per_kib;
        });
    auto const descriptors = fd_count(fds);
    auto const threads = status_field(status, "Threads:");
    auto const heap = malloc_info_bytes(open, write);
    for (auto const& read : {rss, descriptors, threads, heap})
        if (!read)
            return std::unexpected(aletheia::detail::error_of(read));
    return Snapshot{
        .rss_bytes = rss.value(),
        .fd_count = descriptors.value(),
        .active_thread_count = threads.value(),
        .malloc_info_bytes = heap.value(),
    };
}

} // namespace aletheia::bench
