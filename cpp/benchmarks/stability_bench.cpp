// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// Long-run resource-leakage stability harness.
//
// Exercises the FFI surface for cycles × frames (default 10 × 100_000 = 1M
// total frames) and asserts no per-iteration drift on:
//
//   - RSS (soft threshold)         — /proc/self/status VmRSS
//   - FD count (hard zero)         — /proc/self/fd, anon_inode filtered
//   - active_thread_count (hard zero)
//                                  — /proc/self/status Threads
//   - malloc_info (soft threshold) — glibc malloc_info(0, FILE*) total bytes
//
// Per the long-run resource-leakage sub-checks in AGENTS/cpp.md, drift on any
// sub-check is a finding.  Hard-zero gates are exact equality (no noise
// tolerance allowed); soft-threshold gates carry an empirically-tuned cap
// inline below, so changing the value makes the diff visible.  A probe under
// probes/ compiles a variant that leaks one descriptor per cycle and checks
// that the FD gate fails on it.
//
// Output: JSON to stdout (and optionally
// benchmarks/stability/<commit>/cpp.json when invoked through
// tools/stability_run.py).
//
// Linux-specific (relies on /proc and glibc malloc_info).

#include <aletheia/aletheia.hpp>

#include <algorithm>
#include <charconv>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <exception>
#include <filesystem>
#include <format>
#include <fstream>
#include <malloc.h>
#include <memory>
#include <print>
#include <ranges>
#include <stdexcept>
#include <stop_token>
#include <string>
#include <string_view>
#include <system_error>
#include <vector>

namespace {

// Soft-threshold caps, established empirically on a quiet WSL2 host; revise
// inline if a host rejects them as too tight or too loose.
constexpr std::int64_t k_rss_delta_bytes_cap = 50LL * 1024 * 1024;    // 50 MiB
constexpr std::int64_t k_malloc_delta_bytes_cap = 50LL * 1024 * 1024; // 50 MiB

// Warmup cycles before the measurement window opens.  The GHC RTS heap,
// MAlonzo dictionaries and lazy Agda structures need a substantial workload
// before they reach steady state: measured, the heap plateaus around the
// seventh cycle of 100k frames, and a warmup of a few hundred frames leaves
// on the order of 138 MiB of RTS growth inside the measurement window.  Seven
// cycles give at least 30 MiB of headroom under the 50 MiB cap without pushing
// the bench beyond a few seconds of wall time.
constexpr int k_warmup_cycles = 7;

struct Snapshot {
    std::int64_t rss_bytes;
    std::int64_t fd_count;
    std::int64_t active_thread_count;
    std::int64_t malloc_info_bytes;
};

struct SubCheck {
    std::string name;
    std::string gate; // "hard_zero" or "soft_threshold"
    std::int64_t start;
    std::int64_t end;
    std::int64_t delta;
    std::int64_t threshold;
    bool passed;
};

} // namespace

// Parse a /proc/self/status field (e.g., "VmRSS:" or "Threads:"): the number
// that follows the label.
static auto parse_status_field(std::string_view field) -> std::int64_t {
    std::ifstream status("/proc/self/status");
    for (std::string line; std::getline(status, line);) {
        if (!line.starts_with(field))
            continue;
        auto digits = std::string_view{line}.substr(field.size());
        digits.remove_prefix(std::min(digits.find_first_not_of(" \t"), digits.size()));
        std::int64_t value = 0;
        [[maybe_unused]] auto const read =
            std::from_chars(std::to_address(digits.begin()), std::to_address(digits.end()), value);
        return value;
    }
    return 0;
}

static auto vm_rss_bytes() -> std::int64_t {
    return parse_status_field("VmRSS:") * 1024; // VmRSS is in kB
}

static auto threads_count() -> std::int64_t {
    return parse_status_field("Threads:");
}

// Count /proc/self/fd entries that point to real resources (regular files,
// pipes, sockets) — the things a forgotten Close can leak.  Excludes
// anon_inode targets (eventfd/eventpoll/timerfd/signalfd) which are runtime
// I/O multiplexer machinery the GHC RTS / glibc allocate lazily based on
// workload.  Counting them defeats hard-zero gating.
static auto fd_count() -> std::int64_t {
    std::int64_t count = 0;
    std::error_code ec;
    for (auto const& entry : std::filesystem::directory_iterator("/proc/self/fd", ec)) {
        if (ec) {
            continue;
        }
        std::error_code link_ec;
        auto const target = std::filesystem::read_symlink(entry, link_ec);
        if (link_ec) {
            continue;
        }
        auto const target_str = target.string();
        if (target_str.starts_with("anon_inode:")) {
            continue;
        }
        ++count;
    }
    return count;
}

// glibc malloc_info emits XML to a FILE*: one <heap> element per arena, each
// with its own <total type="fast"/> and <total type="rest"/>, followed by the
// process-wide aggregate (<total> entries for fast, rest and mmap) after the
// last </heap>.  Only the aggregate is summed; summing every <total> would
// count the arena bytes twice.  Imperfect but stable enough to gate
// fragmentation drift.
static auto malloc_info_bytes() -> std::int64_t {
    char* raw = nullptr;
    std::size_t raw_size = 0;
    const std::unique_ptr<char, decltype(&std::free)> buf_owner(nullptr, &std::free);
    std::string xml;
    {
        const std::unique_ptr<FILE, decltype(&std::fclose)> stream(open_memstream(&raw, &raw_size),
                                                                   &std::fclose);
        if (stream == nullptr)
            return 0;
        if (malloc_info(0, stream.get()) != 0)
            return 0;
        // open_memstream publishes raw/raw_size only once the stream is closed,
        // which the unique_ptr does at the end of this block.
    }
    const std::unique_ptr<char, decltype(&std::free)> raw_owner(raw, &std::free);
    xml.assign(raw, raw_size);

    const std::string_view view{xml};
    auto const last_heap = view.rfind("</heap>");
    std::int64_t total_bytes = 0;
    for (auto pos = last_heap == std::string_view::npos ? 0 : last_heap;
         (pos = view.find("<total type=", pos)) != std::string_view::npos;) {
        auto const size_attr = view.find("size=\"", pos);
        if (size_attr == std::string_view::npos)
            break;
        auto const value_start = size_attr + 6;
        auto const value_end = view.find('"', value_start);
        if (value_end == std::string_view::npos)
            break;
        std::int64_t value = 0;
        auto const digits = view.substr(value_start, value_end - value_start);
        [[maybe_unused]] auto const read =
            std::from_chars(std::to_address(digits.begin()), std::to_address(digits.end()), value);
        total_bytes += value;
        pos = value_end;
    }
    return total_bytes;
}

static auto take_snapshot() -> Snapshot {
    return Snapshot{
        .rss_bytes = vm_rss_bytes(),
        .fd_count = fd_count(),
        .active_thread_count = threads_count(),
        .malloc_info_bytes = malloc_info_bytes(),
    };
}

// minimal_dbc constructs a single-message DBC sufficient for parse_dbc +
// start_stream to succeed.  Mirrors the can20_dbc helper in
// cpp/benchmarks/benchmark.cpp but trimmed to one signal so the harness
// measures resource accounting, not Stream LTL semantics.
static auto minimal_dbc() -> aletheia::DbcDefinition {
    using aletheia::AlwaysPresent, aletheia::BitLength, aletheia::BitPosition, aletheia::ByteOrder,
        aletheia::CanId, aletheia::DbcDefinition, aletheia::DbcMessage, aletheia::DbcSignal,
        aletheia::Dlc, aletheia::MessageName, aletheia::NodeName, aletheia::Rational,
        aletheia::RationalBound, aletheia::RationalFactor, aletheia::RationalOffset,
        aletheia::SignalName, aletheia::StandardId, aletheia::Unit;
    DbcSignal engine_speed{
        .name = SignalName{"EngineSpeed"},
        .start_bit = BitPosition{0},
        .bit_length = BitLength{16},
        .byte_order = ByteOrder::LittleEndian,
        .is_signed = false,
        .factor = RationalFactor{Rational{1, 4}},
        .offset = RationalOffset{Rational{0, 1}},
        .minimum = RationalBound{Rational{0, 1}},
        .maximum = RationalBound{Rational{8000, 1}},
        .unit = Unit{"rpm"},
        .presence = AlwaysPresent{},
    };
    DbcMessage engine_msg{
        .id = CanId{StandardId::create(0x100).value()},
        .name = MessageName{"EngineStatus"},
        .dlc = Dlc::create(8).value(),
        .sender = NodeName{"ECU1"},
        .signals = {engine_speed},
    };
    return DbcDefinition{.version = "", .messages = {engine_msg}};
}

// A cycle that fails any step measures nothing, so every std::expected the
// client returns is checked and its error thrown.
template<typename T>
static void require(const aletheia::Result<T>& result, std::string_view step) {
    if (!result)
        throw std::runtime_error(std::format("{} failed: {}", step, result.error().message()));
}

static void run_cycle(const std::filesystem::path& lib, const aletheia::DbcDefinition& dbc,
                      int frames_per_cycle) {
    using aletheia::AletheiaClient, aletheia::CanId, aletheia::Dlc, aletheia::FramePayload,
        aletheia::make_ffi_backend, aletheia::StandardId, aletheia::Timestamp;
    AletheiaClient client(make_ffi_backend(lib));
    require(client.parse_dbc(std::stop_token{}, dbc), "parse_dbc");
    require(client.start_stream(std::stop_token{}), "start_stream");

    constexpr auto id = CanId{StandardId::create(0x100).value()};
    constexpr auto dlc = Dlc::create(8).value();
    const FramePayload frame{std::byte{0x40}, std::byte{0x1F}, std::byte{0x82}, std::byte{0x00},
                             std::byte{0x00}, std::byte{0x00}, std::byte{0x00}, std::byte{0x00}};
    for (auto const i : std::views::iota(0, frames_per_cycle))
        require(client.send_frame(std::stop_token{}, Timestamp{i}, id, dlc, frame), "send_frame");
    require(client.end_stream(std::stop_token{}), "end_stream");
    // ~AletheiaClient runs here; backend dlcloses the .so handle if it was
    // the last reference.
}

// The binding's one search. This used to return a single relative path without
// checking it exists, so a run from the wrong directory failed at the load
// rather than at the search.
static auto find_library() -> std::filesystem::path {
    return aletheia::find_ffi_library();
}

// A count variable is unset (default applies) or a positive whole number;
// anything else is a setup error, never a silent fallback to the default.
static auto env_count(const char* name, int default_value) -> int {
    const char* env = std::getenv(name);
    if (env == nullptr)
        return default_value;
    const std::string_view text{env};
    int value = 0;
    auto const* const last = std::to_address(text.end());
    auto [end, ec] = std::from_chars(std::to_address(text.begin()), last, value);
    if (ec != std::errc{} || end != last || value <= 0)
        throw std::runtime_error(
            std::format("{} must be a positive whole number, got '{}'", name, text));
    return value;
}

static void emit_sub_check_json(const SubCheck& c, bool first) {
    std::print("{}    {{\n"
               "      \"name\": \"{}\",\n"
               "      \"gate\": \"{}\",\n"
               "      \"start\": {},\n"
               "      \"end\": {},\n"
               "      \"delta\": {},\n"
               "      \"threshold\": {},\n"
               "      \"passed\": {}\n"
               "    }}",
               first ? "" : ",\n", c.name, c.gate, c.start, c.end, c.delta, c.threshold, c.passed);
}

// Each resource the harness watches, as the pair of snapshots it is judged on.
static auto build_sub_checks(const Snapshot& start, const Snapshot& end) -> std::vector<SubCheck> {
    return {
        {.name = "rss",
         .gate = "soft_threshold",
         .start = start.rss_bytes,
         .end = end.rss_bytes,
         .delta = end.rss_bytes - start.rss_bytes,
         .threshold = k_rss_delta_bytes_cap,
         .passed = std::abs(end.rss_bytes - start.rss_bytes) <= k_rss_delta_bytes_cap},
        {.name = "fd_count",
         .gate = "hard_zero",
         .start = start.fd_count,
         .end = end.fd_count,
         .delta = end.fd_count - start.fd_count,
         .threshold = 0,
         .passed = end.fd_count == start.fd_count},
        {.name = "active_thread_count",
         .gate = "hard_zero",
         .start = start.active_thread_count,
         .end = end.active_thread_count,
         .delta = end.active_thread_count - start.active_thread_count,
         .threshold = 0,
         .passed = end.active_thread_count == start.active_thread_count},
        {.name = "malloc_info",
         .gate = "soft_threshold",
         .start = start.malloc_info_bytes,
         .end = end.malloc_info_bytes,
         .delta = end.malloc_info_bytes - start.malloc_info_bytes,
         .threshold = k_malloc_delta_bytes_cap,
         .passed =
             std::abs(end.malloc_info_bytes - start.malloc_info_bytes) <= k_malloc_delta_bytes_cap},
    };
}

static auto run() -> int {
    int cycles = 0;
    int frames = 0;
    try {
        cycles = env_count("ALETHEIA_STABILITY_CYCLES", 10);
        frames = env_count("ALETHEIA_STABILITY_FRAMES", 100000);
    } catch (const std::exception& e) {
        std::println(stderr, "setup: {}", e.what());
        return 2;
    }
    auto const lib = find_library();
    auto const dbc = minimal_dbc();

    // Multi-cycle warmup to absorb the GHC RTS heap warmup + lazy MAlonzo /
    // Agda structure realization.  See k_warmup_cycles for empirical rationale.
    try {
        for ([[maybe_unused]] auto const cycle : std::views::repeat(0, k_warmup_cycles))
            run_cycle(lib, dbc, frames);
    } catch (const std::exception& e) {
        std::println(stderr, "warm-up: {}", e.what());
        return 2;
    }

    auto const start = take_snapshot();
    auto const t0 = std::chrono::steady_clock::now();

    for (auto const i : std::views::iota(0, cycles)) {
        try {
            run_cycle(lib, dbc, frames);
        } catch (const std::exception& e) {
            std::println(stderr, "cycle {}: {}", i, e.what());
            return 2;
        }
    }

    auto const end = take_snapshot();
    auto const elapsed =
        std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();

    auto const sub_checks = build_sub_checks(start, end);
    auto const all_passed = std::ranges::all_of(sub_checks, &SubCheck::passed);

    std::print("{{\n"
               "  \"binding\": \"cpp\",\n"
               "  \"cycles\": {},\n"
               "  \"frames_per_cycle\": {},\n"
               "  \"total_frames\": {},\n"
               "  \"elapsed_seconds\": {},\n"
               "  \"sub_checks\": [\n",
               cycles, frames, static_cast<std::int64_t>(cycles) * frames, elapsed);
    for (auto const [i, sub_check] : std::views::enumerate(sub_checks))
        emit_sub_check_json(sub_check, i == 0);
    std::print("\n  ],\n"
               "  \"passed\": {}\n"
               "}}\n",
               all_passed);

    return all_passed ? 0 : 1;
}

// Nothing leaves main: the lane that drives this binary reads its exit code,
// and an escaping exception would arrive as a signal instead.
auto main() -> int {
    try {
        return run();
    } catch (...) {
        return 2;
    }
}
