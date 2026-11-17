// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// Long-run resource-leakage stability harness.
//
// Exercises the FFI surface for cycles × frames (default 10 × 100_000 = 1M
// total frames) and asserts no per-iteration drift on:
//
//   - FD count (hard zero): /proc/self/fd, anon_inode filtered
//   - active_thread_count (hard zero): /proc/self/status Threads
//   - kernel_allocation (equal per cycle): the bytes the kernel allocates in
//     each measured cycle, the same in every cycle, so a cycle doing more work
//     than the one before it fails
//
// Per the long-run resource-leakage sub-checks in AGENTS/cpp.md, drift on any
// sub-check is a finding.  Every gate is an exact count, so the runner's speed
// and load decide nothing.  The resident set (/proc/self/status VmRSS) and
// glibc's malloc_info total are reported beside them and decide nothing: they
// move with when the collectors run.  The reads live in
// stability_snapshot.hpp and the gates in stability_report.hpp.  The process tests
// in cpp/tests/stability_bench_tests.cpp hold the exit statuses below, among
// them a run that leaks a descriptor between the snapshots failing the FD gate.
//
// Output: JSON to stdout (and optionally
// benchmarks/stability/<commit>/cpp.json when invoked through
// tools/stability_run.py).  The exit status is that runner's contract: 0 when
// every gate passed, 1 when one failed and the verdict is in the report, and 2
// for a run with no verdict, such as a refused count, a library the search
// refuses, a failed warm-up, cycle or snapshot, or a report that cannot be
// written.
//
// Linux-specific (relies on /proc and glibc malloc_info).

#include "measure.hpp"
#include "stability_report.hpp"
#include "stability_snapshot.hpp"

#include <aletheia/aletheia.hpp>
#include <aletheia/detail/checked.hpp>

#include <algorithm>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <exception>
#include <expected>
#include <filesystem>
#include <format>
#include <limits>
#include <print>
#include <ranges>
#include <stdexcept>
#include <stop_token>
#include <string>
#include <vector>

namespace {

// Warmup cycles before the measurement window opens.  The first cycles a
// process runs allocate more in the kernel than every later one, and the
// resident set the report prints settles around the seventh cycle of 100k
// frames.
constexpr int k_warmup_cycles = 7;

} // namespace

using aletheia::bench::all_passed;
using aletheia::bench::build_sub_checks;
using aletheia::bench::report_text;
using aletheia::bench::Snapshot;
using aletheia::bench::write_report_text;

// The snapshot of this process the gates judge, or the read that refused it.
static auto snapshot_self() -> std::expected<Snapshot, std::string> {
    return aletheia::bench::take_snapshot("/proc/self/status", "/proc/self/fd");
}

// The bytes the kernel has allocated, or why they cannot be read.
static auto kernel_allocated() -> std::expected<std::int64_t, std::string> {
    auto const count = aletheia::allocated_bytes();
    if (!count)
        return std::unexpected("reading the kernel's allocated bytes: the runtime is not running");
    if (*count > static_cast<std::uint64_t>(std::numeric_limits<std::int64_t>::max()))
        return std::unexpected(std::format(
            "reading the kernel's allocated bytes: {} bytes, past the int64 the gate compares",
            *count));
    return static_cast<std::int64_t>(*count);
}

// minimal_dbc constructs a single-message DBC sufficient for parse_dbc +
// start_stream to succeed.  Mirrors the make_can20_dbc helper in
// cpp/benchmarks/benchmark_fixtures.cpp but trimmed to one signal so the harness
// measures resource accounting, not Stream LTL semantics.
static auto minimal_dbc() -> aletheia::DbcDefinition {
    using aletheia::AlwaysPresent, aletheia::BitLength, aletheia::BitPosition, aletheia::ByteOrder,
        aletheia::CanId, aletheia::DbcDefinition, aletheia::DbcMessage, aletheia::DbcSignal,
        aletheia::Dlc, aletheia::MessageName, aletheia::NodeName, aletheia::Rational,
        aletheia::RationalBound, aletheia::RationalFactor, aletheia::RationalOffset,
        aletheia::SignalName, aletheia::StandardId, aletheia::Unit;
    DbcSignal const engine_speed{
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
    DbcMessage const engine_msg{
        .id = CanId{StandardId::create(0x100).value()},
        .name = MessageName{"EngineStatus"},
        .dlc = Dlc::create(8).value(),
        .sender = NodeName{"ECU1"},
        .signals = {engine_speed},
    };
    return DbcDefinition{.version = "", .messages = {engine_msg}};
}

static void run_cycle(std::filesystem::path const& lib, aletheia::DbcDefinition const& dbc,
                      int frames_per_cycle) {
    using aletheia::AletheiaClient, aletheia::CanId, aletheia::Dlc, aletheia::FramePayload,
        aletheia::IBackend, aletheia::make_ffi_backend, aletheia::StandardId, aletheia::Timestamp;
    using aletheia::bench::require, aletheia::bench::value_or_throw;
    auto client = value_or_throw(AletheiaClient::open({.library = lib}));
    require(client.parse_dbc(std::stop_token{}, dbc), "parse_dbc");
    require(client.start_stream(std::stop_token{}), "start_stream");

    constexpr auto id = CanId{StandardId::create(0x100).value()};
    constexpr auto dlc = Dlc::create(8).value();
    FramePayload const frame{std::byte{0x40}, std::byte{0x1F}, std::byte{0x82}, std::byte{0x00},
                             std::byte{0x00}, std::byte{0x00}, std::byte{0x00}, std::byte{0x00}};
    for (auto const i : std::views::iota(0, frames_per_cycle))
        require(client.send_frame(std::stop_token{}, Timestamp{i}, id, dlc, frame), "send_frame");
    require(client.end_stream(std::stop_token{}), "end_stream");
    // ~AletheiaClient runs here; backend dlcloses the .so handle if it was
    // the last reference.
}

// A count variable is unset, and its default applies, or sets a count as
// count_setting reads one; anything else is a setup error, never a silent
// fallback to the default.
static auto env_count(char const* name, int default_value) -> int {
    char const* const env = std::getenv(name);
    if (env == nullptr)
        return default_value;
    auto const count = aletheia::bench::count_setting(name, env);
    if (!count)
        throw std::runtime_error(aletheia::detail::error_of(count));
    return count.value();
}

static auto run() -> int {
    int cycles = 0;
    int frames = 0;
    try {
        cycles = env_count("ALETHEIA_STABILITY_CYCLES", 10);
        frames = env_count("ALETHEIA_STABILITY_FRAMES", 100000);
    } catch (std::exception const& e) {
        std::println(stderr, "setup: {}", e.what());
        return 2;
    }
    auto const found = aletheia::find_ffi_library();
    if (!found) {
        std::println(stderr, "setup: {}", aletheia::detail::error_of(found).text());
        return 2;
    }
    auto const& lib = found.value();
    auto const dbc = minimal_dbc();

    // Multi-cycle warmup to absorb the GHC RTS heap warmup + lazy MAlonzo /
    // Agda structure realization.  See k_warmup_cycles for empirical rationale.
    try {
        std::ranges::for_each(std::views::repeat(0, k_warmup_cycles),
                              [&](auto) { run_cycle(lib, dbc, frames); });
    } catch (std::exception const& e) {
        std::println(stderr, "warm-up: {}", e.what());
        return 2;
    }

    auto const start = snapshot_self();
    if (!start) {
        std::println(stderr, "the opening snapshot failed: {}", aletheia::detail::error_of(start));
        return 2;
    }
    auto const first = kernel_allocated();
    if (!first) {
        std::println(stderr, "the opening snapshot failed: {}", aletheia::detail::error_of(first));
        return 2;
    }
    std::vector<std::int64_t> readings{first.value()};
    auto const t0 = std::chrono::steady_clock::now();

    for (auto const i : std::views::iota(0, cycles)) {
        try {
            run_cycle(lib, dbc, frames);
        } catch (std::exception const& e) {
            std::println(stderr, "cycle {}: {}", i, e.what());
            return 2;
        }
        auto const reading = kernel_allocated();
        if (!reading) {
            std::println(stderr, "cycle {}: {}", i, aletheia::detail::error_of(reading));
            return 2;
        }
        readings.push_back(reading.value());
    }

    auto const end = snapshot_self();
    if (!end) {
        std::println(stderr, "the closing snapshot failed: {}", aletheia::detail::error_of(end));
        return 2;
    }
    auto const elapsed =
        std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();

    auto const sub_checks = build_sub_checks(start.value(), end.value(), readings);
    if (auto const written =
            write_report_text(stdout, report_text(cycles, frames, elapsed, sub_checks));
        !written) {
        std::println(stderr, "writing the report failed: {}", aletheia::detail::error_of(written));
        return 2;
    }
    return all_passed(sub_checks) ? 0 : 1;
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
