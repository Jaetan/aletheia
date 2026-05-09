// Long-run resource-leakage stability harness (R18 cluster 6 / C++ cat 26).
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
// Per AGENTS.md C++ cat 26 "Long-run resource leakage sub-checks": drift on
// any sub-check is a finding.  Hard-zero gates are exact equality (no noise
// tolerance allowed); soft-threshold gates carry an empirically-tuned cap
// inline below — change the value, the diff is visible.
//
// Output: JSON to stdout (and optionally
// benchmarks/stability/<commit>/cpp.json when invoked through
// tools/stability_run.py).
//
// Forward-revert verified 2026-05-08: introducing an intentional non-Close
// makes the harness fail with a precise FD-delta diagnostic; restoring
// brings it back to 0 drift.
//
// Linux-specific (relies on /proc and glibc malloc_info).

#include <aletheia/aletheia.hpp>

#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <malloc.h>
#include <sstream>
#include <stop_token>
#include <string>
#include <vector>

namespace {

// Soft-threshold caps (empirically established 2026-05-08, WSL2 quiet host;
// revise inline if a future reviewer runs the harness on a host that
// rejects these as too tight or too loose).
constexpr std::int64_t kRssDeltaBytesCap = 50LL * 1024 * 1024;    // 50 MiB
constexpr std::int64_t kMallocDeltaBytesCap = 50LL * 1024 * 1024; // 50 MiB

// Warmup cycles before the measurement window opens.  The GHC RTS heap +
// MAlonzo dictionaries + lazy Agda structures need a substantial workload
// before they reach steady state — empirical probe (2026-05-09 cluster 7
// orchestrator e2e) showed the heap plateaus around cycle 7 of 100k frames;
// a 100-frame warmup as cluster 6 originally shipped left ~138 MiB of RTS
// warmup leaking into the measurement window.  7 cycles of WARMUP gives
// ≥ 30 MiB headroom over the 50 MiB threshold without inflating the bench
// beyond ~3-4s wall.
constexpr int kWarmupCycles = 7;

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

// Parse a /proc/self/status field (e.g., "VmRSS:" or "Threads:") in kB.
auto parse_status_field(const std::string& field) -> std::int64_t {
    std::ifstream status("/proc/self/status");
    std::string line;
    while (std::getline(status, line)) {
        if (line.starts_with(field)) {
            std::istringstream iss(line);
            std::string label;
            std::int64_t value{};
            iss >> label >> value;
            return value;
        }
    }
    return 0;
}

auto vm_rss_bytes() -> std::int64_t {
    return parse_status_field("VmRSS:") * 1024; // VmRSS is in kB
}

auto threads_count() -> std::int64_t {
    return parse_status_field("Threads:");
}

// Count /proc/self/fd entries that point to real resources (regular files,
// pipes, sockets) — the things a forgotten Close can leak.  Excludes
// anon_inode targets (eventfd/eventpoll/timerfd/signalfd) which are runtime
// I/O multiplexer machinery the GHC RTS / glibc allocate lazily based on
// workload.  Counting them defeats hard-zero gating.
auto fd_count() -> std::int64_t {
    std::int64_t count = 0;
    std::error_code ec;
    for (const auto& entry : std::filesystem::directory_iterator("/proc/self/fd", ec)) {
        if (ec) {
            continue;
        }
        std::error_code link_ec;
        auto target = std::filesystem::read_symlink(entry, link_ec);
        if (link_ec) {
            continue;
        }
        const auto target_str = target.string();
        if (target_str.starts_with("anon_inode:")) {
            continue;
        }
        ++count;
    }
    return count;
}

// glibc malloc_info emits XML to a FILE*.  We summarize by extracting the
// total <total ... size="N"/> value across all heaps.  Imperfect but stable
// enough to gate fragmentation drift.
auto malloc_info_bytes() -> std::int64_t {
    char* buf = nullptr;
    std::size_t buf_size = 0;
    FILE* stream = open_memstream(&buf, &buf_size);
    if (stream == nullptr) {
        return 0;
    }
    if (malloc_info(0, stream) != 0) {
        std::fclose(stream);
        std::free(buf);
        return 0;
    }
    std::fclose(stream);
    std::string xml(buf, buf_size);
    std::free(buf);

    // Sum every <total type="..." count="..." size="N"/> we find at the
    // top level — glibc emits one per heap plus an outer aggregate.  We
    // sum the per-heap "total" entries to avoid double-counting via the
    // outer <heap>...</heap> wrapper's <total>.
    std::int64_t total_bytes = 0;
    std::size_t pos = 0;
    const std::string needle = "<total type=";
    while ((pos = xml.find(needle, pos)) != std::string::npos) {
        const std::size_t size_attr = xml.find("size=\"", pos);
        if (size_attr == std::string::npos) {
            break;
        }
        const std::size_t value_start = size_attr + 6;
        const std::size_t value_end = xml.find('"', value_start);
        if (value_end == std::string::npos) {
            break;
        }
        try {
            total_bytes += std::stoll(xml.substr(value_start, value_end - value_start));
        } catch (...) {
            // ignore unparseable entries
        }
        pos = value_end;
    }
    return total_bytes;
}

auto take_snapshot() -> Snapshot {
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
auto minimal_dbc() -> aletheia::DbcDefinition {
    using namespace aletheia;
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

void run_cycle(const std::filesystem::path& lib, const aletheia::DbcDefinition& dbc,
               int frames_per_cycle) {
    using namespace aletheia;
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));
    auto parse = client.parse_dbc(std::stop_token{}, dbc);
    if (!parse) {
        throw std::runtime_error("parse_dbc failed: " + std::string(parse.error().message()));
    }
    (void)client.start_stream(std::stop_token{});

    const auto id = CanId{StandardId::create(0x100).value()};
    const auto dlc = Dlc::create(8).value();
    const FramePayload frame{std::byte{0x40}, std::byte{0x1F}, std::byte{0x82}, std::byte{0x00},
                             std::byte{0x00}, std::byte{0x00}, std::byte{0x00}, std::byte{0x00}};
    for (int i = 0; i < frames_per_cycle; ++i) {
        (void)client.send_frame(std::stop_token{}, Timestamp{i}, id, dlc, frame);
    }
    (void)client.end_stream(std::stop_token{});
    // ~AletheiaClient runs here; backend dlcloses the .so handle if it was
    // the last reference.
}

auto find_library() -> std::filesystem::path {
    if (const char* env = std::getenv("ALETHEIA_LIB")) {
        return std::filesystem::path{env};
    }
    return std::filesystem::path{"build/libaletheia-ffi.so"};
}

auto env_int(const char* name, int default_value) -> int {
    if (const char* env = std::getenv(name); env != nullptr && env[0] != '\0') {
        try {
            int value = std::stoi(env);
            if (value > 0) {
                return value;
            }
        } catch (...) {
            // fall through to default
        }
    }
    return default_value;
}

void emit_sub_check_json(std::ostream& out, const SubCheck& c, bool first) {
    if (!first)
        out << ",\n";
    out << "    {\n";
    out << "      \"name\": \"" << c.name << "\",\n";
    out << "      \"gate\": \"" << c.gate << "\",\n";
    out << "      \"start\": " << c.start << ",\n";
    out << "      \"end\": " << c.end << ",\n";
    out << "      \"delta\": " << c.delta << ",\n";
    out << "      \"threshold\": " << c.threshold << ",\n";
    out << "      \"passed\": " << (c.passed ? "true" : "false") << "\n";
    out << "    }";
}

} // namespace

auto main() -> int {
    const int cycles = env_int("ALETHEIA_STABILITY_CYCLES", 10);
    const int frames = env_int("ALETHEIA_STABILITY_FRAMES", 100000);
    const auto lib = find_library();
    const auto dbc = minimal_dbc();

    // Multi-cycle warmup to absorb the GHC RTS heap warmup + lazy MAlonzo /
    // Agda structure realization.  See kWarmupCycles for empirical rationale.
    try {
        for (int i = 0; i < kWarmupCycles; ++i) {
            run_cycle(lib, dbc, frames);
        }
    } catch (const std::exception& e) {
        std::cerr << "warm-up: " << e.what() << "\n";
        return 2;
    }

    const auto start = take_snapshot();
    const auto t0 = std::chrono::steady_clock::now();

    for (int i = 0; i < cycles; ++i) {
        try {
            run_cycle(lib, dbc, frames);
        } catch (const std::exception& e) {
            std::cerr << "cycle " << i << ": " << e.what() << "\n";
            return 2;
        }
    }

    const auto end = take_snapshot();
    const auto elapsed =
        std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();

    auto abs64 = [](std::int64_t x) { return x < 0 ? -x : x; };

    const std::vector<SubCheck> sub_checks = {
        {.name = "rss",
         .gate = "soft_threshold",
         .start = start.rss_bytes,
         .end = end.rss_bytes,
         .delta = end.rss_bytes - start.rss_bytes,
         .threshold = kRssDeltaBytesCap,
         .passed = abs64(end.rss_bytes - start.rss_bytes) <= kRssDeltaBytesCap},
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
         .threshold = kMallocDeltaBytesCap,
         .passed = abs64(end.malloc_info_bytes - start.malloc_info_bytes) <= kMallocDeltaBytesCap},
    };

    bool all_passed = true;
    for (const auto& c : sub_checks) {
        if (!c.passed)
            all_passed = false;
    }

    std::cout << "{\n";
    std::cout << "  \"binding\": \"cpp\",\n";
    std::cout << "  \"cycles\": " << cycles << ",\n";
    std::cout << "  \"frames_per_cycle\": " << frames << ",\n";
    std::cout << "  \"total_frames\": " << (cycles * frames) << ",\n";
    std::cout << "  \"elapsed_seconds\": " << elapsed << ",\n";
    std::cout << "  \"sub_checks\": [\n";
    for (std::size_t i = 0; i < sub_checks.size(); ++i) {
        emit_sub_check_json(std::cout, sub_checks[i], i == 0);
    }
    std::cout << "\n  ],\n";
    std::cout << "  \"passed\": " << (all_passed ? "true" : "false") << "\n";
    std::cout << "}\n";

    return all_passed ? 0 : 1;
}
