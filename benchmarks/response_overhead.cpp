// Microbenchmark: response parsing overhead on the C++ side.
//
// Measures the cost of each step in the ack response path:
// 1. string_view comparison (current fast path)
// 2. nlohmann::json::parse (slow path / baseline)
// 3. Hypothetical binary: read status byte
//
// Build: g++-15 -std=c++23 -O3 -o response_overhead benchmarks/response_overhead.cpp
// Run:   ./response_overhead

#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <string>
#include <string_view>
#include <variant>

// Minimal JSON parsing simulation (no nlohmann dependency for standalone build)
// We'll time string operations and simulate the parse cost.

static constexpr std::string_view ack_compact = R"({"status":"ack"})";
static constexpr std::string_view ack_spaced  = R"({"status": "ack"})";

static constexpr std::string_view violation_json =
    R"({"type":"property","status":"fails","property_index":0,)"
    R"("timestamp":1234567890,"reason":"Signal EngineSpeed exceeded 220"})";

struct Ack {};
struct Violation { int property_index; uint64_t timestamp; std::string reason; };
using FrameResponse = std::variant<Ack, Violation>;

static constexpr int ITERATIONS = 5'000'000;
static constexpr int WARMUP     = 500'000;

template <typename F>
auto bench(const char* name, F&& func, int iterations = ITERATIONS) -> double {
    // Warmup
    for (int i = 0; i < WARMUP; ++i)
        func();

    auto start = std::chrono::high_resolution_clock::now();
    for (int i = 0; i < iterations; ++i)
        func();
    auto end = std::chrono::high_resolution_clock::now();

    double ns = std::chrono::duration<double, std::nano>(end - start).count();
    double ns_per_op = ns / iterations;
    std::printf("  %-45s  %8.1f ns/op\n", name, ns_per_op);
    return ns_per_op;
}

// Prevent optimizing away results
template <typename T>
void do_not_optimize(T const& val) {
    asm volatile("" : : "r,m"(val) : "memory");
}

int main() {
    std::puts("Response parsing overhead (C++)");
    std::printf("Iterations: %'d\n\n", ITERATIONS);

    // Build test strings (simulate what FFI returns)
    std::string ack_str{ack_compact};
    std::string viol_str{violation_json};

    std::puts("=== Ack response (hot path, ~99% of frames) ===");

    // 1. string_view comparison (current fast path)
    auto t_cmp = bench("string_view comparison", [&] {
        std::string_view sv{ack_str};
        bool is_ack = (sv == ack_compact) || (sv == ack_spaced);
        do_not_optimize(is_ack);
    });

    // 2. std::string construction from C string (simulates CString → string)
    const char* c_ack = ack_str.c_str();
    auto t_str = bench("std::string from c_str", [&] {
        std::string s{c_ack};
        do_not_optimize(s);
    });

    // 3. Full fast path: string construction + comparison
    auto t_fast = bench("string + comparison (full fast)", [&] {
        std::string s{c_ack};
        std::string_view sv{s};
        bool is_ack = (sv == ack_compact) || (sv == ack_spaced);
        do_not_optimize(is_ack);
    });

    // 4. String scan for "ack" (simulates minimal JSON field check)
    auto t_find = bench("string::find(\"ack\")", [&] {
        std::string s{c_ack};
        bool found = s.find("ack") != std::string::npos;
        do_not_optimize(found);
    });

    // 5. strcmp (raw C comparison, no string construction)
    auto t_strcmp = bench("strcmp (raw C)", [&] {
        bool is_ack = (std::strcmp(c_ack, "{\"status\":\"ack\"}") == 0);
        do_not_optimize(is_ack);
    });

    // 6. Hypothetical binary: read status byte
    uint8_t binary_ack = 0x00;
    auto t_bin = bench("binary: read status byte", [&] {
        bool is_ack = (binary_ack == 0x00);
        do_not_optimize(is_ack);
    });

    // 7. memcmp (fixed-size comparison)
    auto t_memcmp = bench("memcmp (16 bytes)", [&] {
        bool is_ack = (std::memcmp(c_ack, "{\"status\":\"ack\"}", 16) == 0);
        do_not_optimize(is_ack);
    });

    std::puts("");
    double budget = 1'000'000'000.0 / 48'000;  // ~20.8 us at 48k fps
    std::printf("  Fast path saves vs string+cmp:  %8.1f ns/frame\n", t_str - t_cmp);
    std::printf("  Binary saves vs fast path:      %8.1f ns/frame\n", t_fast - t_bin);
    std::printf("\n=== Context ===\n");
    std::printf("  Per-frame budget at 48k fps:    %8.0f ns\n", budget);
    std::printf("  Fast path %% of budget:          %8.1f%%\n", t_fast / budget * 100);
    std::printf("  Binary %% of budget:             %8.1f%%\n", t_bin / budget * 100);

    // --- Violation path (for reference) ---
    std::puts("\n=== Violation response (rare) ===");

    const char* c_viol = viol_str.c_str();
    bench("std::string from c_str (violation)", [&] {
        std::string s{c_viol};
        do_not_optimize(s);
    }, 2'000'000);

    // Manual field extraction (simulates what we'd do without nlohmann)
    bench("find fields manually", [&] {
        std::string s{c_viol};
        auto idx = s.find("\"property_index\":");
        auto ts = s.find("\"timestamp\":");
        do_not_optimize(idx);
        do_not_optimize(ts);
    }, 2'000'000);

    return 0;
}
