// Layer 3: Integration tests with real libaletheia-ffi.so.
// Requires: cabal run shake -- build (produces build/libaletheia-ffi.so)
// Run with: ctest -R integration (or ./integration_tests)
#include <catch2/catch_approx.hpp>
#include <catch2/catch_test_macros.hpp>

#include <aletheia/aletheia.hpp>

#include <fcntl.h>
#include <unistd.h>

#include <algorithm>
#include <array>
#include <barrier>
#include <cstdio>
#include <cstdlib>
#include <filesystem>
#include <string>
#include <string_view>
#include <thread>

using namespace aletheia;
namespace fs = std::filesystem;

// ---------------------------------------------------------------------------
// Find the shared library
// ---------------------------------------------------------------------------

static auto find_lib() -> fs::path {
    // Check environment variable first (CI / custom builds)
    if (auto* env = std::getenv("ALETHEIA_LIB"))
        return env;

    // Default: project build directory
    auto project_root = fs::path{__FILE__}.parent_path().parent_path().parent_path();
    auto lib = project_root / "build" / "libaletheia-ffi.so";
    if (fs::exists(lib))
        return lib;

    // Dist directory
    auto dist = project_root / "dist" / "aletheia" / "lib" / "libaletheia-ffi.so";
    if (fs::exists(dist))
        return dist;

    SKIP("libaletheia-ffi.so not found — run 'cabal run shake -- build' first");
    return {};
}

// ---------------------------------------------------------------------------
// Test DBC for integration tests
// ---------------------------------------------------------------------------

static auto make_integration_dbc() -> DbcDefinition {
    auto speed_id = StandardId::create(0x100).value();
    auto speed_dlc = Dlc::create(8).value();

    DbcSignal speed_sig{
        .name = SignalName{"Speed"},
        .start_bit = BitPosition{0},
        .bit_length = BitLength{16},
        .byte_order = ByteOrder::LittleEndian,
        .is_signed = false,
        .factor = RationalFactor{Rational{1, 10}},
        .offset = RationalOffset{Rational{0, 1}},
        .minimum = RationalBound{Rational{0, 1}},
        .maximum = RationalBound{Rational{65535, 100}},
        .unit = Unit{"km/h"},
        .presence = AlwaysPresent{},
    };

    DbcSignal rpm_sig{
        .name = SignalName{"RPM"},
        .start_bit = BitPosition{16},
        .bit_length = BitLength{16},
        .byte_order = ByteOrder::LittleEndian,
        .is_signed = false,
        .factor = RationalFactor{Rational{1, 1}},
        .offset = RationalOffset{Rational{0, 1}},
        .minimum = RationalBound{Rational{0, 1}},
        .maximum = RationalBound{Rational{65535, 1}},
        .unit = Unit{"rpm"},
        .presence = AlwaysPresent{},
    };

    return DbcDefinition{
        .version = "1.0",
        .messages = {DbcMessage{
            .id = CanId{speed_id},
            .name = MessageName{"VehicleSpeed"},
            .dlc = speed_dlc,
            .sender = NodeName{"ECU1"},
            .signals = {speed_sig, rpm_sig},
        }},
    };
}

// ---------------------------------------------------------------------------
// Integration tests
// ---------------------------------------------------------------------------

TEST_CASE("parse DBC via real FFI", "[integration]") {
    auto lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    auto result = client.parse_dbc(make_integration_dbc());
    CHECK(result.has_value());
}

TEST_CASE("extract signals via real FFI", "[integration]") {
    auto lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    auto dbc = make_integration_dbc();
    REQUIRE(client.parse_dbc(dbc).has_value());

    // Speed = 1000 raw * 0.1 factor = 100.0 km/h
    // RPM   = 3000 raw * 1.0 factor = 3000 rpm
    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data{std::byte{0xE8}, std::byte{0x03}, // 1000 LE
                      std::byte{0xB8}, std::byte{0x0B}, // 3000 LE
                      std::byte{0},    std::byte{0},    std::byte{0}, std::byte{0}};

    auto result = client.extract_signals(id, dlc, data);
    REQUIRE(result.has_value());
    CHECK(result->values.size() == 2);
    CHECK(result->get(SignalName{"Speed"}).get().to_double() == Catch::Approx(100.0));
    CHECK(result->get(SignalName{"RPM"}).get().to_double() == Catch::Approx(3000.0));
}

TEST_CASE("build frame via real FFI", "[integration]") {
    auto lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(make_integration_dbc()).has_value());

    auto id = CanId{StandardId::create(0x100).value()};
    std::vector<SignalValue> signals{
        {SignalName{"Speed"}, PhysicalValue{Rational{100, 1}}}, // raw = 1000
        {SignalName{"RPM"}, PhysicalValue{Rational{3000, 1}}},  // raw = 3000
    };

    auto result = client.build_frame(id, Dlc::create(8).value(), signals);
    REQUIRE(result.has_value());
    // Speed: 1000 = 0x03E8 LE → [0xE8, 0x03]
    CHECK((*result)[0] == std::byte{0xE8});
    CHECK((*result)[1] == std::byte{0x03});
    // RPM: 3000 = 0x0BB8 LE → [0xB8, 0x0B]
    CHECK((*result)[2] == std::byte{0xB8});
    CHECK((*result)[3] == std::byte{0x0B});
}

TEST_CASE("build then extract round-trip via real FFI", "[integration]") {
    auto lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(make_integration_dbc()).has_value());

    auto id = CanId{StandardId::create(0x100).value()};
    std::vector<SignalValue> signals{
        {SignalName{"Speed"}, PhysicalValue{Rational{85, 2}}},
        {SignalName{"RPM"}, PhysicalValue{Rational{1500, 1}}},
    };

    auto built = client.build_frame(id, Dlc::create(8).value(), signals);
    REQUIRE(built.has_value());

    auto extracted = client.extract_signals(id, Dlc::create(8).value(), *built);
    REQUIRE(extracted.has_value());
    // Round-trip: values should match (within quantization)
    CHECK(extracted->get(SignalName{"Speed"}).get().to_double() == Catch::Approx(42.5).margin(0.1));
    CHECK(extracted->get(SignalName{"RPM"}).get().to_double() == Catch::Approx(1500.0));
}

TEST_CASE("streaming LTL check via real FFI — property holds", "[integration]") {
    auto lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(make_integration_dbc()).has_value());

    // Property: always(Speed < 200)
    auto formula =
        ltl::always(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{200, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));

    REQUIRE(client.set_properties(props).has_value());
    REQUIRE(client.start_stream().has_value());

    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();

    // Send frames with Speed = 100, 120, 150 (all < 200)
    for (double speed : {100.0, 120.0, 150.0}) {
        auto raw = static_cast<std::uint16_t>(speed / 0.1);
        FramePayload data{static_cast<std::byte>(raw & 0xFF),
                          static_cast<std::byte>((raw >> 8) & 0xFF),
                          std::byte{0},
                          std::byte{0},
                          std::byte{0},
                          std::byte{0},
                          std::byte{0},
                          std::byte{0}};
        auto result = client.send_frame(Timestamp{1'000'000}, id, dlc, data);
        REQUIRE(result.has_value());
        CHECK(std::holds_alternative<Ack>(*result));
    }

    auto end = client.end_stream();
    REQUIRE(end.has_value());
    REQUIRE(end->results.size() == 1);
    CHECK(end->results[0].verdict == Verdict::Holds);
}

TEST_CASE("streaming LTL check via real FFI — property violated", "[integration]") {
    auto lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(make_integration_dbc()).has_value());

    // Property: always(Speed < 120) — will be violated by Speed=150
    auto formula =
        ltl::always(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{120, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));

    REQUIRE(client.set_properties(props).has_value());
    REQUIRE(client.start_stream().has_value());

    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    bool got_violation = false;

    for (double speed : {100.0, 110.0, 150.0}) {
        auto raw = static_cast<std::uint16_t>(speed / 0.1);
        FramePayload data{static_cast<std::byte>(raw & 0xFF),
                          static_cast<std::byte>((raw >> 8) & 0xFF),
                          std::byte{0},
                          std::byte{0},
                          std::byte{0},
                          std::byte{0},
                          std::byte{0},
                          std::byte{0}};
        auto result = client.send_frame(Timestamp{1'000'000}, id, dlc, data);
        REQUIRE(result.has_value());
        if (std::holds_alternative<Violation>(*result))
            got_violation = true;
    }

    auto end = client.end_stream();
    REQUIRE(end.has_value());

    // Either got a mid-stream violation or end-of-stream violation
    bool eos_violation = !end->results.empty() && end->results[0].verdict == Verdict::Fails;
    CHECK((got_violation || eos_violation));
}

TEST_CASE("non-monotonic timestamp rejected by Agda via real FFI", "[integration][monotonic]") {
    // Backward timestamps would make metric LTL operators silently produce
    // wrong verdicts (∸ clamps to 0 on negative differences). Agda's
    // handleDataFrame refuses them — this is the single source of truth
    // across all bindings. See FrameProcessor/Properties.agda PROPERTY 28.
    auto lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(make_integration_dbc()).has_value());

    auto formula =
        ltl::always(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{500, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));

    REQUIRE(client.set_properties(props).has_value());
    REQUIRE(client.start_stream().has_value());

    auto id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload payload{std::byte{10}, std::byte{0}, std::byte{0}, std::byte{0},
                         std::byte{0},  std::byte{0}, std::byte{0}, std::byte{0}};

    // First frame at t=5000 µs — accepted.
    auto ok = client.send_frame(Timestamp{5000}, id, dlc, payload);
    REQUIRE(ok.has_value());
    CHECK(std::holds_alternative<Ack>(*ok));

    // Regressing to t=4999 µs — rejected by Agda.
    auto err = client.send_frame(Timestamp{4999}, id, dlc, payload);
    REQUIRE_FALSE(err.has_value());
    CHECK(err.error().code() == ErrorCode::HandlerNonMonotonicTimestamp);

    // Same-timestamp frames (≥, not >) are accepted.
    auto eq = client.send_frame(Timestamp{5000}, id, dlc, payload);
    REQUIRE(eq.has_value());
    CHECK(std::holds_alternative<Ack>(*eq));

    // Anchor unchanged after rejection — next ≥ 5000 still accepted.
    auto fwd = client.send_frame(Timestamp{6000}, id, dlc, payload);
    REQUIRE(fwd.has_value());
    CHECK(std::holds_alternative<Ack>(*fwd));

    auto end = client.end_stream();
    REQUIRE(end.has_value());
}

TEST_CASE("validate DBC via real FFI", "[integration]") {
    auto lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    auto result = client.validate_dbc(make_integration_dbc());
    REQUIRE(result.has_value());
    // Our test DBC is well-formed — no errors expected
    CHECK_FALSE(result->has_errors);
}

// ---------------------------------------------------------------------------
// Concurrent client isolation test
// ---------------------------------------------------------------------------
// Two threads operate on independent AletheiaClient instances, synchronized
// via std::barrier so that operations interleave deterministically:
//
//   Thread A (lenient)                Thread B (strict)
//   ────────────────                  ────────────────
//   parse_dbc(dbc)                    parse_dbc(dbc)
//   ── barrier ──                     ── barrier ──
//   set_properties(Speed < 200)       set_properties(Speed < 100)
//   ── barrier ──                     ── barrier ──
//   start_stream()                    start_stream()
//   ── barrier ──                     ── barrier ──
//   send_frame(Speed = 150)           send_frame(Speed = 150)
//   ── barrier ──                     ── barrier ──
//   end_stream() → Holds              end_stream() → Fails
//
// Same DBC, same frame data, different properties → different verdicts.
// This proves each client owns independent state.

TEST_CASE("concurrent clients have independent state via real FFI", "[integration][concurrent]") {
    auto lib = find_lib();

    // Barrier with 2 participants — blocks until both threads arrive.
    std::barrier sync(2);

    struct ThreadResult {
        bool ok = false;
        Verdict verdict = Verdict::Fails;
        std::string error;
    };

    auto run_client = [&](PhysicalValue threshold, ThreadResult& out) {
        try {
            auto backend = make_ffi_backend(lib);
            AletheiaClient client(std::move(backend));

            // Step 1: parse DBC
            auto dbc = make_integration_dbc();
            auto parse_result = client.parse_dbc(dbc);
            if (!parse_result.has_value()) {
                out.error = "parse_dbc failed";
                sync.arrive_and_drop();
                return;
            }
            sync.arrive_and_wait();

            // Step 2: set properties — each thread has a different threshold
            auto formula = ltl::always(ltl::atomic(ltl::less_than(SignalName{"Speed"}, threshold)));
            std::vector<LtlFormula> props;
            props.push_back(std::move(formula));
            if (!client.set_properties(props).has_value()) {
                out.error = "set_properties failed";
                sync.arrive_and_drop();
                return;
            }
            sync.arrive_and_wait();

            // Step 3: start stream
            if (!client.start_stream().has_value()) {
                out.error = "start_stream failed";
                sync.arrive_and_drop();
                return;
            }
            sync.arrive_and_wait();

            // Step 4: send frame with Speed = 150
            auto id = CanId{StandardId::create(0x100).value()};
            auto dlc = Dlc::create(8).value();
            auto raw = static_cast<std::uint16_t>(150.0 / 0.1); // 1500
            FramePayload data{static_cast<std::byte>(raw & 0xFF),
                              static_cast<std::byte>((raw >> 8) & 0xFF),
                              std::byte{0},
                              std::byte{0},
                              std::byte{0},
                              std::byte{0},
                              std::byte{0},
                              std::byte{0}};
            auto send_result = client.send_frame(Timestamp{1'000'000}, id, dlc, data);
            if (!send_result.has_value()) {
                out.error = "send_frame failed";
                sync.arrive_and_drop();
                return;
            }
            sync.arrive_and_wait();

            // Step 5: end stream and capture verdict
            auto end = client.end_stream();
            if (!end.has_value() || end->results.empty()) {
                out.error = "end_stream failed or empty results";
                return;
            }

            // Check both mid-stream and EOS for the verdict
            bool mid_violation = std::holds_alternative<Violation>(*send_result);
            out.verdict = (mid_violation || end->results[0].verdict == Verdict::Fails)
                              ? Verdict::Fails
                              : Verdict::Holds;
            out.ok = true;
        } catch (const std::exception& e) {
            out.error = e.what();
        }
    };

    ThreadResult result_lenient; // threshold = 200: Speed 150 < 200 → Holds
    ThreadResult result_strict;  // threshold = 100: Speed 150 >= 100 → Fails

    std::thread thread_a(run_client, PhysicalValue{Rational{200, 1}}, std::ref(result_lenient));
    std::thread thread_b(run_client, PhysicalValue{Rational{100, 1}}, std::ref(result_strict));

    thread_a.join();
    thread_b.join();

    INFO("Thread A error: " << result_lenient.error);
    INFO("Thread B error: " << result_strict.error);
    REQUIRE(result_lenient.ok);
    REQUIRE(result_strict.ok);

    // Same data, different properties → different verdicts proves isolation
    CHECK(result_lenient.verdict == Verdict::Holds);
    CHECK(result_strict.verdict == Verdict::Fails);
}

// ---------------------------------------------------------------------------
// Nested multiplexing
// ---------------------------------------------------------------------------
//
// Three signals on message 0x300:
//   Mode    : always present (8 bits @ 0)
//   SubMode : present when Mode == 3 (8 bits @ 8)
//   Detail  : present when SubMode == 7 (16 bits @ 16)
//
// Detail is reachable only when Mode == 3 AND SubMode == 7. The Aletheia core
// walks the multiplexor chain bottom-up — both ancestors must validate before
// the leaf is extracted. This DBC mirrors the Python and Go nested-mux tests.

static auto make_nested_mux_dbc() -> DbcDefinition {
    auto sid = StandardId::create(0x300).value();
    auto dlc = Dlc::create(8).value();

    auto unit_factor = RationalFactor{Rational{1, 1}};
    auto zero_offset = RationalOffset{Rational{0, 1}};
    auto zero_min = RationalBound{Rational{0, 1}};
    auto byte_max = RationalBound{Rational{255, 1}};
    auto u16_max = RationalBound{Rational{65535, 1}};

    DbcSignal mode_sig{
        .name = SignalName{"Mode"},
        .start_bit = BitPosition{0},
        .bit_length = BitLength{8},
        .byte_order = ByteOrder::LittleEndian,
        .is_signed = false,
        .factor = unit_factor,
        .offset = zero_offset,
        .minimum = zero_min,
        .maximum = byte_max,
        .unit = Unit{""},
        .presence = AlwaysPresent{},
    };

    DbcSignal submode_sig{
        .name = SignalName{"SubMode"},
        .start_bit = BitPosition{8},
        .bit_length = BitLength{8},
        .byte_order = ByteOrder::LittleEndian,
        .is_signed = false,
        .factor = unit_factor,
        .offset = zero_offset,
        .minimum = zero_min,
        .maximum = byte_max,
        .unit = Unit{""},
        .presence = Multiplexed{SignalName{"Mode"}, {MultiplexValue{3}}},
    };

    DbcSignal detail_sig{
        .name = SignalName{"Detail"},
        .start_bit = BitPosition{16},
        .bit_length = BitLength{16},
        .byte_order = ByteOrder::LittleEndian,
        .is_signed = false,
        .factor = unit_factor,
        .offset = zero_offset,
        .minimum = zero_min,
        .maximum = u16_max,
        .unit = Unit{""},
        .presence = Multiplexed{SignalName{"SubMode"}, {MultiplexValue{7}}},
    };

    return DbcDefinition{
        .version = "1.0",
        .messages = {DbcMessage{
            .id = CanId{sid},
            .name = MessageName{"NestedMuxMessage"},
            .dlc = dlc,
            .sender = NodeName{"ECU"},
            .signals = {mode_sig, submode_sig, detail_sig},
        }},
    };
}

static auto contains_signal(const std::vector<SignalName>& names, std::string_view want) -> bool {
    return std::ranges::any_of(names, [&](const auto& n) { return n.get() == want; });
}

TEST_CASE("nested mux DBC validates clean via real FFI", "[integration][nested_mux]") {
    auto lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    auto result = client.validate_dbc(make_nested_mux_dbc());
    REQUIRE(result.has_value());
    CHECK_FALSE(result->has_errors);
}

TEST_CASE("nested mux full chain match extracts leaf via real FFI", "[integration][nested_mux]") {
    auto lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(make_nested_mux_dbc()).has_value());

    // Mode=3, SubMode=7, Detail=0xABCD (43981)
    auto id = CanId{StandardId::create(0x300).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data{std::byte{0x03}, std::byte{0x07}, std::byte{0xCD}, std::byte{0xAB},
                      std::byte{0},    std::byte{0},    std::byte{0},    std::byte{0}};

    auto result = client.extract_signals(id, dlc, data);
    REQUIRE(result.has_value());
    CHECK(result->values.size() == 3);
    CHECK(result->absent.empty());
    CHECK(result->get(SignalName{"Mode"}).get().to_double() == Catch::Approx(3.0));
    CHECK(result->get(SignalName{"SubMode"}).get().to_double() == Catch::Approx(7.0));
    CHECK(result->get(SignalName{"Detail"}).get().to_double() == Catch::Approx(43981.0));
}

TEST_CASE("nested mux inner mismatch marks leaf absent via real FFI", "[integration][nested_mux]") {
    auto lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(make_nested_mux_dbc()).has_value());

    // Mode=3 (matches), SubMode=5 (≠7) — Detail should be reported absent.
    auto id = CanId{StandardId::create(0x300).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data{std::byte{0x03}, std::byte{0x05}, std::byte{0xCD}, std::byte{0xAB},
                      std::byte{0},    std::byte{0},    std::byte{0},    std::byte{0}};

    auto result = client.extract_signals(id, dlc, data);
    REQUIRE(result.has_value());
    CHECK(result->values.size() == 2); // Mode and SubMode extracted
    CHECK(result->absent.size() == 1);
    CHECK(contains_signal(result->absent, "Detail"));
    CHECK(result->get(SignalName{"Mode"}).get().to_double() == Catch::Approx(3.0));
    CHECK(result->get(SignalName{"SubMode"}).get().to_double() == Catch::Approx(5.0));
}

TEST_CASE("nested mux outer mismatch marks inner and leaf absent via real FFI",
          "[integration][nested_mux]") {
    auto lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(make_nested_mux_dbc()).has_value());

    // Mode=2 (≠3) — both SubMode and Detail should be reported absent.
    auto id = CanId{StandardId::create(0x300).value()};
    auto dlc = Dlc::create(8).value();
    FramePayload data{std::byte{0x02}, std::byte{0x07}, std::byte{0xCD}, std::byte{0xAB},
                      std::byte{0},    std::byte{0},    std::byte{0},    std::byte{0}};

    auto result = client.extract_signals(id, dlc, data);
    REQUIRE(result.has_value());
    CHECK(result->values.size() == 1); // only Mode extracted
    CHECK(result->absent.size() == 2);
    CHECK(contains_signal(result->absent, "SubMode"));
    CHECK(contains_signal(result->absent, "Detail"));
    CHECK(result->get(SignalName{"Mode"}).get().to_double() == Catch::Approx(2.0));
}

TEST_CASE("mux cycle rejected by validator via real FFI", "[integration][nested_mux]") {
    auto lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    // Two signals A and B that mutually multiplex on each other → cycle.
    auto sid = StandardId::create(0x301).value();
    auto dlc = Dlc::create(8).value();

    auto unit_factor = RationalFactor{Rational{1, 1}};
    auto zero_offset = RationalOffset{Rational{0, 1}};
    auto zero_min = RationalBound{Rational{0, 1}};
    auto byte_max = RationalBound{Rational{255, 1}};

    DbcSignal sig_a{
        .name = SignalName{"A"},
        .start_bit = BitPosition{0},
        .bit_length = BitLength{8},
        .byte_order = ByteOrder::LittleEndian,
        .is_signed = false,
        .factor = unit_factor,
        .offset = zero_offset,
        .minimum = zero_min,
        .maximum = byte_max,
        .unit = Unit{""},
        .presence = Multiplexed{SignalName{"B"}, {MultiplexValue{1}}},
    };

    DbcSignal sig_b{
        .name = SignalName{"B"},
        .start_bit = BitPosition{8},
        .bit_length = BitLength{8},
        .byte_order = ByteOrder::LittleEndian,
        .is_signed = false,
        .factor = unit_factor,
        .offset = zero_offset,
        .minimum = zero_min,
        .maximum = byte_max,
        .unit = Unit{""},
        .presence = Multiplexed{SignalName{"A"}, {MultiplexValue{1}}},
    };

    DbcDefinition cycle_dbc{
        .version = "1.0",
        .messages = {DbcMessage{
            .id = CanId{sid},
            .name = MessageName{"CycleMsg"},
            .dlc = dlc,
            .sender = NodeName{"ECU"},
            .signals = {sig_a, sig_b},
        }},
    };

    auto result = client.validate_dbc(cycle_dbc);
    REQUIRE(result.has_value());
    REQUIRE(result->has_errors);
    bool found_cycle = std::ranges::any_of(result->issues, [](const auto& issue) {
        return issue.code == IssueCode::MultiplexorCycle;
    });
    CHECK(found_cycle);
}

// ---------------------------------------------------------------------------
// End-of-stream three-valued Kleene finalization (Path G, 2026-04-09)
// ---------------------------------------------------------------------------
//
// These tests mirror python/tests/test_eos_finalization.py::TestMissingSignalFinalization
// to give C++ client-level coverage of the Unresolved (Unsure) verdict. The
// Agda coalgebra finalizes an Atomic whose signal was never observed to
// FinalVerdict.Unsure; this propagates through And/Or via the Kleene truth
// tables (Unsure ∧ Holds = Unsure, Unsure ∨ Fails = Unsure) and reaches the
// binding as Verdict::Unresolved. Prior to Path G these cases collapsed to
// Fails, so these tests also act as a regression guard.
//
// make_two_message_dbc() gives two messages: Msg256 carries Speed, Msg512
// carries Rpm. The LTL property references Speed; sending only Msg512 frames
// leaves the Speed atomic unresolved.

static auto make_two_message_dbc() -> DbcDefinition {
    auto speed_id = StandardId::create(0x100).value();
    auto rpm_id = StandardId::create(0x200).value();
    auto dlc = Dlc::create(8).value();

    DbcSignal speed_sig{
        .name = SignalName{"Speed"},
        .start_bit = BitPosition{0},
        .bit_length = BitLength{16},
        .byte_order = ByteOrder::LittleEndian,
        .is_signed = false,
        .factor = RationalFactor{Rational{1, 1}},
        .offset = RationalOffset{Rational{0, 1}},
        .minimum = RationalBound{Rational{0, 1}},
        .maximum = RationalBound{Rational{65535, 1}},
        .unit = Unit{"kph"},
        .presence = AlwaysPresent{},
    };

    DbcSignal rpm_sig{
        .name = SignalName{"Rpm"},
        .start_bit = BitPosition{0},
        .bit_length = BitLength{16},
        .byte_order = ByteOrder::LittleEndian,
        .is_signed = false,
        .factor = RationalFactor{Rational{1, 1}},
        .offset = RationalOffset{Rational{0, 1}},
        .minimum = RationalBound{Rational{0, 1}},
        .maximum = RationalBound{Rational{65535, 1}},
        .unit = Unit{"rpm"},
        .presence = AlwaysPresent{},
    };

    return DbcDefinition{
        .version = "1.0",
        .messages =
            {
                DbcMessage{
                    .id = CanId{speed_id},
                    .name = MessageName{"Msg256"},
                    .dlc = dlc,
                    .sender = NodeName{"ECU"},
                    .signals = {speed_sig},
                },
                DbcMessage{
                    .id = CanId{rpm_id},
                    .name = MessageName{"Msg512"},
                    .dlc = dlc,
                    .sender = NodeName{"ECU"},
                    .signals = {rpm_sig},
                },
            },
    };
}

static auto bytes_of(std::uint16_t raw) -> FramePayload {
    return FramePayload{static_cast<std::byte>(raw & 0xFF),
                        static_cast<std::byte>((raw >> 8) & 0xFF),
                        std::byte{0},
                        std::byte{0},
                        std::byte{0},
                        std::byte{0},
                        std::byte{0},
                        std::byte{0}};
}

TEST_CASE("end_stream: Always on never-observed signal after 1 frame → Unresolved",
          "[integration][eos][unresolved]") {
    // Path G: single Msg512 frame (no Speed) leaves the Always(Speed<100)
    // atomic unresolved. Under three-valued Kleene this propagates via
    // And (Atomic) (Always _) as Unsure ∧ Holds = Unsure.
    auto lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(make_two_message_dbc()).has_value());

    auto formula =
        ltl::always(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{100, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));
    REQUIRE(client.set_properties(props).has_value());
    REQUIRE(client.start_stream().has_value());

    auto rpm_id = CanId{StandardId::create(0x200).value()};
    auto dlc = Dlc::create(8).value();
    auto ack = client.send_frame(Timestamp{0}, rpm_id, dlc, bytes_of(5));
    REQUIRE(ack.has_value());
    CHECK(std::holds_alternative<Ack>(*ack));

    auto end = client.end_stream();
    REQUIRE(end.has_value());
    REQUIRE(end->results.size() == 1);
    CHECK(end->results[0].verdict == Verdict::Unresolved);
}

TEST_CASE("end_stream: Always on never-observed signal after 5 frames → Unresolved",
          "[integration][eos][unresolved]") {
    // Multiple frames without the referenced signal should still finalize to
    // Unresolved — the Kleene fixed point persists regardless of progression
    // count.
    auto lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(make_two_message_dbc()).has_value());

    auto formula =
        ltl::always(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{100, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));
    REQUIRE(client.set_properties(props).has_value());
    REQUIRE(client.start_stream().has_value());

    auto rpm_id = CanId{StandardId::create(0x200).value()};
    auto dlc = Dlc::create(8).value();
    for (std::uint64_t i = 0; i < 5; ++i) {
        auto ack = client.send_frame(Timestamp{i * 1000}, rpm_id, dlc, bytes_of(5));
        REQUIRE(ack.has_value());
    }

    auto end = client.end_stream();
    REQUIRE(end.has_value());
    REQUIRE(end->results.size() == 1);
    CHECK(end->results[0].verdict == Verdict::Unresolved);
}

TEST_CASE("end_stream: changed_by on one-frame trace → Unresolved",
          "[integration][eos][unresolved]") {
    // A single frame gives changed_by(0) no prior observation to compare
    // against, so it finalizes to Unsure. The negation stays Unsure (Kleene
    // fixed point) and Always on a non-empty trace leaves behind And (Not
    // Atomic) (Always ...) which reduces to Unsure ∧ Holds = Unsure.
    auto lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(make_two_message_dbc()).has_value());

    auto formula =
        ltl::always(ltl::negate(ltl::atomic(ltl::changed_by(SignalName{"Speed"}, Delta{0.0}))));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));
    REQUIRE(client.set_properties(props).has_value());
    REQUIRE(client.start_stream().has_value());

    auto speed_id = CanId{StandardId::create(0x100).value()};
    auto dlc = Dlc::create(8).value();
    auto ack = client.send_frame(Timestamp{0}, speed_id, dlc, bytes_of(10));
    REQUIRE(ack.has_value());

    auto end = client.end_stream();
    REQUIRE(end.has_value());
    REQUIRE(end->results.size() == 1);
    CHECK(end->results[0].verdict == Verdict::Unresolved);
}

TEST_CASE("end_stream: Eventually on never-observed signal → Unresolved (regression guard)",
          "[integration][eos][unresolved]") {
    // Pre-Path-G this collapsed to Fails via the Or φ (Eventually ψ) →
    // Eventually ψ absorption. Path G guards that rewrite with
    // finalizesFails φ = true, so bare Atomic (finalizeL = Unsure) no longer
    // triggers it; the Or persists and finalizes via Unsure ∨ Fails = Unsure.
    auto lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(make_two_message_dbc()).has_value());

    auto formula =
        ltl::eventually(ltl::atomic(ltl::greater_than(SignalName{"Speed"}, PhysicalValue{Rational{10, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));
    REQUIRE(client.set_properties(props).has_value());
    REQUIRE(client.start_stream().has_value());

    auto rpm_id = CanId{StandardId::create(0x200).value()};
    auto dlc = Dlc::create(8).value();
    for (std::uint64_t i = 0; i < 5; ++i) {
        auto ack = client.send_frame(Timestamp{i * 1000}, rpm_id, dlc, bytes_of(5));
        REQUIRE(ack.has_value());
    }

    auto end = client.end_stream();
    REQUIRE(end.has_value());
    REQUIRE(end->results.size() == 1);
    CHECK(end->results[0].verdict == Verdict::Unresolved);
}

TEST_CASE("end_stream: Eventually on 0 frames still finalizes to Fails",
          "[integration][eos][unresolved]") {
    // Contrast with the N ≥ 1 case above. With no progression, finalizeL is
    // applied directly to Eventually _ which returns Fails (liveness
    // operators do not get three-valued absorption on the empty trace).
    auto lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(make_two_message_dbc()).has_value());

    auto formula =
        ltl::eventually(ltl::atomic(ltl::greater_than(SignalName{"Speed"}, PhysicalValue{Rational{10, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));
    REQUIRE(client.set_properties(props).has_value());
    REQUIRE(client.start_stream().has_value());

    auto end = client.end_stream();
    REQUIRE(end.has_value());
    REQUIRE(end->results.size() == 1);
    CHECK(end->results[0].verdict == Verdict::Fails);
}

TEST_CASE("end_stream: 0 frames + Always(missing) → Holds (vacuous)",
          "[integration][eos][unresolved]") {
    // Standard LTLf vacuous truth: G φ on the empty trace holds regardless
    // of whether φ's signal is observable. This differentiates the
    // empty-trace path (direct finalizeL on Always) from the non-empty path
    // (finalizeL after progression leaves an And behind).
    auto lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(make_two_message_dbc()).has_value());

    auto formula =
        ltl::always(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{100, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));
    REQUIRE(client.set_properties(props).has_value());
    REQUIRE(client.start_stream().has_value());

    auto end = client.end_stream();
    REQUIRE(end.has_value());
    REQUIRE(end->results.size() == 1);
    CHECK(end->results[0].verdict == Verdict::Holds);
}

TEST_CASE("end_stream: signal recovers after missing → Holds", "[integration][eos][unresolved]") {
    // Once the signal is observed at least once with a true value, the
    // And (Atomic) (Always ...) absorption collapses back to Always (Atomic)
    // via combineAnd Satisfied l. Confirms the Unresolved path only bites
    // when the signal is missing for the entire stream.
    auto lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(make_two_message_dbc()).has_value());

    auto formula =
        ltl::always(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{100, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));
    REQUIRE(client.set_properties(props).has_value());
    REQUIRE(client.start_stream().has_value());

    auto speed_id = CanId{StandardId::create(0x100).value()};
    auto rpm_id = CanId{StandardId::create(0x200).value()};
    auto dlc = Dlc::create(8).value();

    // Three frames of Msg512 (Speed absent).
    for (std::uint64_t i = 0; i < 3; ++i) {
        auto ack = client.send_frame(Timestamp{i * 1000}, rpm_id, dlc, bytes_of(5));
        REQUIRE(ack.has_value());
    }
    // Two frames of Msg256 with Speed = 10 (< 100).
    auto ack1 = client.send_frame(Timestamp{3000}, speed_id, dlc, bytes_of(10));
    REQUIRE(ack1.has_value());
    auto ack2 = client.send_frame(Timestamp{4000}, speed_id, dlc, bytes_of(10));
    REQUIRE(ack2.has_value());

    auto end = client.end_stream();
    REQUIRE(end.has_value());
    REQUIRE(end->results.size() == 1);
    CHECK(end->results[0].verdict == Verdict::Holds);
}

TEST_CASE("end_stream: K3 combination — Unresolved And Holds = Unresolved",
          "[integration][eos][unresolved]") {
    // Kleene truth table: Unsure ∧ Holds = Unsure. Left conjunct references
    // Speed (never observed → Unsure), right conjunct references Rpm
    // (observed < 100 → Holds). End result must be Unresolved.
    auto lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(make_two_message_dbc()).has_value());

    auto lhs = ltl::always(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{100, 1}})));
    auto rhs = ltl::always(ltl::atomic(ltl::less_than(SignalName{"Rpm"}, PhysicalValue{Rational{100, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(ltl::both(std::move(lhs), std::move(rhs)));
    REQUIRE(client.set_properties(props).has_value());
    REQUIRE(client.start_stream().has_value());

    auto rpm_id = CanId{StandardId::create(0x200).value()};
    auto dlc = Dlc::create(8).value();
    for (std::uint64_t i = 0; i < 3; ++i) {
        auto ack = client.send_frame(Timestamp{i * 1000}, rpm_id, dlc, bytes_of(5));
        REQUIRE(ack.has_value());
    }

    auto end = client.end_stream();
    REQUIRE(end.has_value());
    REQUIRE(end->results.size() == 1);
    CHECK(end->results[0].verdict == Verdict::Unresolved);
}

TEST_CASE("end_stream: K3 combination — Unresolved Or Fails = Unresolved",
          "[integration][eos][unresolved]") {
    // Kleene truth table: Unsure ∨ Fails = Unsure. Left disjunct references
    // Speed (never observed → Unsure), right disjunct is an Eventually that
    // references Rpm but requires an unsatisfiable threshold (→ Fails under
    // direct finalization since Eventually doesn't get K3 absorption when it
    // appears inside Or's right branch and both operands finalize directly).
    //
    // Using Always(Rpm > 999999) which Holds vacuously on no matching frames
    // is wrong (it would Hold, not Fail). Instead we use Eventually on a
    // threshold Rpm never reaches, which does Fail on a non-empty trace
    // because Eventually is a liveness operator — Path G keeps Fails on
    // liveness when no progression satisfied it.
    //
    // Wait — on a non-empty trace with Rpm observed, Eventually(Rpm > big)
    // progresses to Or (Atomic ...) (Eventually ...) and finalizes via
    // Or's K3 rules. Since the left Atomic finalizes to Fails here (Rpm was
    // observed and predicate was false each frame), and Eventually on the
    // non-empty remainder also Fails by direct finalization, the Or becomes
    // Fails ∨ Fails = Fails.
    auto lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(make_two_message_dbc()).has_value());

    auto lhs = ltl::always(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{100, 1}})));
    auto rhs =
        ltl::eventually(ltl::atomic(ltl::greater_than(SignalName{"Rpm"}, PhysicalValue{Rational{999999, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(ltl::either(std::move(lhs), std::move(rhs)));
    REQUIRE(client.set_properties(props).has_value());
    REQUIRE(client.start_stream().has_value());

    auto rpm_id = CanId{StandardId::create(0x200).value()};
    auto dlc = Dlc::create(8).value();
    for (std::uint64_t i = 0; i < 3; ++i) {
        auto ack = client.send_frame(Timestamp{i * 1000}, rpm_id, dlc, bytes_of(5));
        REQUIRE(ack.has_value());
    }

    auto end = client.end_stream();
    REQUIRE(end.has_value());
    REQUIRE(end->results.size() == 1);
    CHECK(end->results[0].verdict == Verdict::Unresolved);
}

TEST_CASE("end_stream: Unresolved result carries enrichment when diagnostics present",
          "[integration][eos][unresolved][enrich]") {
    // client.cpp end_stream() calls enrich_property_result for both Fails
    // and Unresolved verdicts. Verify the enrichment pipeline runs on the
    // Unresolved branch by checking that reason and enrichment are populated.
    auto lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(make_two_message_dbc()).has_value());

    auto formula =
        ltl::always(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{Rational{100, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));
    REQUIRE(client.set_properties(props).has_value());
    REQUIRE(client.start_stream().has_value());

    auto rpm_id = CanId{StandardId::create(0x200).value()};
    auto dlc = Dlc::create(8).value();
    for (std::uint64_t i = 0; i < 3; ++i) {
        auto ack = client.send_frame(Timestamp{i * 1000}, rpm_id, dlc, bytes_of(5));
        REQUIRE(ack.has_value());
    }

    auto end = client.end_stream();
    REQUIRE(end.has_value());
    REQUIRE(end->results.size() == 1);
    const auto& pr = end->results[0];
    CHECK(pr.verdict == Verdict::Unresolved);
    // The Agda core emits a human-readable reason for Unresolved verdicts.
    CHECK_FALSE(pr.reason.empty());
    // enrich_property_result runs unconditionally for Unresolved — the
    // ViolationEnrichment field should be populated.
    REQUIRE(pr.enrichment.has_value());
    CHECK_FALSE(pr.enrichment->enriched_reason.empty());
}

// ---------------------------------------------------------------------------
// Parse error codes from the PhysicallyValid gate (2026-04-08)
// ---------------------------------------------------------------------------
// The JSON parser now enforces PhysicallyValid at parse time via
// DBC/JSONParser.agda's physicalGate (closes deferred item §12.1). LE
// signals pass through unchanged; BigEndian signals must satisfy three
// constraints, each mapped to a distinct ParseError:
//   • bitLength ≥ 1                     → SignalBitLengthZero
//   • csb + bl − 1 < frameBytes * 8      → SignalOverflowsFrame
//   • bl − 1 ≤ csb                      → SignalMSBBelowBitLength
// where csb = convertStartBit(frameBytes, BE, startBit, bitLength).
// These tests verify the C++ binding surfaces each parse error code via
// AletheiaError::code() when feeding a malformed DBC through the real FFI.

namespace {

// Minimal DBC helper that wraps a single BE signal inside a one-message DBC.
// Callers supply the signal's start_bit, bit_length, and the message DLC.
auto make_single_be_signal_dbc(std::uint16_t start_bit, std::uint8_t bit_length,
                               std::uint8_t dlc_bytes) -> DbcDefinition {
    DbcSignal sig{
        .name = SignalName{"Bad"},
        .start_bit = BitPosition{start_bit},
        .bit_length = BitLength{bit_length},
        .byte_order = ByteOrder::BigEndian,
        .is_signed = false,
        .factor = RationalFactor{Rational{1, 1}},
        .offset = RationalOffset{Rational{0, 1}},
        .minimum = RationalBound{Rational{0, 1}},
        .maximum = RationalBound{Rational{255, 1}},
        .unit = Unit{""},
        .presence = AlwaysPresent{},
    };
    auto id = StandardId::create(0x100).value();
    auto dlc = Dlc::create(dlc_bytes).value();
    return DbcDefinition{
        .version = "1.0",
        .messages = {DbcMessage{
            .id = CanId{id},
            .name = MessageName{"Msg1"},
            .dlc = dlc,
            .sender = NodeName{"ECU"},
            .signals = {sig},
        }},
    };
}

} // namespace

TEST_CASE("parse DBC: BigEndian signal with length=0 → parse_signal_bit_length_zero",
          "[integration][parse_error]") {
    auto lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    // BE signal, length=0 → physicalGate's `1 ≤ᵇ bl` check fails → SignalBitLengthZero.
    auto dbc = make_single_be_signal_dbc(/*start_bit=*/7, /*bit_length=*/0, /*dlc_bytes=*/1);

    auto result = client.parse_dbc(dbc);
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().code() == ErrorCode::ParseSignalBitLengthZero);
    CHECK(result.error().kind() == ErrorKind::Protocol);
}

TEST_CASE("parse DBC: BigEndian signal overflowing frame → parse_signal_overflows_frame",
          "[integration][parse_error]") {
    auto lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    // BE signal: start_bit=7 (MSB of byte 0), length=33, dlc=4 → 32 bits of frame.
    // physicalBitPos(4, BE, 7) = 31, csb = 31 ∸ 32 = 0 (monus),
    // csb + bl − 1 = 32, 32 < 32 is false → SignalOverflowsFrame.
    // Mirrors python/tests/test_dbc_validator.py::test_big_endian_signal_exceeds_dlc.
    auto dbc = make_single_be_signal_dbc(/*start_bit=*/7, /*bit_length=*/33, /*dlc_bytes=*/4);

    auto result = client.parse_dbc(dbc);
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().code() == ErrorCode::ParseSignalOverflowsFrame);
    CHECK(result.error().kind() == ErrorKind::Protocol);
}

TEST_CASE(
    "parse DBC: BigEndian signal with MSB below bitLength → parse_signal_msb_below_bit_length",
    "[integration][parse_error]") {
    auto lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    // BE signal: start_bit=0, length=2, dlc=1.
    // physicalBitPos(1, BE, 0) = 0, csb = 0 ∸ 1 = 0 (monus),
    // csb + bl − 1 = 1, 1 < 8 → passes overflow check,
    // bl − 1 ≤ csb → 1 ≤ 0 is false → SignalMSBBelowBitLength.
    auto dbc = make_single_be_signal_dbc(/*start_bit=*/0, /*bit_length=*/2, /*dlc_bytes=*/1);

    auto result = client.parse_dbc(dbc);
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().code() == ErrorCode::ParseSignalMsbBelowBitLength);
    CHECK(result.error().kind() == ErrorKind::Protocol);
}

TEST_CASE("validate DBC: LittleEndian signal with length=0 bypasses physicalGate",
          "[integration][parse_error]") {
    // LE signals pass through physicalGate unchanged (physicalGate matches
    // `LittleEndian _ _ sig = inj₂ sig` in DBC/JSONParser.agda). A length=0
    // LE signal is therefore accepted by the parser — the downstream
    // validator then catches it with IssueCode::BitLengthZero. Contrast
    // with BE, which fails at parse time with ParseSignalBitLengthZero.
    //
    // Note: parse_dbc also runs validateDBCFull and rejects on any error
    // issue, so we route via validate_dbc to observe the issue directly.
    auto lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    DbcSignal sig{
        .name = SignalName{"ZeroLenLE"},
        .start_bit = BitPosition{0},
        .bit_length = BitLength{0},
        .byte_order = ByteOrder::LittleEndian,
        .is_signed = false,
        .factor = RationalFactor{Rational{1, 1}},
        .offset = RationalOffset{Rational{0, 1}},
        .minimum = RationalBound{Rational{0, 1}},
        .maximum = RationalBound{Rational{255, 1}},
        .unit = Unit{""},
        .presence = AlwaysPresent{},
    };
    DbcDefinition dbc{
        .version = "1.0",
        .messages = {DbcMessage{
            .id = CanId{StandardId::create(0x100).value()},
            .name = MessageName{"Msg1"},
            .dlc = Dlc::create(8).value(),
            .sender = NodeName{"ECU"},
            .signals = {sig},
        }},
    };

    // validate_dbc: the parser accepts the LE signal, validator flags it.
    auto validation = client.validate_dbc(dbc);
    REQUIRE(validation.has_value());
    CHECK(validation->has_errors);
    bool found_zero_length = false;
    for (const auto& issue : validation->issues) {
        if (issue.code == IssueCode::BitLengthZero)
            found_zero_length = true;
    }
    CHECK(found_zero_length);
}

// ---------------------------------------------------------------------------
// RTS cores mismatch warning (2026-04-09)
// ---------------------------------------------------------------------------
// make_ffi_backend's second argument (rts_cores) only takes effect on the
// first call in a process. Subsequent calls with a different rts_cores value
// must log a warning to stderr via std::println(stderr, ...) in
// ffi_backend.cpp's hs_init guard. This test captures the C stderr stream
// using dup/dup2 and verifies the warning message contents.

namespace {

// Capture the C stderr stream for the duration of the callable's execution.
// Returns the captured bytes as a std::string.
template<typename F>
auto capture_stderr(F&& fn) -> std::string {
    std::fflush(stderr);
    const int saved_stderr = ::dup(::fileno(stderr));
    REQUIRE(saved_stderr >= 0);

    std::array<char, 64> tmpl{};
    const std::string_view name = "/tmp/aletheia_stderr_XXXXXX";
    std::copy(name.begin(), name.end(), tmpl.begin());
    const int fd = ::mkstemp(tmpl.data());
    REQUIRE(fd >= 0);

    REQUIRE(::dup2(fd, ::fileno(stderr)) >= 0);
    fn();
    std::fflush(stderr);
    REQUIRE(::dup2(saved_stderr, ::fileno(stderr)) >= 0);
    ::close(saved_stderr);

    REQUIRE(::lseek(fd, 0, SEEK_SET) == 0);
    std::array<char, 4096> buf{};
    const auto n = ::read(fd, buf.data(), buf.size() - 1);
    ::close(fd);
    ::unlink(tmpl.data());

    return std::string(buf.data(), n > 0 ? static_cast<std::size_t>(n) : 0);
}

} // namespace

TEST_CASE("make_ffi_backend warns on mismatched rts_cores", "[integration][ffi_backend]") {
    auto lib = find_lib();

    // Establish deterministic RTS state: first call initializes to 1 if the
    // RTS has not yet been touched this process, else a no-op if a prior
    // test already initialized with the default (1). Either way, the RTS
    // cores count is 1 after this block.
    {
        auto backend = make_ffi_backend(lib);
        REQUIRE(backend != nullptr);
    }

    // Second call with rts_cores != 1 must trigger the warning path.
    auto backend = make_ffi_backend(lib, /*rts_cores=*/8);
    REQUIRE(backend != nullptr);
    auto warning = backend->pending_warning();

    CHECK(warning.find("already initialized") != std::string::npos);
    CHECK(warning.find("rts_cores=8") != std::string::npos);
    CHECK(warning.find("1 core") != std::string::npos);
}

TEST_CASE("make_ffi_backend is silent on matching rts_cores", "[integration][ffi_backend]") {
    auto lib = find_lib();

    // Ensure the RTS is already initialized (1 core) from prior tests or
    // this test's first call.
    {
        auto backend = make_ffi_backend(lib);
        REQUIRE(backend != nullptr);
    }

    // Second call with matching rts_cores (1) must NOT warn.
    auto backend = make_ffi_backend(lib, /*rts_cores=*/1);
    REQUIRE(backend != nullptr);

    CHECK(backend->pending_warning().empty());
    CHECK_FALSE(backend->rts_mismatch_info().has_value());
}

TEST_CASE("rts.cores_mismatch structured fields match Go/Python schema",
          "[integration][ffi_backend]") {
    auto lib = find_lib();

    // First init fixes the core count to 1 (deterministic prior state).
    {
        auto backend = make_ffi_backend(lib);
        REQUIRE(backend != nullptr);
    }

    auto backend = make_ffi_backend(lib, /*rts_cores=*/4);
    REQUIRE(backend != nullptr);

    const auto info = backend->rts_mismatch_info();
    REQUIRE(info.has_value());
    // active_cores = what the RTS was already running with; requested_cores =
    // what this call asked for. Both integer fields must be populated for
    // parity with Go's slog `active_cores` / `requested_cores` (ffi.go:337-338)
    // and Python's logging record (client/_ffi.py:79-82).
    CHECK(info->first == 1);
    CHECK(info->second == 4);
}

TEST_CASE("make_ffi_backend rejects rts_cores < 1", "[integration][ffi_backend]") {
    auto lib = find_lib();
    CHECK_THROWS_AS(make_ffi_backend(lib, /*rts_cores=*/0), std::invalid_argument);
    CHECK_THROWS_AS(make_ffi_backend(lib, /*rts_cores=*/-1), std::invalid_argument);
}

// ---------------------------------------------------------------------------
// Event ack wire-contract tests (closes SC.22.3 from R11 review).
//
// send_error and send_remote go through `parse_event_ack`, which is
// authoritative for the `{"status":"ack"}` wire returned by the real FFI
// (see Aletheia/Protocol/StreamState.agda:81-82). MockBackend's default
// happens to return `"success"` — these tests exercise the real `"ack"`
// path end-to-end, catching regressions where parse_success and
// parse_event_ack drift or the Agda handler stops emitting `"ack"`.
// ---------------------------------------------------------------------------

TEST_CASE("send_error returns ack via real FFI", "[integration][event_ack]") {
    auto lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(make_integration_dbc()).has_value());
    REQUIRE(client.set_properties({}).has_value());
    REQUIRE(client.start_stream().has_value());

    // send_error carries only a timestamp; the real FFI must return
    // {"status":"ack"} and the Client must accept it.
    auto r = client.send_error(Timestamp{1'000});
    REQUIRE(r.has_value());

    auto end = client.end_stream();
    REQUIRE(end.has_value());
}

TEST_CASE("send_remote returns ack via real FFI", "[integration][event_ack]") {
    auto lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(make_integration_dbc()).has_value());
    REQUIRE(client.set_properties({}).has_value());
    REQUIRE(client.start_stream().has_value());

    // send_remote carries a timestamp + CAN id; the real FFI must return
    // {"status":"ack"} and the Client must accept it.
    auto id = CanId{StandardId::create(0x100).value()};
    auto r = client.send_remote(Timestamp{1'000}, id);
    REQUIRE(r.has_value());

    auto end = client.end_stream();
    REQUIRE(end.has_value());
}
