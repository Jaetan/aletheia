// Layer 3: Integration tests with real libaletheia-ffi.so.
// Requires: cabal run shake -- build (produces build/libaletheia-ffi.so)
// Run with: ctest -R integration (or ./integration_tests)
#include <catch2/catch_approx.hpp>
#include <catch2/catch_test_macros.hpp>

#include <aletheia/aletheia.hpp>

#include <barrier>
#include <cstdlib>
#include <filesystem>
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
    CHECK(result->get(SignalName{"Speed"}).get() == Catch::Approx(100.0));
    CHECK(result->get(SignalName{"RPM"}).get() == Catch::Approx(3000.0));
}

TEST_CASE("build frame via real FFI", "[integration]") {
    auto lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(make_integration_dbc()).has_value());

    auto id = CanId{StandardId::create(0x100).value()};
    std::vector<SignalValue> signals{
        {SignalName{"Speed"}, PhysicalValue{100.0}}, // raw = 1000
        {SignalName{"RPM"}, PhysicalValue{3000.0}},  // raw = 3000
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
        {SignalName{"Speed"}, PhysicalValue{42.5}},
        {SignalName{"RPM"}, PhysicalValue{1500.0}},
    };

    auto built = client.build_frame(id, Dlc::create(8).value(), signals);
    REQUIRE(built.has_value());

    auto extracted = client.extract_signals(id, Dlc::create(8).value(), *built);
    REQUIRE(extracted.has_value());
    // Round-trip: values should match (within quantization)
    CHECK(extracted->get(SignalName{"Speed"}).get() == Catch::Approx(42.5).margin(0.1));
    CHECK(extracted->get(SignalName{"RPM"}).get() == Catch::Approx(1500.0));
}

TEST_CASE("streaming LTL check via real FFI — property holds", "[integration]") {
    auto lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(make_integration_dbc()).has_value());

    // Property: always(Speed < 200)
    auto formula =
        ltl::always(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{200.0})));
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
        ltl::always(ltl::atomic(ltl::less_than(SignalName{"Speed"}, PhysicalValue{120.0})));
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

    std::thread thread_a(run_client, PhysicalValue{200.0}, std::ref(result_lenient));
    std::thread thread_b(run_client, PhysicalValue{100.0}, std::ref(result_strict));

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
