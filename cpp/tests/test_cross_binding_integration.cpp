// Cross-binding integration test (R18 cluster 5 — Cat 33d).
//
// Counterpart of python/tests/test_cross_binding_integration.py and
// go/aletheia/cross_binding_integration_test.go. All three tests construct
// identical canonical inputs in code (no shared corpus, no golden output to
// diff against) and assert the binding's response shape matches the
// structural invariants documented in docs/architecture/PROTOCOL.md.
//
// The shared truth is PROTOCOL.md (text + JSON examples). Corpus-style
// integration tests bit-rot fast and tie every binding to one binding's exact
// emit format. By asserting structural invariants here (member presence,
// value types, count relationships, error-code identity), each binding's
// drift from the documented protocol surfaces locally without depending on
// the other bindings being run.

#include <catch2/catch_test_macros.hpp>

#include <aletheia/aletheia.hpp>

#include <array>
#include <cstdlib>
#include <filesystem>
#include <span>
#include <stop_token>
#include <variant>
#include <vector>

using namespace aletheia;
namespace fs = std::filesystem;

namespace {

// Matches python/tests/test_cross_binding_integration.py::_CANONICAL_DBC and
// go/aletheia/cross_binding_integration_test.go::canonicalDBC. Drift of any
// of the three is the cross-binding hazard the test is designed to catch.
auto canonical_dbc() -> DbcDefinition {
    auto sig_id = StandardId::create(256).value();
    auto dlc = Dlc::create(8).value();
    DbcSignal test_sig{
        .name = SignalName{"TestSignal"},
        .start_bit = BitPosition{0},
        .bit_length = BitLength{16},
        .byte_order = ByteOrder::LittleEndian,
        .is_signed = false,
        .factor = RationalFactor{Rational{1, 1}},
        .offset = RationalOffset{Rational{0, 1}},
        .minimum = RationalBound{Rational{0, 1}},
        .maximum = RationalBound{Rational{65535, 1}},
        .unit = Unit{""},
        .presence = AlwaysPresent{},
    };
    return DbcDefinition{
        .version = "1.0",
        .messages = {DbcMessage{
            .id = CanId{sig_id},
            .name = MessageName{"TestMessage"},
            .dlc = dlc,
            .sender = NodeName{"ECU"},
            .signals = {test_sig},
        }},
    };
}

auto find_lib() -> fs::path {
    if (auto* env = std::getenv("ALETHEIA_LIB"))
        return env;
    auto project_root = fs::path{__FILE__}.parent_path().parent_path().parent_path();
    auto lib = project_root / "build" / "libaletheia-ffi.so";
    if (fs::exists(lib))
        return lib;
    SKIP("libaletheia-ffi.so not found — run 'cabal run shake -- build' first");
    return {};
}

} // namespace

TEST_CASE("ParsedDBC response has documented shape", "[cross_binding]") {
    auto lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    auto result = client.parse_dbc(std::stop_token{}, canonical_dbc());
    REQUIRE(result.has_value());
    const auto& parsed = result.value();

    // ParsedDBC: { dbc: DbcDefinition, warnings: vector<ValidationIssue> }.
    // Round-trip identity invariant on canonical content.
    REQUIRE(parsed.dbc.messages.size() == 1);
    CHECK(parsed.dbc.messages[0].name.get() == "TestMessage");
    REQUIRE(parsed.dbc.messages[0].signals.size() == 1);
    CHECK(parsed.dbc.messages[0].signals[0].name.get() == "TestSignal");
    // Warnings vector must be empty (canonical DBC is well-formed); the
    // member's presence + size-zero is the cross-binding parity check.
    CHECK(parsed.warnings.empty());
}

TEST_CASE("ValidationResult response has documented shape", "[cross_binding]") {
    auto lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    auto result = client.validate_dbc(std::stop_token{}, canonical_dbc());
    REQUIRE(result.has_value());
    const auto& validation = result.value();

    // ValidationResult: { has_errors: bool, issues: vector<ValidationIssue> }.
    CHECK_FALSE(validation.has_errors);
    CHECK(validation.issues.empty());
}

TEST_CASE("send_frame ack response has documented shape", "[cross_binding]") {
    auto lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(std::stop_token{}, canonical_dbc()).has_value());
    auto formula = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"TestSignal"}, PhysicalValue{Rational{1000, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));
    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto sid = StandardId::create(256).value();
    auto dlc = Dlc::create(8).value();
    auto payload = std::array<std::byte, 8>{};
    auto resp = client.send_frame(std::stop_token{}, Timestamp{1000}, CanId{sid}, dlc,
                                  std::span<const std::byte>{payload});
    REQUIRE(resp.has_value());
    // FrameResponse = variant<Ack, Violation>; signal value 0 < 1000 → Ack.
    CHECK(std::holds_alternative<Ack>(resp.value()));
}

TEST_CASE("send_frame violation response has documented shape", "[cross_binding]") {
    auto lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(std::stop_token{}, canonical_dbc()).has_value());
    auto formula = ltl::always(
        ltl::atomic(ltl::less_than(SignalName{"TestSignal"}, PhysicalValue{Rational{100, 1}})));
    std::vector<LtlFormula> props;
    props.push_back(std::move(formula));
    REQUIRE(client.set_properties(std::stop_token{}, props).has_value());
    REQUIRE(client.start_stream(std::stop_token{}).has_value());

    auto sid = StandardId::create(256).value();
    auto dlc = Dlc::create(8).value();
    // Signal value 0xFFFF (65535) > 100 → violation.
    auto payload = std::array<std::byte, 8>{
        std::byte{0xFF}, std::byte{0xFF}, std::byte{0}, std::byte{0},
        std::byte{0},    std::byte{0},    std::byte{0}, std::byte{0},
    };
    auto resp = client.send_frame(std::stop_token{}, Timestamp{1000}, CanId{sid}, dlc,
                                  std::span<const std::byte>{payload});
    REQUIRE(resp.has_value());
    REQUIRE(std::holds_alternative<Violation>(resp.value()));
    const auto& v = std::get<Violation>(resp.value());
    // Documented Violation members: property_index, timestamp, reason,
    // optional<enrichment>; assert the timestamp survived round-trip.
    CHECK(v.timestamp.count() > 0);
}

TEST_CASE("invalid CAN ID is rejected at type boundary", "[cross_binding]") {
    // CAN ID 0x800 = 2048 is out of standard 11-bit range; StandardId::create
    // rejects it before the FFI is reached. This is the C++ analogue of
    // Python raising on out-of-range and Go returning an Error variant — the
    // cross-binding invariant is "invalid CAN ID is rejected somewhere on
    // the path", satisfied here by the strong-typed factory.
    auto sid = StandardId::create(0x800);
    CHECK_FALSE(sid.has_value());

    // Extended ID just over the 29-bit cap (2^29 = 0x20000000) is also rejected.
    auto xid = ExtendedId::create(0x20000000);
    CHECK_FALSE(xid.has_value());
}
