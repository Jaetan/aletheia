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

// R19 cluster 8 phase e.1 — Identifier validity record enforces
// max_identifier_length.  The Agda kernel's `validIdentifierᵇ` predicate
// gained a third conjunct asserting `length name <ᵇ suc max-identifier-
// length`.  Identifiers at the limit (128 chars) still parse; anything
// longer is rejected at `mkIdentFromChars` and surfaces as a parse error
// on the wire (currently `dbc_text_trailing_input` due to parser-monad
// position semantics; refining to typed `InputBoundExceeded
// IdentifierLength` is downstream parser-monad plumbing).

TEST_CASE("identifier at max length is accepted", "[cross_binding][cluster8][e1]") {
    auto lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    const std::string name(aletheia::max_identifier_length, 'A');
    const std::string dbc_text = "VERSION \"\"\nNS_:\nBS_:\nBU_:\nBO_ 100 " + name + ": 8 ECU\n";
    auto result = client.parse_dbc_text(std::stop_token{}, dbc_text);
    REQUIRE(result.has_value());
    REQUIRE(result->dbc.messages.size() == 1);
    CHECK(result->dbc.messages[0].name.get() == name);
}

TEST_CASE("identifier over max length is rejected", "[cross_binding][cluster8][e1]") {
    auto lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    const std::string name(aletheia::max_identifier_length + 1, 'A');
    const std::string dbc_text = "VERSION \"\"\nNS_:\nBS_:\nBU_:\nBO_ 100 " + name + ": 8 ECU\n";
    auto result = client.parse_dbc_text(std::stop_token{}, dbc_text);
    REQUIRE_FALSE(result.has_value());
}

// R19 AGDA-D-13.4 phase 2a — typed NestingDepth wire-error.  A
// deeply-nested LTL formula triggers the kernel's `jsonDepth` check at
// `handleParsedJSON`, emitting `ParseErr (InputBoundExceeded NestingDepth …)`
// instead of the pre-phase-2a untyped `DispatchErr InvalidJSON`.  The wire
// carries `bound_kind / observed / limit` which `make_json_error` lifts
// into `AletheiaError::bound_info()`.  Mirrors Python's
// `TestNestingDepthBound::test_nested_at_depth_63_rejected` and Go's
// `TestCrossBinding_NestingDepthLiftsToInputBoundExceeded`.
TEST_CASE("nesting depth over limit lifts to InputBoundExceeded",
          "[cross_binding][cluster8][phase2a]") {
    auto lib = find_lib();
    auto backend = make_ffi_backend(lib);
    AletheiaClient client(std::move(backend));

    REQUIRE(client.parse_dbc(std::stop_token{}, canonical_dbc()).has_value());
    // 63 always-wrappers + atomic + predicate = JSON depth 65 (> 64).
    LtlFormula inner =
        ltl::atomic(ltl::equals(SignalName{"TestSignal"}, PhysicalValue{Rational{0, 1}}));
    for (std::size_t i = 0; i < 63; ++i)
        inner = ltl::always(std::move(inner));
    std::vector<LtlFormula> props;
    props.push_back(std::move(inner));
    auto result = client.set_properties(std::stop_token{}, props);
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().kind() == ErrorKind::InputBoundExceeded);
    CHECK(result.error().code() == ErrorCode::ParseInputBoundExceeded);
    REQUIRE(result.error().bound_info().has_value());
    CHECK(result.error().bound_info()->bound_kind == bound_kind_nesting_depth);
    CHECK(result.error().bound_info()->limit == max_nesting_depth);
    CHECK(result.error().bound_info()->observed > max_nesting_depth);
}
