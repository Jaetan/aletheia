// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// Adversarial-input bounds, and their cross-binding parity.
//
// `aletheia::InputBoundExceededError` exists, carries kind/observed/limit
// fields and the field a DBC size bound names, and the FFI-entry process()
// short-circuits oversize JSON inputs to a wire-format error response with
// code "input_bound_exceeded" before marshaling the input across the
// dlopen-loaded `aletheia_process`.
//
// The Agda kernel ALSO rejects (parseJSON's input-length cap returns an
// `input_bound_exceeded` error response); the binding-side guard
// fires first so we do not allocate a 100 MiB null-terminated buffer
// only to be rejected on the other side.

#include <aletheia/backend.hpp>
#include <aletheia/client.hpp>
#include <aletheia/dbc.hpp>
#include <aletheia/error.hpp>
#include <aletheia/limits.hpp>

#include "detail/json.hpp"
#include "detail/mock_backend.hpp"
#include "required.hpp"
#include "u128_testing.hpp"

#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>

#include <limits>
#include <memory>
#include <stop_token>
#include <string>
#include <string_view>
#include <utility>

using aletheia::test::required;

TEST_CASE("InputBoundExceededError carries kind / observed / limit, and no field unless given",
          "[input_bounds]") {
    aletheia::InputBoundExceededError const err{
        .bound_kind = std::string{aletheia::bound_kind_input_length_bytes},
        .observed = 100,
        .limit = 50,
    };
    CHECK(err.bound_kind == "input_length_bytes");
    CHECK(err.observed == 100);
    CHECK(err.limit == 50);
    // The binding's own input-length refusals construct it this way.
    CHECK_FALSE(err.field.has_value());
}

TEST_CASE("Numeric limit constants mirror Aletheia.Limits values", "[input_bounds]") {
    CHECK(aletheia::max_dbc_text_bytes == 64ULL * 1024 * 1024);
    CHECK(aletheia::max_json_bytes == 64ULL * 1024 * 1024);
    CHECK(aletheia::max_nesting_depth == 64);
    CHECK(aletheia::max_messages_per_file == 10'000);
    CHECK(aletheia::max_signals_per_message == 1024);
    CHECK(aletheia::max_attributes_per_file == 10'000);
    CHECK(aletheia::max_value_descriptions_per_file == 1'000'000);
    CHECK(aletheia::max_comments_per_file == 10'000);
    CHECK(aletheia::max_nodes_per_file == 10'000);
    CHECK(aletheia::max_value_tables_per_file == 10'000);
    CHECK(aletheia::max_signal_groups_per_file == 10'000);
    CHECK(aletheia::max_environment_variables_per_file == 10'000);
    CHECK(aletheia::max_unresolved_value_descriptions_per_file == 10'000);
    CHECK(aletheia::max_enum_labels_per_attribute == 10'000);
    CHECK(aletheia::max_multiplex_values_per_signal == 1024);
    CHECK(aletheia::max_identifier_length == 128);
    CHECK(aletheia::max_string_length_characters == 64ULL * 1024);
    CHECK(aletheia::max_atom_count_per_property == 1024);
    CHECK(aletheia::max_properties_per_stream == 1024);
    CHECK(aletheia::max_rational_component_magnitude ==
          std::numeric_limits<unsigned __int128>::max());
}

TEST_CASE("BoundKind wire codes mirror boundKindCode in Aletheia.Limits", "[input_bounds]") {
    CHECK(aletheia::bound_kind_input_length_bytes == "input_length_bytes");
    CHECK(aletheia::bound_kind_nesting_depth == "nesting_depth");
    CHECK(aletheia::bound_kind_array_cardinality == "array_cardinality");
    CHECK(aletheia::bound_kind_identifier_length == "identifier_length");
    CHECK(aletheia::bound_kind_string_length == "string_length");
    CHECK(aletheia::bound_kind_atom_count == "atom_count");
    CHECK(aletheia::bound_kind_property_count == "property_count");
    CHECK(aletheia::bound_kind_rational_component_magnitude == "rational_component_magnitude");
}

TEST_CASE("New ErrorCode entries map from string", "[input_bounds]") {
    // The parse / dbc_text / frame input-bound codes consolidated to a single
    // InputBoundExceeded; discriminate the source bound via the structured
    // bound_kind field.
    CHECK(aletheia::error_code_from_string("input_bound_exceeded") ==
          aletheia::ErrorCode::InputBoundExceeded);
    CHECK(aletheia::error_code_from_string("parse_invalid_identifier") ==
          aletheia::ErrorCode::ParseInvalidIdentifier);
    CHECK(aletheia::error_code_from_string("text_parse_failure") ==
          aletheia::ErrorCode::TextParseFailure);
    CHECK(aletheia::error_code_from_string("text_trailing_input") ==
          aletheia::ErrorCode::TextTrailingInput);
    CHECK(aletheia::error_code_from_string("dbc_text_attribute_refinement_failed") ==
          aletheia::ErrorCode::DBCTextAttributeRefinementFailed);
}

TEST_CASE("parse_non_integer_multiplex_value maps from string", "[parse_error]") {
    // A wire code of its own, distinct from `parse_invalid_presence`: that one
    // is a presence string other than "always", this one a non-natural element
    // in the multiplex-values array. The binding must decode it to the
    // matching enumerator.
    CHECK(aletheia::error_code_from_string("parse_non_integer_multiplex_value") ==
          aletheia::ErrorCode::ParseNonIntegerMultiplexValue);
}

TEST_CASE("the binary entries' frame and signal-value refusals map from string", "[parse_error]") {
    // The kernel parses what a binary entry is handed and names each refusal;
    // each name decodes to its own enumerator.
    CHECK(aletheia::error_code_from_string("parse_dlc_code_out_of_range") ==
          aletheia::ErrorCode::ParseDlcCodeOutOfRange);
    CHECK(aletheia::error_code_from_string("parse_payload_length_mismatch") ==
          aletheia::ErrorCode::ParsePayloadLengthMismatch);
    CHECK(aletheia::error_code_from_string("parse_payload_byte_out_of_range") ==
          aletheia::ErrorCode::ParsePayloadByteOutOfRange);
    CHECK(aletheia::error_code_from_string("parse_non_positive_denominator") ==
          aletheia::ErrorCode::ParseNonPositiveDenominator);
    CHECK(aletheia::error_code_from_string("parse_signal_array_length_mismatch") ==
          aletheia::ErrorCode::ParseSignalArrayLengthMismatch);
    CHECK(aletheia::error_code_from_string("parse_timestamp_past_wire") ==
          aletheia::ErrorCode::ParseTimestampPastWire);
}

// Every detail::parse_* reads its reply through detail::parse_json, which holds
// every event of nlohmann's SAX parse to max_nesting_depth. Defense-in-depth
// against malformed-but-bound-passing responses (the FFI-entry size cap fires
// first for oversize inputs; a 1 MiB response with 10⁵ nesting still depth-
// bombs the recursive-descent parser via stack overflow without this guard).
//
// The cases pick parse_success as a representative entry point; every
// detail::parse_* entry point goes through parse_json, so the depth bound
// covers them uniformly.

TEST_CASE("parse_json rejects JSON exceeding nesting depth", "[input_bounds]") {
    // Build a JSON with (max_nesting_depth + 1) levels of array nesting.
    std::string deep_json;
    deep_json.reserve(2 * (aletheia::max_nesting_depth + 2));
    deep_json.append(aletheia::max_nesting_depth + 1, '[');
    deep_json += '1';
    deep_json.append(aletheia::max_nesting_depth + 1, ']');

    // The scalar inside the innermost array is the event past the bound.
    auto const result = aletheia::detail::parse_success(deep_json);
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().kind() == aletheia::ErrorKind::Protocol);
    CHECK(result.error().message() ==
          "reply: expected JSON text, got JSON nesting depth 65 exceeds limit 64");
}

TEST_CASE("parse_json accepts JSON at nesting depth", "[input_bounds]") {
    // A value at the bound itself: the scalar sits inside max_nesting_depth
    // arrays.
    std::string ok_json;
    ok_json.append(aletheia::max_nesting_depth, '[');
    ok_json += '1';
    ok_json.append(aletheia::max_nesting_depth, ']');

    // parse_success refuses this for not being an object, which it could
    // only say once the depth bound let the whole text be read.
    auto const result = aletheia::detail::parse_success(ok_json);
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().message() == "reply: expected object, got array");
}

// parse_dbc_text pre-checks the inner text size against max_dbc_text_bytes
// before wrapping it in a JSON command, so the rejection carries the
// consolidated InputBoundExceeded error code and InputBoundExceeded error
// kind.

TEST_CASE("parse_dbc_text rejects oversize DBC text", "[input_bounds]") {
    // Mock backend that never returns — the bound check fires before any
    // backend call. Construct with no scripted responses.
    auto mock = std::make_unique<aletheia::MockBackend>();
    auto client = required(aletheia::AletheiaClient::create(std::move(mock)));

    std::string const big_text(aletheia::max_dbc_text_bytes + 1, 'x');
    std::stop_source const stop_source;
    auto const result = client.parse_dbc_text(stop_source.get_token(), big_text);
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().kind() == aletheia::ErrorKind::InputBoundExceeded);
    CHECK(result.error().code() == aletheia::ErrorCode::InputBoundExceeded);
    CHECK_THAT(
        std::string{result.error().message()},
        Catch::Matchers::ContainsSubstring("input length (bytes) 67108865 exceeds limit 67108864"));

    // bound_info() is populated with the structured triple, matching Python's
    // `InputBoundExceededError.kind`
    // / `.observed` / `.limit` and Go's `*InputBoundExceededError.BoundKind`
    // / `.Observed` / `.Limit`.
    REQUIRE(result.error().bound_info().has_value());
    CHECK(result.error().bound_info()->bound_kind == aletheia::bound_kind_input_length_bytes);
    CHECK(result.error().bound_info()->observed == aletheia::max_dbc_text_bytes + 1);
    CHECK(result.error().bound_info()->limit == aletheia::max_dbc_text_bytes);
}

// The FFI-entry oversize-JSON short-circuit in FfiBackend::process emits
// structured bound_kind/observed/limit fields
// alongside the wire code; the public parse_* paths lift those into the
// AletheiaError's bound_info() so consumers get the typed triple regardless
// of which parser surface rejected the input.  Tested here against a hand-
// crafted wire-form JSON that mirrors the FFI backend's synthesis.

TEST_CASE("Input-bound error JSON lifts structured fields into bound_info", "[input_bounds]") {
    std::string const err_json =
        R"({"status":"error",)"
        R"("code":"input_bound_exceeded",)"
        R"("message":"input length (bytes) 100000000 exceeds limit 67108864",)"
        R"("bound_kind":"input_length_bytes",)"
        R"("observed":100000000,)"
        R"("limit":67108864})";
    auto const result = aletheia::detail::parse_success(err_json);
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().kind() == aletheia::ErrorKind::InputBoundExceeded);
    CHECK(result.error().code() == aletheia::ErrorCode::InputBoundExceeded);
    REQUIRE(result.error().bound_info().has_value());
    CHECK(result.error().bound_info()->bound_kind == "input_length_bytes");
    CHECK(result.error().bound_info()->observed == 100000000ULL);
    CHECK(result.error().bound_info()->limit == 67108864ULL);
    // An input-length bound names no field, and the envelope carries none.
    CHECK_FALSE(result.error().bound_info()->field.has_value());
}

TEST_CASE("Input-bound error JSON without structured fields is refused at its bound_kind",
          "[input_bounds]") {
    // The kernel writes the triple on every bound refusal, so an envelope
    // without it is the wire's fault, refused as every reply place is.
    std::string const err_json = R"({"status":"error",)"
                                 R"("code":"input_bound_exceeded",)"
                                 R"("message":"input length exceeded"})";
    auto const result = aletheia::detail::parse_success(err_json);
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().kind() == aletheia::ErrorKind::Protocol);
    CHECK(result.error().message() == "reply bound_kind: expected string, got nothing");
    CHECK_FALSE(result.error().bound_info().has_value());
}

// The kernel refuses a DBC past a size bound on every command that takes one;
// the client surfaces that refusal as one typed error whichever command met it.
template<typename T>
static void check_signal_groups_refusal(aletheia::Result<T> const& result) {
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().kind() == aletheia::ErrorKind::InputBoundExceeded);
    CHECK(result.error().code() == aletheia::ErrorCode::InputBoundExceeded);
    CHECK(result.error().message() == "signal groups array: array cardinality 10001 exceeds limit "
                                      "10000");
    REQUIRE(result.error().bound_info().has_value());
    CHECK(result.error().bound_info()->bound_kind == aletheia::bound_kind_array_cardinality);
    CHECK(result.error().bound_info()->observed == aletheia::max_signal_groups_per_file + 1);
    CHECK(result.error().bound_info()->limit == aletheia::max_signal_groups_per_file);
    CHECK(result.error().bound_info()->field == "signal groups array");
}

TEST_CASE("every DBC command surfaces a size-bound refusal as InputBoundExceeded",
          "[input_bounds]") {
    constexpr std::string_view refusal =
        R"({"status":"error","code":"input_bound_exceeded",)"
        R"("message":"signal groups array: array cardinality 10001 exceeds limit 10000",)"
        R"("field":"signal groups array",)"
        R"("bound_kind":"array_cardinality","observed":10001,"limit":10000})";
    auto mock = std::make_unique<aletheia::MockBackend>();
    // One answer for each of the three commands below.
    mock->queue_response(std::string{refusal});
    mock->queue_response(std::string{refusal});
    mock->queue_response(std::string{refusal});
    auto client = required(aletheia::AletheiaClient::create(std::move(mock)));
    aletheia::DbcDefinition const dbc{};

    check_signal_groups_refusal(client.parse_dbc(std::stop_token{}, dbc));
    check_signal_groups_refusal(client.validate_dbc(std::stop_token{}, dbc));
    check_signal_groups_refusal(client.format_dbc_text(std::stop_token{}, dbc));
}
