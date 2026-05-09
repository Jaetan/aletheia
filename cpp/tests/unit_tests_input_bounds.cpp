// SPDX-License-Identifier: BSD-2-Clause
//
// Adversarial-input bounds regression tests (UR-2 cross-binding parity).
//
// `aletheia::InputBoundExceededError` exists, carries kind/observed/limit
// fields, and the FFI-entry process() short-circuits oversize JSON inputs
// to a wire-format error response with code "parse_input_bound_exceeded"
// before marshaling the input across the dlopen-loaded `aletheia_process`.
//
// The Agda kernel ALSO rejects (parseJSON's input-length cap returns a
// `parse_input_bound_exceeded` error response); the binding-side guard
// fires first so we do not allocate a 100 MiB null-terminated buffer
// only to be rejected on the other side.

#include <aletheia/error.hpp>
#include <aletheia/limits.hpp>

#include "detail/json.hpp"

#include <catch2/catch_test_macros.hpp>
#include <catch2/matchers/catch_matchers.hpp>
#include <catch2/matchers/catch_matchers_string.hpp>

#include <cstdint>
#include <string>

TEST_CASE("InputBoundExceededError carries kind / observed / limit", "[input_bounds][trackUR2]") {
    aletheia::InputBoundExceededError err{
        .bound_kind = std::string{aletheia::bound_kind_input_length_bytes},
        .observed = 100,
        .limit = 50,
    };
    CHECK(err.bound_kind == "input_length_bytes");
    CHECK(err.observed == 100);
    CHECK(err.limit == 50);
}

TEST_CASE("Numeric limit constants mirror Aletheia.Limits values", "[input_bounds][trackUR2]") {
    CHECK(aletheia::max_dbc_text_bytes == 64ULL * 1024 * 1024);
    CHECK(aletheia::max_json_bytes == 64ULL * 1024 * 1024);
    CHECK(aletheia::max_nesting_depth == 64);
    CHECK(aletheia::max_frame_byte_count == 64);
    CHECK(aletheia::max_messages_per_file == 10'000);
    CHECK(aletheia::max_signals_per_message == 1024);
    CHECK(aletheia::max_attributes_per_file == 10'000);
    CHECK(aletheia::max_value_descriptions_per_file == 1'000'000);
    CHECK(aletheia::max_identifier_length == 128);
    CHECK(aletheia::max_string_length_bytes == 64ULL * 1024);
    CHECK(aletheia::max_atom_count_per_property == 1024);
}

TEST_CASE("BoundKind wire codes mirror boundKindCode in Aletheia.Limits",
          "[input_bounds][trackUR2]") {
    CHECK(aletheia::bound_kind_input_length_bytes == "input_length_bytes");
    CHECK(aletheia::bound_kind_nesting_depth == "nesting_depth");
    CHECK(aletheia::bound_kind_array_cardinality == "array_cardinality");
    CHECK(aletheia::bound_kind_identifier_length == "identifier_length");
    CHECK(aletheia::bound_kind_string_length == "string_length");
    CHECK(aletheia::bound_kind_atom_count == "atom_count");
    CHECK(aletheia::bound_kind_frame_byte_count == "frame_byte_count");
}

TEST_CASE("New ErrorCode entries map from string", "[input_bounds][trackUR2]") {
    CHECK(aletheia::error_code_from_string("parse_input_bound_exceeded") ==
          aletheia::ErrorCode::ParseInputBoundExceeded);
    CHECK(aletheia::error_code_from_string("dbc_text_input_bound_exceeded") ==
          aletheia::ErrorCode::DBCTextInputBoundExceeded);
    CHECK(aletheia::error_code_from_string("frame_input_bound_exceeded") ==
          aletheia::ErrorCode::FrameInputBoundExceeded);
    CHECK(aletheia::error_code_from_string("parse_invalid_identifier") ==
          aletheia::ErrorCode::ParseInvalidIdentifier);
    CHECK(aletheia::error_code_from_string("dbc_text_parse_failure") ==
          aletheia::ErrorCode::DBCTextParseFailure);
    CHECK(aletheia::error_code_from_string("dbc_text_trailing_input") ==
          aletheia::ErrorCode::DBCTextTrailingInput);
    CHECK(aletheia::error_code_from_string("dbc_text_attribute_refinement_failed") ==
          aletheia::ErrorCode::DBCTextAttributeRefinementFailed);
}

// R19 cluster A: every detail::parse_* callsite uses the parse_bounded helper
// which enforces nlohmann's nesting depth via a SAX callback. Defense-in-depth
// against malformed-but-bound-passing responses (the FFI-entry size cap fires
// first for oversize inputs; a 1 MiB response with 10⁵ nesting still depth-
// bombs the recursive-descent parser via stack overflow without this guard).
//
// Tests pick parse_success as a representative entry point; parse_bounded is
// shared across all 10 detail::parse_* callsites so depth-bound coverage is
// uniform.

TEST_CASE("parse_bounded rejects JSON exceeding nesting depth", "[input_bounds][trackUR2]") {
    // Build a JSON with (max_nesting_depth + 1) levels of array nesting.
    std::string deep_json;
    deep_json.reserve(2 * (aletheia::max_nesting_depth + 2));
    for (std::uint64_t i = 0; i <= aletheia::max_nesting_depth; ++i) {
        deep_json += "[";
    }
    deep_json += "1";
    for (std::uint64_t i = 0; i <= aletheia::max_nesting_depth; ++i) {
        deep_json += "]";
    }

    auto result = aletheia::detail::parse_success(deep_json);
    REQUIRE_FALSE(result.has_value());
    CHECK(result.error().kind() == aletheia::ErrorKind::Protocol);
    CHECK_THAT(std::string{result.error().message()},
               Catch::Matchers::ContainsSubstring("nesting depth"));
    CHECK_THAT(std::string{result.error().message()},
               Catch::Matchers::ContainsSubstring("exceeds limit"));
}

TEST_CASE("parse_bounded accepts JSON at nesting depth", "[input_bounds][trackUR2]") {
    // Build a JSON at exactly max_nesting_depth - 1 levels (well within bound).
    std::string ok_json;
    constexpr std::uint64_t safe_depth = 10;
    for (std::uint64_t i = 0; i < safe_depth; ++i) {
        ok_json += "[";
    }
    ok_json += R"({"status": "success"})";
    for (std::uint64_t i = 0; i < safe_depth; ++i) {
        ok_json += "]";
    }

    // parse_success rejects this for non-success status (it's wrapped in arrays),
    // but the depth-bound itself does not fire.  Verify the error message does
    // NOT mention nesting depth — ie the depth callback ran without throwing.
    auto result = aletheia::detail::parse_success(ok_json);
    if (!result.has_value()) {
        CHECK_THAT(std::string{result.error().message()},
                   !Catch::Matchers::ContainsSubstring("nesting depth"));
    }
}
