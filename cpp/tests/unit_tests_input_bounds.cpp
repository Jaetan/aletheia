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

#include <catch2/catch_test_macros.hpp>

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
