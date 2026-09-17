#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/aletheia/cross_binding_integration_test.go,
# cpp/tests/test_cross_binding_integration.cpp, cpp/tests/integration_tests.cpp,
# python/tests/test_cross_binding_integration.py and the Python test files the
# roster below names.
# Claim: every case the Go binding carries for the shared protocol has a case
# in the C++ and Python trees asserting the same thing. AGENTS/go.md cat 33(d)
# makes a case one binding carries and another lacks a finding, and nothing
# reads the three rosters together: the siblings are real but scattered, so a
# case deleted or renamed in one tree leaves the other two saying nothing.
# The roster is the table below, one row per Go case, each naming what to look
# for in each tree. It is the record of a reading done once.
# Non-zero exit: a case named here is not in its tree. Exits 2 when a file is
# not where this expects it.
set -u
cd "$(dirname "$0")/.." || exit 2

go_file=go/aletheia/cross_binding_integration_test.go
cpp_cross=cpp/tests/test_cross_binding_integration.cpp
cpp_integration=cpp/tests/integration_tests.cpp
py_cross=python/tests/test_cross_binding_integration.py
for f in "$go_file" "$cpp_cross" "$cpp_integration" "$py_cross"; do
	[ -f "$f" ] || exit 2
done

# go case | c++ file | c++ case | python file | python case
roster=$(
	cat <<'ROWS'
TestCrossBinding_ParseDBCResponseShape|cpp_cross|ParsedDBC response has documented shape|python/tests/test_cross_binding_integration.py|test_parse_dbc_response_shape
TestCrossBinding_ValidateDBCResponseShape|cpp_cross|ValidationResult response has documented shape|python/tests/test_cross_binding_integration.py|test_validate_dbc_response_shape
TestCrossBinding_SendFrameAck|cpp_cross|send_frame ack response has documented shape|python/tests/test_cross_binding_integration.py|test_send_frame_ack_response_shape
TestCrossBinding_SendFrameViolation|cpp_cross|send_frame violation response has documented shape|python/tests/test_cross_binding_integration.py|test_send_frame_violation_response_shape
TestCrossBinding_SendFrameMultiEvent|cpp_cross|send_frame multi-event batch|python/tests/test_classify_satisfied_complete.py|test_multi_event_frame_satisfaction_plus_violation
TestCrossBinding_CANIDRefusedAtTheTypeBoundary|cpp_cross|invalid CAN ID is rejected at type boundary|python/tests/test_cross_binding_integration.py|test_send_frame_error_response_shape
TestCrossBinding_SendFrameBrsEsiPassthrough|cpp_cross|send_frame with BRS / ESI passthrough|python/tests/test_unified_client_canfd_mux.py|test_canfd_brs_esi_passthrough
TestCrossBinding_IdentifierAtMaxLengthAccepted|cpp_cross|identifier at max length is accepted|python/tests/test_input_bounds.py|test_identifier_at_max_length_accepted
TestCrossBinding_IdentifierOverMaxRejected|cpp_cross|identifier over max length is rejected|python/tests/test_input_bounds.py|test_identifier_one_over_max_rejected
TestCrossBinding_GeometryGateRefusesOutOfFrameStartBit|cpp_integration|out-of-frame start bit|python/tests/test_parse_dbc_text.py|test_text_route_refuses_out_of_frame_start_bit
TestCrossBinding_MotorolaFullFrameClosure|cpp_integration|text-loaded Motorola full-frame signal is accepted back by the JSON route|python/tests/test_parse_dbc_text.py|test_text_loaded_motorola_rounds_through_json_surface
TestCrossBinding_NestingDepthLiftsToInputBoundExceeded|cpp_cross|nesting depth over limit lifts to InputBoundExceeded|python/tests/test_input_bounds.py|test_nested_at_depth_63_rejected
TestCrossBinding_BinaryExtractionReasonParity|cpp_integration|binary extraction decodes values, wire reasons, and absent exactly|python/tests/test_binary_extraction.py|test_known_code_surfaces_wire_reason_verbatim
ROWS
)

status=0
rows=0
while IFS='|' read -r go_case cpp_where cpp_case py_file py_case; do
	[ -n "$go_case" ] || continue
	rows=$((rows + 1))
	case $cpp_where in
		cpp_cross) cpp_file=$cpp_cross ;;
		cpp_integration) cpp_file=$cpp_integration ;;
		*) echo "$go_case: the roster names no C++ file"; status=1; continue ;;
	esac
	grep -q "^func $go_case(" "$go_file" || {
		echo "$go_case: not in $go_file"
		status=1
	}
	grep -qF "$cpp_case" "$cpp_file" || {
		echo "$go_case: its C++ sibling \"$cpp_case\" is not in $cpp_file"
		status=1
	}
	[ -f "$py_file" ] || { echo "$go_case: $py_file is not there"; status=1; continue; }
	grep -qE "def $py_case\(" "$py_file" || {
		echo "$go_case: its Python sibling $py_case is not in $py_file"
		status=1
	}
done <<< "$roster"

# Every Go case of the file is in the roster, so a new one cannot be added
# without saying where its siblings are.
while read -r name; do
	grep -q "^$name|" <<< "$roster" || {
		echo "$name is in $go_file and not in this roster"
		status=1
	}
done < <(grep -oE "^func TestCrossBinding_[A-Za-z0-9_]+" "$go_file" | sed 's/func //')

[ "$status" -eq 0 ] || exit 1
echo "PASS: each of the $rows cross-binding cases has its sibling in both other trees"
