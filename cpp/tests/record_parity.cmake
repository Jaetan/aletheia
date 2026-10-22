# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
# The tests that hold the C++ binding to a record under docs/: the feature
# matrix, the log events, the object layout and the wire codes. The test
# section of cpp/CMakeLists.txt includes this file and shares its scope, so
# paths are relative to cpp/, and Catch2, yaml-cpp, the library targets and
# ALETHEIA_TEST_REPO_ROOT are the ones defined there.

# Feature matrix parity test (yaml-cpp, Catch2). Reads
# docs/FEATURE_MATRIX.yaml and verifies every C++ implemented entry
# ("<header>#<symbol>") resolves to an existing header containing the
# symbol as a whole-word match. Parity source: docs/FEATURE_MATRIX.yaml.
add_executable(feature_matrix_tests tests/test_feature_matrix_parity.cpp)
target_compile_features(feature_matrix_tests PRIVATE cxx_std_23)
target_link_libraries(feature_matrix_tests
    PRIVATE yaml-cpp::yaml-cpp Catch2::Catch2WithMain)
add_test(NAME feature_matrix_tests COMMAND feature_matrix_tests)
set_tests_properties(feature_matrix_tests PROPERTIES
    ENVIRONMENT "${ALETHEIA_TEST_REPO_ROOT}")

# Cross-binding log-event parity test (yaml-cpp + aletheia-cpp,
# Catch2). Reads docs/LOG_EVENTS.yaml, runs a comprehensive mock-backend
# workflow capturing LogRecord events, and asserts each emitted event is
# a member of the canonical name set.
# rts_setup_listener.cpp: set_properties renders the condition descriptions,
# which needs the GHC RTS up; this mock-backend test creates no real
# FfiBackend, so the listener brings the runtime up for the process.
add_executable(log_events_tests tests/test_log_events_parity.cpp tests/rts_setup_listener.cpp)
target_include_directories(log_events_tests PRIVATE src)
target_link_libraries(log_events_tests
    PRIVATE aletheia-cpp yaml-cpp::yaml-cpp Catch2::Catch2WithMain)
add_test(NAME log_events_tests COMMAND log_events_tests)
set_tests_properties(log_events_tests PROPERTIES
    ENVIRONMENT "${ALETHEIA_TEST_REPO_ROOT}")

# The wrapper's object layout against docs/CPP_LAYOUT.yaml (yaml-cpp,
# Catch2): sizeof and alignof of every public type tests/layout_roster.inc
# lists. Header-only measurement, so no RTS and no FFI backend. The record
# is the shipped build's layout; the mutation tree's debug-mode containers
# are laid out otherwise, so it does not register the test.
if(NOT ALETHEIA_MUTATION)
    add_executable(layout_tests tests/test_cpp_layout.cpp)
    target_link_libraries(layout_tests
        PRIVATE aletheia-cpp yaml-cpp::yaml-cpp Catch2::Catch2WithMain)
    add_test(NAME layout_tests COMMAND layout_tests)
    set_tests_properties(layout_tests PROPERTIES
        ENVIRONMENT "${ALETHEIA_TEST_REPO_ROOT}")
endif()

# Cross-binding wire-code parity test (yaml-cpp + aletheia-cpp, Catch2).
# Reads docs/WIRE_CODES.yaml (the kernel-anchored wire-code SSOT) and
# asserts the IssueCode and ErrorCode enums are each a bijection with
# their YAML section: every wire code maps to a non-Unknown enumerator
# and no enumerator lacks an SSOT row. Pure vocabulary test: no RTS, no
# FFI backend, so no rts_setup_listener.cpp.
add_executable(wire_codes_tests tests/test_wire_codes_parity.cpp)
target_link_libraries(wire_codes_tests
    PRIVATE aletheia-cpp yaml-cpp::yaml-cpp Catch2::Catch2WithMain)
add_test(NAME wire_codes_tests COMMAND wire_codes_tests)
set_tests_properties(wire_codes_tests PROPERTIES
    ENVIRONMENT "${ALETHEIA_TEST_REPO_ROOT}")
