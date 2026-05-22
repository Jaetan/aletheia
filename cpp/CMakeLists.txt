cmake_minimum_required(VERSION 3.25)
project(aletheia-cpp VERSION 1.1.1 LANGUAGES CXX)

# Default to Release when no build type is specified (avoids -O0 benchmarks)
if(NOT CMAKE_BUILD_TYPE AND NOT CMAKE_CONFIGURATION_TYPES)
    set(CMAKE_BUILD_TYPE Release CACHE STRING "Build type" FORCE)
endif()

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

# ---------------------------------------------------------------------------
# clang-tidy integration (opt-in)
# ---------------------------------------------------------------------------
#
# When enabled, clang-tidy runs on every compile of the aletheia-cpp library
# target, turning .clang-tidy findings into build-time errors (via
# WarningsAsErrors: '*' in the project .clang-tidy). Scoped to the library
# only — tests use Catch2 conventions that trigger many cognitive-complexity
# and designated-initialiser findings that are not worth fixing.
#
# Enable with: cmake -B build -DALETHEIA_CLANG_TIDY=ON
option(ALETHEIA_CLANG_TIDY "Run clang-tidy on aletheia-cpp sources" OFF)

if(ALETHEIA_CLANG_TIDY)
    find_program(CLANG_TIDY_EXE NAMES clang-tidy REQUIRED)
    set(ALETHEIA_CLANG_TIDY_COMMAND "${CLANG_TIDY_EXE};--quiet")
    message(STATUS "clang-tidy integration enabled: ${CLANG_TIDY_EXE}")
endif()

# ---------------------------------------------------------------------------
# Sanitizer lanes (R18 cluster 5 — Cat 33a, advisor option (d))
# ---------------------------------------------------------------------------
#
# Plan (d) per cluster 5 architectural choice: ASan against C++ unit tests
# that don't load libaletheia-ffi.so (MockBackend-only), plus UBSan against
# every test target including those that DO load the .so.  ASan and the
# GHC RTS conflict on signal handlers and shadow-memory layout — the gap is
# documented in docs/architecture/CGO_NOTES.md, not papered over.  UBSan
# tolerates the foreign runtime and catches signed-overflow / shift /
# null-deref UB on the C++ side regardless of the FFI load state.
#
# Enable with one of:
#   cmake -B build-asan   -DALETHEIA_SANITIZER=address
#   cmake -B build-ubsan  -DALETHEIA_SANITIZER=undefined
#   cmake -B build-tsan   -DALETHEIA_SANITIZER=thread
#
# Use a separate build directory per sanitizer — sanitizer flags are not
# safe to mix on the same archive.
set(ALETHEIA_SANITIZER "" CACHE STRING
    "Sanitizer lane: address | undefined | thread (empty = off)")

set(ALETHEIA_SANITIZER_FLAGS "")
if(ALETHEIA_SANITIZER STREQUAL "address")
    set(ALETHEIA_SANITIZER_FLAGS -fsanitize=address -fno-omit-frame-pointer)
elseif(ALETHEIA_SANITIZER STREQUAL "undefined")
    set(ALETHEIA_SANITIZER_FLAGS
        -fsanitize=undefined -fno-omit-frame-pointer -fno-sanitize-recover=undefined)
elseif(ALETHEIA_SANITIZER STREQUAL "thread")
    set(ALETHEIA_SANITIZER_FLAGS -fsanitize=thread -fno-omit-frame-pointer)
elseif(ALETHEIA_SANITIZER)
    message(FATAL_ERROR
        "ALETHEIA_SANITIZER='${ALETHEIA_SANITIZER}' invalid; "
        "use one of: address, undefined, thread (or unset).")
endif()

if(ALETHEIA_SANITIZER_FLAGS)
    message(STATUS "Sanitizer lane: ${ALETHEIA_SANITIZER}")
    # Apply a sanitizer ignorelist so vendored third-party UB (zippy.hpp
    # inside OpenXLSX) doesn't trip our own UBSan lane.  Aletheia code
    # stays fully instrumented; only the specific paths listed in
    # sanitizer-ignorelist.txt are exempt.  See cpp/sanitizer-ignorelist.txt
    # for the per-entry rationale.
    #
    # -fsanitize-ignorelist= is a clang feature; g++ has no equivalent.
    # When the sanitizer lane is configured under g++, third-party UB in
    # OpenXLSX/zippy will surface — use clang for the canonical sanitizer
    # build (matches the libFuzzer lane's clang requirement).
    if(CMAKE_CXX_COMPILER_ID STREQUAL "Clang")
        set(ALETHEIA_SAN_IGNORE "${CMAKE_CURRENT_SOURCE_DIR}/sanitizer-ignorelist.txt")
        list(APPEND ALETHEIA_SANITIZER_FLAGS
            "-fsanitize-ignorelist=${ALETHEIA_SAN_IGNORE}")
    else()
        message(WARNING
            "ALETHEIA_SANITIZER set under ${CMAKE_CXX_COMPILER_ID}; "
            "third-party UB in OpenXLSX/zippy will surface (g++ lacks "
            "-fsanitize-ignorelist=).  Use clang for clean sanitizer runs: "
            "-DCMAKE_CXX_COMPILER=clang++")
    endif()
    add_compile_options(${ALETHEIA_SANITIZER_FLAGS})
    add_link_options(${ALETHEIA_SANITIZER_FLAGS})
endif()

# ---------------------------------------------------------------------------
# Mutation testing (R18 cluster 7 / Cat 14(g))
# ---------------------------------------------------------------------------
# Opt-in via -DALETHEIA_MUTATION=ON.  When enabled, the Mull IR-pass plugin
# is attached to the aletheia-cpp library + unit_tests target ONLY (NOT to
# Catch2 / OpenXLSX / yaml-cpp / nlohmann_json — third-party code with heavy
# templates triggers compiler crashes under the plugin, and we don't care
# about their mutation score anyway).
#
# Build into a dedicated directory so the instrumented artifacts are not
# mixed with the standard build:
#
#   cmake -B build-mutation -DALETHEIA_MUTATION=ON \
#         -DCMAKE_C_COMPILER=clang-19 -DCMAKE_CXX_COMPILER=clang++-19
#   cmake --build build-mutation --target unit_tests
#   mull-runner-19 ./build-mutation/unit_tests
#
# Requires Mull-19 (LLVM 19) installed (see docs/operations/MUTATION.md §
# Installation) and clang-19 from the apt repo.  Mull's IR pass uses LLVM
# version-specific APIs, so the compiler version MUST match the Mull binary
# version (mull-ir-frontend-19 ↔ clang-19; the next Mull release will be
# Mull-20 ↔ clang-20).  -O0 -g is mandatory: optimisations elide AST nodes
# Mull would otherwise mutate, debug info pins source locations in the
# survivor report.  ALETHEIA_MUTATION_FLAGS is consumed by the per-target
# target_compile_options() calls below (next to the add_library /
# add_executable definitions for aletheia-cpp + unit_tests).
option(ALETHEIA_MUTATION "Build aletheia-cpp + unit_tests with Mull IR pass plugin" OFF)
set(ALETHEIA_MUTATION_FLAGS "")
if(ALETHEIA_MUTATION)
    if(NOT CMAKE_CXX_COMPILER_ID STREQUAL "Clang")
        message(FATAL_ERROR
            "ALETHEIA_MUTATION requires clang-19 (got ${CMAKE_CXX_COMPILER_ID}); "
            "use a separate build dir: -DCMAKE_C_COMPILER=clang-19 "
            "-DCMAKE_CXX_COMPILER=clang++-19")
    endif()
    set(MULL_PLUGIN "$ENV{HOME}/.local/bin/mull-ir-frontend-19")
    if(NOT EXISTS "${MULL_PLUGIN}")
        message(FATAL_ERROR
            "Mull IR pass plugin not found at ${MULL_PLUGIN}; "
            "install Mull-19 per docs/operations/MUTATION.md § Installation")
    endif()
    message(STATUS "Mutation lane: -fpass-plugin=${MULL_PLUGIN} (aletheia-cpp + unit_tests only)")
    set(ALETHEIA_MUTATION_FLAGS -fpass-plugin=${MULL_PLUGIN} -g -O0)
endif()

# ---------------------------------------------------------------------------
# Dependencies (fetched, not exported to consumers)
# ---------------------------------------------------------------------------

include(FetchContent)

set(JSON_Install OFF CACHE BOOL "" FORCE)
FetchContent_Declare(json
    URL https://github.com/nlohmann/json/releases/download/v3.11.3/json.tar.xz
    URL_HASH SHA256=d6c65aca6b1ed68e7a182f4757257b107ae403032760ed6ef121c9d55e81757d)

FetchContent_Declare(yaml-cpp
    URL https://github.com/jbeder/yaml-cpp/archive/refs/tags/0.8.0.tar.gz
    URL_HASH SHA256=fbe74bbdcee21d656715688706da3c8becfd946d92cd44705cc6098bb23b3a16)
set(YAML_CPP_BUILD_TESTS OFF CACHE BOOL "" FORCE)
set(YAML_CPP_BUILD_TOOLS OFF CACHE BOOL "" FORCE)

# OpenXLSX is pinned to a master commit (2025-07-14) because the latest tagged
# release is v0.3.2 from 2021, which the upstream README explicitly flags as
# "severely outdated" and predates the <cstdint> include fix needed for GCC 15.
# Re-evaluate when troldal/OpenXLSX cuts a new release tag past v0.3.2.
FetchContent_Declare(OpenXLSX
    URL https://github.com/troldal/OpenXLSX/archive/5723411d47643ce3b5b9994064c26ca8cd841f13.tar.gz
    URL_HASH SHA256=86bdb7aa594a0b2bea31cae9e4603832844be2095d7e281e9d7e74003bc16b98)

# yaml-cpp 0.8.0 has a latent bug around missing <cstdint> / uint16_t that
# only links cleanly when the parent project defines CMAKE_CXX_STANDARD to at
# least C++20 (works around the transitive-include path on GCC 15). Scope the
# workaround to the FetchContent configure step with block(SCOPE_FOR VARIABLES)
# instead of a global set() — the project's own C++23 requirement (on
# aletheia-cpp, via target_compile_features below) is then not polluted.
# CMAKE_POLICY_VERSION_MINIMUM 3.5 also belongs here: yaml-cpp 0.8.0 and
# OpenXLSX use an old cmake_minimum_required that CMake 4.x rejects without
# this nudge.
#
# TODO(R12-M3): Drop this block when yaml-cpp ≥ 0.8.1 (or whatever release
# follows 0.8.0) publishes the upstream-merged <cstdint> include fix and we
# bump FetchContent_Declare above.
block(SCOPE_FOR VARIABLES)
    set(CMAKE_CXX_STANDARD 20)
    set(CMAKE_CXX_STANDARD_REQUIRED ON)
    set(CMAKE_POLICY_VERSION_MINIMUM 3.5)
    FetchContent_MakeAvailable(json yaml-cpp OpenXLSX)
endblock()

# ---------------------------------------------------------------------------
# Library
# ---------------------------------------------------------------------------

add_library(aletheia-cpp
    src/backend.cpp
    src/client.cpp
    src/dbc.cpp
    src/detail/loader_utils.cpp
    src/enrich.cpp
    src/excel.cpp
    src/ffi_backend.cpp
    src/mock_backend.cpp
    src/json_serialize.cpp
    src/json_parse.cpp
    src/rational_renderer.cpp
    src/types.cpp
    src/yaml.cpp)

target_include_directories(aletheia-cpp
    PUBLIC
        $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
        $<INSTALL_INTERFACE:${CMAKE_INSTALL_INCLUDEDIR}>
    PRIVATE src)

target_compile_features(aletheia-cpp PUBLIC cxx_std_23)

# R18 cluster 7 — apply Mull IR pass plugin to aletheia-cpp ONLY when
# ALETHEIA_MUTATION=ON.  The plugin would crash clang on Catch2's heavy
# templates if applied globally; per-target keeps it scoped to the code we
# actually want to mutate.
if(ALETHEIA_MUTATION)
    target_compile_options(aletheia-cpp PRIVATE ${ALETHEIA_MUTATION_FLAGS})
endif()

# UR-3.3 (Reproducible build verification): strip the build-host absolute path
# from __FILE__ macros and any debug info embedded in the library, so binaries
# produced from /home/$USER/aletheia on different hosts are byte-identical.
# Defense-in-depth — Release builds don't currently emit DWARF that would carry
# host paths, but the flag prevents future regression if anyone enables -g.
# GCC and Clang both support -ffile-prefix-map (covers -fdebug-prefix-map +
# -fmacro-prefix-map) since GCC 8 / Clang 10.
#
# NOT applied when ALETHEIA_MUTATION=ON: Mull-19's IR pass crashes (clang
# exit 139) when -ffile-prefix-map is in the flag list.  The mutation lane
# uses `cpp/build-mutation/` exclusively and is dev-only (never shipped),
# so reproducibility doesn't apply there.
if(CMAKE_CXX_COMPILER_ID MATCHES "GNU|Clang" AND NOT ALETHEIA_MUTATION)
    target_compile_options(aletheia-cpp PRIVATE
        "-ffile-prefix-map=${CMAKE_SOURCE_DIR}=.")
endif()

target_link_libraries(aletheia-cpp
    PRIVATE dl
        $<BUILD_INTERFACE:nlohmann_json::nlohmann_json>
        $<BUILD_INTERFACE:yaml-cpp::yaml-cpp>
        $<BUILD_INTERFACE:OpenXLSX::OpenXLSX>)

set_target_properties(aletheia-cpp PROPERTIES
    SOVERSION 1
    VERSION ${PROJECT_VERSION})

if(ALETHEIA_CLANG_TIDY)
    set_target_properties(aletheia-cpp PROPERTIES
        CXX_CLANG_TIDY "${ALETHEIA_CLANG_TIDY_COMMAND}")
endif()

# ---------------------------------------------------------------------------
# Install & export (allows find_package(aletheia-cpp) by downstream projects)
# ---------------------------------------------------------------------------

include(GNUInstallDirs)
include(CMakePackageConfigHelpers)

install(TARGETS aletheia-cpp
    EXPORT aletheia-cpp-targets
    LIBRARY  DESTINATION ${CMAKE_INSTALL_LIBDIR}
    ARCHIVE  DESTINATION ${CMAKE_INSTALL_LIBDIR}
    INCLUDES DESTINATION ${CMAKE_INSTALL_INCLUDEDIR})

# include/aletheia/detail/cache_keys.hpp is intentionally exported even though
# it lives under detail/. The <aletheia/client.hpp> facade includes it directly
# and uses the concrete types (FrameKey, FrameKeyLess, SignalKey, MessageKey)
# in AletheiaClient's private member layout, so stripping it from the install
# would leave the installed facade uncompilable. The header is marked
# `IWYU pragma: private, include "aletheia/client.hpp"` and documents that
# its layout is not part of the supported API.
install(DIRECTORY include/ DESTINATION ${CMAKE_INSTALL_INCLUDEDIR})

install(EXPORT aletheia-cpp-targets
    NAMESPACE aletheia::
    DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/aletheia-cpp)

configure_package_config_file(
    ${CMAKE_CURRENT_SOURCE_DIR}/cmake/aletheia-cpp-config.cmake.in
    ${CMAKE_CURRENT_BINARY_DIR}/aletheia-cpp-config.cmake
    INSTALL_DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/aletheia-cpp)

write_basic_package_version_file(
    ${CMAKE_CURRENT_BINARY_DIR}/aletheia-cpp-config-version.cmake
    VERSION ${PROJECT_VERSION}
    COMPATIBILITY ExactVersion)

install(FILES
    ${CMAKE_CURRENT_BINARY_DIR}/aletheia-cpp-config.cmake
    ${CMAKE_CURRENT_BINARY_DIR}/aletheia-cpp-config-version.cmake
    DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/aletheia-cpp)

# ---------------------------------------------------------------------------
# Tests (only when building standalone, not as a subdirectory)
# ---------------------------------------------------------------------------

option(BUILD_TESTING "Build test suite" ON)

if(BUILD_TESTING AND CMAKE_SOURCE_DIR STREQUAL CMAKE_CURRENT_SOURCE_DIR)
    FetchContent_Declare(Catch2
        URL https://github.com/catchorg/Catch2/archive/refs/tags/v3.7.1.tar.gz
        URL_HASH SHA256=c991b247a1a0d7bb9c39aa35faf0fe9e19764213f28ffba3109388e62ee0269c)
    FetchContent_MakeAvailable(Catch2)

    enable_testing()

    # Layer 1: Compile-time tests (no framework — just needs to compile)
    add_executable(static_tests tests/static_tests.cpp)
    target_link_libraries(static_tests PRIVATE aletheia-cpp)
    add_test(NAME static_tests COMMAND static_tests)

    # Layer 2: Unit tests (mock backend, Catch2). Split across multiple
    # translation units by concern (see tests/test_helpers.hpp for the shared
    # fixture). Catch2::Catch2WithMain provides main(), so all sources link
    # into a single executable registered as one ctest name.
    add_executable(unit_tests
        tests/unit_tests_json.cpp
        tests/unit_tests_client.cpp
        tests/unit_tests_enrich.cpp
        tests/unit_tests_validation.cpp
        tests/unit_tests_check.cpp
        tests/unit_tests_dbc.cpp
        tests/unit_tests_log.cpp
        tests/unit_tests_cancel.cpp
        tests/unit_tests_input_bounds.cpp
        tests/unit_tests_property.cpp)
    target_include_directories(unit_tests PRIVATE src)
    target_link_libraries(unit_tests
        PRIVATE aletheia-cpp nlohmann_json::nlohmann_json Catch2::Catch2WithMain)
    # Mutation lane: instrument unit_tests sources too (the test logic
    # itself is part of the operational surface — a test that asserts "x
    # > 0" but is mutated to "x >= 0" should still pass against any
    # surviving production mutant).  Catch2 stays uninstrumented because
    # of compiler crashes on its templates; aletheia-cpp + this target
    # are the actual mutation surface.
    if(ALETHEIA_MUTATION)
        target_compile_options(unit_tests PRIVATE ${ALETHEIA_MUTATION_FLAGS})
    endif()
    add_test(NAME unit_tests COMMAND unit_tests)

    # Layer 3: Integration tests (real .so, Catch2, threads for concurrent test)
    find_package(Threads REQUIRED)
    add_executable(integration_tests tests/integration_tests.cpp)
    target_link_libraries(integration_tests
        PRIVATE aletheia-cpp Threads::Threads Catch2::Catch2WithMain)
    add_test(NAME integration_tests COMMAND integration_tests)

    # Layer 3b: B.3.j cross-binding parity gate (real .so, Catch2, nlohmann_json,
    # detail/json.hpp). Reads python/tests/fixtures/dbc_corpus/*.dbc through the
    # real-FFI parse_dbc_text and asserts byte-identical canonical output
    # against the committed parity snapshots. The Python and Go counterparts
    # use the same snapshots; together the three gates pin cross-binding
    # DbcDefinition shape.
    add_executable(dbc_corpus_parity_tests tests/dbc_corpus_parity_tests.cpp)
    target_include_directories(dbc_corpus_parity_tests PRIVATE src)
    target_link_libraries(dbc_corpus_parity_tests
        PRIVATE aletheia-cpp nlohmann_json::nlohmann_json Catch2::Catch2WithMain)
    add_test(NAME dbc_corpus_parity_tests COMMAND dbc_corpus_parity_tests)

    # Layer 4: YAML loader tests (yaml-cpp, Catch2)
    add_executable(yaml_tests tests/yaml_tests.cpp)
    target_link_libraries(yaml_tests
        PRIVATE aletheia-cpp yaml-cpp::yaml-cpp Catch2::Catch2WithMain)
    add_test(NAME yaml_tests COMMAND yaml_tests)

    # Layer 5: Excel loader tests (OpenXLSX, Catch2)
    add_executable(excel_tests tests/excel_tests.cpp)
    target_link_libraries(excel_tests
        PRIVATE aletheia-cpp OpenXLSX::OpenXLSX Catch2::Catch2WithMain)
    add_test(NAME excel_tests COMMAND excel_tests)

    # Layer 6: Feature matrix parity test (yaml-cpp, Catch2). Reads
    # docs/FEATURE_MATRIX.yaml and verifies every C++ implemented entry
    # ("<header>#<symbol>") resolves to an existing header containing the
    # symbol as a whole-word match. See docs/development/PARITY_PLAN.md.
    add_executable(feature_matrix_tests tests/test_feature_matrix_parity.cpp)
    target_link_libraries(feature_matrix_tests
        PRIVATE yaml-cpp::yaml-cpp Catch2::Catch2WithMain)
    add_test(NAME feature_matrix_tests COMMAND feature_matrix_tests)
    # CPP-D-18.1 R23: pass repo root via env var, not compile-time define,
    # so the binary is bit-identical regardless of build location
    # (reproducible-build invariant).
    set_tests_properties(feature_matrix_tests PROPERTIES
        ENVIRONMENT "ALETHEIA_REPO_ROOT=${CMAKE_CURRENT_SOURCE_DIR}/..")

    # Layer 6b: Cross-binding log-event parity test (yaml-cpp + aletheia-cpp,
    # Catch2). Reads docs/LOG_EVENTS.yaml, runs a comprehensive mock-backend
    # workflow capturing LogRecord events, and asserts each emitted event is
    # a member of the canonical name set. The "missing mechanism" gate added
    # alongside R18 cluster 10's surface fix (Go's rogue dbc.text_parsed event).
    add_executable(log_events_tests tests/test_log_events_parity.cpp)
    target_include_directories(log_events_tests PRIVATE src)
    target_link_libraries(log_events_tests
        PRIVATE aletheia-cpp yaml-cpp::yaml-cpp Catch2::Catch2WithMain)
    add_test(NAME log_events_tests COMMAND log_events_tests)
    # CPP-D-18.1 R23: see feature_matrix_tests above.
    set_tests_properties(log_events_tests PROPERTIES
        ENVIRONMENT "ALETHEIA_REPO_ROOT=${CMAKE_CURRENT_SOURCE_DIR}/..")

    # R18 cluster 5 — Cat 33d cross-binding integration. Counterpart of
    # python/tests/test_cross_binding_integration.py and
    # go/aletheia/cross_binding_integration_test.go.  No shared corpus or
    # golden output — each binding asserts its own response against the
    # documented PROTOCOL.md shape.
    add_executable(cross_binding_integration_tests
        tests/test_cross_binding_integration.cpp)
    target_link_libraries(cross_binding_integration_tests
        PRIVATE aletheia-cpp Catch2::Catch2WithMain)
    add_test(NAME cross_binding_integration_tests
        COMMAND cross_binding_integration_tests)

    # Layer 7: Track D.1 doc-example harness (R17-DEF-6).
    #
    # Mirror of python/tests/test_doc_examples_harness.py + repo-root
    # conftest.py and go/aletheia/doc_examples_test.go. Every ```cpp fence
    # in the tracked user-facing markdown files is extracted, wrapped,
    # compiled by ${CMAKE_CXX_COMPILER}, and executed end-to-end. Failing
    # fences (compile or runtime) report `file:Lline` precision through
    # Catch2's DYNAMIC_SECTION. Skipped automatically when libaletheia-ffi.so
    # is missing.
    #
    # The harness shells out to ${CMAKE_CXX_COMPILER} per fence rather than
    # treating fences as additional sources of this target — each fence
    # ships its own `int main()` (or one synthesized by the wrapper), so a
    # single-binary link would conflict on `main`. The TARGET_FILE generator
    # expressions below capture aletheia-cpp + the static yaml-cpp / OpenXLSX
    # archives so the subprocess link line resolves the transitive symbol
    # closure that aletheia-cpp's PRIVATE deps would normally provide.
    add_executable(doc_example_tests tests/doc_example_tests.cpp)
    target_link_libraries(doc_example_tests
        PRIVATE aletheia-cpp Catch2::Catch2WithMain)
    # When the parent build is sanitizer-instrumented, propagate the flag
    # to per-fence subprocess compiles so the link to libaletheia-cpp.a
    # resolves the sanitizer runtime's __ubsan_handle_* / __asan_* symbols.
    set(ALETHEIA_DOC_SANITIZER_FLAG_VALUE "")
    if(ALETHEIA_SANITIZER STREQUAL "address")
        set(ALETHEIA_DOC_SANITIZER_FLAG_VALUE "-fsanitize=address")
    elseif(ALETHEIA_SANITIZER STREQUAL "undefined")
        set(ALETHEIA_DOC_SANITIZER_FLAG_VALUE "-fsanitize=undefined")
    elseif(ALETHEIA_SANITIZER STREQUAL "thread")
        set(ALETHEIA_DOC_SANITIZER_FLAG_VALUE "-fsanitize=thread")
    endif()
    # CPP-D-18.1 R23: ALETHEIA_REPO_ROOT and ALETHEIA_DOC_INCLUDE moved
    # to runtime env vars via set_tests_properties below; the remaining
    # defines (CXX / LIB_FILE / YAML_LIB / OPENXLSX_LIB / SANITIZER_FLAG)
    # come from CMake-resolved tool paths and TARGET_FILE generator
    # expressions, not from CMAKE_CURRENT_SOURCE_DIR.  Reproducibility of
    # those is a separate concern tracked outside R23.
    target_compile_definitions(doc_example_tests
        PRIVATE
            ALETHEIA_DOC_CXX="${CMAKE_CXX_COMPILER}"
            ALETHEIA_DOC_LIB_FILE="$<TARGET_FILE:aletheia-cpp>"
            ALETHEIA_DOC_YAML_LIB="$<TARGET_FILE:yaml-cpp::yaml-cpp>"
            ALETHEIA_DOC_OPENXLSX_LIB="$<TARGET_FILE:OpenXLSX::OpenXLSX>"
            ALETHEIA_DOC_CXX_STD="23"
            ALETHEIA_DOC_SANITIZER_FLAG="${ALETHEIA_DOC_SANITIZER_FLAG_VALUE}")
    add_test(NAME doc_example_tests COMMAND doc_example_tests)
    set_tests_properties(doc_example_tests PROPERTIES
        ENVIRONMENT "ALETHEIA_REPO_ROOT=${CMAKE_CURRENT_SOURCE_DIR}/..;ALETHEIA_DOC_INCLUDE=${CMAKE_CURRENT_SOURCE_DIR}/include")

    # R18 cluster 5 — Cat 33b libFuzzer harnesses.  Opt-in via
    # -DALETHEIA_FUZZ=ON because the harnesses require clang with
    # -fsanitize=fuzzer, which is incompatible with gcc-built artifacts in
    # the same build dir.  Build in a separate directory:
    #   cmake -B build-fuzz -DALETHEIA_FUZZ=ON \
    #       -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++
    #   cmake --build build-fuzz --target fuzz_parse_response
    # Run a corpus pass (60s smoke):
    #   ./build-fuzz/fuzz_parse_response -max_total_time=60 \
    #       cpp/tests/fuzz/seed/parse_response/
    option(ALETHEIA_FUZZ "Build libFuzzer harnesses" OFF)
    if(ALETHEIA_FUZZ)
        if(NOT CMAKE_CXX_COMPILER_ID STREQUAL "Clang")
            message(FATAL_ERROR
                "ALETHEIA_FUZZ requires clang (got ${CMAKE_CXX_COMPILER_ID}); "
                "use a separate build dir: -DCMAKE_C_COMPILER=clang "
                "-DCMAKE_CXX_COMPILER=clang++")
        endif()
        foreach(target_name parse_response decode_binary_frame parse_dbc_json
                            parse_rational_number)
            add_executable(fuzz_${target_name}
                tests/fuzz/fuzz_${target_name}.cpp)
            target_link_libraries(fuzz_${target_name} PRIVATE aletheia-cpp)
            target_compile_options(fuzz_${target_name}
                PRIVATE -fsanitize=fuzzer,address,undefined
                        -fno-omit-frame-pointer)
            target_link_options(fuzz_${target_name}
                PRIVATE -fsanitize=fuzzer,address,undefined)
        endforeach()
    endif()

    # Benchmark (uses real FFI backend — requires libaletheia-ffi.so at runtime,
    # loaded via dlopen. The CMake build will succeed without the .so, but the
    # resulting binary will fail at startup with a dlopen error. Build the
    # Haskell shim first with `cabal run shake -- build` from the repo root.)
    add_executable(benchmark benchmarks/benchmark.cpp)
    target_link_libraries(benchmark PRIVATE aletheia-cpp nlohmann_json::nlohmann_json)

    # Stability benchmark (R18 cluster 6 / C++ cat 26 long-run leak detection).
    # Same dlopen/.so requirement as `benchmark`.  Output is JSON to stdout.
    add_executable(stability_bench benchmarks/stability_bench.cpp)
    target_link_libraries(stability_bench PRIVATE aletheia-cpp)

    message(STATUS
        "benchmark + stability_bench targets require libaletheia-ffi.so at runtime — "
        "build the Haskell shim first with `cabal run shake -- build`")
endif()
