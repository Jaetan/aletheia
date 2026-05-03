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
    src/enrich.cpp
    src/excel.cpp
    src/ffi_backend.cpp
    src/mock_backend.cpp
    src/json_serialize.cpp
    src/json_parse.cpp
    src/types.cpp
    src/yaml.cpp)

target_include_directories(aletheia-cpp
    PUBLIC
        $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
        $<INSTALL_INTERFACE:${CMAKE_INSTALL_INCLUDEDIR}>
    PRIVATE src)

target_compile_features(aletheia-cpp PUBLIC cxx_std_23)

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
        tests/unit_tests_log.cpp)
    target_include_directories(unit_tests PRIVATE src)
    target_link_libraries(unit_tests
        PRIVATE aletheia-cpp nlohmann_json::nlohmann_json Catch2::Catch2WithMain)
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
    target_compile_definitions(feature_matrix_tests
        PRIVATE ALETHEIA_REPO_ROOT="${CMAKE_CURRENT_SOURCE_DIR}/..")
    add_test(NAME feature_matrix_tests COMMAND feature_matrix_tests)

    # Benchmark (uses real FFI backend — requires libaletheia-ffi.so at runtime,
    # loaded via dlopen. The CMake build will succeed without the .so, but the
    # resulting binary will fail at startup with a dlopen error. Build the
    # Haskell shim first with `cabal run shake -- build` from the repo root.)
    add_executable(benchmark benchmarks/benchmark.cpp)
    target_link_libraries(benchmark PRIVATE aletheia-cpp nlohmann_json::nlohmann_json)
    message(STATUS
        "benchmark target requires libaletheia-ffi.so at runtime — "
        "build the Haskell shim first with `cabal run shake -- build`")
endif()
