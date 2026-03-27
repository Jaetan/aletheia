cmake_minimum_required(VERSION 3.25)
project(aletheia-cpp VERSION 1.0.0 LANGUAGES CXX)

# Default to Release when no build type is specified (avoids -O0 benchmarks)
if(NOT CMAKE_BUILD_TYPE AND NOT CMAKE_CONFIGURATION_TYPES)
    set(CMAKE_BUILD_TYPE Release CACHE STRING "Build type" FORCE)
endif()

set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

# ---------------------------------------------------------------------------
# Dependencies (fetched, not exported to consumers)
# ---------------------------------------------------------------------------

include(FetchContent)

set(JSON_Install OFF CACHE BOOL "" FORCE)
FetchContent_Declare(json
    URL https://github.com/nlohmann/json/releases/download/v3.11.3/json.tar.xz
    URL_HASH SHA256=d6c65aca6b1ed68e7a182f4757257b107ae403032760ed6ef121c9d55e81757d)

FetchContent_MakeAvailable(json)

# ---------------------------------------------------------------------------
# Library
# ---------------------------------------------------------------------------

add_library(aletheia-cpp
    src/client.cpp
    src/enrich.cpp
    src/ffi_backend.cpp
    src/mock_backend.cpp
    src/json_serialize.cpp
    src/json_parse.cpp)

target_include_directories(aletheia-cpp
    PUBLIC
        $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
        $<INSTALL_INTERFACE:${CMAKE_INSTALL_INCLUDEDIR}>
    PRIVATE src)

target_link_libraries(aletheia-cpp
    PRIVATE dl $<BUILD_INTERFACE:nlohmann_json::nlohmann_json>)

set_target_properties(aletheia-cpp PROPERTIES
    SOVERSION 1
    VERSION ${PROJECT_VERSION})

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
    COMPATIBILITY SameMajorVersion)

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

    # Layer 2: Unit tests (mock backend, Catch2)
    add_executable(unit_tests tests/unit_tests.cpp)
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

    # Benchmark (uses real FFI backend — requires libaletheia-ffi.so)
    add_executable(benchmark benchmarks/benchmark.cpp)
    target_link_libraries(benchmark PRIVATE aletheia-cpp nlohmann_json::nlohmann_json)
endif()
