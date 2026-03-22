cmake_minimum_required(VERSION 3.25)
project(aletheia-cpp LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

# ---------------------------------------------------------------------------
# Dependencies (fetched, not exported to consumers)
# ---------------------------------------------------------------------------

include(FetchContent)

FetchContent_Declare(json
    URL https://github.com/nlohmann/json/releases/download/v3.11.3/json.tar.xz)

FetchContent_Declare(Catch2
    URL https://github.com/catchorg/Catch2/archive/refs/tags/v3.7.1.tar.gz)

FetchContent_MakeAvailable(json Catch2)

# ---------------------------------------------------------------------------
# Library
# ---------------------------------------------------------------------------

add_library(aletheia-cpp
    src/client.cpp
    src/ffi_backend.cpp
    src/mock_backend.cpp
    src/json_serialize.cpp
    src/json_parse.cpp)

target_include_directories(aletheia-cpp
    PUBLIC  include
    PRIVATE src)

target_link_libraries(aletheia-cpp
    PRIVATE dl nlohmann_json::nlohmann_json)

# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------

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
