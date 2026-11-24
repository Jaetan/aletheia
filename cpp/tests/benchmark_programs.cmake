# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
# The two benchmark programs, the timing harness and the stability harness,
# and the tests that run each built program. The test section of
# cpp/CMakeLists.txt includes this file and shares its scope, so paths are
# relative to cpp/, and Catch2, nlohmann_json, the library target,
# ALETHEIA_STAND_IN_DIR, ALETHEIA_TEST_REPO_ROOT and ALETHEIA_TEST_LIB are the
# ones defined there.

# Benchmark (uses real FFI backend, requires libaletheia-ffi.so at runtime,
# loaded via dlopen. The CMake build will succeed without the .so, but the
# resulting binary will fail at startup with a dlopen error. Build the
# Haskell shim first with `cabal run shake -- build` from the repo root.)
add_executable(benchmark
    benchmarks/benchmark.cpp
    benchmarks/benchmark_fixtures.cpp
    benchmarks/benchmark_stats.cpp
    benchmarks/benchmark_output.cpp
    benchmarks/benchmark_throughput.cpp
    benchmarks/benchmark_latency.cpp
    benchmarks/benchmark_scaling.cpp)
target_link_libraries(benchmark PRIVATE aletheia-cpp nlohmann_json::nlohmann_json)

# The benchmark program's exit status, held by running the built program:
# an argument it refuses, refused before the kernel is searched for, and a
# report its stdout refuses. The run that writes a report loads the kernel.
add_executable(benchmark_program_tests tests/benchmark_program_tests.cpp)
target_compile_features(benchmark_program_tests PRIVATE cxx_std_23)
target_link_libraries(benchmark_program_tests PRIVATE Catch2::Catch2WithMain)
target_compile_definitions(benchmark_program_tests
    PRIVATE ALETHEIA_BENCHMARK_BIN="$<TARGET_FILE:benchmark>")
add_dependencies(benchmark_program_tests benchmark)
aletheia_add_catch_test(benchmark_program_tests)
set_tests_properties(benchmark_program_tests PROPERTIES
    ENVIRONMENT "${ALETHEIA_TEST_REPO_ROOT};${ALETHEIA_TEST_LIB}")

# Stability benchmark (long-run leak detection).
# Same dlopen/.so requirement as `benchmark`.  Output is JSON to stdout.
add_executable(stability_bench benchmarks/stability_bench.cpp)
target_link_libraries(stability_bench PRIVATE aletheia-cpp)

# The stability harness's exit paths, each held by a run of the built
# harness in a process of its own. A snapshot fails, a descriptor leaks
# between the snapshots, or a measured cycle cannot load the kernel,
# through status_open_fault, a library the test preloads into the harness
# alone, so no case needs privilege. The harness loads the kernel the test
# names, or the stand-in that refuses every call.
add_library(status_open_fault SHARED tests/status_open_fault.cpp)
target_compile_features(status_open_fault PRIVATE cxx_std_23)
# The preload reads its counts with the harness's whole-number read, an
# inline function of the snapshot header, whose includes reach the
# library's headers; it links nothing of the library.
target_include_directories(status_open_fault PRIVATE src benchmarks include)
target_link_libraries(status_open_fault PRIVATE ${CMAKE_DL_LIBS})
add_executable(stability_bench_tests tests/stability_bench_tests.cpp)
target_compile_features(stability_bench_tests PRIVATE cxx_std_23)
target_link_libraries(stability_bench_tests
    PRIVATE nlohmann_json::nlohmann_json Catch2::Catch2WithMain)
target_compile_definitions(stability_bench_tests PRIVATE
    ALETHEIA_STABILITY_BENCH="$<TARGET_FILE:stability_bench>"
    ALETHEIA_STATUS_OPEN_FAULT="$<TARGET_FILE:status_open_fault>"
    ALETHEIA_TEST_RECORDING_KERNEL="${ALETHEIA_STAND_IN_DIR}/recording_kernel.so")
add_dependencies(stability_bench_tests stability_bench status_open_fault)
aletheia_add_catch_test(stability_bench_tests)
set_tests_properties(stability_bench_tests PROPERTIES ENVIRONMENT "${ALETHEIA_TEST_REPO_ROOT}")

message(STATUS
    "benchmark + stability_bench targets require libaletheia-ffi.so at runtime: "
    "build the Haskell shim first with `cabal run shake -- build`")
