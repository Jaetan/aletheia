# Round base record, taken at b222b613 on 2026-09-15

Every line below is a measurement from a file in this directory; re-run the command named to reproduce it.

## Gate audit over the C++ component (gates.txt, gates2.txt)

- build: `cmake -B build` + `cmake --build build`, clean
- ctest deterministic: 100% tests passed, 0 tests failed out of 15
- ctest --schedule-random: 100% tests passed, 0 tests failed out of 15
- clang-format --dry-run -Werror over include src tests benchmarks: exit 0
- run-clang-tidy-22 over cpp/src/ (the CI gate): exit 0, 0 diagnostics
- check_clang_tidy_coverage: 17 cpp/src sources all in the compile DB
- UBSan lane (build-ubsan): 100% tests passed, 0 tests failed out of 15
- ASan lane (build-asan, fresh tree): 100% tests passed, 0 tests failed out of 15
- static fast tier (run_ci_fast.txt): ALL 11 STEPS PASSED, with the new probes/ store in the tree

## Mutation sweep (mutation.raw.txt, mull/base.txt, mull/base.json, mull/per_file.tsv)

- `mull-runner-22 ./build-mutation/unit_tests` under the ALETHEIA_MUTATION build, default operator set (no mull.yml, as in the CI lane)
- 65 mutants: 64 killed, 1 timeout, score 100%, no survivor
- files carrying mutants: cpp/src/client.cpp(2) cpp/src/detail/ffi_logic.cpp(6) cpp/src/ffi_backend.cpp(16) cpp/src/json_parse.cpp(17) cpp/src/json_serialize.cpp(6) cpp/src/rational_renderer.cpp(7) cpp/tests/integration_tests.cpp(4) cpp/tests/unit_tests_cancel.cpp(2) cpp/tests/unit_tests_client.cpp(3) cpp/tests/unit_tests_ffi_logic.cpp(1) cpp/tests/unit_tests_validation.cpp(1) 
- the recorded baseline in docs/MUTATION_BENCH.yaml says total_mutants 60; follow-up task 092

## Lenses

- comment/code ratio (linecount.tsv, method lens/linecount.py): code 17404, comment 4737, blank 2808, ratio 0.27
- clang-tidy over cpp/tests and cpp/benchmarks, informational since the gate excludes them (clang_tidy_tests.txt, clang_tidy_tests_summary.txt): unique diagnostics: 1435; counts pushed into each test task
- fuzz smoke, 60 s per harness over its seed corpus (fuzz.txt): parse_response, decode_binary_frame, parse_dbc_json, parse_rational_number all exit 0, no crash
- file-to-gate map (file_gate_map.tsv): 10 files named by a gate, parity test or workflow outside cpp/src

## Probe store

- created probes/ with probes/run_all.sh and README.md; run over the empty store: probes: 0 run, exit 0

## Catalogue for point 4

- AGENTS/cpp.md (33 categories, read whole at round start) and docs/development/BUILDING.md section Toolchain support policy (Clang 22, C++23 library required)
