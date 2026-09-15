# Round end record, taken on 2026-09-15 over the worktree the round leaves

Every line below is a measurement from a file in this directory; re-run the command named to reproduce it. Each section names what moved against `base/`.

## Gate audit over the C++ component (gates.txt, gates2.txt, ubsan.txt, asan.txt, run_ci_fast.txt)

- build: fresh configure plus `cmake --build build`, clean
- ctest deterministic: 100% tests passed, 0 tests failed out of 15
- ctest --schedule-random: 100% tests passed, 0 tests failed out of 15
- clang-format --dry-run -Werror over every tracked source: exit 0
- run-clang-tidy-22 -quiet -p build cpp/src/ from `cpp/`: exit 0, 0 diagnostics
- UBSan lane (build-ubsan): 100% tests passed, 0 tests failed out of 15
- ASan lane (build-asan): 100% tests passed, 0 tests failed out of 15
- static fast tier: ALL 11 STEPS PASSED

Against base: the same result everywhere, with one correction to how it is measured. The tidy line at base was produced from the repository root, where no configuration is in scope, so the driver ran no checks at all and its empty output read as clean. The task that found it corrected the coding standard, added a probe that injects a discarded return, and this run is from `cpp/`. The first correct run had one real finding, an include an earlier task in this round left unused, fixed before this record.

## Mutation sweep (mull/end.txt, mull/end.json, mull/per_file.tsv)

- `mull-runner-22 ./unit_tests` under the ALETHEIA_MUTATION build, with ALETHEIA_REPO_ROOT set as the folded-in integration tests now require
- 61 mutants: 60 killed, 1 timeout, score 100%, no survivor
- against base: 65 mutants, 64 killed, 1 timeout. The count fell because deduplication removed code that carried mutants and rose where new guards were added; the same single timeout, a loop counter in the integration suite, is present at both ends and Mull counts it toward the score rather than as a survivor
- `docs/MUTATION_BENCH.yaml` recorded 60 at base and records 61 now, with the timeout beside it and a probe that re-runs the sweep and compares all three numbers

## Lenses

- comment and code ratio (linecount.tsv, lens/linecount.py): code 17404 to 17412, comments 4737 to 4773, blank 2808 to 2896, ratio 0.27 at both ends. 105 rows against 92: thirteen files are new, eleven of them probes' subjects or shared test headers. 36 files carry more comment lines than at base, each in a task that fixed a defect in that file, which is the only case the contract allows
- clang-tidy over cpp/tests and cpp/benchmarks, informational since the gate excludes them (clang_tidy_tests.txt, clang_tidy_tests_summary.txt): 1434 unique diagnostics at base, 1120 now
- fuzz smoke, 61 s per harness over its seed corpus (fuzz.txt): all four exit 0 with no crash. Runs per harness: parse_response 600947, decode_binary_frame 46437162, parse_dbc_json 893910, parse_rational_number 1222599
- UBSan with the ignorelist withheld (ubsan_without_ignorelist.txt, lens/ubsan_without_ignorelist.sh): 67 reports across four kinds, every one inside the vendored spreadsheet library, which is what the ignorelist exempts. The base row recorded one site because the run stopped at the first; the lens deleted the line carrying the flag, and a task in this round moved that flag onto a continuation line, which left the call unbalanced. The lens now points the flag at an empty list instead of deleting its line, which is the same measurement and survives the shape
- report shape (report_shape.txt, lens/report_shape.py): 107 completed reports, 103 file-review, 2 document-review, 2 directory-review, 0 out of shape. Three tasks are not completed and wait on rulings
- file-to-gate map (file_gate_map.tsv) and file-to-probe map (file_probe_map.tsv): 104 tracked files in cpp/, 35 named by a gate, tool, workflow or sibling test, 39 named by at least one probe. The base map's generator was not kept under lens/, so its total of 10 cannot be reproduced and the two are not comparable row by row; that a lens without a saved method cannot be diffed is itself worth carrying to the next round

## Probe store (probes.txt)

- 62 probes, 60 pass, 2 fail
- both failures are red by design and were red when written: the installed-consumer loader link and the public mock factory answering its first call. Each proves a defect whose fix waits on a ruling, and each is cited by its accumulator entry. Neither is a regression: the store was empty at base, so every probe in it was written during this round and read red before its own fix, or is one of these two
