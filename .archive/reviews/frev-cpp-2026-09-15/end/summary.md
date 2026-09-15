# Round end record, taken on 2026-09-15 over the worktree the ruling pass leaves

Re-taken at the close of the ruling pass. The pre-ruling close survives as its own
snapshot, so each row below is read against two earlier states: the base the round
opened over, and that close.

## What the record holds

- `clang_tidy_src.txt`: the lint gate as it now runs, `run-clang-tidy-22 -quiet -p build cpp/src/
  cpp/tests/ cpp/benchmarks/` from `cpp/`, 47 translation units, no finding. At the base the same gate
  ran over `cpp/src` alone, 17 translation units.
- `clang_tidy_tests.txt`: the four libFuzzer harnesses, linted against the fuzz tree because they
  compile only under that configuration. No finding. At the base and at the pre-ruling close this file
  held an informational run over the tests and the benchmarks together, 1434 diagnostics then and 1120
  at the close, none of them gated.
- `clang_tidy_tests_summary.txt`: the split that ruling asked for, tests from benchmarks, with the
  count each was at when its ruling was taken and the zero each reads now.
- `gates.txt`: fifteen suites, deterministic order and randomised order, all passing.
- `gates2.txt`: the format gate over every tracked C++ source and the lint gate over both trees.
- `asan.txt`, `ubsan.txt`: the two sanitizer lanes, fifteen suites each, all passing.
- `ubsan_without_ignorelist.txt`: the measurement behind the sanitizer ignorelist, re-taken after the
  spreadsheet library was bumped. Two reports, both from one file; the vendored zip implementation the
  earlier measurement found is no longer in the fetched tree.
- `fuzz.txt`: the four fuzz targets, eight seconds each, no crash.
- `mull/`: the sweep. 62 mutants, 62 killed, no survivor and no timeout. The pre-ruling close read 61
  mutants with one timeout.
- `probes.txt`: the probe store. 77 probes, 77 pass. The base ran 62 and passed 60.
- `linecount.tsv`: comment and code lines per tracked file under `cpp/`. Code 17404 to 17798, comments
  4737 to 4989, ratio 0.27 to 0.28.
- `file_gate_map.tsv`, `file_gate_map.summary.txt`: which tracked file is named by a gate. 91 files and
  44 gated at the base; 104 and 43 at the pre-ruling close; 107 and 83 now. The jump is the test tree
  entering the lint gate.
- `file_probe_map.tsv`, from `lens/file_probe_map.py`: which tracked file is named by a probe. 42 of
  107. Both maps now have a saved generator, which is what the pre-ruling close said they lacked; a
  probe holds each generator against the row it produced.
- `report_shape.txt`: every completed task's report carries the lines its own contract asks for. None
  out of shape.
- `run_ci_fast.txt`: the fast tier, twelve steps, all passing.

## What moved since the pre-ruling close

The eleven rulings landed as fourteen tasks, and a fifteenth carried the ruling the benchmarks
measurement opened. The library is built shared, so an installed consumer links
the loaders; four dependencies are at their current releases; the public mock factory answers with canned
successes and has no branch to get wrong; the rational type no longer converts to double and the tests
that measured it were rewritten against exact fractions; the four library searches are one; every node
field and message target carries its vocabulary type; a member name follows the wire; the format
configuration lists only the project's own decisions; CMake files have a style and a gate; and the test
sources are inside the lint gate with a configuration of their own, and so are the benchmarks, which
needed no configuration at all.

One probe that could flake was found and fixed at the close: the mutation baseline check inherited an
environment variable that changes the sweep's own score.

Four gates that could not fail on the defect they exist to catch were found and fixed along the way: the
em-dash check read captured tool output as prose, the snapshot's staging list was incomplete and the check
over it could not see a created file, the mutation lane collapsed to a fraction of its surface while still
reporting a full score, and the CMake lint gate scanned no files while exiting zero.
