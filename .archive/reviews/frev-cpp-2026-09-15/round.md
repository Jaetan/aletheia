# File review round over `cpp/`

- opened: 2026-09-15
- base commit: 726198bb
- branch at opening: fix/benchmark-harness-staleness
- scope: every tracked file under `cpp/` (91 files), one task each, in `tasks/`
- contract: `contract.md` (also carried whole inside every task)
- decision points: `decision-points.md`
- round-start record (gate audit, mutation sweep over the directory, the whole probe store through its runner, every mechanical lens): to be written under `base/` before the first task is worked
- round-end record: `end/`, diffed against `base/`
- comment/code ratio table for the directory: at round start under `base/`, at round end under `end/`

## Working order

Tasks are worked in id order. Follow-ups created during the run get the next free id and are part of the run.

## Resume

- branch: `review/frev-cpp`, forked at `b222b613`
- parked WIP: stash "benchmark-harness WIP PARKED for the cpp file review" (four benchmark files belonging to `fix/benchmark-harness-staleness`)
- commit mechanics: per task `bash .git/frev/snapshot.sh <id> <msgfile>` stages every path in `.git/frev/touched.txt`, writes a tree anchored at `refs/frev/<id>` and appends it to `.git/frev/manifest.tsv`; the user's `.commands-to-run.sh` signs the pending manifest with `git commit-tree -S` and moves the branch. The dribble never touches the index.
- message files: `.git/frev/msg-<id>.txt`
- probe store: `probes/` with `probes/run_all.sh`
- lens: `lens/linecount.py` (comment/code per file), `base/linecount.tsv`, `base/file_gate_map.tsv`
- current task: none; the list is empty. 001 to 094 and 096 to 110 are completed; 095, 099 and 100 wait on rulings and no new round opens over them until they are ruled or exempted.
- 063, 064 and 065 share one snapshot (refs/frev/063): their three fixes are one corpus enrichment written in one pass, and three commits over one tree would have left two of them empty
- follow-ups created: 092 (`docs/MUTATION_BENCH.yaml`, mutant count drift found by the base sweep), 093 (`.gitignore`, build-tsan/ not ignored, from task 003), 094 (`docs/reference/CPP_API.md`, streaming fence hides its parse failure, from task 004), 095 (installed consumers cannot link the loaders, from task 007, gated by a ruling), 096 (XREV: backend interface handles, from task 009), 097 (XREV: clones and inconsistencies spanning files, from task 010), 098 (`tools/check_limits_parity.py`, gate excludes the C++ mirror, from task 019), 099 (`cpp/include/aletheia/backend.hpp`, the canned-responses comment and the factories without `[[nodiscard]]`, from task 047), 100 (the two documents describing the public mock, from task 047, gated by a ruling), 101 (`cpp/src/excel.cpp`, a comment that describes the defect the loader no longer has, from task 050), 102 (`tools/check_spdx_headers.py`, the gate checks presence and not agreement, from task 053), 103 (`cpp/tests/fuzz/fuzz_parse_rational_number.cpp`, the envelope is refused before the rational parser runs, from task 059, worked before 061), 104 (`cpp/src/json_parse.cpp`, a wire integer past the signed 64-bit maximum is refused as negative, from task 062), 105 (`cpp/CMakeLists.txt`, one test target compiles at the default language standard, from task 072)

## Round end

- round-end record written under `end/`, diffed section by section against `base/` in `end/summary.md`
- every gate green: fifteen suites deterministic and randomised, the two sanitizer lanes, the format gate over every tracked source, the tidy gate over `cpp/src` run from `cpp/`, and the eleven fast-tier steps
- mutation sweep 61 mutants, 60 killed, one timeout Mull counts toward the score, no survivor
- probe store 62 probes, 60 pass; the two failures are red by design and cited by the rulings that gate their fixes
- report shape checked mechanically by `lens/report_shape.py`, keyed on the contract each task carries: 107 completed reports, none out of shape
- decision points: eleven in the accumulator, four of them opened by the directory pass. Two of the eleven gate
  the three tasks that wait: the ruling on the installed consumer and the loader dependencies gates 095, and
  the ruling on what the public mock factory should be gates both 099 and 100
