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

## Ruling pass

Opened 2026-09-15, after every point in the accumulator was ruled. The three tasks that were pending on a ruling resume where their descriptions left off, and each of the other rulings is a task of this pass. Every entry of the accumulator carries the ruling that decides it and the task that lands it.

Working order:

1. 111, the file-to-gate lens has no saved generator, so the pass opens with a lens it can diff at its close
2. 112, the backend interface takes typed shapes, before anything that implements it is touched
3. 113, the public mock factory answers with canned successes
4. 099, the header comment the mock ruling gated
5. 100, the two documents the mock ruling gated
6. 114, the member name follows the record and the wire
7. 115, every node field and message target takes its vocabulary type
8. 116, the rational-to-double conversion is removed and its assertions are evaluated by sweep
9. 117, the four library searches unify on the renderer's order
10. 095, the library is built shared so installed consumers link the loaders
11. 118, the four dependency pins are bumped
12. 119, the format configuration lists only the project's own decisions
13. 120, CMake files get a style configuration and a lint gate
14. 121, the tests get their own lint configuration and enter the gate

Six of these are breaking changes to the C++ surface and each carries its changelog entry as it lands: the shared library, the removed conversion, the unified search order, the two vocabulary changes to the DBC header, and the interface's typed shapes.

The round-end record is re-taken under `end/` when this pass closes. The record of the pre-ruling close survives as its own snapshot, so the pass is diffed against both the base and that close.

## Ruling pass close

Closed 2026-09-15. Fifteen tasks, 111 to 122 and 124 plus 095, 099 and 100, each snapshotted with its
own message. 124 carries the ruling the benchmarks measurement opened at the first close: the gate
widened to them and all 94 of their findings were fixed, with no configuration of their own needed.
The list is empty. One piece of work was requested during the pass rather than found by it, a rewrite
of the suites in behaviour phrasing, and is ruled to open its own round; it is recorded in the
repository's task store rather than here, because a task is not a file this record writes.

- round-end record re-taken under `end/`, diffed against `base/` and against the pre-ruling close in
  `end/summary.md`. The pre-ruling close survives as its own snapshot.
- every gate green: fifteen suites deterministic and randomised, both sanitizer lanes, the format gate
  over every tracked C++ source, the lint gate over `cpp/src`, `cpp/tests` and `cpp/benchmarks` run
  from `cpp/`, the CMake lint gate, and the twelve fast-tier steps
- mutation sweep 62 mutants, 62 killed, no survivor and no timeout; the recorded baseline was corrected
  to the run
- probe store 77 probes, 77 pass. The base ran 62 and passed 60; the two that were red by design are
  green because the rulings that gated them landed
- report shape checked mechanically by `lens/report_shape.py`: no completed report out of shape
- file-to-gate map 107 tracked files, 83 named by a gate, against 91 and 44 at the base. The jump is the
  test tree entering the lint gate
- four gates that could not fail on the defect they exist to catch were found and fixed during the pass:
  the em-dash check read captured tool output as prose, the snapshot's staging list was incomplete and
  the check over it could not see a created file, the mutation lane collapsed to a fraction of its
  surface while still reporting a full score, and the CMake lint gate scanned no files while exiting zero
- both lens gaps the pre-ruling close carried are closed: the file-to-gate map's generator was saved by
  task 111 and reproduces the base row, and the file-to-probe map's generator is saved now and
  reproduces the row recorded at this close. A probe holds each
- every tracked shell script states its own interpreter now. Seventy-nine carried no shebang, the
  whole probe store among them, so running one directly handed it to a shell it was not written for;
  five use process substitution and would not have run at all. Each opens with the interpreter and
  carries the exec bit, and the store was re-run from the user's own shell with no prefix
- one probe that could flake was found and fixed: the mutation baseline check inherited an environment
  variable that changes the sweep's own score, so it answered differently depending on whether the
  caller had sourced the environment script. It and the mutation runner drop the variable now
- decision points: two were opened at the first close and both are ruled. The benchmarks are carried
  by 124; the dependency pins now cover the two projects the spreadsheet library fetches for itself,
  each pinned to a release archive with a measured hash, and the probe that held the claim reads what
  the configured tree fetched rather than only what this file declares. None carries to a next round
- follow-ups created during the pass: one, a rewrite of the suites in behaviour phrasing, requested
  rather than found, not worked, and recorded in the repository's task store
