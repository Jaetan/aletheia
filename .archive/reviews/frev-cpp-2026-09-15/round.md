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
- current task: 043 (001 to 042 completed; 013 was worked before 011 and 012 by a numbering slip, its fix is in snapshot refs/frev/011; snapshots refs/frev/001 to 011)
- follow-ups created: 092 (`docs/MUTATION_BENCH.yaml`, mutant count drift found by the base sweep), 093 (`.gitignore`, build-tsan/ not ignored, from task 003), 094 (`docs/reference/CPP_API.md`, streaming fence hides its parse failure, from task 004), 095 (installed consumers cannot link the loaders, from task 007, gated by a ruling), 096 (XREV: backend interface handles, from task 009), 097 (XREV: clones and inconsistencies spanning files, from task 010), 098 (`tools/check_limits_parity.py`, gate excludes the C++ mirror, from task 019)
