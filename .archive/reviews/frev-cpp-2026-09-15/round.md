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
