# Changelog

All notable changes to Aletheia are documented in this file.

The format follows [Keep a Changelog 1.1.0][kac] and the project adheres to
[Semantic Versioning 2.0.0][semver].

[kac]: https://keepachangelog.com/en/1.1.0/
[semver]: https://semver.org/spec/v2.0.0.html

## [2.0.0] — Unreleased

This release bundles ~5 weeks of work since v1.1.1 (2026-04-03): the
verified Agda DBC text parser and formatter, the cross-binding cancellation
contract, the Python async client, DBC metadata Tier 1 + Tier 2 + signal
receivers + VAL_ promotion, the cross-binding feature-matrix gate, the
doc-example harnesses for all three bindings, and machine-readable error
codes mirrored across the bindings.

Breaking changes are concentrated in the Go and C++ Client signatures
(see § Changed). The Agda kernel and FFI wire format are stable.

### Added

#### Cross-binding (Python / Go / C++)

- `format_dbc_text` Client method — emit a `DbcDefinition` as canonical
  DBC text via the verified Agda formatter (Track E.10).
- `parse_dbc_text` Client method — parse DBC text directly through the
  verified Agda kernel (Track B.3 / E.10). Replaces the previous
  `cantools`-based path on Python.
- `send_error` and `send_remote` Client methods — emit CAN error and
  remote frames.
- `DbcSignal.value_descriptions` (Python `value_descriptions`,
  Go `ValueDescriptions`, C++ `value_descriptions`) — VAL_ entries
  promoted onto the owning signal (Track E.1 – E.12).
- `DbcSignal.receivers` — per-signal receiver-node list from `SG_` lines
  (Track B.1.x commit 2).
- `DbcDefinition.{signal_groups, environment_vars, value_tables}` —
  Tier 1 DBC metadata (Track B.1).
- `DbcDefinition.{nodes, comments, attributes}` — Tier 2 DBC metadata
  (Track B.1.x).
- `DbcDefinition.unresolved_value_descriptions` — VAL_ lines that did
  not resolve to a signal on the text-parse path (Track E.8 / E.11).
- `IssueCode.UnknownSignalReceiver` (Python `UNKNOWN_SIGNAL_RECEIVER`)
  — CHECK 21 warning surfaced on the typed binding API as a named
  constant (Track E.11 binding mirror).
- `IssueCode.UnknownValueDescriptionTarget` (Python
  `UNKNOWN_VALUE_DESCRIPTION_TARGET`) — CHECK 23 warning for VAL_
  lines whose target signal does not exist (Track E.11).
- Machine-readable `ErrorCode` constants mirroring the seven Agda
  Error ADTs (`ParseError`, `FrameError`, `RouteError`,
  `HandlerError`, `DispatchError`, `DBCTextParseError`,
  `ExtractionError`) across all three bindings: Python `ErrorCode`
  enum, Go `Code*` constants in `error.go`, C++ `ErrorCode` in
  `error.hpp`.
- `docs/FEATURE_MATRIX.yaml` plus three structural parity-gate tests
  (`python/tests/test_feature_matrix_parity.py`,
  `go/aletheia/feature_matrix_test.go`,
  `cpp/tests/test_feature_matrix_parity.cpp`) — every `implemented`
  row must resolve to a real symbol or the build fails (Track A).
- `docs/LOG_EVENTS.yaml` SSOT for the 15-event structured-log
  vocabulary plus three per-binding parity-gate tests
  (`python/tests/test_log_events_parity.py`,
  `go/aletheia/log_events_test.go`,
  `cpp/tests/test_log_events_parity.cpp`) — captures every event
  emitted by a comprehensive workflow and asserts membership in the
  canonical YAML name set, so a future binding-side emit-call that
  drifts from the cross-binding vocabulary fails the build (R18
  cluster 10).
- Doc-example harnesses across all three bindings: Python
  `pytest --markdown-docs`, Go `TestDocExamples`, C++
  `doc_example_tests` Catch2 binary. Every fenced ```python``` /
  ```go``` / ```cpp``` block in the documented file set runs against
  the real FFI (Track D).
- `tools/check-changelog.sh` offline gate enforcing R18 Universal Rule
  UR-1 (Public API stability and CHANGELOG discipline). Detects
  public-API drift since merge-base with `main` and fails if
  `CHANGELOG.md` was not also modified; wired into the Shake target
  `check-changelog` so the same gate runs from the build system, the
  pre-push hook (Phase 3), and from local CI without rebuilding the
  Shake binary. Branch-level granularity for v0; gate-shape verified
  by forward-revert test in a detached worktree (R18 cluster 1
  phase 1).
- `tools/check-gate-claim.sh` offline enforcer for the gate-claim
  integrity rule (`memory/feedback_gate_claim_integrity.md`). Detects
  commits whose message asserts "all gates clean" / "gates green" /
  similar and verifies that `build/libaletheia-ffi.so` mtime postdates
  every build-relevant staged source file's mtime — i.e., the gates
  the commit claims to have run on actually observed the post-edit
  state. Three modes: `pre-commit` (read `.git/COMMIT_EDITMSG`),
  `HEAD` / `post-commit`, and explicit commit-hash for audit. Wired
  into Shake as `phony "check-gate-claim"`. Conservative claim
  detection — only "all gates" / "gates green" / "All N gates"
  patterns trigger; per-gate status lines do not (R18 cluster 1
  phase 2).
- `tools/run-ci.sh` offline CI orchestrator chaining the full 17-step
  gate sweep that R18 commit messages have historically asserted "all
  gates clean" against. Steps: 8 Agda gates (build /
  check-properties / check-invariants / check-no-properties-in-runtime
  / check-erasure / check-fidelity / check-ffi-exports / count-modules)
  + 2 offline enforcers (check-changelog / check-gate-claim) + 3
  binding tests (Python pytest / Go test -race / C++ ctest) + 4 lints
  (basedpyright / pylint / gofmt + go vet / clang-format). Captures
  all output to `tools/ci-output/ci-<branch>-<timestamp>.log` (gitignored)
  for use as falsifiable gate-claim-integrity evidence. Total ~12-15 min
  on a warm system. Invoked directly (not via Shake) to avoid
  `cabal run` flock recursion (R18 cluster 1 phase 3).
- `tools/install-hooks.sh` idempotent installer for Aletheia's git
  hooks. Currently installs a `pre-push` hook that invokes
  `tools/run-ci.sh` before allowing push, refusing the push on any
  non-zero exit. Skip with `git push --no-verify` for incident
  response. Backs up any existing pre-push hook to
  `pre-push.aletheia-backup-<timestamp>` (R18 cluster 1 phase 3).
- `tools/ci-output/` directory with `.gitignore` reserving the
  directory for runtime CI logs while keeping logs themselves out
  of source tracking (R18 cluster 1 phase 3).
- `.actrc` configuration for [`act`](https://github.com/nektos/act),
  the local-GHA-replay tool. Pins `ubuntu-latest` to
  `catthehacker/ubuntu:act-latest` (~5 GB curated image) and
  `--container-architecture linux/amd64` for cross-platform
  reproducibility. Used by devs to validate workflow changes before
  pushing, without consuming GitHub Actions minutes (R18 cluster 1
  phase 4).
- `docs/development/CI_LOCAL.md` documenting the local-first CI
  architecture: offline correctness sweep via `tools/run-ci.sh`
  (pre-push hook), push-time meta-gates via `.github/workflows/`,
  and `act` Docker pairing for local GHA replay. Includes install
  / usage / troubleshooting (R18 cluster 1 phase 4).
- `.github/workflows/gha-checks.yml` push-time meta-gate workflow,
  three jobs running in parallel: `actionlint` (workflow YAML lint),
  `action-pins` (verify SHA-pinning policy via `tools/check-action-pins.sh`),
  `permissions-check` (verify minimal permissions via
  `tools/check-workflow-permissions.sh`). actionlint v1.7.7 installed
  via direct release download (no third-party action dependency).
  Triggers on every push and PR; wall-clock ~1-2 min on `ubuntu-latest`.
  `permissions: contents: read` default (R18 cluster 1 phases 5+6).
- `tools/check-action-pins.sh` offline gate enforcing action-pin policy:
  GitHub-owned actions (`actions/*`, `github/*`) accept `@v<n>` tags;
  third-party actions must be SHA-pinned (40-char hex). Branch refs
  (`@main`, `@master`, etc.) are rejected even for GitHub-owned to
  defend against tag-mutability supply-chain attacks. Gate-shape
  verified inline via synthetic violation worktree (R18 cluster 1
  phase 6).
- `tools/check-workflow-permissions.sh` offline gate verifying that
  every workflow declares a top-level `permissions:` mapping or every
  job declares its own. Uses python3 + yaml for proper parsing.
  Rejects `read-all` / `write-all` defaults. Gate-shape verified
  inline (R18 cluster 1 phase 6).
- `.github/dependabot.yml` weekly dependency-update schedule covering
  Python (`pip` in `python/`), Go (`gomod` in `go/` and `go/excel/`),
  and GitHub Actions. Cabal not covered (dependabot-core does not
  support Hackage); GHC toolchain manual via the Phase 6 `--bignum=native`
  rebuild deliverable. Per-ecosystem `commit-message.prefix` and
  `labels` set for traceability (R18 cluster 1 phase 6).
- Optional GHA toolchain documented in `CLAUDE.md § Development
  Environment` — `actionlint` and `act` install commands. Both are
  optional locally; `tools/run-ci.sh` step 18 (actionlint) skips
  gracefully if not installed (R18 cluster 1 phase 6).
- `tools/run-ci.sh` extended from 17 to 20 steps, adding GHA meta-checks
  18-20 (actionlint with skip-if-missing, check-action-pins,
  check-workflow-permissions) so the offline pre-push hook now covers
  the same surface as the GHA workflow (R18 cluster 1 phase 6).

#### Python

- `aletheia.asyncio.AletheiaClient` — async mirror of the sync client;
  cancellation observed at per-frame `await` boundaries via
  `asyncio.CancelledError` (Track C.1).
- `AletheiaClient.send_frames_iter()` — lazy generator yielding
  `FrameResult` per committed frame; consumer-driven cancellation via
  `break` / `gen.close()` (Track C.2).
- `aletheia.validation` module exposing `IssueSeverity`, `IssueCode`,
  `ValidationIssue` — extracted from `protocols.py` to keep that file
  under the pylint 1000-line gate (Track E.11). Importable from the
  package root: `from aletheia import IssueCode, ValidationIssue`.

#### Go

- `Client.FormatDBCText`, `ParseDBCText`, `SendError`, `SendRemote` —
  see § Cross-binding.
- `IssueCode` string enum and `ValidationIssue` struct in `result.go`.
- `Code*` error-code constants on `error.go`.
- Public validated newtypes `BitPosition` / `BitLength` with
  constructors `NewBitPosition` / `NewBitLength`, plus public limits
  `MaxBitPosition`, `MaxBitLength`, `MaxStandardID`, `MaxExtendedID`.

#### C++

- `AletheiaClient::format_dbc_text`, `parse_dbc_text`, `send_error`,
  `send_remote` — see § Cross-binding.
- `validation.hpp` — `IssueCode` enum, `IssueSeverity`,
  `ValidationIssue` struct, `ParsedDBC` result type carrying `dbc` +
  `warnings`.
- `error.hpp` — `ErrorCode` enum and `AletheiaError::code()` accessor.
- `ErrorKind::BinaryUnsupported` (mirrors Go's
  `ErrBinaryPathUnsupported`) and `ErrorKind::Cancellation` (mirrors
  Go's `context.Canceled` wrapping).

### Changed

#### BREAKING — Go: `ctx context.Context` is now the first parameter on every Client operation method (Track C.3)

Affects `SendFrame`, `SendFrames`, `StartStream`, `EndStream`,
`SendError`, `SendRemote`, `LoadDBC`, `ParseDBC`, `ParseDBCText`,
`FormatDBC`, `FormatDBCText`, `SetProperties`, `AddChecks`,
`ExtractSignals`, `BuildFrame`, `UpdateFrame`, `ValidateDBC`.
Migration: pass `context.Background()` to recover prior behavior, or
thread a real `ctx` through to enable cancellation. `Close()` and
`NewClient(...)` deliberately do not take `ctx` (mirrors `db.Close()`
/ `sql.Open(...)` precedent).

#### BREAKING — C++: `std::stop_token` is now the first parameter on every Client operation method (Track C.4)

Affects `parse_dbc`, `parse_dbc_text`, `format_dbc`, `format_dbc_text`,
`extract_signals`, `build_frame`, `update_frame`, `send_frame`,
`send_frames`, `send_error`, `send_remote`, `start_stream`,
`end_stream`, `set_properties`, `add_checks`, `validate_dbc`.
Migration: pass `std::stop_token{}` to recover prior behavior.
`~AletheiaClient()` and `make_ffi_backend(...)` deliberately do not
take a stop_token (mirrors stdlib container constructor conventions).

#### BREAKING — All bindings: `parse_dbc` returns a richer success-path result

The success path now carries the parsed DBC plus validation warnings:
Python `ParsedDBCResponse`, Go `*ParsedDBC`, C++ `ParsedDBC`. Prior
callers that consumed a bare success acknowledgement need to access
`.dbc` and inspect `.warnings`.

#### Other

- DBC text parsing migrated from `cantools` (Python) to the verified
  Agda kernel (Track B.3). User-visible behavior is byte-identical on
  the test corpus; round-trip warnings now surface through
  `ValidationIssue` rather than `cantools` exceptions.

### Removed

- `cantools` is no longer a Python runtime dependency. The verified
  Agda DBC text parser replaces every code path that previously
  delegated to it (Track B.3.g). `python-can` remains an optional
  dependency under the `can` extra for log-file readers (ASC / BLF /
  MF4 etc.); replacing it is a Phase 6 goal.

### Fixed

- DBC `CM_` / `BU_` / `EV_` / `BA_*` / `VAL_TABLE_` / `VAL_` /
  `BO_TX_BU_` round-trip parity is now provable: the universal
  theorem `parseText (formatText d) ≡ inj₂ d` holds for every
  `WellFormedTextDBCAgg d` in the verified kernel
  (`Aletheia/DBC/TextParser/Properties/Substrate/Unsafe.agda`,
  Track B.3.d closure `bca99f2`). This eliminates several silent-drop
  pathways present in the prior `cantools`-based round-trip.
- **Go**: `Client.ParseDBCText` previously emitted a non-canonical
  `"dbc.text_parsed"` log event, diverging from the `"dbc.parsed"`
  event used by `Client.ParseDBC` and the Python / C++ bindings'
  matching paths. Renamed to `"dbc.parsed"` so all DBC parse paths
  in all bindings emit a single canonical event name (R18 cluster 10).
  Affects log collectors, dashboards, or alerting rules that filter
  by event name on Go logs from the text-parse path.
- **Docs**: `docs/architecture/CANCELLATION.md` Python example now
  uses the real `AletheiaClient(default_checks=...)` constructor and
  `await client.parse_dbc_text(...)` flow — the previous
  `AletheiaClient(dbc=..., checks=...)` form was a hallucination
  (no such kwargs ever existed). Stale `AsyncAletheiaClient` symbol
  references corrected to `aletheia.asyncio.AletheiaClient`, and stale
  matrix-row IDs (`lazy_frame_iter`, `cancellation`) corrected to the
  IDs actually present in `docs/FEATURE_MATRIX.yaml`
  (`lazy_streaming_batch`, `cancellation_contract`). Same kwargs fix
  applied to the `aletheia.asyncio` package docstring example. Added
  `CANCELLATION.md` to the Python doc-example harness scope (it was
  already in the Go and C++ harness scopes) so future drifts in
  imports / class names fail the build (R18 cluster 13).
- **C++**: JSON parser previously dropped the `unresolvedValueDescs`
  field on the parse path even though the serializer emitted it. A
  `DbcDefinition` carrying Track E.8 unresolved VAL\_ entries (from the
  text-parse path) would survive the serializer round-trip on Python
  (`_helpers.py::_normalize_raw_value_desc`) and Go
  (`json.go::parseUnresolvedValueDescs`) but lose them on C++. Added
  `parse_raw_value_desc` to `json_parse.cpp` mirroring
  `raw_value_desc_to_json` in `json_serialize.cpp`; cross-binding wire
  parity restored. Three regression tests pin the parse arm + the
  serialize→parse roundtrip in `cpp/tests/unit_tests_json.cpp` (R18
  cluster 12).
- **Docs**: `iter_can_log` is documented to yield 5-tuples
  `(timestamp_us, arbitration_id, dlc, data, extended)`, but seven doc
  sites unpacked them as 4-tuples (`for ts, can_id, dlc, data in
  iter_can_log(...)`). Every such site would have raised
  `ValueError: too many values to unpack (expected 4)` at runtime if
  the loop body executed against a real frame, but the doc-example
  harness mocked `iter_can_log` to return an empty iterator — silently
  passing any unpack arity. Fixed all seven sites
  (QUICKSTART, PITCH, TUTORIAL, PYTHON_API ×4 — including the
  `iter_can_log` reference example at the top of its API section) to
  unpack the 5-tuple as `(ts, can_id, dlc, data, _extended)`, and
  flipped `conftest._harness_iter_can_log` to yield one synthetic
  `CANFrameTuple` so future unpack-arity drift fails fast at
  fence-execution time (R18 cluster 11).
- **Agda kernel (proof internal)**: the text-roundtrip aggregator
  predicate previously named `WellFormedDBC` in
  `Aletheia.DBC.TextParser.Properties.Aggregator.Universal` collided
  with the JSON-side `WellFormedDBC` in
  `Aletheia.DBC.Formatter.WellFormed` (1 field vs 8 fields, structurally
  distinct because text emission is materially lossier than JSON).
  Renamed the text-side record to `WellFormedTextDBCAgg` and split it
  into its own module `Aletheia.DBC.TextParser.WellFormed`; the
  earlier 1-field stub `Aletheia.DBC.Formatter.WellFormedText.WellFormedTextDBC`
  was unused and removed. Both `WellFormedDBC` (JSON-side) and
  `WellFormedTextDBCAgg` (text-side) module headers now document the
  asymmetry explicitly. The `formatDBCText` FFI handler's
  caller-obligation contract for `WellFormedTextDBCAgg` is documented
  in-source per G-A7(c) (no behavioral change — the formatter remains
  best-effort; callers requiring round-trip equivalence must validate
  via `validateDBC` for CHECK 18 / CHECK 23, or feed input from
  `parseDBCText`). No public-API impact: all four affected names live
  in the proof tree, not the binding surface (R18 cluster 14:
  AGDA-D-11.1, AGDA-D-11.2, AGDA-D-15.4, AGDA-D-19.6, AGDA-D-GA20.4).

---

## [1.1.1] — 2026-04-03 and earlier

This file was bootstrapped at v2.0.0; pre-v2.0.0 history is not
retroactively documented here. Tag history (`git tag -l`): `v1.1.1`,
`v1.0.0`, `v0.3.2`, `v0.3.1-beta`, `v0.3.0-alpha`,
`v0.1.0-proof-research`, `v0.1.0-alpha`. Use `git log <tag>` for the
historical record.
