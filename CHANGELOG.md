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

- `format_dbc_text` Client method — emit a DBC definition (Python
  `DBCDefinition`, Go `DBCDefinition`, C++ `DbcDefinition`) as canonical
  DBC text via the verified Agda formatter (Track E.10).
- `parse_dbc_text` Client method — parse DBC text directly through the
  verified Agda kernel (Track B.3 / E.10). Replaces the previous
  `cantools`-based path on Python.
- `send_error` and `send_remote` Client methods — emit CAN error and
  remote frames.
- DBC signal `value_descriptions` field (Python `DBCSignal.value_descriptions`,
  Go `DBCSignal.ValueDescriptions`, C++ `DbcSignal::value_descriptions`) —
  VAL_ entries promoted onto the owning signal (Track E.1 – E.12).
- DBC signal `receivers` field — per-signal receiver-node list from `SG_`
  lines (Track B.1.x commit 2).
- DBC definition Tier 1 metadata fields (`signal_groups`, `environment_vars`,
  `value_tables`) on Python `DBCDefinition` / Go `DBCDefinition` /
  C++ `DbcDefinition` (Track B.1).
- DBC definition Tier 2 metadata fields (`nodes`, `comments`, `attributes`)
  on Python `DBCDefinition` / Go `DBCDefinition` / C++ `DbcDefinition`
  (Track B.1.x).
- DBC definition `unresolved_value_descriptions` field (same naming
  rule as Tier 1/2) — VAL_ lines that did not resolve to a signal on the
  text-parse path (Track E.8 / E.11).
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
- `tools/check_changelog.py` offline gate enforcing R18 Universal Rule
  UR-1 (Public API stability and CHANGELOG discipline). Detects
  public-API drift since merge-base with `main` and fails if
  `CHANGELOG.md` was not also modified; wired into the Shake target
  `check-changelog` so the same gate runs from the build system, the
  pre-push hook (Phase 3), and from local CI without rebuilding the
  Shake binary. Branch-level granularity for v0; gate-shape verified
  by forward-revert test in a detached worktree (R18 cluster 1
  phase 1).
- `tools/check_gate_claim.py` offline enforcer for the gate-claim
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
- `tools/run_ci.py` offline CI orchestrator chaining the full 17-step
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
- `tools/install_hooks.py` idempotent installer for Aletheia's git
  hooks. Currently installs a `pre-push` hook that invokes
  `tools/run_ci.py` before allowing push, refusing the push on any
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
  architecture: offline correctness sweep via `tools/run_ci.py`
  (pre-push hook), push-time meta-gates via `.github/workflows/`,
  and `act` Docker pairing for local GHA replay. Includes install
  / usage / troubleshooting (R18 cluster 1 phase 4).
- `.github/workflows/gha-checks.yml` push-time meta-gate workflow,
  three jobs running in parallel: `actionlint` (workflow YAML lint),
  `action-pins` (verify SHA-pinning policy via `tools/check_action_pins.py`),
  `permissions-check` (verify minimal permissions via
  `tools/check_workflow_permissions.py`). actionlint v1.7.7 installed
  via direct release download (no third-party action dependency).
  Triggers on every push and PR; wall-clock ~1-2 min on `ubuntu-latest`.
  `permissions: contents: read` default (R18 cluster 1 phases 5+6).
- `tools/check_action_pins.py` offline gate enforcing action-pin policy:
  GitHub-owned actions (`actions/*`, `github/*`) accept `@v<n>` tags;
  third-party actions must be SHA-pinned (40-char hex). Branch refs
  (`@main`, `@master`, etc.) are rejected even for GitHub-owned to
  defend against tag-mutability supply-chain attacks. Gate-shape
  verified inline via synthetic violation worktree (R18 cluster 1
  phase 6).
- `tools/check_workflow_permissions.py` offline gate verifying that
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
  optional locally; `tools/run_ci.py` step 18 (actionlint) skips
  gracefully if not installed (R18 cluster 1 phase 6).
- `tools/run_ci.py` extended from 17 to 20 steps, adding GHA meta-checks
  18-20 (actionlint with skip-if-missing, check-action-pins,
  check-workflow-permissions) so the offline pre-push hook now covers
  the same surface as the GHA workflow (R18 cluster 1 phase 6).
- `tools/run_ci.py` extended from 20 to 21 steps with the addition of
  `clang-tidy -p build src/*.cpp` (canonical invocation per AGENTS.md
  L580) — mandatory correctness gate per AGENTS.md L494 +
  `feedback_clang_tidy_mandatory.md`, was missing from phase 3 / phase 6
  ships and revealed by the first end-to-end run (R18 cluster 1 phase 7).
- `docs/operations/RUNBOOK.md` — operations runbook keyed on operator
  symptoms.  Per AGENTS.md cat 22, every one of the 15 structured log
  events from `docs/LOG_EVENTS.yaml` has a `symptom / cause / action`
  entry, and every failure mode documented elsewhere (BUILDING.md
  troubleshooting, CANCELLATION.md edge cases, PROTOCOL.md
  `InputBoundExceeded` bounds, OOM / heap pressure, DBC validation
  rejection) is captured in one operator-facing reference (R18
  cluster 4).
- `tools/check_runbook_coverage.py` offline gate enforcing AGENTS.md
  cat 22.  Parses `docs/LOG_EVENTS.yaml` for event names and verifies
  every event appears as a `#### `<name>`` heading in
  `docs/operations/RUNBOOK.md`; missing entries fail the gate.  Wired
  as Shake `phony "check-runbook"` and as step 11 of `tools/run_ci.py`
  (which moves to 22 always-on steps total).  Forward-revert verified:
  deleting a heading fires the gate with a precise diagnostic;
  restoring it returns to exit 0 (R18 cluster 4).
- Long-run stability bench harnesses across all three bindings, with a
  GHC RTS heap-typed profile capture for the Agda kernel.  Per AGENTS.md
  cat 16 / 25 / 26 / 27 each binding now exercises ≥ 1M frames in a
  multi-cycle Init/Close pattern and asserts no per-iteration drift on
  RSS / FD count / binding-specific resource accounting (R18 cluster 6).
  Files: `python/benchmarks/stability.py` (psutil — RSS, num_fds,
  RTSState refcount, logger handlers); `go/benchmarks/stability/main.go`
  (runtime/metrics, /proc/self/fd, NumGoroutine,
  `aletheia.StablePtrCount()`); `cpp/benchmarks/stability_bench.cpp`
  (VmRSS, /proc/self/fd, Threads, glibc malloc_info).  Two-tier
  threshold model: hard zero on real-resource leaks (FD / goroutine /
  StablePtr / ctypes / logger handlers), soft threshold on RSS and
  malloc_info.  Runtime-infrastructure FDs (anon_inode eventfd /
  eventpoll / timerfd) are filtered out across all three bindings —
  they grow lazily based on workload regardless of Close discipline.
- `aletheia.StablePtrCount()` — Go-side counter exposing live
  `aletheia_init`-allocated StablePtrs (incremented in `FFIBackend.Init`,
  decremented in `FFIBackend.Close`).  Used by the long-run stability
  harness to detect Init/Close imbalance.  Production code does not
  need to call this (R18 cluster 6).
- `ALETHEIA_RTS_OPTS` env-var path in the Python binding's
  `RTSState.acquire` — additional RTS flags (e.g., `-hT` for heap
  profiling, `-p` for time profiling) are appended to the argv passed
  to `hs_init_with_rtsopts`.  Lets the stability bench drive the GHC
  RTS heap profile without rebuilding the `.so` (R18 cluster 6).
- `docs/STABILITY_BENCH.yaml` SSOT declaring per-binding sub-checks +
  source markers; `tools/check_stability_bench.py` static gate
  verifies every (binding, sub_check) pair's marker is present in the
  named harness (Shake `phony "check-stability-bench"`, step 12 of
  `tools/run_ci.py`).  `tools/stability_run.py` dynamic runner
  invokes each harness sequentially and archives per-binding JSON
  + GHC RTS `aletheia-ffi.hp` to `benchmarks/stability/<short-sha>/`
  (opt-in via `ALETHEIA_STABILITY_CHECK=1`, step 29 of `tools/run_ci.py`).
  `docs/operations/STABILITY.md` documents the procedure.  Forward-
  revert verified: per-cycle FD leak in any harness fires its
  hard-zero gate with a precise `delta=N` diagnostic (R18 cluster 6).
- `Aletheia.Limits` Agda module + `docs/architecture/PROTOCOL.md § Limits`
  documenting the compile-time adversarial-input bounds enforced at every
  parser at a trust boundary (R18 cluster 2 / Universal Rule UR-2). 11
  numeric bounds (`max-dbc-text-bytes`, `max-json-bytes`, `max-nesting-depth`,
  `max-messages-per-file`, `max-signals-per-message`, `max-attributes-per-file`,
  `max-value-descriptions-per-file`, `max-identifier-length`,
  `max-string-length-bytes`, `max-atom-count-per-property`,
  `max-frame-byte-count`) plus a 7-variant `BoundKind` enum with canonical
  wire codes via `boundKindCode`. `parseJSON` and `parseDBCText` reject
  oversize inputs at their FFI-layer entry handlers (`Main.JSON.processJSONLine`
  and `Protocol.Handlers.ParseDBCText.handleParseDBCText`) with typed
  `InputBoundExceeded` errors. The frame-byte-count bound (`max-frame-byte-count`
  = 64) is already enforced runtime-side by `validateDLCAndLen` in the
  Haskell shim's DLC validation (DLC ≤ 15 → bytes ≤ 64 via `dlcToBytes`).
- `InputBoundExceeded` constructor on `ParseError`, `DBCTextParseError`,
  and `FrameError` ADTs in `Aletheia.Error` carrying
  `BoundKind × ℕ × ℕ` (kind, observed, limit). Wire codes
  `parse_input_bound_exceeded` / `dbc_text_input_bound_exceeded` /
  `frame_input_bound_exceeded` (R18 cluster 2 / Universal Rule UR-2).

#### Python

- `aletheia.Backend` Protocol (R20 cluster P — PY-D-24.1) — FFI-boundary
  abstraction promoted to the public surface alongside `aletheia.FFIBackend`
  (production wrapper around `libaletheia-ffi.so`) and `aletheia.MockBackend`
  (canned-response replay for tests).  Cross-binding parity with Go
  `aletheia.Backend` interface (`go/aletheia/backend.go`) and C++
  `aletheia::IBackend` (`cpp/include/aletheia/backend.hpp`).
  `AletheiaClient.__init__` accepts a new `backend=` kwarg; when omitted
  an `FFIBackend` is constructed on `__enter__` from the resolved .so
  path. Client-constructed backends are torn down on `close()`;
  caller-injected backends persist (cross-binding ownership parity).
- `aletheia.MockBackend` (R20 cluster P — PY-B-22.2) — drop-in mock
  exposing the 13-method `Backend` Protocol.  Records every input
  (`process()` JSON commands + binary-shim sentinels), pops canned
  responses from a FIFO queue, falls back to fire-and-forget ack /
  success defaults on empty queue.  `extract_signals_bin` raises
  `aletheia.BinaryPathUnsupportedError` — Client catches it and falls
  back to the JSON-out `extract_signals_binary` path (mirrors Go's
  `ErrBinaryPathUnsupported` contract at `go/aletheia/mock.go:222`).
  Closes `docs/FEATURE_MATRIX.yaml` row `mock_backend` Python entry +
  new row `backend_di_seam` (all three bindings).
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
- `aletheia.limits` module mirroring `Aletheia.Limits` (Agda) — bound
  constants (`MAX_JSON_BYTES`, `MAX_DBC_TEXT_BYTES`, etc.) and bound-kind
  wire codes (`BOUND_KIND_INPUT_LENGTH_BYTES`, etc.) for use at FFI
  entries and in user code (R18 cluster 2).
- `aletheia.InputBoundExceededError` exception class, subclass of
  `AletheiaError`, carrying `kind` / `observed` / `limit` fields.
  Raised by `_send_command` when a JSON payload exceeds `MAX_JSON_BYTES`
  before marshaling across ctypes; raised by `dbc_to_json` when a DBC
  file exceeds `MAX_DBC_TEXT_BYTES`; raised by `yaml_loader.load_checks`
  when a YAML file/string exceeds `MAX_DBC_TEXT_BYTES`. Importable as
  `from aletheia import InputBoundExceededError` (R18 cluster 2 /
  Universal Rule UR-2).
- `CANFrameTuple` gains `brs` / `esi` fields — pass-through CAN-FD
  Bit Rate Switch (ISO 11898-1:2015 §10.4.2) and Error State Indicator
  (§10.4.3) metadata. Both default to `None` for CAN 2.0B frames where
  the bits do not exist; `AletheiaClient.send_frame` / `send_frames`
  accept matching kwargs and `iter_can_log` / `load_can_log` surface
  them per-frame from python-can readers. The Aletheia kernel does
  NOT consume these bits — pass-through metadata only (R19 Phase 2
  cluster 18).
- Loader path-hardening: `excel_loader.load_checks_from_excel`,
  `load_dbc_from_excel`, and `yaml_loader.load_checks(Path(...))` now
  refuse symbolic links outright with `ValidationError`. Mirrors the
  same C++ rejection so cross-binding semantics stay aligned (R20
  cluster N — PY-B-26.2 / cross-binding parity).
- `aletheia.client._ffi.find_ffi_library` extends the R19-cluster-12
  symlink + group/world-writable check from the `ALETHEIA_LIB` env
  path to every fallback resolution path (`_install_config`,
  `build/`, `dist-newstyle/`); a tampered fallback can no longer
  bypass the gate (R20 cluster N — PY-B-26.2 / PY-A-27.2).

#### Go

- `Client.FormatDBCText`, `ParseDBCText`, `SendError`, `SendRemote` —
  see § Cross-binding.
- `IssueCode` string enum and `ValidationIssue` struct in `result.go`.
- `Code*` error-code constants on `error.go`.
- Public validated newtypes `BitPosition` / `BitLength` with
  constructors `NewBitPosition` / `NewBitLength`, plus public limits
  `MaxBitPosition`, `MaxBitLength`, `MaxStandardID`, `MaxExtendedID`.
- `aletheia/limits.go` mirroring `Aletheia.Limits` (Agda): numeric
  bound constants (`MaxJSONBytes`, `MaxDBCTextBytes`, ...) and
  bound-kind wire-code constants (`BoundKindInputLengthBytes`, ...)
  (R18 cluster 2).
- `*aletheia.InputBoundExceededError` typed error in `error.go` with
  `BoundKind` / `Observed` / `Limit` / `Code` fields. Returned by
  `FFIBackend.Process` when input exceeds `MaxJSONBytes` before the
  cgo `aletheia_process` call. Discoverable via `errors.As`. New
  `Code*` error codes: `CodeParseInvalidIdentifier`,
  `CodeParseInputBoundExceeded`, `CodeDBCTextParseFailure`,
  `CodeDBCTextTrailingInput`, `CodeDBCTextAttributeRefinementFailed`,
  `CodeDBCTextInputBoundExceeded`, `CodeFrameInputBoundExceeded`
  (R18 cluster 2 / Universal Rule UR-2).
- Loader hardening: `excel.LoadChecks`, `excel.LoadDbc`,
  `excel.CreateTemplate`, `aletheia.LoadChecksFromYAMLFile`, and the
  file-branch of `aletheia.LoadChecksFromYAML` now reject symbolic
  links outright; the excel entry points additionally enforce a
  64 MiB raw file-size cap and walk the ZIP central directory via
  stdlib `archive/zip`, returning `*InputBoundExceededError`
  (`BoundKind="input_length_bytes"`) when the sum of uncompressed
  entry sizes exceeds the cap (ZIP-bomb defence).
  `excel.CreateTemplate` validates the destination's parent dir.
  Cross-binding mirror of the C++ and Python hardening (R20
  cluster N follow-up).

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
- `aletheia/limits.hpp` mirroring `Aletheia.Limits` (Agda): inline
  `constexpr` bound constants (`max_json_bytes`, `max_dbc_text_bytes`,
  ...) and `inline constexpr std::string_view` bound-kind wire codes
  (`bound_kind_input_length_bytes`, ...). Plus
  `aletheia::InputBoundExceededError` value-type struct with
  `bound_kind` / `observed` / `limit` fields. Re-exported from the
  umbrella header `<aletheia/aletheia.hpp>` (R18 cluster 2).
- New `ErrorCode` enumerators: `ParseInvalidIdentifier`,
  `ParseInputBoundExceeded`, `DBCTextParseFailure`,
  `DBCTextTrailingInput`, `DBCTextAttributeRefinementFailed`,
  `DBCTextInputBoundExceeded`, `FrameInputBoundExceeded` — plus
  matching `error_code_from_string` table entries (51 → 58 entries).
  `FfiBackend::process` synthesizes a `parse_input_bound_exceeded`
  error response when input exceeds `max_json_bytes` before
  calling the dlopen'd `aletheia_process` (R18 cluster 2 / Universal
  Rule UR-2).
- `error.hpp` — `AletheiaException` class deriving from
  `std::runtime_error` and carrying an `AletheiaError` value
  accessible via `kind()` / `code()` / `error()`. Used for FFI
  boundary failures (`dlopen` / `dlsym` / `aletheia_init() → null`)
  that emit `ErrorKind::Ffi`, plus `ErrorKind::Protocol` for
  runtime `aletheia_*() → null` cases and `ErrorKind::Validation`
  for caller-argument rejections (`rts_cores < 1`, oversize
  payload). Mirrors Python `FFIError` / `ProtocolError` /
  `ValidationError` and Go `ErrFFI` / `ErrProtocol` /
  `ErrValidation`. Pre-R20 these paths threw `std::runtime_error`;
  existing `catch (const std::exception&)` blocks keep working via
  the base, new code can `catch (const AletheiaException&)` to
  recover the kind tag (R20 cluster K).
- Loader hardening: `load_checks_from_excel`, `load_dbc_from_excel`,
  `load_checks_from_yaml`, and `create_excel_template` now reject
  symbolic links, enforce a 64 MiB raw file-size cap, and (for
  `.xlsx`) walk the ZIP central directory and reject when the sum
  of uncompressed entry sizes exceeds the cap (ZIP-bomb defence).
  Symbolic-link / non-regular-file rejection emits
  `ErrorKind::Validation`; size-cap and uncompressed-bound emit
  `ErrorKind::InputBoundExceeded` with structured `bound_info`
  (`{kind="input_length_bytes", observed, limit}`) — same shape as
  Python `InputBoundExceededError` / Go `*InputBoundExceededError`.
  `create_excel_template` additionally validates the destination's
  parent directory exists before letting OpenXLSX raise an opaque
  exception (R20 cluster N — CPP-B-29.1/2/3 / CPP-D-21.2).
- `aletheia::Logger::enabled(LogLevel) const noexcept` — fast-path
  predicate letting hot-path callers short-circuit before
  constructing `std::initializer_list<LogField>`. Mirrors Go
  `slog.Logger.Enabled(ctx, level)` and Python
  `logging.Logger.isEnabledFor(level)`. Hot-path Debug call sites
  in `AletheiaClient` (`frame.processed`, `error_event.sent`,
  `remote_event.sent`, `cache.hit`, `cache.miss`) now guard with
  `enabled(LogLevel::Debug)` before building the field list, so a
  disabled-Debug logger never pays the per-frame `LogField`
  construction cost (R20 cluster M — CPP-A-30.1).

#### Build / release tooling (R18 cluster 3)

- `cabal run shake -- dist` now records SHA-256 hashes for the source
  and post-strip artifacts in `dist/aletheia/MANIFEST.txt`, generates
  a CycloneDX 1.5 SBOM at `dist/aletheia/aletheia-sbom.cdx.json`,
  produces a sidecar `dist/aletheia.tar.gz.sha256` for
  `sha256sum -c`, and signs the tarball with cosign at
  `dist/aletheia.tar.gz.sig` when `$ALETHEIA_COSIGN_KEY` is set.  The
  tarball is built reproducibly (`tar --sort=name --mtime=@<commit-epoch>
  --owner=0 --group=0 --numeric-owner --use-compress-program='gzip -n'`)
  — two `dist` runs of the same commit produce bit-identical
  `aletheia.tar.gz` (R18 cluster 3 / Universal Rule UR-3).
- `keys/cosign.pub` — committed public half of the release-signing
  cosign keypair.  Verification command:
  `cosign verify-blob --key keys/cosign.pub --signature dist/aletheia.tar.gz.sig dist/aletheia.tar.gz`.
- `tools/check_reproducible_build.py` — UR-3 gate enforcing
  bit-identical `libaletheia-ffi.so` across two clean
  `cabal run shake -- build` invocations.  Opt-in into the offline CI
  battery via `ALETHEIA_REPRO_CHECK=1 tools/run_ci.py` (~10 min cold).
- `tools/sbom_generate.py` — CycloneDX 1.5 SBOM generator (toolchain
  pin + GHC runtime deps + main artifact hash).
- `docs/development/RELEASE.md` — release-process documentation
  (sign + verify + reproducible-build flow + key rotation + checklist).
- All `tools/*.sh` scripts migrated to Python (≥ 3.13.7) per user
  direction 2026-05-08: `check_changelog.py`, `check_gate_claim.py`,
  `check_action_pins.py`, `check_workflow_permissions.py`,
  `install_hooks.py`, `run_ci.py`.  No bash entry points remain
  under `tools/` (snake_case `.py` is the new convention).
- C++ `aletheia-cpp` library target compiled with
  `-ffile-prefix-map=${CMAKE_SOURCE_DIR}=.` for path-leak hardening.
- GHC build receives `--ghc-options=-optc-ffile-prefix-map=$REPO_ROOT=.`
  (defense-in-depth — same-host repro already held without this flag).
- `Dockerfile.runtime` base image pinned by SHA-256 digest
  (`python:3.13-slim@sha256:a0779d7c...`, OCI multi-arch index).
  `cabal run shake -- docker` now tags both `aletheia:latest` (moving)
  and `aletheia:<git-short-sha>` (immutable per-commit) so consumers
  can pin to a specific build (R18 cluster 3 follow-up / CICD-5.5).
- `dist/aletheia/README.txt` — deterministic in-tarball consumer entry
  point: file inventory, quick-start gcc command, verify-then-trust
  order, and cross-references to `DISTRIBUTION.md` / `RELEASE.md`.
  Content derived from commit time only — no wall-clock — so the
  tarball stays bit-reproducible (R18 cluster 3 follow-up / CICD-5.7).
- **Cross-binding integration tests** in all three bindings
  (`python/tests/test_cross_binding_integration.py`,
  `go/aletheia/cross_binding_integration_test.go`,
  `cpp/tests/test_cross_binding_integration.cpp`).  Each binding
  constructs identical canonical inputs and asserts the response shape
  matches the documented PROTOCOL.md invariants — no shared corpus, no
  golden output to diff against (R18 cluster 5 — Cat 33d / 34d).
- **Sanitizer build matrix** (R18 cluster 5 — Cat 33a, advisor option (d)).
  `cpp/CMakeLists.txt` adds `-DALETHEIA_SANITIZER=address|undefined|thread`
  for opt-in ASan / UBSan / TSan lanes; `cpp/sanitizer-ignorelist.txt`
  filters vendored third-party UB in OpenXLSX.  Requires clang for the
  ignorelist feature; `tools/run_ci.py` step 26 (`ALETHEIA_SAN_CHECK=1`)
  wires the canonical UBSan ctest battery.
- **`docs/architecture/CGO_NOTES.md`** documents the GHC RTS / cgo /
  sanitizer interaction surface — the AST→compile→link path, sanitizer
  blind spots, the rationale behind each lane decision, and the
  compiler requirement (R18 cluster 5 — Cat 33a / CPP-B-33.5).
- **Native fuzz harnesses** in all three bindings:
  - Go: `aletheia/fuzz_test.go` adds `FuzzParseResponse`,
    `FuzzMarshalCommand`, `FuzzDecodeBinaryFrame`,
    `FuzzParseRationalNumber`, `FuzzParseDBCJSON` (Cat 33b).
  - C++: `cpp/tests/fuzz/` ships 4 libFuzzer harnesses behind the
    `-DALETHEIA_FUZZ=ON` clang+`-fsanitize=fuzzer` opt-in (Cat 33b).
  - Python: `python/tests/fuzz/` ships 3 atheris harnesses behind the
    new `aletheia[fuzz]` extra (Cat 34c).
- **Property tests** in all three bindings:
  - Go: `aletheia/property_test.go` adds 5 `testing/quick` properties
    (rational round-trip, parser totality, command round-trip, rational
    monotonicity, mock/real shape parity) (Cat 33c).
  - C++: `cpp/tests/unit_tests_property.cpp` adds 5 Catch2 GENERATE
    properties (Cat 33c).
  - Python: `python/tests/test_property_hypothesis.py` adds 8
    hypothesis property tests (Cat 34b); `aletheia[dev]` extras gain
    `hypothesis>=6.0,<7`.
- **Python `-X dev` lane** at `tools/run_ci.py` step 14 — surfaces
  `ResourceWarning`, debug asyncio warnings, deprecation noise that
  the standard pytest lane silently masks (Cat 34a).
- **`aletheia.asyncio.AletheiaClient(sync_client=…)`** — public
  dependency-injection seam.  When provided, the AsyncClient wraps the
  pre-built sync client instead of constructing one internally; enables
  test scaffolding (and downstream advanced uses) to interpose on the
  sync layer without touching private attributes (R18 cluster 5).
- **`aletheia.asyncio.testing.gate_send_frame(sync, after_n)`** —
  public testing helper for deterministic async-cancellation contracts.
  Wraps the public ``send_frame`` method on a sync client to block the
  worker thread after frame ``after_n`` commits; pairs with the new
  ``sync_client=…`` injection seam so tests need no protected-access
  suppressions (R18 cluster 5).  Used by
  ``python/tests/test_cancellation.py`` to verify the cancellation
  contract with no physical-time dependence — pytest's session timeout
  is the only safety net for genuine hangs.
- **Python `--random-order` lane** at `tools/run_ci.py` step 15 —
  exercises the `pytest-random-order` plugin per AGENTS.md cat 14(f);
  the dep was pinned in `pyproject.toml [dev]` extras when the cat
  landed but the lane never followed.  Both deterministic and
  randomized-order lanes must stay green (Cat 14f / 34d).
- **Python doc-example harness lane** at `tools/run_ci.py` step 13 —
  the `pytest --markdown-docs` invocation was silently absent from the
  orchestrator before C5; recovering it adds 114 doc-fence executions
  (R18 cluster 5 follow-up / Cat 32 enforcement).

#### Mutation testing infrastructure (R18 cluster 7)

Per AGENTS.md cat 14(g): per-binding mutation testing on hot-path
modules.  Infrastructure shipped; per-binding survivor baselines
established post-merge.

- **`docs/MUTATION_BENCH.yaml`** — single source of truth: per-binding
  tool, hot-path module list (mapped to actual on-disk paths after the
  protocols split / Track E.11 extraction), baseline survivor count.
- **`tools/check_mutation_setup.py`** — static gate (~1 sec), wired as
  Shake `phony "check-mutation-setup"` and `tools/run_ci.py` step 13
  (always-on).  Verifies every declared hot-path source file exists
  on disk; catches silent rename / removal of a hot-path file.
- **`tools/mutation_run.py`** — dynamic runner (opt-in,
  ~30 min - 2 hrs).  Drives `mutmut` / `gremlins` / `Mull` per binding,
  archives JSON to `benchmarks/mutation/<short-sha>/`.  Per-binding
  skip env vars (`ALETHEIA_MUTATION_SKIP_{PYTHON,GO,CPP}=1`) for
  partial runs.  Gremlins substitutes for AGENTS.md cat 14(g)
  go-mutesting (the named tool is unmaintained since 2021); same
  operator set, same per-binding intent.
- **`docs/operations/MUTATION.md`** — procedure doc covering the
  threshold model (drift gate against per-binding YAML baseline +
  null-baseline-first-run special case), per-binding install steps,
  forward-revert verification protocol, and CI wiring.
- **`python/pyproject.toml [tool.mutmut]`** — mutmut 3.x config
  (paths_to_mutate = 5 hot-path modules; also_copy = aletheia/ for
  importability inside the mutated tree; tests_dir + 7 ignores for
  tests that need repo-root-relative paths).
- **`python/pyproject.toml [project.optional-dependencies] mutation`**
  — `mutmut>=3.5,<4` extras group; install via
  `pip install -e python/.[mutation]`.
- **`cpp/CMakeLists.txt -DALETHEIA_MUTATION=ON`** — opt-in build
  flag.  When enabled (clang-19 required), adds `-fpass-plugin=
  ${HOME}/.local/bin/mull-ir-frontend-19 -g -O0` to all targets.
  Build into a dedicated tree: `cmake -B build-mutation -DALETHEIA_MUTATION=ON`.

#### `tools/run_ci.py` CLI overhaul (R18 cluster 7)

Switched from env-var-only triggers to argparse-driven CLI flags,
with env-var fallback for back-compat.

- **`--san` / `--no-san`** — UBSan ctest battery (was: `ALETHEIA_SAN_CHECK=1`).
- **`--repro` / `--no-repro`** — reproducible build gate (was: `ALETHEIA_REPRO_CHECK=1`).
- **`--stability` / `--no-stability`** — long-run stability bench (was: `ALETHEIA_STABILITY_CHECK=1`).
- **`--mutation` / `--no-mutation`** — mutation testing across 3 bindings
  (NEW; pairs with `ALETHEIA_MUTATION_CHECK=1`).
- **`--full`** — enable every opt-in lane.  `--no-<lane>` always
  overrides, so `--full --no-mutation` runs everything except mutation
  testing.

Precedence: **CLI > env > default-off**.  All four env vars stay
supported; the legacy form remains valid for scripts and pre-push
hook callers.

Always-on step count: 26 → 27 (+1 for `check-mutation-setup` at
step 13; `check-stability-bench` at step 12 was added by cluster 6).

#### `tools/check_limits_parity.py` + Shake `check-limits-parity` gate (R20-GO-A-4.10 closure)

Static parity gate enforcing that
`go/aletheia/limits.go`'s mirrored constants and BoundKind wire codes
match the Agda SSOT at `src/Aletheia/Limits.agda`.  The Go mirror's
header has long claimed "Single source of truth:
src/Aletheia/Limits.agda; numeric values are mirrored here verbatim";
this gate enforces that promise.  Diffs every `boundKindCode <Tag>`
mapping (7 entries) plus every `max-<kebab-name>` numeric constant
(14 entries) against the Go-side `BoundKind*` / `Max*` mirror via
the explicit `NAME_MAPPING` / `BOUND_KIND_MAPPING` tables.

Categorisation:

- **REQUIRED** constants (`max-dbc-text-bytes`, `max-json-bytes`,
  `max-nesting-depth`, `max-identifier-length`, `max-string-length-bytes`,
  `max-atom-count-per-property`, `max-frame-byte-count`,
  `max-messages-per-file`, `max-signals-per-message`,
  `max-attributes-per-file`, `max-value-descriptions-per-file`) —
  input-length / structural bounds where cgo-boundary rejection is
  strictly preferable.  Mismatch is a hard error.
- **OPTIONAL** constants (`max-comments-per-file`, `max-nodes-per-file`,
  `max-value-tables-per-file`) — kernel-only list-cardinality bounds
  enforced after JSON parsing; no cgo-boundary advantage.  Omission
  from Go is acceptable.

Wired into `Shakefile.hs` as `phony "check-limits-parity"` and into
`tools/run_ci.py` as offline-enforcer step 12.  Python and C++ are
out of scope (no local mirror — they observe the typed
`InputBoundExceeded` error returned from the kernel).  Always-on
step count: 27 → 28.

### Changed

#### Changed — Parsers: LittleEndian `bitLength = 0` now rejected at parse time (R5-B1 / R6-B7.1 closure)

**BREAKING** — `validate_dbc` (and `parse_dbc` / `parse_dbc_text`) on a
DBC containing a LittleEndian signal with `length = 0` now surfaces a
`parse_signal_bit_length_zero` parse error instead of returning a
validation result with a `bit_length_zero` issue.  BigEndian was already
rejected at parse time since 2026-04-08; this change completes BE-LE
parity uniformly across both parse surfaces (JSON + text).

Caller migration: any code expecting `"bit_length_zero" in
result["issues"]` (Python) / `IssueCode::BitLengthZero` (C++) /
`IssueBitLengthZero` (Go) from `validate_dbc` on a LittleEndian
zero-length signal must now catch the parse error.  Python's
`ProtocolError` exception with `code = parse_signal_bit_length_zero`,
C++'s `Result<...>` with `ErrorCode::ParseSignalBitLengthZero`, Go's
`*aletheia.Error` with `Code = CodeParseSignalBitLengthZero` — same
wire code across all three bindings.  The validator's
`checkBitLengthZero` check remains as defense-in-depth but is
unreachable from any parse-driven external entry point.

This change addresses the in-source caveat at
`Aletheia.DBC.Formatter.WellFormed.PhysicallyValid` (the previous
asymmetry where `pv-BE` carried `1 ≤ bitLength` but `pv-LE` did not);
the constraint is now uniform across byte orders.  Both parse surfaces
are updated:
- `Aletheia.DBC.JSONParser.physicalGate` (JSON path) emits a typed
  `ParseErr SignalBitLengthZero` (wire code `parse_signal_bit_length_zero`).
- `Aletheia.DBC.TextParser.Topology.SignalLine.buildSignal` (text path)
  returns `nothing`, which propagates through `buildAllRaw` →
  `resolveSignalList` → `buildMessage` (parser `fail`) and surfaces at
  the top level as `DBCTextParseError.ParseFailure` (wire code
  `dbc_text_parse_failure`).  The text-parser error vocabulary is
  intentionally coarser than the JSON parser's (`DBCTextParseError`
  has three constructors; expanding it to mirror JSON's per-cause
  codes is out of scope for this entry).  The functional outcome is
  identical — zero-length LE signals are rejected at parse time on
  every external entry point.

#### Changed — LTL metric operators: `window` parameter typed as `Timestamp μs` instead of raw `ℕ` (R6-B7.2 closure)

Internal Agda kernel refinement — `MetricEventually`, `MetricAlways`,
`MetricUntil`, and `MetricRelease` now take their window parameter as
`Timestamp μs` (a wrapped `ℕ` with microsecond dimension tag) rather
than a bare `ℕ`.  The JSON wire shape is unchanged — the LTL JSON
parser wraps incoming `ℕ` via `mkTs` at the boundary, and the
formatter unwraps via `tsValue`.  No binding-facing or wire change.

This closes a pre-user audit finding (the previous "NO-FIX" rationale
that the window was a frame count rather than microseconds was
factually incorrect — the values flow into
`metricElapsed s curr ≤ᵇ tsValue w` window-check arithmetic in
`Aletheia.LTL.Coalgebra.stepL`, which is microsecond-vs-microsecond
comparison).  The `startTime` slot stays a suc-encoded `ℕ` because
the encoding carries a load-bearing
"uninitialized sentinel vs legitimate timestamp 0" distinction.

#### Changed — Agda kernel: `injectHelper` lifted to top-level + Bool fast-path via `Reflects` (R20-AGDA-B-26.3 / R20-AGDA-B-GA9.1 closure)

Internal Agda kernel + proof refactor — no binding, wire, or runtime
behavior change.  Three coordinated changes ship together to close two
R20 deferrals that the R19 cluster D + F four-approach probe had marked
as RE-DEFER on grounds of an Agda elaboration barrier:

1. `injectHelper` lifted from where-bound inside `injectSignal` to a
   top-level definition in `Aletheia.CAN.Encoding`.  Proofs (`Encoding/
   Properties/Roundtrip.agda`, `Encoding/Properties/Disjoint.agda`) name
   it directly via new top-level lemmas `injectHelper-reduces-{unsigned,
   signed}` and `injectHelper-preserves-disjoint-bits{,-physical}`.
   New top-level reduction lemmas `injectSignal-bounds-{true,false}`
   dispatch the outer `inBounds` guard in a single-line `rewrite`.
2. New smart constructor `Aletheia.Data.BitVec.Conversion.mkBoundedBitVec :
   (n bl : ℕ) → Maybe (BitVec bl)` using stdlib's `Reflects` data carrier
   (`with n <ᵇ bl | <ᵇ-reflects-< n bl`).  The `ofʸ`/`ofⁿ` constructors
   carry the bound-fit witness as data, sidestepping the `with ... in eq`
   ↔ outer-with-abstraction trap the R19 four-approach probe hit.
   Reduction equation `mkBoundedBitVec-just` lets consumers compose into
   `trans`/`with … | reduction` chains without crossing the barrier.
3. `injectHelper`'s Dec dispatch (`_<?_`) swapped for `mkBoundedBitVec`.
   MAlonzo output confirmed: the Dec constructor and `<?` are gone from
   `MAlonzo.Code.Aletheia.CAN.Encoding`.

The R19 cluster D + F probe's framing ("the barrier is structural to
Agda's `with ... in eq` elaboration mechanism") is empirically correct
— `mkBoundedBitVec-just` written with `with ... in eq` still triggers
the exact `[UnequalTerms]` "ill-typed with-abstraction" error in a
17-line minimal reproduction.  But the conclusion ("workaround: keep
`Dec`") was over-strong: the `Reflects` two-with pattern is the
structural escape hatch the four-approach probe didn't try.  The
updated guidance lives in `memory/feedback_with_in_eq_outer_abstraction_barrier.md`.

**Perf:** no measurable Frame Building gain over the post-`@0` baseline
(R19 cluster D's `@0`-erasure of `ℕToBitVec`'s bound slot already
captured the throughput win).  Benchmark deltas across all three
bindings are within WSL2 session-distant ±10% jitter per
`feedback_wsl2_variance_stance.md`.  Reason: MAlonzo emits
`Reflects.fromEquivalence` for `mkBoundedBitVec`, which allocates a
Reflects wrapper via `du_of_30` + two closures per call — one heap
cell, structurally similar to post-`@0` Dec.  The architectural win is
proof clarity (no 3-deep `with`-mirror, no where-bound runtime helper,
helper-level lemmas readable in isolation) and the reopening of the
"closed by upstream Agda fix" framing — `Reflects` is a stdlib-available
escape hatch that should be the first choice when a Bool fast-path needs
to bridge to a proof witness.

R20-AGDA-B-18.3 (the `nothing = nothing` arm on `mkBoundedBitVec`'s
result) stays DEFER — the branch is now via `Maybe` instead of `Dec`,
still structurally required by coverage and still provably dead.  An
in-source DO-NOT-RE-RAISE block at the branch documents the rationale
for future review-round agents.

#### Changed — All bindings: predicate pretty-printer renders Rationals via cross-binding-identical exact-decimal algorithm (R20 cluster Y — GO-D-19.1)

`format_formula` (Python) / `FormatFormula` (Go) / `format_formula` (C++)
previously delegated Rational rendering to each language's `:g` / `%g`
float-formatting default, which has different precision rules per
language (Python and C++ truncate to 6 significant digits; Go uses
round-trip-shortest precision).  The renderer now uses a single
exact-decimal algorithm in all three bindings, so the same Rational
value renders to byte-identical output regardless of language.

The renderer classifies on the GCD-reduced denominator: when the
denominator divides a power of 10 (terminating in decimal), the value
is emitted as an exact decimal computed via integer arithmetic on the
numerator/denominator pair (no floating-point step).  Non-terminating
Rationals are emitted as literal reduced `N/D`.  Examples:

- `Rational{23, 2}` → `"11.5"` (terminating, integer-exact)
- `Rational{1, 3}` → `"1/3"` (non-terminating; previously `"0.333333"`)
- `Rational{1234567, 1}` → `"1234567"` (previously `"1.23457e+06"` in
  Python/C++ — lossy 6-sig-fig truncation; `"1.234567e+06"` in Go)
- `Rational{123456789, 10**9}` → `"0.123456789"` (previously
  `"0.123457"` in Python/C++)
- `Rational{1, 1000000}` → `"0.000001"` (previously `"1e-06"` in C++)
- `Rational{50, 100}` → `"0.5"` (reduces, trims trailing zeros)

The dominant DBC-source case (factor / offset / min / max — all
human-authored decimals) is unaffected because those values canonicalise
as `n / (2^a · 5^b)` and fit in ≤ 6 significant figures.  The
divergence only bit on user-constructed values exceeding 6 significant
figures or values exceeding the language's scientific-notation
threshold.  Pathological case: terminating Rationals whose denominator
requires k > 18 decimal places render as the GCD-reduced `N/D` form
(same shape as the non-terminating branch) so that all three bindings
emit byte-identical strings — Go and C++ would otherwise risk int64
multiplier overflow, and Python (arbitrary-precision) would otherwise
emit a long exact decimal that diverged from the other two.  Typical
DBC predicate values stay well under k=10.  Wire JSON shape
(`{"numerator": N, "denominator": D}`) is unchanged.

Implementation: the renderer lives in the Agda kernel
(`Aletheia.DBC.RationalRenderer.formatRational`); each binding calls it
via FFI rather than maintaining a parallel implementation.  All three
bindings dlopen `libaletheia-ffi.so` lazily on first use of the
display path (Python `_get_or_load_renderer_lib`, Go `sync.Once` in
`renderer.go`, C++ `std::call_once` in `rational_renderer.cpp`),
independent of whether a backend (`AletheiaClient`, `FFIBackend`,
`FfiBackend`) has been instantiated.  Cross-binding output equality is
therefore an architectural invariant of the kernel-via-FFI design
rather than a test-corpus convention.  A missing `libaletheia-ffi.so`
surfaces as a typed error / panic from the display path rather than
silently selecting a parallel algorithm.

#### Changed — Python: DSL float-input conversion now mirrors Go/C++ `from_double` (R20 cluster Y — GO-D-19.1)

`Signal(...).equals(value)` and sibling comparison methods previously
converted float inputs via `Fraction(value)`, which produces the
exact IEEE 754 binary fraction (e.g. `Fraction(0.1)` =
`Fraction(3602879701896397, 36028797018963968)`).  The new
`to_predicate_fraction` helper uses 10^9 scaling
(`Fraction(round(value * 10**9), 10**9)`), matching Go's
`floatToRational` and C++'s `Rational::from_double` exactly.

Without this change, the same user call produced structurally different
Rationals across bindings (Python: huge IEEE-754 fraction; Go/C++:
human-friendly fraction like `1/10` for `0.1`), and the new
exact-decimal renderer would emit a 56-character exact decimal of the
IEEE-754 noise on the Python side.  After this change,
`Signal("S").equals(0.1)` produces `Fraction(1, 10)` and renders as
`"0.1"` in all three bindings.

`int` and `Fraction` inputs flow through unchanged.
`to_signal_fraction` (used by the Excel / YAML loader for DBC
factor / offset / min / max parsing) still uses `limit_denominator`
since those values arrive as parsed text, not as the user's runtime
floats.

#### BREAKING — Go and C++: `mux_values` field + method renamed to `multiplex_values` for cross-binding parity (R20 GO-A-3.5)

The `Multiplexed` struct's value-list field and the `DBCMessage` /
`DbcMessage` query method were both spelled `MuxValues` (Go) /
`mux_values` (C++) — the same identifier doing double duty as a struct
field and as a query method on a different type. The field name now
matches the canonical wire-JSON form (Python's `multiplex_values` on
`DBCSignalMultiplexed`, which was already the source of truth):

- **Go** — `aletheia.Multiplexed.MuxValues` → `MultiplexValues`;
  `(aletheia.DBCMessage).MuxValues(SignalName)` → `MultiplexValues(SignalName)`.
  Migration: rename field references and method calls; the type
  signature is unchanged.
- **C++** — `aletheia::Multiplexed::mux_values` → `multiplex_values`;
  `aletheia::DbcMessage::mux_values(const SignalName&) const` →
  `multiplex_values(const SignalName&) const`. Migration: same rename
  on the field designator and method call.

Python is unaffected: the wire-canonical `multiplex_values` field on
`DBCSignalMultiplexed` was already correct, and the
`aletheia.mux_values(msg, multiplexor)` module-level query function
keeps its short name (function vs. dict-key namespaces don't collide).
The `signals_for_mux_value` sibling, the `MultiplexValue` type, and the
Go `ContainsMuxValue` helper all keep their existing names — this
rename only targets the field/method that previously shared the
`mux_values` identifier. Closes R20 GO-A-3.5.

#### BREAKING — C++: `StrongString<Tag>` merged into `Strong<Tag, T>` (R20 cluster X — CPP-D-15.3)

The previously-separate `StrongString<Tag>` template is removed. `Strong<Tag, T>`
now exposes a concept-gated `operator std::string_view()` when `T == std::string`,
so existing `std::string_view{name}` direct-init sites for `SignalName` /
`MessageName` / `NodeName` / `Unit` continue to work unchanged. The four name
aliases now read `Strong<..., std::string>` instead of `StrongString<...>`.
Out-of-tree consumers that referenced the `StrongString` template name must
substitute `Strong<Tag, std::string>`. Closes CPP-D-15.3.

#### Added — C++: `Strong<Tag, T>::of(...)` perfect-forwarding factory (R20 cluster X — CPP-D-15.2)

New static factory: `PhysicalValue::of(1, 10)` constructs a `PhysicalValue`
from `Rational{1, 10}` without the explicit inner-type call site. Works for
every `Strong<Tag, T>` instantiation (numeric, string, bit-position). Chosen
over per-tag free `make_*` factories so the convenience scales without N new
symbols. Old `PhysicalValue{Rational{1, 10}}` form continues to compile.

#### Changed — C++: `LtlFormula` switched from `std::variant` inheritance to composition (R20 cluster X — CPP-D-15.4 / 17.3)

`struct LtlFormula : std::variant<...>` was a portability hazard across
libstdc++ versions (special-member-function constraints, `in_place_index_t`
deduction edge cases under derived ctors). The variant is now a member:

```cpp
using LtlFormulaVariant = std::variant<Atomic, Not, And, Or, /* ... 14 total */>;
struct LtlFormula {
    LtlFormulaVariant value;
    template<typename T>
        requires(!std::same_as<std::decay_t<T>, LtlFormula>) &&
                std::constructible_from<LtlFormulaVariant, T>
    LtlFormula(T&& v) : value(std::forward<T>(v)) {}
    template<typename Visitor> constexpr auto visit(Visitor&&) const& -> decltype(auto);
    /* + & and && overloads */
};
```

Existing builder functions (`ltl::atomic`, `ltl::always`, etc.) work
unchanged thanks to the constrained converting ctor. Consumers that previously
called `std::visit(visitor, formula)` should call `formula.visit(visitor)`,
or use the explicit `formula.value` member. Two `std::get_if<T>(uniq.get())`
sites in `enrich.cpp` now read `std::get_if<T>(&uniq->value)`. The
14-alternative list is now centralized in the `LtlFormulaVariant` alias —
single source of truth.

The reviewer's "Visitor pattern for binary-compat extension" framing
(virtual-dispatch class hierarchy, finding CPP-D-17.3) is intentionally
**not pursued**: header-only template consumption + 1:1 Agda kernel ADT
mapping means virtual dispatch would lose constexpr and break the lambda
idiom for no architectural gain. Documented in `cpp/include/aletheia/ltl.hpp`.

#### BREAKING — Python: `aletheia.asyncio.testing.gate_send_frame` replaced by `gated_backend` (R20 cluster P — PY-D-24.2)

Test scaffolding for deterministic cancellation rendezvous moves from
monkey-patching `sync_client.send_frame` (via `setattr`) to wrapping the
Backend via the new public DI seam. Old:

```python
sync = AletheiaClient()
with gate_send_frame(sync, after_n=1) as (started, proceed):
    async with AsyncClient(sync_client=sync) as client:
        ...
```

New:

```python
from aletheia import AletheiaClient, FFIBackend
from aletheia.asyncio.testing import gated_backend

with gated_backend(FFIBackend(), after_n=1) as (backend, started, proceed):
    sync = AletheiaClient(backend=backend)
    async with AsyncClient(sync_client=sync) as client:
        ...
```

Same `(started, proceed)` `threading.Event` rendezvous; same
deterministic cancellation point between frame `after_n - 1` and frame
`after_n`. The wrapper is a `_CountingGateBackend` instance that
delegates all 13 Backend methods to the inner backend and counts
`send_frame_binary` calls only. Closes PY-D-24.2 (closed naturally with
the Backend DI seam).

#### BREAKING — Python: `aletheia.load_checks` dispatch is now strict by argument type (R19 cluster B)

`load_checks(source: str | Path)` previously auto-promoted any string that
matched an existing file path to a file load (path-confusion vector,
PY-B-26.12). The dispatch is now strict: `pathlib.Path` → file load,
`str` → inline YAML parse. Callers passing a file path as a bare string
must wrap in `Path`:

```python
# before
checks = load_checks("checks.yaml")

# after
from pathlib import Path
checks = load_checks(Path("checks.yaml"))
```

Inline YAML strings continue to work unchanged. Static type checkers
(pyright/mypy) catch non-(`str`|`Path`) callers at check time.

#### Changed — Python: `ALETHEIA_LIB` now rejects group/world-writable paths (R19 cluster B)

`AletheiaClient` startup raises `PermissionError` if the path resolved
from `ALETHEIA_LIB` is writable by anyone but its owner (mode bits
`S_IWGRP | S_IWOTH`). Defense against the case where an unprivileged
third party who cannot set the env var poisons an existing legitimate
path. Owner-of-file ≠ current uid is still allowed (a shared
`/usr/local` install with root-owned `.so` loaded by a non-root user
remains a supported deployment). Owner-only writes are accepted (mode
`644` / `600`); fix with `chmod go-w $ALETHEIA_LIB` if rejected.

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

#### BREAKING — Python: `ProcessError` removed in favor of kind-tagged hierarchy (R19 Phase 2 cluster 17 / PY-D-20.1)

The overloaded `aletheia.ProcessError` class was removed.  Replacement:
the kind-tagged `AletheiaError` subclasses mirror Go's `ErrorKind`
4-kind enum and C++'s `ErrorKind` 7-kind enum.  By category:
  - FFI / null-pointer / RTS-init failures → `aletheia.FFIError`
  - "Client not initialized" / "DBC not loaded" (client-side cache) →
    `aletheia.StateError`
  - "no DBC message for CAN ID" / "unknown signal" / "payload length
    mismatch" (client-side validation) → `aletheia.ValidationError`
  - Kernel `ErrorResponse` + binary FFI rejection paths →
    `aletheia.ProtocolError`

Migration: replace `except ProcessError` with `except AletheiaError` for
the catch-all form, or with the specific subclass per the category map
above for finer-grained handling.

#### BREAKING — Go: `Dbc*` → `DBC*` and `CanID` → `CANID` rename across exported surface (R19 Phase 2 cluster 5)

Go's acronym-casing convention (per `golangci-lint revive var-naming`)
calls for fully-capitalised initialisms in exported names.  The R19
Phase 2 cluster 5 sweep renamed 52 distinct `Dbc*` identifiers to
`DBC*` and ~40 `CanID` references to `CANID`.  Affected names include
the public types `DBCDefinition`, `DBCMessage`, `DBCSignal`,
`DBCAttribute`, `DBCComment`, `DBCNode`, `DBCSignalGroup`,
`DBCEnvironmentVar`, `DBCValueTable`, `DBCValueEntry`, and the
identifier-type alias `CANID`.  Constructor functions retained the
old `Dbc` casing (`NewDbcMessage`, `NewDbcDefinition`) and are
themselves a follow-up rename pending — flagged under R20 GO-D-15.1.

Migration: mechanical sed/perl rename on the consumer side
(`s/\bDbc/DBC/g` on type references, `s/\bCanID\b/CANID/g`); no
behavioral change.  C++ keeps the `Dbc*` form (its idiom); Python
already had `DBCDefinition` as the canonical name.

#### BREAKING — Go: `Dbc*` → `DBC*` rename completion + `DBCRawValueDesc.CANID` stutter fix (R20 cluster O / GO-D-15.1 / GO-D-15.2)

Closes the R19 cluster 5 follow-up flagged in the entry above.
Constructor functions, the `Backend` binary-FFI method, the excel
sub-module option, the unexported `parseDbc*` family, and the
private `formatDbcFn` field-of-struct all gain the fully-capitalised
initialism:

  - `aletheia.NewDbcMessage` → `aletheia.NewDBCMessage`
  - `aletheia.NewDbcDefinition` → `aletheia.NewDBCDefinition`
  - `Backend.FormatDbcBinary` interface method (and its `FFIBackend`
    / `MockBackend` / nocgo-stub implementations) →
    `Backend.FormatDBCBinary`
  - `excel.WithDbcSheet` option function → `excel.WithDBCSheet`

`DBCRawValueDesc.CANID` field renamed to `ID` (Go field-stutter
convention — field name should not repeat its containing type).
Affects struct-literal construction and field access.

Migration: mechanical sed on consumer side
(`s/\bNewDbcMessage\b/NewDBCMessage/g`,
 `s/\bNewDbcDefinition\b/NewDBCDefinition/g`,
 `s/\bFormatDbcBinary\b/FormatDBCBinary/g`,
 `s/\bWithDbcSheet\b/WithDBCSheet/g`,
 `s/\.CANID\b/.ID/g` scoped to `DBCRawValueDesc` value sites).  No
behavioral change.

#### BREAKING — Go: predicate value fields are now `Rational` (R19 Phase 2 cluster 17 / GO-D-19.1)

The Between / ChangedBy / StableWithin / Equals / LessThan / etc.
predicate types previously declared `PhysicalValue` / `Delta` /
`Tolerance` as `float64`.  Per the cross-binding DecRat universal
principle (Python `Fraction`, C++ `Rational`), these fields are now
`Rational`.

New constructor helpers on `go/aletheia/types.go`:
  - `IntRational(n int64) Rational` — exact `n/1`.
  - `RationalFromFloat(v float64) Rational` — 10⁹ fixed-point scaling
    matching the FFI signal-value ppb precision; NaN / ±Inf clamp to
    `0/1`.

Migration: change `Between{Signal: "Speed", Min: 0, Max: 250}` to
`Between{Signal: "Speed", Min: aletheia.IntRational(0), Max:
aletheia.IntRational(250)}` (or `RationalFromFloat(...)` for fractional
literals).  ~150 test sites were updated mechanically in the same
commit (`1e4becc`).

#### BREAKING — Go: `Client.SendFrame` adds trailing `brs, esi *bool` parameters (R19 Phase 2 cluster 18 phase C)

The `Backend.SendFrameBinary` interface and `Client.SendFrame` /
`Client.SendFrames` method-set now accept CAN-FD BRS (bit-rate-switch)
and ESI (error-state-indicator) metadata per ISO 11898-1:2015 §10.4.2
/ §10.4.3.  Migration: pass `nil, nil` to recover prior CAN-2.0B
behaviour; pass `&trueVal` / `&falseVal` for CAN-FD frames where the
controller emitted the bits.  The Aletheia kernel does NOT consume
these bits — pass-through metadata only.

#### BREAKING — Python: `CANFrameTuple` is now a 7-tuple (`brs` / `esi` appended) (R19 Phase 2 cluster 18 / R20 cluster L)

`CANFrameTuple` gains two trailing optional fields — `brs` and `esi`
— exposing CAN-FD Bit Rate Switch / Error State Indicator metadata
per ISO 11898-1:2015 §10.4.2 / §10.4.3. Construction stays back-compat
(both default to `None`), but **unpacking arity changes** from 5 to
7. Migration: extend `for ts, can_id, dlc, data, _ext in
iter_can_log(...)` to `for ts, can_id, dlc, data, _ext, _brs, _esi in
iter_can_log(...)`, or switch to named-tuple field access (`frame.brs`,
`frame.esi`). The Aletheia kernel does NOT consume these bits —
pass-through metadata only.

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
- Agda kernel facade `Aletheia.Main` re-exports five additional
  `Aletheia.Protocol.Message` constructors that had drifted out of the
  `using` list: `SendFrame` / `ParseDBCText` / `FormatDBCText` /
  `DBCTextResponse` / `ParsedDBCResponse`.  No runtime change — the FFI
  dispatcher (`processStreamCommand`) was already handling them; the
  facade now matches the actual protocol surface (R20 cluster Q —
  AGDA-A-1.1).
- Go `Backend` interface docstring at `go/aletheia/backend.go` gains
  structured grouping (session lifecycle + JSON command bus; binary-FFI
  send / event / state-transition endpoints; binary-FFI bidirectional
  endpoints) mirroring C++ `IBackend`'s [MANDATORY] / [OPTIONAL] split
  at `cpp/include/aletheia/backend.hpp`.  Doc-only; method signatures
  and behaviour unchanged (R20 cluster R — GO-D-20.1).
- Two new step-level structural lemmas in
  `Aletheia.LTL.Coalgebra.Properties`:
  `stepL-always-never-satisfied` (proves `stepL (Always φ) y ≢
  Satisfied` — the `Satisfied` branch of the streaming runtime's
  `classifyStepResult` is unreachable when properties are wrapped in
  `Always(...)`, the canonical CAN safety pattern) and
  `stepL-eventually-never-violated` (proves `stepL (Eventually φ) y ≢
  Violated ce` — re-stepping an `Eventually`-shaped proc after
  `Satisfied` is safe).  Comment rewrite in
  `Aletheia.Protocol.StreamState.Internals.classifyStepResult` corrects
  the prior informal "stability argument" which conflated runL-level
  short-circuit semantics with stepL-level invariance and named
  `Always`/`Release` as "the only safety operators that yield
  Satisfied" — `Always` in fact never yields `Satisfied` (its
  `combineAnd` RHS is always `Continue`).  Latent gap for top-level
  `Until`/`Release`/`MetricUntil`/`MetricRelease`/raw `Atomic` proc
  shapes documented in-source + carried to DEFER-end-of-round as
  `AGDA-B-9.2-residual` (R20 cluster S — AGDA-B-9.2 partial closure).
  No runtime change.
- `Aletheia.DBC.JSONParser._≟-LC_` (decidable `List Char` equality)
  renamed to `_≟ₗᶜ_` (subscript-ell + superscript-c) to match the prior
  convention referenced in `Aletheia.LTL.SignalPredicate.Cache`; 8 use
  sites in JSONParser.agda updated.  `Aletheia.Parser.Combinators.elem`
  (private `Char → List Char → Bool` membership test) replaced with a
  point-free `elem c = any (c ≈ᵇ_)` over stdlib's `Data.Bool.ListAction.any`
  (≡ `or ∘ map p`); behaviour preserved, definition is no longer
  hand-rolled (R20 cluster U — AGDA-C-27.2 + AGDA-C-27.3).  No runtime
  semantics change.
- `AGENTS.md` § CI/CD final paragraph rewritten from future-tense ("the
  first review round under this section will surface...") to past-tense
  reflecting current state: the three audit scripts and `dependabot.yml`
  are in place (2026-05-09); subsequent rounds maintain them (R20 cat 1
  surfaced `CICD-1.2 / 1.3 / 2.3 / 3.2 / 5.1` against the scripts
  themselves); action references in `.github/workflows/` are still
  tag-pinned (`@v4`), SHA migration remains the next reviewable cat 1
  change (R20 cluster T — DOC-A-1.14).
- New module `Aletheia.DBC.BoundWalks` hosts the handler-boundary
  bound walks (cardinality `vds*` family + string-length
  `firstOverBound*` family — 18 functions total) previously duplicated
  between `Aletheia.Protocol.Handlers` and
  `Aletheia.Protocol.Handlers.ParseDBCText`.  The original duplication
  was cycle-avoidance (ParseDBCText cannot import from Handlers because
  Handlers imports ParseDBCText); the new sibling module sits at the
  leaf level so both consumers can pull from it without closing a
  cycle.  Per-handler aggregators (`signalsBound` /
  `firstDBCOverBound` / `firstStringOverBound`) stay local because
  their return types differ — `Handlers` carries
  `Maybe (String × ℕ × ℕ)` for field-name-tagged JSON error messages
  while `ParseDBCText` carries `Maybe (ℕ × ℕ)` without context — so
  the field-tagging choice stays at the call site rather than baked
  into the helpers.  Module count **247 → 248** (R20 cluster V —
  AGDA-A-1.3).  No runtime semantics change.
- Doc-fence harness defense-in-depth: new autouse `_sandbox_cwd` fixture
  in the repo-root `conftest.py` pins every fence's cwd to a per-test
  `tmp_path` via `monkeypatch.chdir`.  Defense on top of the existing
  `pytest_sessionstart` loader patches: even if a future regression
  removes a `create_template` / loader patch or adds a new
  file-emitting fence, writes land in pytest's auto-cleaned `tmp_path`
  rather than the repo root.  Doc fences are cwd-independent (loader
  fakes ignore path args), so the chdir is invisible to fence
  behaviour (R20 cluster T — vehicle_checks.xlsx doc-harness
  recreation).
- Streaming runtime now drops a property from the active iteration set
  when its `stepL` returns `Satisfied`, instead of re-evaluating the same
  proc on subsequent frames.  `Aletheia.Protocol.Iteration.StepOutcome`
  gains a parameterless `complete : StepOutcome S E` constructor;
  `iterateImpl` skips the property on `complete`; `length-specResult-≤`
  proves active-set monotonicity.  Internal kernel change — no
  binding-side API surface change.  See the corresponding § Fixed entry
  for the observable behaviour change (R20 cluster W —
  AGDA-B-9.2-residual operational fix).

- `cantools` is no longer a Python runtime dependency. The verified
  Agda DBC text parser replaces every code path that previously
  delegated to it (Track B.3.g). `python-can` remains an optional
  dependency under the `can` extra for log-file readers (ASC / BLF /
  MF4 etc.); replacing it is a Phase 6 goal.

### Fixed

- **Streaming runtime soundness** (R20 cluster W — AGDA-B-9.2-residual).
  Two related bugs are closed by the same structural fix
  (`classifyStepResult Satisfied _ = complete` — see corresponding
  § Changed entry on `StepOutcome.complete`).
  (1) **Mid-stream false counterexample on raw `Until` / `Release` /
  `MetricUntil` / `MetricRelease` / raw `Atomic` / `And`/`Or`-of-atomic
  shapes** (LTL formulas submitted via the JSON wire without the
  canonical Python DSL `.always()` / `.eventually()` wrapping):
  `Until (Atomic 0) (Atomic 1)` at frame y₁ where atom 1 holds
  returns `Satisfied` via `combineOr Satisfied _ = Satisfied`; at frame
  y₂ where both atoms are False the runtime would re-evaluate the same
  proc and return `Violated` via `combineOr (Violated _) (Violated _)
  = Violated`, emitting a PropertyResponse violation for a property
  that the user had already been told was satisfied.  Post-fix the
  property is dropped from the active set on `Satisfied`, so
  subsequent frames cannot re-evaluate the proc.
  (2) **EndStream false-`Fails` for `Eventually` / `Until` / `MetricUntil`
  / `MetricEventually` / `Release` / `MetricRelease` properties that
  satisfied mid-stream**: pre-fix the original-shape proc was kept in
  the active set on `Satisfied`, and at EndStream `finalizeL` (which
  inspects formula structure only, not stepL history) returned
  `Fails EventuallyUnsatisfied` / `Fails UntilUnsatisfied` for properties
  that had in fact been satisfied during the stream.  Concrete witness
  observed pre-fix on `Eventually(TestSignal == 42)` with TestSignal=42
  at y₂: EndStream returns `{'status': 'fails', 'reason': 'Eventually:
  never satisfied before end of stream'}`.  Post-fix the property
  drops from the active set on satisfaction, so EndStream's
  `Complete` response simply omits it (no false negative).
  `Always`-wrapped formulas are unaffected (per the R20 cluster S
  `stepL-always-never-satisfied` lemma `Always` proc never returns
  `Satisfied`, so the `complete` branch is unreachable for the
  canonical safety surface).  **Observability shift on satisfied
  `Eventually` / raw temporal formulas at EndStream**: pre-fix the
  `Complete` response listed every input property's verdict (some
  incorrect per (2) above); post-fix only the properties that were
  still in the active set at EndStream appear in `Complete.results`.
  Properties that satisfied mid-stream are absent rather than
  misclassified.  Lifting `PropertyResult.Satisfaction` emission into
  the streaming dispatch (so users get an explicit positive verdict
  on satisfaction) is a separate enhancement — landing it would
  require threading per-step completion events through
  `dispatchIterResult` and surfacing them on the wire alongside
  `Ack` / `PropertyResponse(Violation)`.  Python regression test
  `python/tests/test_classify_satisfied_complete.py` exercises the
  witnesses through the JSON wire end-to-end.
- **CI orchestrator** (`tools/run_ci.py`): fixed three defects surfaced
  by cluster 6's first end-to-end run per
  `feedback_orchestrator_end_to_end_validation.md`.  (1) `total_steps`
  default bumped from 25 to 26 to reflect the cluster-6 addition of
  `check-stability-bench` at step 12 (and opt-in bumps shifted +1 to
  preserve relative offsets).  (2) pylint command switched from bare
  `pylint` (system-wide pylint, no visibility into venv-only packages)
  to `<venv-python> -m pylint` so cluster-5's `hypothesis` import in
  `tests/test_property_hypothesis.py` resolves and stops emitting
  E0401 (the system pylint was scoring 9.98/10 from import-error,
  blocking the gate).  (3) `clang-format` find-prune list extended
  with `./build-asan` and `./build-ubsan` so cluster-5 sanitizer build
  trees' CMake-generated test files don't trip the lint
  (R18 cluster 6 follow-up).
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
- **Go**: `parseValidationResponse` and `parseParsedDBCResponse`
  previously emitted `nil` slices for empty `Issues` / `Warnings`,
  diverging from Python's `[]` (empty list) default.  JSON-marshaling
  the responses produced `null` rather than `[]`.  Now initialized as
  empty slices.  Surfaced by the cross-binding integration test
  (R18 cluster 5).
- **Python**: 3 cancellation tests (`test_timeout_mid_batch_raises_cancelled`,
  `test_explicit_task_cancel`, `test_timeout_during_iter`) intermittently
  failed under `python -X dev` due to `asyncio.timeout(0)` / `asyncio.sleep(0)`
  races in the test scaffolding.  Replaced with the public
  `aletheia.asyncio.testing.gate_send_frame` helper (paired with the
  `AsyncClient(sync_client=…)` injection seam) using `threading.Event`
  primitives without timeouts; cancellation point is pinned between
  committed frames purely via synchronization, no physical time
  involved.  50/50 runs under `-X dev` pass (R18 cluster 5 / PY-B-14a.1).
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
- **Tooling**: `tools/run_ci.py` orchestrator defects revealed by the
  first end-to-end run post phase 6 — fixed in phase 7. (a) Steps
  13 (ctest), 16 (gofmt + vet), 17 (clang-format) silently no-op'ing
  because `run_step_in`'s `$*` expansion drops quoting on inner
  `bash -c "..."` arguments; the inner bash ran only the first word as
  command and left the rest as positional args, so cmake / gofmt /
  clang-format ran without their actual arguments (cmake printed
  Usage, gofmt processed no input, clang-format scanned every file
  including yaml/.clang-tidy/etc). Steps 13/16 "passed" for the wrong
  reason (vacuous); step 17 finally hit a real diagnostic against
  unfiltered files. Fix: switch to direct `run_step` + a single
  `bash -c` with `cd` folded in. (b) Step 15 (pylint) used exit-code
  gating; pylint's exit code is a bit-flag (1=fatal/2=error/4=warning/
  8=refactor/16=convention) and exit 8 fires whenever R0801
  duplicate-code is issued, even at score 10.00/10. Fix: capture
  output and grep for `rated at 10\.00/10` per the SCORE-based gate
  defined in AGENTS.md L611. (c) Step 16 used `gofmt -d` (diff,
  exits 0 even on dirty source); fix: use `gofmt -l` (list) and gate
  on output-empty AND rc=0, matching AGENTS.md L190. (d) Step 18
  (clang-tidy) was missing entirely despite AGENTS.md L494 marking it
  mandatory; added with the canonical `clang-tidy -p build src/*.cpp`
  invocation per AGENTS.md L580 (src/ only — tests/ scope is a
  separate concern, tracked as R18 Cluster 1 deferred). Total step count 20→21. First genuine end-to-end pass
  logged at `tools/ci-output/ci-review-r18_-2026-05-08T*.log` (18m38s
  wall, ALL 21 STEPS PASSED). Forward-revert gate-shape verified for
  steps 15/16/17/18 (R18 cluster 1 phase 7).

---

## [1.1.1] — 2026-04-03 and earlier

This file was bootstrapped at v2.0.0; pre-v2.0.0 history is not
retroactively documented here. Tag history (`git tag -l`): `v1.1.1`,
`v1.0.0`, `v0.3.2`, `v0.3.1-beta`, `v0.3.0-alpha`,
`v0.1.0-proof-research`, `v0.1.0-alpha`. Use `git log <tag>` for the
historical record.
