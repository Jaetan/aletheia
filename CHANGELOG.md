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
  separate concern, tracked in `review-r18-findings.md` Cluster 1
  deferred). Total step count 20→21. First genuine end-to-end pass
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
