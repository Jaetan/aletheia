# Changelog

All notable changes to Aletheia are documented in this file.

The format follows [Keep a Changelog 1.1.0][kac] and the project adheres to
[Semantic Versioning 2.0.0][semver].

[kac]: https://keepachangelog.com/en/1.1.0/
[semver]: https://semver.org/spec/v2.0.0.html

## [Unreleased]

## [5.0.0] — 2026-07-24

### Added

- **Hot-path Bool predicates are now self-certifying (`Dec₀` reification,
  kernel-only, runtime-neutral).** A new `Aletheia.Data.Dec0` module packages
  a fast-path Bool with an ERASED `Reflects` certificate; MAlonzo compiles
  the record to a GHC newtype over `Bool` (pinned by a new `check-erasure`
  guard), so a certified predicate costs exactly what the bare Bool cost —
  measured identical across all four bindings' benchmark lanes. Reified
  sites, several of which previously had NO machine-checked meaning at all:
  the LTL atom comparators (`Aletheia.Data.Dec0.Rational` — equality via
  antisymmetry, order via the stdlib `≤ᵇ` bridges), the `finalizesHolds` /
  `finalizesFails` absorption guards (certified against `finalizeL`), the
  extraction bounds check `inBounds` (certified as the `min ≤ v ≤ max`
  conjunction), CAN-ID equality `canIdEquals`, the multiplexor selector
  match (certified as Any-membership), the bit-membership/intersection
  checks and the frame-building overlap family (certified against a new
  `HasPairOverlap` proposition), and a `_≟cs₀_` twin packaging identifier
  equality with its retained lemma family. Existing Bool call sites and
  every existing proof are unchanged — the Bools are now definitional
  projections of their certified twins, so the fast path and its meaning
  can no longer drift apart. Sites whose proofs consume witnesses
  relevantly (`_≡ᵇ-proc_`, `findSignalInList`, `mkBoundedBitVec`'s
  reduction lemma) deliberately keep their relevant-proof form; the
  reasoning is recorded at each site.


- **C++: `ltl::implies(antecedent, consequent)` combinator.** The C++ binding
  gains an implication constructor (the standard `!antecedent || consequent`
  encoding, `either(negate(a), c)`), reaching parity with Go's `Implies`, Rust's
  `Formula::implies`, and Python's `.implies()`. Implication is now offered by
  all four bindings rather than three.
- **Cross-binding benchmark-schema SSOT + conformance gate**
  (`benchmarks/SCHEMA.yaml`, `tools/check_bench_schema.py`, wired into
  `tools/run_ci.py` and the benchmark workflow). Every binding's benchmark now
  emits an identical JSON schema — same CLI flags, `results` container, per-row
  keys, and verbatim lane/sweep labels — for each mode; the gate drives each
  built binary and fails on any drift. The C++/Go/Rust `scaling` benchmarks
  gained the trace-size (CAN 2.0B + CAN-FD) and property-complexity sweeps that
  previously only Python ran, and every scaling point is now run-averaged
  (`--runs`) across all four bindings.
- **A binary-wire encoder guard with a new extraction error code
  (`extraction_value_exceeds_wire_range`).** Exact-arithmetic reduction can
  push an extracted value's numerator or denominator past the signed 64-bit
  binary-wire slots even when every ingested literal was in range, so the
  FFI shim's response encoder now bounds-checks both components before the
  wire pokes and reroutes the affected signal to the existing per-signal
  error stream, with the code minted in the kernel's extraction-error
  vocabulary per the wire-code SSOT protocol (YAML row, per-binding
  vocabulary members and decoder messages, parity-gate anchors). Regression
  suites pin both directions: over-range components become a typed error
  entry, and components exactly at the Int64 boundary still travel exactly.
- **The Python client caps the embedded kernel's heap by default.** The GHC
  RTS runs uncapped unless told otherwise, so a runaway allocation inside
  the kernel previously escalated to a host-level out-of-memory kill instead
  of a failed call. `hs_init` now always receives a heap cap (a containment
  bound far above the kernel's measured working set); flags in
  `ALETHEIA_RTS_OPTS` are appended after it, so a caller-supplied `-M`
  still wins.
- **Native `.deb` / `.rpm` packages and a GHCR-published container image join
  the release.** `cabal run shake -- packages` builds both native packages
  from one declarative `packaging/nfpm.yaml` (nfpm, SHA-pinned in CI): the
  payload is the release bundle mapped wholesale to `/opt/aletheia` — proven
  byte-identical to the tarball's tree by extraction diff — with strictly
  opt-in environment wiring (no maintainer scripts, no `profile.d`; consumers
  source `/opt/aletheia/env.sh` or `env.fish`), x86-64-only metadata, and the
  GMP runtime as the only dependency beyond glibc (`libgmp10` for deb; the
  `libgmp.so.10()(64bit)` soname for rpm, which resolves across rpm distros
  regardless of the owning package's name). Packages are hash-pinned and
  keyless-signed per release — deliberately not claimed bit-reproducible:
  `SOURCE_DATE_EPOCH` empirically pins nfpm's own metadata but not payload
  mtimes. The release workflow builds and publishes them with the cosign
  self-verify loop extended over every signed artifact, a real `dpkg -i`
  install smoke, and an rpm payload structural check. The runtime container
  image is now published to `ghcr.io/jaetan/aletheia` (version + latest tags)
  with its digest keyless-signed and OCI source/description/licenses labels;
  the push runs last, after the draft Release publishes, so a failed release
  never leaves a live orphaned image. `Dockerfile.runtime` installs the
  Python binding from the bundled payload rather than the worktree (fixing a
  skew where the image's binding could differ from the bundle it shipped)
  and gains throwaway BuildKit verify stages — Go, Rust, and C++ (clang-22,
  the enforced toolchain) each build a consumer against the image's own
  `/opt/aletheia` — so the image cannot build unless every compiled binding
  works against the exact bytes it ships, while the final image stays slim
  with no toolchains aboard.
- **Release bundles are validated end-to-end across the compiled bindings,
  gating publish.** `tools/bundle_validate.py` unpacks the distribution
  tarball, runs both bundled installers capturing their printed per-language
  recipes, executes those exact recipe lines (the recipes users read are the
  recipes CI runs), checks `install.sh`/`install.fish` recipe parity and an
  absolute `ALETHEIA_LIB` from `env.sh`/`env.fish` sourced in a foreign cwd,
  then builds and runs one consumer program per compiled binding (C++, Go,
  Rust) through the verified kernel: parse a real `.dbc`, arm an LTL
  property, stream a conforming and a violating frame, and assert exactly
  one violation with the expected enrichment. A missing toolchain is a
  precise skip locally and a failure under `--require`; `--self-test`
  proves the gate has teeth by corrupting bundle copies and asserting each
  corruption fails validation. `release.yml` now gates publish on this
  validation (consumer toolchains installed with cache keys shared with the
  PR workflows), and the repo's first scheduled workflow
  (`bundle-validation.yml`, weekly + manual dispatch) both builds an
  unsigned `dist` from HEAD and replays the published-Release consumer path
  verbatim — download, `sha256sum -c`, cosign keyless verification against
  the release workflow's identity, then the same validation — so staging,
  recipe, or binding rot surfaces between releases instead of at the next
  tag.
- **The release SBOM now bills the bundled binding source trees, gated.**
  `tools/sbom_generate.py` gains hand-rolled manifest parsers — one per
  bundled binding, still zero external SBOM tooling — behind `--bindings-dir`,
  reading the STAGED `dist/aletheia/bindings` tree (the SBOM must describe
  the bytes that ship, not the worktree): Python optional-extra requirements
  (scope `optional`, the requirement range carried verbatim — a purl never
  gets an invented pin), `go.mod` requires (scope `required`; the `go.sum`
  `h1:` Merkle dirhash rides a `golang:h1` property, deliberately never a
  `hashes`/SHA-256 entry a validator could not reproduce), `Cargo.toml` +
  `Cargo.lock` (direct dependencies classified by default-feature
  reachability; the remaining lock closure — which Cargo cannot split into
  runtime vs dev — over-reported as scope `optional` with a marker property;
  exact lock versions and real SHA-256 checksums), and CMake
  `FetchContent_Declare` pins (URL-derived version, archive SHA-256; the
  test-only Catch2 declare allowlisted; any unparsed declare is a hard error
  via an occurrence-count cross-check). Every binding component carries an
  `aletheia:binding` property and the component list is sorted, keeping two
  `dist` runs of one commit byte-identical. The new
  `tools/check_sbom_coverage.py` gate re-runs the same parsers and fails the
  dist on any manifest-declared dependency missing from the SBOM (wired into
  the Shakefile dist rule right after SBOM generation), and runs always-on in
  `tools/run_ci.py` as `check-sbom-coverage --parse-only` against the repo
  manifests (a parser-rot tripwire — PR runners have no dist tree). The first
  tests for `sbom_generate` land alongside: fixture-matrix coverage in both
  directions per parser, a byte-determinism pin, and teeth tests proving
  every coverage-gate failure mode exits non-zero.
- **Always-on release bundle-staging gate** (`tools/check_dist_staging.py`,
  run_ci step `check-dist-staging`, also in the pre-commit FAST tier). The
  inputs `cabal run shake -- dist` stages — the `stageBinding` pathspec lists
  in `Shakefile.hs`, the `packaging/` consumer entry scripts, `LICENSE.md` —
  used to be exercised only at release time, so a renamed path or an
  untracked script surfaced when a tag was cut. The gate re-checks them on
  every CI run: each positive pathspec must match a tracked file (moving the
  `git archive` release failure to PR time), each `:(exclude)` glob's inner
  pattern must also match (new coverage — `git archive` passes silently over
  a dead exclude, so the Go test files would silently ship if they moved),
  `go/go.work` must stay unselected by the go binding's pathspecs
  (front-running dist's packed-output check), and the packaging scripts must
  be tracked and syntax-clean (`bash -n` / `fish --no-execute`; a CI runner
  without fish fails closed rather than skipping — pr-full-ci.yml now
  installs fish). Fails closed on a Shakefile parse it cannot fully trust;
  regression tests prove every failure mode fails.
- **Cross-binding wire-code SSOT + kernel parity gate** (`docs/WIRE_CODES.yaml`
  + `tools/check_wire_codes.py`, run_ci step `check-wire-codes`). The kernel's
  two wire vocabularies — the validation issue codes (`formatIssueCode`)
  and the error codes (the per-ADT `*ErrorCode` formatter families plus
  the top-level `errorCode`) — are now
  pinned to one reviewed YAML manifest: the gate parses the Agda formatter
  arms and asserts reciprocal set equality plus kernel declaration order, so a
  new kernel code cannot reach the wire without its SSOT row (every binding
  deliberately passes unknown codes through at runtime, so no test failed on
  one before; previously only Python's `ErrorCode` was gated — one vocabulary,
  one binding). The Python `IssueCode`/`ErrorCode` enums are anchored to the
  YAML by `python/tests/test_wire_codes_parity.py`, which supersedes the
  Agda-parsing `test_error_code_sync.py` (removed). Fails closed on a missing
  or malformed YAML; regression tests prove every failure mode fails. The
  other bindings are anchored by the same-shaped parity tests
  `go/aletheia/wire_codes_parity_test.go` (reciprocal set equality against
  the `Issue*`/`Code*` constants), `cpp/tests/test_wire_codes_parity.cpp`
  (bijection with the `IssueCode`/`ErrorCode` enums — every kernel code maps
  to a non-`Unknown` enumerator and vice versa), and `rust/tests/wire_codes.rs`
  (every issue code decodes to a named `IssueCode` variant; error codes —
  Rust has no `ErrorCode` enum by design — are driven through the client
  decode path and must surface verbatim in `Error::Core`, with the
  typed lifts pinned to SSOT membership).
- **Runtime-closure snapshot gate** (`tools/check_runtime_closure.py`, wired
  into `run_ci`). The foreign library's module list is auto-generated from the
  Agda import graph, so a dependency drag — one new import transitively pulling
  proof modules into the compiled `.so` — used to land silently, visible only
  to a human reading the generated cabal diff (name-based checks cannot catch
  proof modules that don't carry `Properties` in their names). The gate pins
  the closure to a reviewed snapshot (`haskell-shim/runtime-closure.snapshot`):
  any growth or shrinkage fails with the exact module lists (proof-shaped
  additions called out first) until the snapshot is consciously regenerated in
  the same change. Fails closed on a missing snapshot and refuses to pass
  vacuously on unreadable input; regression tests prove every failure mode
  fails.

### Changed

- **The binary extraction wire now carries the kernel's detailed error reason
  for every extraction error (BREAKING on the binary wire).** The
  `aletheia_extract_signals_bin` response previously encoded each error as a
  bare `u8` code, so every binding surfaced a generic per-code string
  (`"Value out of bounds"`) while the JSON path surfaced the kernel's detailed
  reason (`"value out of bounds: 16383.75 not in [0, 8000]"`). The wire now
  transports the reason string itself: the header gains a `u32 reasonBytes`
  field, and a cumulative offsets table (`(nErrors+1) × u32`, Arrow-style)
  plus a UTF-8 reason blob sit between the errors and absent segments — every
  segment start stays O(1) arithmetic from the header, and reason *i* is an
  O(1) slice. The reason strings are the kernel's own: both extraction
  categorizers now derive their error text from one shared formatter, so the
  binary and JSON paths agree byte-for-byte — machine-checked
  (`reason-parity` in `Aletheia.CAN.Batch.Properties.ReasonParity`). The `u8`
  code space expands from 4 to 8 so every distinguishable kernel error owns a
  distinct code (mux-chain and bit-extraction failures no longer collapse
  into one catch-all; collision-freedom is machine-checked,
  `extractionErrorCodeToℕ-injective`). All four bindings decode the new
  layout, surface the wire reason verbatim, and drop their generic per-code
  message tables; decoders verify the offsets invariants (zero start,
  monotone, endpoint match) and reject invalid UTF-8. The FFI shim's
  over-range reroute now attaches the kernel-minted `wireRangeReason` string
  and fails loudly (never truncates) if a reason blob could exceed the `u32`
  offset space. Success-path (error-free frame) extraction cost measured
  within the WSL2 variance band against the pre-change baselines in all four
  bindings — the Python and Go decoders take a zero-error fast path that
  collapses the offsets-table validation to a single read.
- **Rust: `Client::extract_signals` now uses the binary FFI fast path (~3.7×
  faster) instead of parsing a JSON DOM per call.** Once a DBC is parsed the
  client caches each message's ordered signal names and decodes the packed
  binary extraction buffer directly (values keyed by signal index), matching the
  Go/Python/C++ hot path; the JSON path remains the fallback when no DBC name
  cache is present or the backend has no binary FFI. Measured on this host:
  CAN 2.0B Signal Extraction 10.2 → 2.7 µs/frame, CAN-FD 137.5 → 37.8 µs/frame
  (Stream LTL / Frame Building unchanged). Additive, non-breaking API: a new
  default `Backend::extract_signals_bin` trait method (returns the new sentinel
  `Error::BinaryPathUnsupported`, so existing `Backend` impls and `MockBackend`
  keep working via the JSON fallback).
- **The loaded kernel's GHC runtime now runs under a default heap cap in every
  binding (Python, C++, Go, Rust), not just Python.** The runtime has no heap
  limit by default, so a runaway allocation in kernel code exhausted host memory
  and the OS OOM killer took the whole machine down; only Python previously
  passed a cap. All four bindings now start the runtime through
  `hs_init_with_rtsopts` with a `-M3G` default cap. The cap is
  **containment-by-abort**, not a recoverable error: when a computation exceeds
  it the process terminates with a diagnostic (a GHC heap-exhaustion abort) so
  the host survives — there is no catchable error and no partial result. The cap
  is a fixed containment bound with measured headroom (far above the heaviest
  observed kernel working set, far below any host's RAM), overridable per
  process with `ALETHEIA_RTS_OPTS` (its flags win, being applied last). The
  runtime RTS parameters are pinned by a new cross-binding SSOT
  (`docs/RESOURCE_BUDGETS.yaml`) and a `check-rts-runtime` parity gate, with the
  method and rationale in `docs/development/RESOURCE_PARAMETERS.md`.
- CI workflows run on `actions/setup-go` and `actions/setup-python` v7
  (folding in Dependabot's individual bumps, which cannot carry the
  CHANGELOG entry the workflow-path gate requires).
- **Every rational component on the JSON wire is now bounded to the Int64
  range (BREAKING on the JSON wire).** The kernel previously accepted bare
  JSON integers of unbounded magnitude in rational positions, while the
  decimal SSOT and the binary wire's rational slots both enforce the signed
  64-bit range — an asymmetry that let a component the wire cannot represent
  enter through the integer channel. A post-parse measurement of the JSON
  tree now refuses any number whose reduced numerator or denominator exceeds
  the bound, with the typed `input_bound_exceeded` envelope carrying the
  structured `bound_kind` / `observed` / `limit` triple (new bound kind:
  `rational_component_magnitude`, mirrored in the Python and Go limits
  surfaces and their parity gate). Callers that relied on out-of-range
  integers being accepted — an accidental capability, observed only as
  divergence between the Python YAML loader and the other bindings — now get
  a truthful refusal, and the YAML loaders of all four bindings converge.
- **The CI sweep streams live per-step progress.** `tools/run_ci.py`
  previously collected every lane's results before printing anything, so
  after the banner the terminal stayed silent until the whole sweep finished
  and the per-step lines arrived in one burst. The scheduler now exposes a
  progress seam observing each step the moment it starts and finishes, and
  the runner streams those events to stderr immediately — a start line when
  a step begins and its ✓/✗ line with duration the moment it completes —
  while the log file keeps its deterministic lane-then-step record
  unchanged (the per-step headers now live in the log only — teeing them to
  the terminal too left the report a burst of content-free header lines).
  Gate output lines also flush per line at the shared `emit`
  chokepoint, so nothing sits in a pipe buffer under the pre-push hook.
  Verified live through a pipe: lines arrive spread across the run rather
  than at exit.
- **Out-of-range signal geometry is refused at entry with typed errors
  (BREAKING on the JSON wire).** Both parse routes previously normalized
  silently — start bits and bit lengths were mod-reduced into range at the
  boundary (a submitted start bit one past the ceiling became zero, with no
  issue reported), and big-endian signals could be relocated by the
  conversion's floor — so `format_dbc_text`'s guarantee was measured against
  values the caller never sent, and the error class of the refusals that did
  fire depended on where the reduction landed. The kernel now refuses: a new
  shared geometry decider family (one `Dec` form per condition, parameterized
  by the containing message's frame capacity — the DLC already distinguishes
  classic CAN from CAN-FD, so the bound is the frame's, not a global
  constant) gates BOTH routes, emitting new typed error codes that name the
  submitted values (`parse_signal_start_bit_exceeds_frame`,
  `parse_signal_bit_length_exceeds_frame`, `parse_signal_big_endian_overflow`,
  and `parse_non_natural_field` for present-but-non-natural numeric fields,
  previously misreported as missing). The big-endian no-wrap check is
  re-aimed at the pre-conversion MSB position — textbook Motorola layouts the
  JSON route falsely refused now load on both routes, restoring the kernel's
  closure under its own emission (a text-loadable DBC's emitted JSON is
  always re-ingestible; regression-tested). The validator's geometry arms now
  consume the same deciders (a machine-checked theorem proves gate acceptance
  implies those arms are empty — deadness is proven, not observed), and every
  binding's response decoder accepts full-frame CAN-FD signal lengths (the
  old classic-CAN cap crashed decoding the kernel's own success response).
  The retired clamp-identity lemmas leave the proof tree; the previously
  surplus round-trip hypotheses are now genuinely consumed by the re-aimed
  gate.
- **The structural validator now names the round-trip-fatal mux shapes.**
  `validate_dbc` and the DBC-loading routes emit warning-class issues for the
  shapes that load cleanly yet cannot survive the text round-trip:
  `multi_value_mux_selector` (a signal multiplexed on more than one selector
  value) and `mux_master_incoherent` (no single Always master, or a selector
  naming a different master — nested-mux chains included). The validator
  reuses the text-round-trip checker's own deciders, so the diagnostics are
  byte-identical to those `format_dbc_text` attaches to its refusal — closing
  the blind spot the tightness classification proved (previously the
  formatter's refusal was the only surface naming these shapes). Warnings
  never block a load: `has_errors` stays false and such DBCs load and stream
  as before. The wire vocabulary is unchanged — the codes already existed and
  every binding already decodes them.
- **The round-trip diagnostics carry a proven tightness classification.** The
  `wfTextIssues` checker's module header now records, for every
  diagnostic-bearing well-formedness condition, whether a flag always means a
  genuine text-form loss (round-trip-necessary: the presence, master-coherence,
  attribute, and unresolved-value-description conditions) or can false-alarm
  (merely-bundled: the uniqueness conditions, whose flags ride along on
  DBCs that provably round-trip — they exist for the first-match collapse of
  id-keyed re-attachment, which only divergent payloads trigger), or can never
  fire on a public route at all (the signal-geometry bounds, made invariant by
  the parse routes' entry clamps) — each verdict backed by a proof trace and a
  kernel-verified witness. The `format_dbc_text` documentation in every
  binding now states the guarantee's exact level: the emitted text re-parses
  to the input at the text-parser level, while a DBC carrying load-error-class
  duplicates round-trips in the proof but is refused by the validating load
  route. Comment/documentation only — no library or runtime behavior change.
- **Rust: `IssueCode` and `Error` are now `#[non_exhaustive]` (BREAKING — Rust
  only).** Both enums mirror vocabularies minted by the kernel, which grow with
  kernel features (the issue-code vocabulary has grown release over
  release), so the
  attribute states what was already true: the authoritative list lives
  upstream, and downstream matches must carry a `_` arm. Future code and
  variant additions thereby stop being breaking changes. Runtime behavior is
  unchanged — unknown wire codes still arrive as `IssueCode::Unknown(String)`
  (a code moves from `Unknown` to a named variant when the crate learns it, so
  logic that must be stable across crate upgrades should key on
  `IssueCode::as_str`, as the enum's documentation now explains). The
  deliberately closed enums (`IssueSeverity`, `Verdict`, the LTL AST) remain
  exhaustive.
- Internal proof-hygiene refactor — wire behavior unchanged. The Bool-valued
  leaves of the `format_dbc_text` well-formedness checker are reified into
  stock `Dec` deciders consumed through the shared `requireDec` combinator, so
  the hand-written Bool-to-predicate pairing lemmas (including the whole
  `Sound/Master` proof module) are deleted; and the attribute-definition
  lookup is single-sourced in a new `Aletheia.DBC.AttrLookup` module shared by
  the text formatter and text parser (previously two identical per-side
  clones, plus a bridging lemma proving them equal — also deleted).
- Internal — no library or runtime behavior change; the one tooling-behavior
  change is that the memory-citation checker becomes strictly stricter (its
  backlog-doc exemption is removed, so the renamed design plan is scanned like
  any other doc). The DBC text round-trip proof documentation now
  lives in the source: the `WellFormedFromValidity` module header explains why
  DBC validity cannot imply the round-trip predicate (text emission is lossy on
  constructs the validator accepts) and why no guarantee depends on that
  implication (the predicate is runtime-decidable, sound and complete, and
  `format_dbc_text`'s guarantee routes through the hypothesis-free exact
  re-parse check). The retired proof-strategy notes were removed alongside; the
  surviving extended-mux design plan carries a content-based name
  (`EXTENDED_MUX_DESIGN.md`), which is what enables the exemption removal above.

### Removed

- Wire codes retired by the geometry entry gate (per the WIRE_CODES removal
  protocol; every binding's vocabulary and the completeness gates updated in
  lockstep): the error codes `parse_signal_overflows_frame` and
  `parse_signal_msb_below_bit_length` (superseded by the frame-capacity and
  pre-conversion no-wrap refusals above) and the issue code
  `big_endian_msb_layout` (its validator arm checked the post-conversion
  value — the condition the re-aim corrected — and no longer exists).

### Fixed

- **Native packages (`.deb`/`.rpm`): the bundled Python binding is now consumed
  in place via `PYTHONPATH`, not `pip install /opt/aletheia/bindings/python`.**
  The package installs the pure-Python binding read-only under `/opt`, but
  `pip install <dir>` builds a wheel *in that source directory* (setuptools
  `egg_info`), so a non-root user's install failed with `Permission denied`. The
  bundle's `install.sh` / `install.fish` and `DISTRIBUTION.md` now lead with
  putting `<bundle>/bindings/python` on `PYTHONPATH` (prepended, preserving any
  existing value) — the cross-binding-consistent in-place recipe (the C++/Go/Rust
  bindings are likewise consumed from `bindings/` in place), which works
  read-only — and the release `.deb` install-smoke exercises that same recipe
  rather than a hardcoded `pip install`.
  The pip path stays documented for a writable source (an unpacked tarball, or a
  copy, e.g. inside a venv).
- **CI: the heavy-lanes workflow (mutation / reproducible-build / stability) no
  longer re-bootstraps the cabal package index on every run.** It restored the
  cabal store cache but still ran `cabal update` unconditionally *before* the
  restore, so each run performed a fresh hackage-security (TUF) `root.json`
  bootstrap — which fails whenever Hackage's root metadata is transiently
  unverifiable even though the primary is up (the `pr-full-ci.yml` lane, which
  runs `cabal update` only on a cache miss, was unaffected). The heavy lanes now
  restore the cache first and update only on a miss, matching that proven
  pattern; on the normal cache-hit path they skip `cabal update` entirely.
- **The Go, C++, and Rust bindings no longer crash at startup when `GHCRTS` is
  set to a non-safe RTS option.** Those bindings initialised the runtime through
  the plain `hs_init`, which — because the shared library is linked with GHC's
  default `RtsOptsSafeOnly` — aborts immediately ("Most RTS options are
  disabled. Use hs_init_with_rtsopts() to enable them.") whenever the
  environment's `GHCRTS` carries any non-safe flag (for example a `-M` heap cap
  or a profiling flag). Switching all three to `hs_init_with_rtsopts` (which
  Python already used) removes the crash and, as a side effect, is what lets
  every binding carry the new default heap cap. The Python binding was
  unaffected.
- **Long-running stream monitoring no longer grows unbounded in memory, and is
  now faster than before.** A monitored stream retained every accepted
  frame behind the signal cache's unevaluated thunks, so residency climbed by
  roughly a kibibyte per frame until the process exhausted the GHC heap and
  aborted — a monitor could not run indefinitely. The streaming step now
  evaluates the signal cache it derives per frame, which bounds residency in
  practice (a regression test asserts a flat plateau over millions of frames), and it
  derives each frame's signal values in a single shared pass consumed by both
  the property evaluation and the cache, replacing the previous two
  independent extraction passes. Net effect on the verified core's streaming
  throughput, measured against the pre-change build: comfortably faster
  (CAN-FD Stream-LTL and classic-CAN Stream-LTL both improved), with residency
  now bounded. The optimization is machine-checked: a new
  verdict-preservation theorem proves the per-frame result is unchanged, and
  the LTL adequacy proofs are untouched.
- **The freshness gate no longer reports a fresh install stale after the
  build-staleness probes relink the kernel.** GHC recompilation is not
  symbol-deterministic, so the staleness gate's edit/revert probes can mint
  a new GNU build-id for a library linked from identical inputs — and the
  freshness gate, comparing build-ids, then failed the pre-push sweep on a
  correctly installed kernel. The staleness gate now records its own proof
  (baseline and post-probe build-ids, chained across consecutive probe
  cycles) in a certificate under `build/`, and the freshness gate accepts
  exactly that certified pair; a real rebuild mints an id the certificate
  does not name, so true rot still fails.
- **Binary extract responses no longer wrap out-of-range values silently.**
  A signal whose exact physical value passed the kernel's own bounds check
  could come back from `extract_signals` as a wrong value with an empty
  error list in every binding: the response encoder poked unbounded
  integers into the Int64 wire slots and the numerator wrapped. Such
  signals now surface as a typed per-signal error entry (see the encoder
  guard under Added); violation enrichment was verified to route through
  the same guarded wire.
- **Excel loaders no longer trust display formatting or prefix parsing for
  numeric cells (Go, C++).** A native number cell storing a fractional
  Message ID under an integer display format loaded as the DISPLAYED id in
  Go (silent wrong message), and C++ accepted dot-free scientific notation
  and empty stored values as valid ids via prefix parsing. Both loaders now
  require the RAW stored value to be exactly integral — Python's reference
  semantics — refusing anything else truthfully; the Go boolean column
  applies the same raw-value discipline. Kernel decimal refusals in both
  loaders now carry the row/field context their sibling diagnostics already
  had, and rejection messages echo the raw stored value
  (shortest-round-trip rendering in C++) instead of a truncated or
  display-formatted one. Rust's Excel loader already reads raw stored
  values and needed no change.
- **Python timestamp ingestion refuses values past the unsigned 64-bit wire
  ceiling.** A large-enough microsecond timestamp silently wrapped at the
  FFI boundary (reachable from a malformed candump line), surfacing only as
  a confusing monotonicity error; all three streaming entry points now
  refuse it with the same `ValidationError` the negative check raises, and
  `iter_can_log` treats every non-finite timestamp uniformly (NaN and
  infinities are skipped in skip mode and raise the documented error class
  otherwise — infinities previously crashed both modes).
- **Python's YAML check loader accepts explicitly `!!float`-tagged scalars
  exactly.** It was the only binding refusing a tagged, losslessly
  representable float that Go, C++, and Rust load exactly — and its
  refusal leaked Excel wording into a YAML context. Finite tagged floats
  now convert to the double's exact rational value; non-finite ones are
  refused with YAML-appropriate wording.
- The `iwyu` import gate no longer crashes when a branch deletes an `.agda`
  module: the per-push scope collector excludes deleted paths
  (`--diff-filter=d`) — a deleted module has no imports left to analyze, and
  its changed importers enter the scope on their own. Regression-tested.

## [4.0.0] — 2026-07-17

### Added

- **Self-contained multi-binding release bundle.** `shake dist` now stages all
  four language wrappers into the tarball (`bindings/{python,cpp,go,rust}` — each
  binding's library files only, via `git archive` from `HEAD`: tracked files, no
  tests/benchmarks, no `go.work`) alongside the verified `libaletheia-ffi.so` and C
  header, plus `env.sh`/`env.fish` (source to export an absolute `ALETHEIA_LIB`) and
  `install.sh`/`install.fish` (print the shell + per-language wiring steps without
  editing any rc file). A consumer unpacks the tarball, sources `env.sh`, and uses
  Aletheia from Python, C++, Go, or Rust with no Agda/GHC toolchain. The tarball
  also carries the project `LICENSE`; the bundled Python wrapper requires Python
  3.14+ and its install notes cover PEP 668 (externally-managed environments). A
  `dist` self-check fails the build if a binding is dropped or `go.work` leaks, and the
  release workflow gains a functional smoke test (unpack → source `env.sh` from a
  foreign directory → load the `.so` from the bundled Python package) that gates
  publish. The C++ `CMakeLists.txt` gains a namespaced `aletheia::aletheia-cpp`
  alias so vendored `add_subdirectory` consumers and installed `find_package`
  consumers use one target name. See `docs/development/DISTRIBUTION.md`.

- **`ALETHEIA_LIB` env-based library location for the Go and C++ bindings.** New
  `NewFFIBackendFromEnv()` (Go) and `make_ffi_backend_from_env()` (C++) load
  `libaletheia-ffi.so` from the path named by the `ALETHEIA_LIB` environment
  variable, mirroring the Python and Rust bindings — so all four bindings can be
  pointed at a shared library by the environment alone (the zero-config path for a
  bundled install). An unset or empty `ALETHEIA_LIB` yields a typed validation
  error; the explicit-path constructors (`NewFFIBackend(path)` /
  `make_ffi_backend(path)`) are unchanged.

- **Keyless-signed GitHub Release automation** (`.github/workflows/release.yml`).
  Pushing a `v*` tag builds the reproducible distribution tarball via `shake dist`,
  signs it, self-verifies the signature, and publishes a draft GitHub Release.
  Signing is **keyless** (Sigstore): cosign mints an ephemeral key from the
  workflow's GitHub Actions OIDC identity, so no signing key or passphrase ever
  lives in CI — consumers verify against the workflow identity (`cosign verify-blob
  --certificate … --certificate-identity-regexp …`) rather than a public key.
  Publishing is gated on the self-verify step, so an unverifiable artifact is never
  released. `shake dist` gains a keyless signing mode (`ALETHEIA_COSIGN_KEYLESS=1`,
  emitting a `.crt` certificate alongside the `.sig`); the maintainer's local cosign
  key remains the fallback for releases cut off CI, and the embedded `MANIFEST.txt`
  carries the exact verify command matching how each tarball was signed. See
  `docs/development/RELEASE.md`.

- **Agent-memory-citation gate** (`tools/check_no_memory_citations.py`, wired into
  `run_ci` and the pre-commit fast tier). The agent-memory store (`feedback_*.md`,
  `project_*.md`, `[[wikilink]]` notes) lives outside the repository, so a pointer
  to it in a tracked file resolves for nobody who cloned the repo. This gate fails
  when such a pointer — a `[[slug]]` wikilink, a `memory/<name>.md` path, or a
  `<slug>.md` note filename — appears in any tracked file expected to read as a
  product: source of every binding language AND the user-facing docs (product
  Markdown, the CHANGELOG, PROJECT_STATUS). Exempt are the AI-process-infra docs
  whose purpose includes citing the store (`CLAUDE.md`, `AGENTS.md`,
  `DEFERRED_ITEMS.md`) and the `E2_*` proof-strategy backlog docs. It complements
  `check_docs` (Markdown links) and `check_no_review_marks` (review-process marks),
  and on its first run caught eleven pointers earlier strips had missed (source
  `.yaml`/`.gitignore` plus product docs). Catches only these unambiguous
  structured shapes, not bare prose.

- Python's public `IssueCode` enum (`aletheia.codes.IssueCode`) gains the eight
  text-round-trip diagnostic codes (`text_roundtrip_divergence`,
  `multi_value_mux_selector`, `mux_master_incoherent`, `big_endian_msb_layout`,
  `unknown_attribute_name`, `attribute_value_type_mismatch`, `attribute_enum_empty`,
  `attribute_enum_default_unstable`) — parity with the Go / C++ / Rust bindings,
  which already exposed them as typed members (E.2 review follow-up).
- **Verified runtime checker for DBC-text round-trip well-formedness** (internal;
  first slice of the E.2 route (b) work — no user-facing change yet). New Agda
  modules add `wfTextIssues : DBC → List ValidationIssue`, a decision procedure
  proven **sound and complete** against `WellFormedTextDBCAgg` (`wfTextIssues d ≡
  [] ⟺ WellFormedTextDBCAgg d`), so a future `format_dbc_text` can report at least
  one reason a DBC falls outside the *proven* round-trip envelope, instead of
  silently emitting lossy output. (`WellFormedTextDBCAgg` is sufficient-not-necessary
  for round-tripping, so a non-empty result means "round-trip not proven", never
  "will not round-trip".) Eight new `IssueCode` constructors (with `formatIssueCode`
  wire arms) carry the per-field diagnostics. The soundness facade is wired into
  the `check-properties` proof gate as a walk root (`Shakefile.hs`); the
  wire/envelope/handler surfacing and the exact-equality verdict land in later
  slices.
- **Verified exact round-trip check + V1↔V2 coherence** (internal; second slice of
  the E.2 route (b) work — still no user-facing change). Adds `roundTripsᵇ : DBC →
  Bool`, a decision procedure that *evaluates* `parseText (formatText d)` and
  deep-compares the parse-back with `d` (via a new full `DBC` decidable-equality
  tower), giving the exact round-trip verdict with zero over-refusal. Its soundness
  is **axiom-free** — `roundTripsᵇ d ≡ true → parseText (formatText d) ≡ inj₂ d`, so
  V2's YES is ground truth by construction — and it composes with slice 1's checker
  into the coherence theorem `wfTextIssues d ≡ [] → roundTripsᵇ d ≡ true` (no V1
  diagnostic ⟹ the DBC round-trips, carrying the same trust base as the headline
  round-trip theorem). Proof-only; the handler/wire surfacing lands in the final
  slice. Wired into the `check-properties` gate (`Shakefile.hs`).
- **Pre-commit hook now blocks non-conforming commits in seconds** (dev-workflow
  change). `tools/run_ci.py` gains a `--fast` tier that runs only the compile-free
  static gates — per-binding format checks (`clang-format`, `gofmt`, `cargo fmt`,
  `ruff format`), SPDX / review-mark / venv hygiene, and the Python linters (`ruff`,
  `pylint`) — and the pre-commit hook runs it against the **staged content**
  (unstaged/untracked changes are stashed for the duration, then restored) and
  refuses the commit on failure. Compiling/artifact-dependent gates (clang-tidy,
  clippy, cargo test, pytest) stay at pre-push, which still runs the full sweep.
  Re-install with `python -m tools.install_hooks`; bypass with
  `git commit --no-verify`. Internal: the `gofmt + go vet` and `cargo fmt + clippy`
  steps were split into separate format/lint steps so the fast tier's allowlist
  (`FAST_STEPS`) can include the format check without pulling in the compile.

### Changed

- **Provenance PR-numbers removed from the workflow docs** (internal — no
  behavior change; docs only). `BRANCH_PR_HYGIENE.md` and `BUILDING.md` cited
  specific PR numbers as historical provenance, which mean nothing to a reader
  without access to this project's tracking; the sentences now state the fact
  without the number. The proof-strategy backlog docs keep their internal IDs by
  design; `DEFERRED_ITEMS.md` records that those files are to be deleted once the
  proof they track lands.
- **Source comments now describe what the code guarantees, not how it got there**
  (internal — no behavior change; comments only, no code was modified). Several
  comments stated things that were no longer true and that a reader would have
  acted on: the DBC-text handler described its well-formedness diagnostics as
  flagging shapes "known to diverge", when a non-empty diagnostic list means only
  "outside the proven envelope" — such a DBC may still round-trip, and its text is
  emitted with those diagnostics attached; the same header stated the universal
  round-trip theorem without its well-formedness hypothesis, which is not a
  theorem this codebase has; an error constructor's arity and emitted field set
  had drifted; and a count of issue codes and of bindings had both rotted. The
  plan-tracking labels, dated status notes, git SHAs and superseded-design stories
  are gone. Cross-file line-number citations became symbolic references — one had
  already rotted past the definition it named. No source file points into the
  agent-memory store any more: those paths lie outside the repository and resolve
  for nobody reading a checkout.
- **`format_dbc_text` is now always-strict and returns structured text + issues
  (BREAKING — all four bindings).** Completes the E.2 route (b) work (the two
  internal verified-checker slices under _Added_ above). `format_dbc_text(dbc)`
  now returns the `.dbc` text together with a warning-severity `issues` list
  **only** when that text provably re-parses to the input DBC; a DBC that cannot
  be expressed as round-tripping `.dbc` text — e.g. a signal multiplexed on
  multiple selector values, which the JSON model admits but the `.dbc` grammar
  cannot encode — is **refused** with a typed round-trip error carrying the
  diverging issues, instead of emitting silently-lossy text. There is no `strict`
  flag: a flag would imply you might sometimes want non-round-tripping text, which
  contradicts the command's purpose. The emitted-text guarantee is machine-checked
  (`formatDBCTextResult-sound`).
  - **Wire**: the `formatDBCText` success response gains an `issues` field
    (`{status, text, issues}`); a non-round-tripping DBC returns the new
    `handler_text_roundtrip_failed` error code with an `issues` array led by the
    error-severity `text_roundtrip_divergence`. The eight new round-trip
    `IssueCode`s are documented in `docs/architecture/PROTOCOL.md` § FormatDBCText.
  - **Bindings** (return type changed in place — no `strict` parameter, no sibling
    methods): Python returns a `DBCTextResponse` and raises
    `TextRoundTripFailedError` on refusal; Go `FormatDBCText` returns
    `(*DBCText, error)` with a typed `*TextRoundTripFailedError`; C++
    `format_dbc_text` returns `Result<DbcText>`, refusal surfacing on
    `AletheiaError` as `ErrorKind::TextRoundtrip` /
    `ErrorCode::HandlerTextRoundtripFailed`; Rust `format_dbc_text` returns
    `Result<DbcText, Error>` with `Error::TextRoundtripFailed`. Rust additionally
    migrated its `format_dbc_text` / `parse_dbc_text` / `parse_dbc` tuple returns
    to named structs (`DbcText`, `ParsedDbc`). New `FEATURE_MATRIX.yaml` row
    `dbc_text_roundtrip_check` + per-binding parity gates.
- Internal (no behavior change): removed the unused `.agda-reference/README.md`
  stub and moved its provenance (the Agda `Parser.y` source URL, the `v2.8.0` pin,
  and the `curl` re-fetch recipe) into the `tools/_agda_opens.py` module docstring
  that grounds in that grammar.
- Internal (no public API or behavior change): the DBC decision procedures —
  decidable equality and the disjointness / well-formedness deciders — now live in
  a new `Aletheia.DBC.Decidable.*` namespace, and `Aletheia.DBC.Properties.*` is
  reserved for the proofs about them. A build gate now enforces exactly that no
  `DBC.Properties.*` proof module is compiled into the runtime shared library
  (`libaletheia-ffi.so`), replacing a narrower interim import check; the
  `@0`-erased Format-DSL round-trip proofs remain in the closure by design.

### Fixed

- **The `iwyu` import gate no longer misses dead imports that elaboration
  mentions** (internal; no user-facing behaviour change). An import could be
  reported USED purely because Agda had baked its name into the module's
  elaborated terms — reducing an imported definition freezes its callees' names
  into the reducing module, and a `with` forces exactly that on its scrutinee —
  even though no source token ever went through the import, which is why the gate
  read a tree holding 20 dead imports as clean. Those references are fully
  qualified and resolve through the transitive import, so they keep no import
  alive; a name in the elaborated terms but not in the source now counts only when
  elaboration had to search the scope to find it (an instance) or when it is
  reached by module-copy delegation. Names with more than one resolution in scope
  (`[]`, which is both the list constructor and `Data.List.Base.InitLast`'s) are
  exempt: Agda's highlighting attributes a token to the single name it resolved
  to, so an overloaded name's occurrences scatter and the source becomes
  unreadable to the gate — there the elaborated terms are still trusted, which
  errs toward keeping an import. The 20 dead imports this uncovered are removed
  (7 modules); new `--self-test` fixtures pin both directions.
- **Build gates can no longer report success while checking nothing** (internal;
  no user-facing behaviour change). Several gates spelled "clean" as an empty
  result, which made "I found no violations" indistinguishable from "I could not
  look" — so a missing input or a matcher that lost its grip read as compliance:
  the action-pin and workflow-permissions gates certified the supply-chain policy
  with no workflows directory present, or with zero refs matched; the invariants
  gate discarded grep's exit code, so a failed scan of `src/` reported "no
  postulates"; the runtime-closure gate did the same, and now matches the module
  closure directly instead of shelling out to grep with a regex; the FFI-export
  gate accepted an emptied snapshot as "0 entries" verified; the clang-tidy
  coverage gate passed when it found no sources. Each now asserts its own input
  and fails loudly, with regression tests pinning both polarities.
- **The install-freshness gate no longer certifies a kernel it cannot verify.** A
  deployed library with no `build/` counterpart reported "nothing to compare (OK)"
  — precisely the unverifiable state the gate exists to catch. It now decides
  deployed-or-not from the deployed side alone: nothing deployed still passes,
  but a deployed artifact with no build to compare against is reported. The gate
  no longer depends on the build step failing first.
- **The pre-commit and pre-push hooks no longer allow the operation when their
  gates did not run.** Both returned success when the CI runner was missing,
  enforcing nothing while appearing to. They now refuse; `--no-verify` remains the
  deliberate, visible bypass.
- **C++ `format_dbc_text` now rejects a non-array `issues` field on a success
  response** (E.2 review follow-up). The decoder's success path iterated `issues`
  with no array check, so an object-typed `issues` was silently harvested from its
  values — diverging from Python / Go / Rust, which all raise a protocol error on a
  present-but-non-array `issues` (an absent `issues` still defaults to empty). Added
  the `is_array()` guard (mirroring `lift_validation_issues`) plus five decode-level
  tests for `parse_dbc_text_response` (C++ was the only binding without them).
- **File loaders no longer mislabel a stat *failure* as "file not found".** A
  transient `stat`/`lstat` failure (EACCES, ELOOP, ENAMETOOLONG, or EMFILE/EIO
  under heavily parallel load) was reported as a missing file by the C++ loader
  (`validate_loader_path` conflated any `std::error_code` with absence) and the
  Python Excel loader (`Path.exists()` swallows every `OSError` since Python
  3.12). Both now key on the errno: ENOENT/ENOTDIR still mean "not found", any
  other errno is surfaced as a distinct stat error — matching the Go and Rust
  loaders, which already distinguished them (`os.ErrNotExist` / raw `io::Error`).
  All four bindings gain a regression test (deterministic ENAMETOOLONG trigger).
  No change to the not-found or success paths.
- **Corrected the C++ Check-API usage example in the `check.hpp` header
  comment.** The shown `never_exceeds(PhysicalValue{220})` form did not compile:
  `PhysicalValue` wraps an exact `Rational`, which — by the float principle —
  has no single-argument constructor, so the brace-init had no matching
  `Rational` ctor. The comment now uses the idiomatic `PhysicalValue::of(220, 1)`
  factory. Documentation-only; no API or behaviour change.

- **DBC text round-trip guarantee: corrected every stale or wrong statement of
  its precondition (E.2 accuracy batch).** README cited the wrong predicate for
  the text round-trip theorem (`WellFormedDBC`, the JSON-side one, instead of
  `WellFormedTextDBCAgg`); all four bindings' `format_dbc_text` doc surfaces
  now state the round-trip qualifier uniformly and name its sense —
  "byte-identical for any text-round-trip well-formed DBC", with a pointer to
  the glossary (Rust previously lacked the qualifier entirely — parity drift);
  `docs/GLOSSARY.md` gains a "well-formed DBC" entry distinguishing
  validator-clean from text-round-trip well-formed;
  `docs/reference/INTERFACES.md` states the qualifier. Agda comment fixes
  (no code change): two CHECK 1 / CHECK 18 mislabels, a stale "(8 fields)"
  count, an over-broad "JSON always defaults `unresolvedValueDescs` to `[]`"
  claim, and the format handler's caller contract no longer claims
  `MessageWF`/`WFAttribute` "hold automatically" from identifier validity.
  Documentation-only; no behaviour change.

## [3.0.0] — 2026-07-09

### Fixed

- **`aletheia check` / `signals` / `validate --excel` now accept an
  Excel-authored DBC instead of failing with "`''` is not a valid DBC
  identifier".** The Excel schema has no transmitter column, so the loader
  built every message with an empty sender — not a legal DBC identifier, which
  the kernel's DBC text parser rejected, so *every* `--excel` command exited 2
  (the technician's Excel on-ramp was broken end-to-end). The loader now emits
  the reserved `Vector__XXX` "no transmitter assigned" placeholder (a valid
  identifier that legitimately repeats across messages, exactly as it marks an
  unassigned receiver on a signal line).
- **`aletheia check` now runs check files that use decimal thresholds
  (e.g. `max: 6553.5`) instead of dying with "GHC runtime not
  initialized".** A decimal check threshold is parsed exactly through the
  kernel's `from_decimal` SSOT, which is RTS-gated and never self-initialises
  the GHC runtime; `_cmd_check` used to load the check files before any
  client (and thus any backend) had brought the runtime up, so in a fresh
  process every decimal threshold aborted the command with exit 2 before a
  single frame streamed. `_cmd_check` now constructs the FFI backend first
  (bringing the RTS up) and injects it into the client, so decimal thresholds
  parse with the runtime already live; `default_checks` still flow through the
  client constructor. Integer thresholds were unaffected.
- **`aletheia check` now fails fast (exit 2) on a per-frame kernel error such
  as a non-monotonic timestamp, instead of dropping the errored frames and
  reporting "all checks passed".** The streaming check pipeline acted only on
  property-batch responses and silently discarded a per-frame error response
  (e.g. the kernel's `handler_non_monotonic_timestamp` rejection — its metric
  LTL operators require monotonic time), so a run over a trace with a clock
  reset or a multi-source merge reported a **false PASS**. Each frame response
  now goes through the same fail-fast path the batch `send_frames` API already
  uses, surfacing the kernel error and exiting 2 (operational error) per the
  CLI's documented 0/1/2 contract.
- **`cabal run shake -- install` completes for the first time since the
  target landed (2026-02-08).** Shake's `cmd` word-splits bare string
  arguments, so the site-packages query `python3 -c "import site; ..."`
  reached python as the lone word `import` and every install died there —
  after copying the libraries and pip-installing the package but before
  writing `_install_config.py`, leaving a partial install the loader
  silently ignores. The `-c` program is now passed as a list argument
  (Shake's no-split form).
- **The local mutation-testing gate no longer reuses a stale mutmut
  work-tree.** `tools/mutation_run.py` now erases `python/mutants/` before
  each `mutmut run`. mutmut invalidates its cached kill/survive verdicts on
  *source* changes but not *test* changes (test files live outside
  `source_paths`, so their content is not hashed), so a test edit — or files
  arriving via `git merge` / `checkout` / `pull` — could yield stale results
  (a merge that added a function together with its killing tests reported 20
  phantom survivors until the tree was cleared). CI was never affected — it
  checks out fresh and `mutants/` is gitignored and uncached — so this only
  brings *local* runs to the same fresh-tree semantics. Cost is ~11 s on the
  Python lane (warm reuse 29 s → clean 40 s), local only.


- **`aletheia validate` on a broken DBC now lists the issues instead of
  dying — the binding/CLI half of the first-touch fix, plus the CLI
  scenario harness that locks it.** All four bindings lift the
  `handler_validation_failed` envelope into a typed error carrying the
  full issue list, mirroring the `input_bound_exceeded` precedent exactly
  (well-formed payload → typed error; malformed/partial → degrade to the
  generic coded error): Python `DBCValidationFailedError`, Go
  `ValidationFailedError`, Rust `Error::ValidationFailed`, and C++ an
  optional `issues()` payload on `AletheiaError` beside `bound_info()`
  (`ValidationIssue` relocated to its own small header,
  `aletheia/validation_issue.hpp`, so `error.hpp` can name it without
  pulling the DBC vocabulary). All three CLIs' `validate` catch the typed
  error from their DBC-load step and render the same report as a
  `has_errors` validation result — "Validation FAILED" + the numbered
  issue list, warnings included — with exit code 1; other subcommands
  keep dying with the message (exit 2), as does a syntactically
  unparseable file. **Behavior change**: `validate --json` with
  `has_errors` now exits 1 in Go and C++ (previously 0 — the exit code
  now reflects the outcome in both output modes, per the CLIs' own
  documented 0/1/2 contract; Python already did this). New
  `validation_rejection_issues` FEATURE_MATRIX row (44 rows). And the
  session's structural lesson became a standing gate: a **cross-CLI
  scenario harness** (`docs/CLI_SCENARIOS.yaml` +
  `python/tests/test_cli_parity.py`) drives all three real CLI binaries
  as subprocesses over a shared fixture corpus (including new
  `python/tests/fixtures/dbc_broken/` files) and pins the exit-code
  contract and per-scenario output markers — the first-touch failure
  mode can no longer reappear silently in any CLI.

- **A rejected DBC parse now reports everything the kernel knows — the
  kernel half of the `aletheia validate` first-touch fix.** `validate` is
  the first command a user with a broken DBC runs, and it used to die with
  a flattened one-line error. Three kernel changes (all additive on the
  wire): (1) the `handler_validation_failed` error envelope now carries the
  **full structured issue list** — errors *and* warnings, in the same
  `{severity, code, detail}` element shape as the `validation` response,
  plus `has_errors` — via a new `errorExtras` case (previously the reject
  carried error-level issues only, silently dropping warnings, and
  flattened even those into the message string; the message itself is
  byte-identical to before). Both the JSON `parseDBC` and text
  `parseDBCText` handlers flow through the same constructor and inherit
  the fix. (2) `dbc_text_trailing_input`'s message is now user-facing —
  "parse failed at line N, column M: first unparseable statement" — instead
  of parser-internals phrasing ("trailing input after parse"); the
  structured `line`/`column` fields were already there. (3)
  `AttributeRefinementFailed` now pinpoints its failure: `refineAttribute`
  returns a typed cause (`UnknownAttrDef` vs `IllTypedValue`) instead of a
  bare `Maybe`, and the error names the offending attribute — the old
  message was an unhelpful disjunction ("references an unknown AttrDef or
  supplies a value outside the declared type" with no name). Proof impact:
  the four per-item inverse lemmas and the two list-level lemmas in
  `Properties/Aggregator/Refine.agda` restated from `≡ just` to `≡ inj₂`
  (bodies unchanged); `Universal.agda` and the universal round-trip
  proof adapt with zero edits; `check-properties` (55 modules) and all six
  Agda gates green. The binding/CLI half (typed validation errors in all
  four bindings; all three CLIs rendering the numbered issue list; the CLI
  scenario harness) follows in the next PR.

- **DRY + hygiene sweep across Go/C++/Rust — internal, with one
  realized silent drift fixed.** The drift: C++ `json_parse.cpp`'s
  hand-maintained `error_code_table` size had decayed — 59 declared vs 57
  real entries after an earlier entry removal — silently padding the array
  with two value-initialized `{"", ErrorCode::Unknown}` elements; lookups
  stayed correct only because `Unknown` is enumerator 0 (a `""` probe matched
  a phantom entry and returned exactly the fall-through value). All three
  string→enum lookup tables there now deduce their size via `std::to_array`,
  so an entry count can never drift again. DRY extractions, each
  behavior-preserving: C++ `parse_issue_entry` (the validate-response and
  parsed-DBC-warnings decoders shared two byte-identical 18-line entry
  blocks — which had even grown their `.code_raw` field in lockstep); the
  same duplication found and fixed in Go (`parseIssueArray`, `json.go` —
  Python and Rust already decode issues at a single shared site); Rust
  `Rational::le` (crate-private inherent method replacing byte-identical free
  `rational_le` fns in `check.rs` + `ltl.rs`; its doc records why
  `PartialOrd`/`Ord` are deliberately absent — the unreduced representation
  makes derived `Eq` structural, so a value-based `Ord` would break the
  `Ord`/`Eq` contract), `set_extended` (encode-side mirror of the existing
  decode helper `extended_flag`; replaces 7 copy-pasted emit sites in
  `dbc.rs`), and `select_diag_values` (the diag-signal filter shared by the
  streaming and end-of-stream enrichment paths in `lib.rs`). Go hygiene:
  `MockBackend`'s three binary send shims now pass `state` through like the
  other six shims (and like the C++ mock; the pointer is still discarded by
  `Process`), and `ExtractSignalsBin` gains the `runtime.KeepAlive(data)` its
  three sibling slice-passing cgo wrappers already had (convention
  consistency — cgo pins the slice for a synchronous call either way, so
  this was never a use-after-free).

- **Logging docs now acknowledge the Rust binding —
  docs only, no behavior change.** `PROTOCOL.md § Structured Logging` (the
  self-declared SSOT for the event taxonomy) and the `docs/LOG_EVENTS.yaml`
  header still described a three-binding world: "all three bindings"
  (Python/C++/Go), a pointer to `go/aletheia/ffi_backend.go` (no such file —
  the slog emit sites are `go/aletheia/client.go` + `go/aletheia/ffi.go`), and
  a pointer to `cpp/include/aletheia/log.hpp` "string constants" that have
  never existed (C++ event names are inline literals at the
  `cpp/src/client.cpp` emit sites; the string-constants module is Rust's
  `rust/src/log.rs`). Both surfaces now name all four bindings, the corrected
  per-binding definition sites, the fourth parity gate
  (`rust/tests/log_events.rs`), and the one scoped exception: Rust defines the
  full 16-event vocabulary but emits all of it except the three `cache.*`
  events (they instrument an extraction memo cache that binding does not
  implement — a perf layer, not part of the contract). The add-an-event recipe
  grew the missing Rust step (`events::*` constant + `events::ALL`, which the
  Rust gate pins to the YAML bijectively). `docs/FEATURE_MATRIX.yaml`: the
  rust `structured_logging` note states the `cache.*` subset explicitly
  (aligning it with the `violation_enrichment` note), and the
  `build_frame`/`update_frame` rust rows now document the `&DbcMessage`
  signature divergence as by-design (the typed `Dbc` is caller-owned in Rust,
  so the caller supplies the resolved message — idiom-permitted under the
  cross-language parity rule).

- **Comment-truth sweep across all four bindings + the CI workflow cache
  comments — internal, no behavior change.** Every flagged comment was
  re-verified against the current code before rewording (a finder-per-binding +
  adversarial-verifier pass; several review findings turned out already fixed
  and were left alone). Highlights: the three workflow build-tree-cache
  comments (`benchmark.yml` / `pr-full-ci.yml` / `pr-heavy-lanes.yml`) claimed
  `build/libaletheia-ffi.so` "symlinks into" `haskell-shim/dist-newstyle` — it
  is `cp`-copied out of it by the Shake rule; the cache matters because that
  tree is the cabal foreign-lib incremental state (the real symlink is
  `haskell-shim/MAlonzo → ../build/MAlonzo`). Go: `Client.mu` → the channel-token
  `lockCh`; the stale "(51 codes)" count and the "eight groups lists 7"
  mismatch in `error.go`; a bogus int64-overflow clause on `validateTimeBound`;
  `Client.process` → `processLocked`; `ValueDescs` → `ValueDescriptions` (+ the
  full shallow-copy aliasing set); the sealed-interface default-arm comments
  (no `sealedFormula`/`sealedPredicate` markers exist — sealing is the
  unexported `formula()`/`predicate()` methods, and the arms are reachable by
  degenerate values, not "unreachable"); `InputBoundExceededError` doc now
  names the consolidated top-level Agda constructor and all three peer
  bindings (including Rust's new `Error::InputBoundExceeded`). Python: the
  `dbc_to_json ∘ dbc_to_text` composition is via a file (not literally
  invocable, and dict-equal, not "byte-identical"); `can_log` docstrings now
  name the 7-field `CANFrameTuple` (brs/esi were missing); the Excel-loader
  docstring's DBC column table was missing the `Extended` column;
  `PropertyResultEntry` is the element type of BOTH mid-stream batches and
  end-of-stream results; `FractionJSONEncoder` cited a non-existent Agda
  function (→ `Protocol.JSON.Lookup.getRational`) and predates Rust; Go peer
  of `from_decimal` is `FromDecimal`, not `ParseDecimal`. C++: `ErrorCode`
  count/family list corrected count-free; `signal_index_`/`signal_names_` are
  rebuilt by `populate_signal_lookup()` on BOTH `parse_dbc()` and
  `parse_dbc_text()`; `last_frames_` is also cleared by `end_stream()`;
  `end_stream` enriches `Unresolved` too, not just `Fails`; the earlier
  "returned Violation" wording → the `PropertyBatch` Fails entry; the cache
  fallback logs a `cache.full` warning (not "silent"); `format_formula` /
  `build_diagnostic` are NOT "always succeeds" — they render thresholds via the
  kernel renderer and throw `AletheiaException(Ffi)` when the library/RTS is
  unavailable (the C++ instance of the cross-binding stale claim); the
  `__int128` comment and `static_assert` diagnostic string (the one
  behaviorally-inert non-comment hunk) no longer name the dropped
  "g++ >= 14 / clang >= 21" toolchain — Clang-only per `cpp/CMakeLists.txt`.
  Rust: the `async_client` module/field/test comments claimed std
  `mpsc::Sender` is `!Sync` (it is `Sync` for a `Send` payload since Rust
  1.72 — the `Mutex` exists for the `Drop`-takeable `Option` slot, not for
  `Sync`ness); the module also uses `futures-util` stream combinators, not
  "only the reply oneshot"; `build_diagnostic`'s `# Errors` now lists
  `RtsNotInitialized` (checked before any dlopen) alongside library-load
  failure; the "render failure is unreachable because extraction loaded the
  library" justification (wrong since the DI seam — an injected backend
  extracts without the `.so`) → the truthful setup-time-render latch argument,
  fixed at both `enrich.rs` and its `lib.rs` twin.
- **`aletheia_parse_decimal` error envelope is now valid JSON for non-ASCII input
  (all bindings).** The Haskell shim built the error envelope's echoed `input`
  (and `message`) field with `show`, which emits a `\NNN` *decimal* escape for a
  non-ASCII or control character — invalid JSON (JSON requires `\uXXXX`). So
  `from_decimal` on a non-ASCII literal (e.g. `"1.5€"`) produced an envelope the
  bindings' decoders could not parse, surfacing a confusing `Protocol`
  "malformed response" error instead of the correct `Validation` "invalid decimal
  literal". `Marshal.hs` now encodes string fields with a proper JSON encoder
  (`jsonString`: escapes the mandatory characters and `\u`-escapes everything
  outside printable ASCII, with surrogate pairs for astral code points). Fixes
  every binding at the shared FFI source of truth; regression-tested per binding.
- **Validation / range error messages render rationals exactly, not a lossy float
  (Go / Rust).** Go's `between: min (…) exceeds max (…)` and `negative tolerance:
  …` errors (`json.go`) rendered the threshold via `%g` — rounding a value beyond
  six significant figures and printing `1/3` as `0.333333`. They now render via a
  new `formatRationalExact` helper: the kernel `format_rational` when the GHC RTS
  is up, else an exact `num/den` fallback (predicate validation can run before any
  backend exists), never lossy. Rust's inverted-range errors (`check.rs`
  `rat_str`) were already exact but printed a bare fraction (`1/2`); they now
  route through `format_rational` too (decimal `0.5` when the RTS is up, the
  fraction as the RTS-down fallback), matching `enrich.rs` and the other bindings.
  This completes the "render rationals exactly in user-facing output" sweep (PR #134
  `extract --json`, PR #135 CLI text).
  (`go/aletheia/json.go`, `rust/src/check.rs`.)

- **CLI human-readable text renders rationals exactly, not a lossy `%g` /
  `to_double` (Go / C++ / Python).** The `extract` and `signals` commands printed
  each signal value, factor, and offset through a lossy float (`%g` in Go/Python,
  `to_double()` in C++), so a value with more significant figures than the
  default six was rounded in the operator-facing output. All three now render via
  the verified kernel `format_rational` (the same renderer behind
  `enriched_reason`): a terminating decimal (`0.25`) or an exact fraction
  (`1/3`), never a rounded float. Go gains a public
  `aletheia.FormatRational(Rational) (string, error)` for this (the CLI is a
  separate package); the now-unused `ratFloat` / `rationalFloat` float helpers are
  removed. Output for typical DBCs (values `%g` already printed in fixed,
  non-scientific notation within six significant figures) is unchanged. PR 2 of
  the "render rationals exactly in user-facing output" sweep.
  (`go/cmd/aletheia/main.go`, `go/aletheia/enrich.go`, `cpp/src/cli/cli.cpp`,
  `python/aletheia/cli.py`.)

- **C++ `extract --json` emits exact rationals, not a lossy `double` (parity
  with Python/Go; BREAKING for that output).** The CLI's `extract --json`
  rendered each signal value via `Rational::to_double()`, so a non-integer
  physical value (e.g. a factor-`0.25` signal → `2500.25`) reached a JSON
  consumer as a lossy IEEE-754 double. It now emits the exact
  `{"numerator","denominator"}`-or-bare-int wire shape — the same
  parser-equivalent shape as Python's `FractionJSONEncoder`, Go's `extract
  --json`, and the binding's own DBC canonical JSON (the parsed value matches;
  byte order does not, since nlohmann emits object keys sorted). The float
  principle bars a lossy float even on machine-readable output. A consumer that
  parsed an `extract --json` value as a plain JSON number must now read the
  rational object for non-integer values (integers stay bare ints).
  (`cpp/src/cli/cli.cpp`.)

- **FFI validation-error envelopes now key the human reason as `message`, not
  `error`** (`haskell-shim/src/AletheiaFFI/Marshal.hs` `mkErrorJson`). The
  cross-binding error-envelope convention — the Agda `responseToJSON` emitter and
  all four bindings — reads `message`; the shim's `mkErrorJson` was the lone
  hold-out keying `error`, so a binding reading a null-guard / FFI-validation
  failure (`code: ffi_validation_error`) surfaced `"Unknown error"` instead of the
  real reason. (The per-signal extraction object `{name, error}` is a different,
  narrower shape and correctly keeps `error`.)
- **The `checkFFINames` mangled-name extractor is robust to surrounding
  punctuation** (`Shakefile.hs` `extractFFIName`). It located the qualifier by
  `drop (length qualifier + 1)` on the whitespace-delimited word, which assumed
  the word *started* with the qualifier — so a paren-prefixed call
  (`unsafeCoerce (AgdaX.d_f_12 …`) or a backtick-wrapped mention in a comment
  mis-extracted to `.d_f_12`, spuriously failing the FFI-name drift gate. It now
  finds the qualifier prefix anywhere in the word and takes the trailing digits,
  so the FFI wrapper can call the export in the natural idiom; the renderer twin
  only passed by happening to be a standalone word.
- **Python & C++ reject floats on the internal wire decode**
  (`python/aletheia/client/_helpers/`, `cpp/src/json_parse.cpp`). A computed value
  crossing the FFI boundary — an extraction signal value, a DBC
  factor/offset/min/max read back from the core, an env-var or attribute bound —
  must be an exact rational (a bare integer or a `{numerator, denominator}`
  object), never a float; a float on the wire would mean a computation escaped the
  rational kernel. Both bindings now reject one:
  - **Python**: a single strict `decode_wire_rational` (rejects float / string /
    bool) replaces the lenient `parse_rational` on *both* wire paths — extraction
    responses (`json_codec.parse_values_list`) and DBC responses (`dbc_normalize`,
    which despite its name decodes `parseDBC`/`formatDBC` *responses*, not user
    input). `parse_rational` — which silently coerced a float via
    `Fraction(x).limit_denominator` — is retired; it had no UI caller.
  - **C++** (`json_parse.cpp`): the `Rational::from_double` branch in
    `parse_signal_value` is dropped, `parse_rational_dict` guards its
    numerator/denominator, and ~17 integer-position reads route through new
    `require_int`/`require_uint` helpers that reject a JSON float (nlohmann
    silently truncates `5.9 → 5` before the range check) — and, for unsigned
    positions, a negative.
  Go (decoder via `UseNumber`) and Rust (serde `as_i64`) were already strict, so
  all four bindings now agree. The UI float-input converters are untouched (a
  follow-up replaces them with an exact Agda decimal parser). Boundary tests per
  binding; the C++ guard is revert-probed (a float `startBit` truncated-and-passed
  without it).
- **Go decodes JSON response numbers exactly, not through `float64`**
  (`go/aletheia/json.go`). `parseResponse` used `json.Unmarshal`, which decodes
  every JSON number as a `float64` — so a rational numerator/denominator above
  2^53 was silently rounded (e.g. `9007199254740993` → `…992`), the one binding
  doing so (Python `json` → `int`, C++ `get<std::int64_t>`, Rust serde `as_i64`
  all read these exactly). It now uses a `json.Decoder` with `UseNumber()`, so
  numbers arrive as `json.Number` and the three numeric helpers (`parseRational`,
  `parseNumberAsInt64`, `jsonNumberToUint64`) read them exactly via
  `strconv.ParseInt`/`ParseUint` (a `float64` path is retained for hand-built
  maps / direct callers). The trailing-byte rejection that `json.Unmarshal`
  provides — but a bare `Decoder` does not — is re-asserted explicitly (a
  response must be exactly one JSON value).
  A boundary test feeds `9007199254740993` through the real `parseResponse`
  path and asserts it survives exactly.
- **Go `DBCDefinition.MessageByID` / `MessageByName` now return a genuine deep
  copy** (`go/aletheia/dbc.go`). `copyMessage`'s doc promised a deep copy, but it
  cloned only the top-level `Signals` slice header — the returned message shared
  the original's `Senders` backing array and each signal's `Receivers`,
  `ValueDescriptions`, and (for a `Multiplexed` presence) `MultiplexValues`
  backing arrays. A caller mutating any of those nested slices on the returned
  message silently corrupted the `DBC`'s stored definition. Every externally
  reachable reference field is now cloned (`slices.Clone`); the unexported,
  build-once `signalIndex` cache stays shared by design (it is read-only, never
  mutated in place, and remains valid for the cloned same-order signals). A new
  `TestMessageByName_DeepCopyIndependence` mutates each cloned field and asserts
  the original is unaffected, with a content-equality guard that the clone is
  faithful (and that an `AlwaysPresent` presence is not clobbered).
- **Python & C++ enrichment now render the observed signal value exactly via the
  kernel `formatℚ`, not lossy `%g`** (`python/aletheia/client/_enrichment.py`,
  `cpp/src/client.cpp`). A violation's `enriched_reason` interpolated the observed
  value through `%g` / `Rational::to_double()`, mangling large integers
  (`1234567` → `1.23457e+06`) and rounding non-terminating fractions
  (`740/3` → `246.667`). Both now delegate to the same Agda kernel renderer the
  predicate threshold already uses (`aletheia_format_rational`), so the observed
  value is exact and byte-identical to the predicate. First step of the "all bindings delegate
  rational rendering to the proven core" effort (Rust + Go to follow).
- **C++ inline YAML check loader now enforces the 64 MiB input bound**
  (`cpp/src/yaml.cpp`). `load_checks_from_yaml_string` parsed an unbounded
  in-memory payload, while the file loader (`load_checks_from_yaml`) and the
  Go/Rust inline loaders all cap input at `max_dbc_text_bytes`. It now checks
  `yaml.size()` before the parse via a shared `check_input_size_bound` helper
  (the in-memory analogue of `check_file_size_bound`), returning the same
  structured `InputBoundExceeded` error. Closes the trust-boundary gap.
- **C++ `build_frame` / `update_frame` now report a distinct error for a CAN ID
  with no DBC message** (`cpp/src/client.cpp`). `resolve_signals` only did a
  per-signal lookup, so a CAN ID absent from the DBC produced a misleading
  "signal '…' not found" error (and a zero-signal call silently succeeded). A
  message-existence guard now returns "no DBC message for CAN ID {id}
  (extended={…})" before the per-signal loop, matching Go (`resolveSignalIndices`)
  and Python (`_resolve_signal_indices`).
- **C++ Excel template headers are now bold** (`cpp/src/excel.cpp`). The
  `create_excel_template` writer emitted plain header cells while its docstring
  claimed bold — and Python (openpyxl) and Go (excelize) both bold their headers.
  Header cells now carry a bold font (verified by a save→reopen round-trip test),
  making the docstring true and the templates consistent across bindings.
- **C++ now rejects a negative-denominator rational on JSON decode instead of
  silently sign-normalizing it** (`cpp/src/json_parse.cpp`). `parse_rational_dict`
  flipped the signs of a `{numerator, denominator}` payload with `denominator < 0`
  and accepted it; the kernel emits a positive denominator (the ℕ⁺ invariant), so
  a negative one is a wire-format violation. It now throws (surfaced as an
  `ErrorKind::Protocol` error) for `denominator <= 0`, matching Python
  (`extract_rational_from_dict`), Go (`parseRational`), and Rust (`Rational::new`),
  which already reject it.
- **C++ preserves the original wire string for an unrecognized validation issue
  code** (`cpp/include/aletheia/validation.hpp`, `cpp/src/json_parse.cpp`).
  An unknown `code` collapsed to the bare `IssueCode::Unknown` enumerator and
  rendered as the literal `"unknown"`, discarding the wire string — so a future
  core code could not round-trip. `ValidationIssue` gains a `code_raw` field (the
  verbatim wire code) and a new `issue_code_label(issue)` helper returns `code_raw`
  when the code is `Unknown`; the CLI `validate` output uses it. This matches Go's
  string-typed `IssueCode`, Rust's `IssueCode::Unknown(String)`, and Python's
  passthrough. Note: adding `code_raw` to the public
  `ValidationIssue` struct changes its layout (ABI) and aggregate-initialization —
  construct via designated initializers (`{.severity = …, .code = …, .detail = …}`,
  which the project already uses everywhere); positional `{sev, code, detail}` now
  binds the third value to `code_raw`. The decoders set it; manual constructors may
  leave it empty.
- **Go `FloatToRational` no longer silently wraps an int64-overflowing integral
  value** (`go/aletheia/types.go`). The integer fast path guarded with
  `v >= math.MinInt64 && v <= math.MaxInt64`, but `math.MaxInt64` (2⁶³−1) is not
  exactly representable as `float64` and rounds *up* to 2⁶³, so `2⁶³` passed the
  bound and `int64(2⁶³)` wrapped to `MinInt64`, returned with `err == nil` — a
  silently-wrong value. The fast path now uses a round-trip guard
  (`n := int64(v); float64(n) == v`), mirroring `cpp/src/types.cpp`: it accepts
  every int64-representable integer (including `MinInt64`) and rejects the rest,
  which fall through to the scaling path's existing overflow error.
- **Python `end_stream` now validates the warning `property_index` instead of
  casting it** (`python/aletheia/client/`). The end-of-stream `complete`-response
  warning parser used `cast("int", w.get("property_index", 0))` — a no-op at
  runtime — so a malformed FFI value (a string, a non-unit-denominator rational,
  or an absent field) flowed through mistyped or silently defaulted to `0`. The
  warning parse moved into `parse_complete_warnings` (beside
  `parse_finalization_results`) and runs `property_index` through
  `validate_integer_field` — the same validator used for the identical field in
  finalization results — raising `ProtocolError` on a bad or missing value, in
  lockstep with Go's `parseNumberAsInt64`. The parser also rejects a non-list
  `warnings` payload or a non-object entry with a typed `ProtocolError` rather
  than a bare `TypeError` / `AttributeError`.
- **C++ / Go memory-safety hardening** — three latent
  out-of-bounds / overflow defects, each now guarded and regression-tested
  (a test that fails without the fix):
  - **C++ `within(ms)` ms→µs overflow** (`cpp/include/aletheia/check.hpp`). The
    `duration_cast<microseconds>` multiplied the millisecond bound by 1000 with
    no guard, so a large bound (reachable from untrusted input, e.g. a YAML check
    with `within_ms: 9300000000000000`) was signed-integer-overflow UB. Both
    `within()` builders now route through a shared `detail::checked_ms_to_us`
    helper that rejects `ms > INT64_MAX/1000` with `std::invalid_argument`,
    mirroring the Go (`MaxInt64/usPerMillisecond`) and Rust guards.
  - **C++ truncated binary extraction now errors instead of silently succeeding**
    (`cpp/src/client.cpp`). `parse_extraction_bin` returned an empty *success*
    (`return {}` → an empty `ExtractionResult`) on a short/truncated FFI buffer,
    so a truncated response decoded as "zero signals" rather than a failure. All
    five truncation paths now return an `ErrorKind::Protocol` error, which the
    call sites already propagate (`extract_signals`) / log + surface as
    `nullopt` (`extract_signals_internal`) — making their comments true. Matches
    Go / Python, which already error.
  - **C++ / Go stale cached-index lookup** (`cpp/src/dbc.cpp`,
    `go/aletheia/dbc.go`). The lazy name/ID lookup caches freeze positional
    indices on first build; if the caller then mutates the public `messages` /
    `signals` slice, the cached index goes stale — out of bounds if the slice
    shrank (OOB read UB in C++, a panic in Go), or in-bounds-but-wrong if it was
    reordered or replaced in place (silently returning the wrong message/signal
    for the requested key). `signal_by_name`, `message_by_id`, and
    `message_by_name` now validate that the cached index still refers to the
    requested entry in both bindings — a bounds check plus a key match; any
    stale or mismatched index reads as not-found (`nullptr` / `nil`).
- **Rust binding review — 8 non-breaking fixes** (the two BREAKING ones are
  under Changed). All are cross-binding parity / determinism / strictness gaps
  that the `fmt`/`clippy`/`cargo test` gates cannot catch, found by the thorough
  Rust review and adversarially verified:
  - **Async `send_frames` is now frame-cancellable** (`rust/src/async_client.rs`).
    It dispatched the whole batch as one atomic job, so dropping the future
    committed *all* N frames (or none) — contradicting `CANCELLATION.md` §1.1. It
    now dispatches one cancellable job per frame, so a dropped future stops at the
    next boundary committing only a prefix; `CANCELLATION.md` §3.4 updated to match.
  - **Deterministic end-of-stream enrichment** (`rust/src/lib.rs`). `enrich_eos`
    merged multi-CAN-id last-frame values in nondeterministic `HashMap` order; it
    now sorts by `(id, extended)`, matching Go's `slices.Sort` / Python's sort.
  - **`extract_signals` retains the per-signal error reason** (see Changed —
    `SignalError`).
  - **Stricter response decoding** (`rust/src/response.rs`): an empty
    `property_batch` or an unrecognised status/type in `decode_frame` is now a
    protocol error, not a silent `Ack` / empty verdicts (mirrors Go's
    `parseFrameResponse`); and `decode_extraction` rejects a non-object `errors`
    entry / a non-string `absent` entry, and `decode_issue` requires `code` and
    `severity` to be present strings — instead of silently blanking/dropping them.
    All match the Go / C++ / Python decoders, which reject these malformed shapes.
  - **Strict validation-severity decode** (see Changed — `IssueSeverity`).
  - **`Rational::from_f64` rejects exactly 2^63** instead of saturating it to
    `i64::MAX` (`rust/src/types.rs` + the `aletheia-excel` integer fast paths): the
    guard was `<= i64::MAX as f64`, but that bound rounds up to 2^63; now `<`.
  - **`MAX_FORMULA_DEPTH` doc corrected** (`rust/src/ltl.rs`): it is a client-side
    recursion guard (100), distinct from the kernel's 64 JSON nesting wire cap —
    the old comment wrongly claimed it was the wire cap "matching every binding".
  - **A compile-time assertion** now pins that the `AsyncClient` method *futures*
    are `Send` (the documented `tokio::spawn` guarantee), plus new tests for the
    `property_index_oob` / `extraction_failed` enrichment-warn paths and the
    multi-frame `enrich_eos` merge loop.
- **Python mutation lane repaired — it had silently produced zero mutants since
  #51.** The advisory `mutation testing` lane was red (not from new survivors —
  it was crash-dead): mutmut runs pytest from a relocated `python/mutants/`
  work-tree, and two post-baseline test additions broke its baseline collection
  there. `tests/test_check_changelog.py` (added in #51) imports the repo-root
  `tools` package, which is absent from `mutants/`, so collection
  `ModuleNotFound`-aborted; and `tests/test_excel_loader.py`'s two
  `demo_workbook` tests (changed in #65) resolve the shared
  `examples/demo/demo_workbook.xlsx` fixture via `parents[2]`, which points
  outside the copied tree. With `-x`, the first failure killed the whole stats
  phase → 0 mutants run. Fixed by adding `test_check_changelog.py` to the
  `[tool.mutmut]` `--ignore` list and `--deselect`-ing only the two out-of-tree
  excel tests (keeping every other excel test's kill signal). The lane now
  reconciles to its documented baseline: **827 killed / 1 survived / 828 total**
  (the lone survivor is the documented `dump_json` `ensure_ascii=False`→`None`
  equivalent); Go (636/636) and C++ (50/50) were already clean.
- **Mutmut config migrated to the mutmut 3.6 key names — zero deprecation
  warnings.** `[tool.mutmut]` `paths_to_mutate` → `source_paths` and
  `tests_dir` → `pytest_add_cli_args_test_selection` (the loader still honored
  the old names but emitted a `UserWarning` on every run). Semantically
  identical; eliminates the warnings so the lane's output stays signal. Docs
  referencing the old keys (`docs/MUTATION_BENCH.yaml`, `AGENTS/python.md`)
  updated to match.
- **CI now tests every Go package, not just `./aletheia/`.** The `run_ci.py` Go
  lane ran `go test ./aletheia/`, silently skipping `go/cmd/aletheia` (4 tests)
  and the separate `go/excel` module (64 tests) — 68 tests that never gated a PR.
  The lane now runs `go test ./...` over the core module (covering `aletheia` +
  `cmd/aletheia`) **and** a second `go test ./...` over the `go/excel` module
  (its own `go.mod` makes `./...` stop at the boundary), both with `ALETHEIA_LIB`
  set so the `.so` is found regardless of each package's test cwd. The `gofmt` /
  `go vet` lint step is likewise widened from `./aletheia/` to all of `go/` plus
  the excel module. (Python's `pytest tests/` and C++'s `ctest` were already
  comprehensive; the Rust `excel` crate gets its own lane when it lands in R3c.)
- **`check-fidelity` no longer fails to find the MAlonzo modules when the build
  is a no-op.** The `haskell-shim/MAlonzo -> ../build/MAlonzo` symlink (which
  cabal resolves the generated `MAlonzo.*` modules through, and which is
  gitignored) was created only *inside* the `.so` rule's action — so when that
  rule no-ops (the `.so` already up to date, e.g. a warm build-tree cache restored
  on a fresh checkout), the symlink was never created, and `check-fidelity`'s
  `cabal test` failed with `Could not find module 'MAlonzo.Code.…'`. `check-fidelity`
  now ensures the symlink itself (idempotent, symmetric with the `.so` rule). This
  was latent until the build-staleness scheduling above made code-only PRs do a
  genuine no-op build on a fresh CI checkout. Reproduced and fixed deterministically
  (remove the symlink against an up-to-date `.so` → fail; with the fix → pass).
- **The build no longer full-recompiles `libaletheia-ffi.so` on every
  invocation, and can no longer ship a stale one.** The `.so` rule forced a
  complete ~280-module MAlonzo rebuild each run (an always-dirty phony symlink
  dependency, plus `rm -rf` of the cabal build tree and a `touch`). That
  sledgehammer masked a real dependency-graph gap: the foreign library's
  `other-modules` did not list the generated MAlonzo modules (and
  `-Wmissing-home-modules` was suppressed), so cabal's up-to-date check never saw
  them change and would skip GHC entirely — a genuine stale-`.so` hazard once the
  sledgehammer was removed. Both are resolved (see Added): the Shake rule depends
  on the Agda sources and cabal now tracks every MAlonzo module, so the build is
  incremental *and* content-hash-correct, verified by the `build-incremental`
  gate.
- **Go and C++ `MockBackend` test doubles record `<binary:OP>` sentinels** for
  binary-path operations (matching the Python mock), instead of fabricating JSON
  wire shapes the real backends never emit. Behavior change to the public test
  doubles only — tests asserting on `MockBackend` recorded inputs now see
  `<binary:OP>` sentinel strings; no production behavior change. The dead
  internal serializers behind the old shapes were removed (`serializeDataFrame`
  / `serializeErrorEvent` / `serializeRemoteEvent` in Go; `serialize_send_frame`
  in C++).

### Changed

- **`MockBackend` errors on queue exhaustion instead of fabricating a default
  response (all four bindings). BREAKING (test doubles).** When a test asks a
  `MockBackend` for more responses than it queued, every binding now
  raises/throws immediately — Python `StateError`, C++ `AletheiaException`
  (`ErrorKind::State`), Go `ErrState`, Rust `Error::Protocol` — with the
  byte-identical message `mock backend: no queued response for {op}`, where
  `{op}` is the starved operation's cross-binding token (the `<binary:OP>`
  sentinel, or `process` for the JSON control-plane path). Previously Python
  and C++ fabricated a `{"status":"ack"}` / `{"status":"success"}` default
  (silently absorbing an under-provisioned test), and Go/Rust already errored
  but with divergent wording and, in Rust, a method-name op token instead of
  the shared sentinel. The starved call is still recorded in
  `inputs()`/`captured()` before the error, and the error *kind* stays
  idiomatic per binding (only the message and op token are unified). An
  under-provisioned mock test now fails loudly at the missing response rather
  than passing on a fabricated one. `MockBackend` is public API in
  Python/Go/Rust (`make_mock_backend` in C++), so test code that relied on the
  fabricated defaults must queue the responses it consumes or assert the error.
- **The Rust binding resolves its FFI symbols once per process instead of
  per call.** `FfiBackend` used to run `dlsym` on every operation — two
  lookups per streamed frame (the op symbol + `aletheia_free_str`); a new
  internal `Symbols` table now resolves every export exactly once, cached
  in a `OnceLock` alongside the process-lifetime `Library` (so each cached
  `Symbol<'static, _>` stays borrow-tied to the mapping that backs it).
  Failure does not latch a poisoned cache: a failed library *load* is
  returned to the caller and retried on the next construction, and a
  resolution failure caches nothing — only a fully successful resolution
  is latched (the RTS-init latch semantics are unchanged). A library that
  loads but lacks exports fail-fasts at construction with the precise
  missing-symbol name instead of erroring on the Nth call — note that such
  a library itself stays loaded for the process lifetime (the pre-existing
  loaded-once contract), so correcting the path after that requires a new
  process. No public API change. Measured with the new
  `rust/examples/bench_send_frame.rs` micro-benchmark (100 000 frames,
  release, WSL2): ~3 913 → ~3 733 ns per `send_frame` (~+4.8% throughput,
  255.6k → 267.9k frames/sec) — consistent direction across all paired
  runs, though within WSL2's ±5% jitter band the margin is at the edge of
  resolution; the structural guarantee is the mechanism itself (two
  `dlsym` per frame → zero).
- **End-of-stream violation enrichment extracts each tracked frame once,
  not once per property (all four bindings, uniform shape).** The Python,
  Go, and C++ clients used to re-extract every last-seen frame for *each*
  Fails/Unresolved property at `end_stream` (P×F FFI crossings); all three
  now run Rust's extract-once shape — collect the todo entries (out-of-range
  `property_index` still warns `enrichment.property_index_oob` and is
  excluded), extract each tracked frame exactly once in ascending
  (CAN-ID, extended) order, merge first-frame-wins, and distribute the
  merged values to every todo property — at most F crossings. All four
  bindings additionally gain two uniform guards: an **empty-union skip**
  (when no todo property wants any signal, the extraction pass is skipped
  entirely — enrichment is still attached with the existing no-values
  fallback reason) and an **early break** once every wanted signal has a
  value (Rust previously always extracted every tracked frame; its
  mock-count pin moved from 2 to 1 accordingly). In the three reshaped
  bindings `enrichment.extraction_failed` now warns once per failed *frame*
  per `end_stream` instead of once per (property, frame) — same event, same
  fields, lower cardinality (Rust keeps its pre-existing property-level
  variant of that warning, emitted at distribution). Frame iteration is now
  uniformly ascending (CAN-ID value, then extended flag) — Go previously
  ordered all standard frames before all extended ones, so first-frame-wins
  could pick a different frame's value than the peers on mixed streams; Go
  also now skips enrichment on an *empty* (not just absent) diagnostics
  list, matching the peers. The enrichment signal collectors are now uniform
  pass-throughs: Python's no longer drops empty signal names — the kernel is
  the single validator of signal identifiers (`setProperties` rejects an
  invalid or empty name with the typed `parse_invalid_identifier` error
  before any diagnostic is built), so no binding second-guesses it. The
  enrichment payload, its attach-always
  contract, and the streaming (mid-stream) enrichment path are unchanged;
  no wire shapes moved. All four bindings gain mock-count regression tests
  over a shared scenario matrix: extractions == frames (not P×F),
  early-break, first-frame-wins vs overwrite, all-satisfied and
  no-tracked-frames at zero, OOB exclusion, and failed-extraction warn
  cardinality.
- **The CLIs parse a DBC once per invocation, not two or three times.**
  Every `.dbc` subcommand in the Python CLI used to parse the file through
  the verified text parser (`dbc_to_json` on a throwaway client — a full
  GHC RTS init, parse, validate, and session-load), then discard that
  session and re-parse the result through the structured-JSON route
  (`parse_dbc`) on the real client; `validate` added a third pass
  (`validate_dbc`). The Go and C++ CLIs each ran the parse plus a
  redundant `ValidateDBC` round-trip. All three now load a DBC exactly
  once: a `.dbc` text file goes through `parse_dbc_text` (which parses,
  validates, and loads the session in one kernel call) on the
  subcommand's own client, and `validate` renders the parse's warnings
  directly — the kernel's parse epilogue *is* full validation, so a
  successful parse has no error-severity issues and its warnings are the
  complete validation result. Excel-sourced DBCs still route through
  `parse_dbc` (they have no text form), now with their parse status
  checked (previously `format-dbc` ignored it, so an invalid
  Excel-sourced DBC misreported as a `formatDBC` failure). Observable
  behavior is unchanged — the 40-scenario cross-CLI parity harness passes
  identically across all three — but large `.dbc` files pay the O(N²)
  text-parse cost once instead of twice. `dbc_to_json` /
  `convert_dbc_file` keep their public ad-hoc contract; `run_checks` gains
  an optional `client=` parameter so a caller that has already loaded the
  DBC skips the redundant `parse_dbc`.
- **The two DBC-loading routes share one validate-and-load pipeline, and
  `validateDBC` gained the adversarial bounds cascade.** A new leaf module
  `Aletheia.Protocol.Handlers.LoadDBC` holds the single *tagged* bound cascade
  (array-cardinality + string-length, each branch field-tagged) and the
  validate-and-load epilogue that the JSON route (`parseDBC`) and the verified
  text route (`parseDBCText`) previously ran as byte-identical copies; the two
  handlers now differ only in the command-context literal. Wire consequences:
  - The **text route's** `input_bound_exceeded` message now names the offending
    field, e.g. `ParseDBCText: version string: string length 65546 exceeds
    limit 65536` (the field label was previously dropped on this route only) —
    parity with the JSON route.
  - **`validateDBC`** now runs the same bounds cascade before validating, so an
    over-cardinality / over-length DBC is rejected with `input_bound_exceeded`
    rather than validated unbounded (hardening parity with the load routes). The
    Python binding's `validate_dbc` lifts that rejection to the typed
    `InputBoundExceededError` via a shared `lift_input_bound_exceeded` helper
    (gated on the wire code, mirroring `lift_validation_issues`;
    `build_error_response` delegates to the same triple extractor), so no route
    re-implements the code→typed-error lift — Go / C++ / Rust already typed it
    via their shared decoders.

  `parseDBCText` also materializes `toList text` once (feeding the `List Char`
  entry point `parseTextChars`) instead of twice. The structured
  `bound_kind` / `observed` / `limit` payload and every error `code` are
  unchanged. Module count 277 → 278; the proof tree type-checks unchanged
  (no proof module referenced the moved definitions).


- **Efficiency batch — off-hot-path allocation and round-trip cuts
  across Go/C++/Rust; no wire or API change.** Go: `serializeDBC` now returns
  the marshaled bytes (`json.RawMessage`), so every DBC-bearing operation
  (`ParseDBC` / `ValidateDBC` / `FormatDBCText` / `DBCDefinition.MarshalJSON` /
  the mock's `RespondParseDBC`) marshals the DBC once instead of twice — the
  defense-in-depth size probe is retained, the single marshal now *is*
  the probe, and the wire bytes are unchanged (`encoding/json` embeds a
  `RawMessage` verbatim). The extraction cache key split into `frameMeta` +
  a payload-keyed inner map, so a cache HIT no longer heap-copies the frame
  payload (`entries[meta][string(data)]` compiles to Go's allocation-free
  map-index form; the 256-entry capacity semantics are preserved by an exact
  total-entry counter). C++: the Excel loader stops deep-copying each row's
  cell map into `data_rows` (`std::move`), and `group_rows_by_message`
  returns groups in first-seen order directly, dropping the per-message
  ordered-map re-lookup in the build loop. Rust: the end-of-stream
  enrichment first-seen merge gains a `HashSet` seen-guard beside the
  ordered Vec — O(N) expected instead of an O(N²) rescan; merge order (and
  therefore `Enrichment.signals`) is byte-identical. CLI (Go and C++, in
  lockstep): `extract` and `format-dbc` no longer re-`ParseDBC` the
  definition their own `loadDBCText` already loaded — the kernel's text
  parse reaches the identical `ReadyToStream` state and both clients
  populate their signal lookup on that path, so the second full
  serialize→FFI→re-validate round-trip was pure repetition. Observable
  deltas: one fewer `dbc.parsed` log event per CLI invocation (the CLIs
  attach no logger), and the kernel now holds the text-parsed DBC rather
  than its JSON round-trip image — identical by the round-trip proof.
  (Python's CLI already loads once — it was the reference; Rust has no CLI.)

- **CI: the two advisory benchmark lanes retry once on failure, always upload
  their variance/result JSONs, and tally every retry (flake hardening).** The
  jitter watch closed with a verdict of intermittent runner noise: 2× the
  stability drift gate failed for Python on runtime-neutral PRs (a doc-only and
  a C++-only change — provably not regressions), and 1× the throughput gate
  failed with a uniform ~2.7× slowdown across every binding and category (a
  slow runner; a real regression is asymmetric). Now: the stability bench
  re-runs once on a failed first attempt; the throughput gate re-MEASURES the
  benchmark once and re-gates (re-judging stale numbers would be pointless).
  Thresholds are unchanged — this is not a gate relaxation. Diagnosability:
  the stability lane's per-binding variance JSONs upload on every run
  (previously never uploaded, so the exact CV that breached a failing run was
  unrecoverable), and a retried run preserves its first attempt as a separate
  `…-attempt1` artifact. Tally: each retry emits a `FLAKE-RETRY` warning
  annotation + a step-summary line, and the count of `attempt1` artifacts
  across runs IS the running tally (query documented in the workflow
  comments). CI-only; local benchmark runs keep the manual-rerun discipline.
- **CI: `actions/cache` bumped v5 → v6 at every cache / restore / save site**
  (`benchmark.yml` / `pr-full-ci.yml` / `pr-heavy-lanes.yml`; Dependabot).
  No workflow logic changed — the same keys, paths, and restore-key prefixes;
  the entry exists because the changelog gate rightly treats a cache-action
  major bump as a CI change worth a line.
- **C++ `Rational` ctor and `Rational::make` reject `double` and
  `bool` at the exact-numeric boundary (BREAKING, C++).** The two-argument
  `Rational(std::int64_t, std::int64_t)` constructor and the `Rational::make`
  factory previously accepted a `double` (silently truncating, e.g.
  `Rational(7.9, 2)` → `7/2`, with only a non-fatal `-Wliteral-conversion`
  warning under paren-init) and a `bool` (silently, `true` → `1`). They are now
  constrained to non-`bool` `std::integral` parameters, so a decimal must go
  through `Rational::from_decimal` (the kernel decimal SSOT) — closing the last
  float-input path in the C++ binding and bringing it to the same compile-time
  bar Go and Rust already had (their rationals are `int64`/`int64`-typed, so a
  float never compiles). `Strong::of` (and thus `PhysicalValue::of` /
  `RationalFactor::of` / …) is closed transitively by the constrained
  constructor via its `std::constructible_from` guard. Ten header
  `static_assert`s prove the boundary (integer construction still works; a
  `double`/`bool` is rejected at the ctor, `make`, and `of`) and fail the build
  on any regression. No in-repo call site passed a `double` or `bool`, so the
  break only affects downstream/future misuse. Because the constrained
  parameters accept any non-`bool` integral type, the ctor and `make` also
  reject a value outside the `int64` range (e.g. a `uint64_t` > `INT64_MAX`) via
  `std::in_range` *before* the narrowing cast — rather than wrapping silently
  and suppressing the `-Wconversion` diagnostic the old `int64_t`-typed
  signature gave for free. Touches `cpp/include/aletheia/types.hpp` plus a
  `unit_tests_decimal` range-rejection test; no proof or other binding touched.
- **Rust lifts the typed `input_bound_exceeded` triple (parity; BREAKING —
  Rust).** The Rust binding previously decoded every `status: "error"` envelope
  to a generic `Error::Core { code, message }`, discarding the structured
  `bound_kind` / `observed` / `limit` triple that Go (`*InputBoundExceededError`),
  C++ (`InputBoundExceededError`), and Python (`InputBoundExceededError`) all lift
  into a typed error. `parse_object` now lifts a well-typed `input_bound_exceeded`
  triple into a new `Error::InputBoundExceeded { code, bound_kind, observed, limit }`
  variant (a malformed or partial triple degrades to `Error::Core`, matching the
  peers; the human-readable message is reconstructed from the triple by `Display`,
  not stored — as in Go / C++ / Python). BREAKING because `Error` is not
  `#[non_exhaustive]`, so a new variant requires an added match arm downstream.
  Closes the one feature divergence the cross-binding decoder audit surfaced, and
  adds an `input_bound_exceeded_error` FEATURE_MATRIX row (all four bindings) so the
  parity gate tracks this capability — the absence of that row is why the
  divergence escaped the matrix and needed an ad-hoc audit to find.
- **Rust wire-decoder reject-branch test coverage — internal, no behavior
  change.** Added inline unit tests in `rust/src/response.rs` covering the
  decoder reject branches a cross-binding coverage audit (parity with the Go
  wire-decoder reject-coverage work) found untested: unknown validation severity, a non-number/non-object
  rational, an unknown verdict, an empty/unexpected frame batch, and an
  unexpected status in the ack / validation / format-text decoders. Tool-measured
  with `cargo-llvm-cov` (`response.rs` line coverage 74.6% → 81.7%). No production
  Rust changed; the entry is required only because the changelog gate matches by
  path and Rust's inline `#[cfg(test)]` tests live under `rust/src/`.
- **Python rejects a `float` at the rational outbound wire fields
  (BREAKING, behavioral).** A `float` in a hand-built `DBCDefinition` rational
  field (signal `factor`/`offset`/`minimum`/`maximum`, env-var
  `initial`/`minimum`/`maximum`, float-kind attribute `min`/`max`/`value`) or in a
  raw `set_properties` `LTLFormula` threshold (`value`/`min`/`max`/`delta`/
  `tolerance`, e.g. one computed as `0.1 + 0.2`) previously serialised to the wire
  as `0.30000000000000004` and was silently absorbed by the Agda kernel as an
  exact-but-*wrong* rational: the DSL value path was guarded by
  `to_exact_fraction`, but these two untyped-dict paths were not. A new validator
  `reject_inexact` (the float-principle SSOT, alongside `to_exact_fraction`) — the
  outbound twin of the inbound `decode_wire_rational` — rejects a `float` or
  `bool` with a `ValidationError` naming the field, applied at exactly the
  kernel's ℚ-valued fields: in `normalize_dbc_for_wire` (covering `parse_dbc` /
  `validate_dbc` / `format_dbc_text`) and over each formula's predicate
  thresholds before `set_properties` sends. It is **field-aware**: integer wire
  fields (`multiplex_values`, `startBit`, `dlc`, `id`, value-table values, int/hex
  attribute bounds) are left to the kernel's own typed validation, which rejects a
  non-integer there loudly (e.g. `parse_non_integer_multiplex_value`) rather than
  silently — so the guard does not mask the kernel's precise integer errors.
  Closes the last float-input path in the Python binding; pass an `int`, a
  `Fraction`, or `from_decimal('...')` for an exact decimal. (Go and Rust reject
  these at compile time; C++ via the constrained `Rational` constructor.) The
  `examples/demo/engine_ecu_sim.py` shared DBC, which used raw float scaling
  params, now uses exact `Fraction`s.
- **CI: cache everything cacheable in the throughput benchmark lane + fix the
  build-tree cache's biggest gap — internal, no behavior change.** The
  `benchmark.yml` lane was ~92 % cold build/setup (the benchmark itself is ~8 %):
  a cold `~342s` FFI build and a `~142s` Release C++ build ran on every PR. It now
  reuses the same caches `pr-full-ci.yml` had — an incremental build-tree cache
  (**restore-only**, sharing pr-full-ci's key so it warms from `main`'s seed on a
  brand-new PR's first push), `ccache`, and the CMake FetchContent deps — plus a
  pip wheel-download cache on `setup-python`. The `ccache` and `_deps` caches use
  benchmark-specific keys (`ccache-bench-*` / `cpp-deps-bench-*`) so a Release-only
  save cannot clobber pr-full-ci's combined Debug+UBSan / three-build-dir caches
  under a shared immutable key. A `paths-ignore` filter (`**/*.md`, `docs/**`)
  skips the lane on doc-only PRs (safe: Benchmark is not a required check).
  The build-tree cache also gains `haskell-shim/dist-newstyle` (the cabal
  foreign-lib build — the 276 MAlonzo `.o`/`.hi`) across all three workflows:
  omitting it made cabal recompile those objects (~47s) on every run; caching it
  lets cabal's content-hash-aware incremental build skip the recompile (verified
  locally: churn all mtimes → `build` still no-ops, `.so` md5 unchanged). The
  `.so` rule `cp`-copies the built library to `build/libaletheia-ffi.so` (it is a
  copy, not a symlink). Applies to `benchmark.yml` + `pr-full-ci.yml` +
  `pr-heavy-lanes.yml`. The redundant
  pre-restore `cabal update` is moved to run only on a cabal-store cache miss
  (`benchmark.yml` + `pr-full-ci.yml`). Caching the GHC toolchain itself was
  evaluated and rejected: the runner's `~/.ghcup` is a symlink to a 6.2 GB
  `/usr/local/.ghcup`, so a working cache would evict the higher-value build-tree
  and cabal caches under the 10 GB repo budget. No production code, public API, or
  proof is touched.
- **Every binding now parses decimals through the kernel SSOT; the
  float→rational heuristics are gone (BREAKING, all four bindings).** Each binding
  exposes `from_decimal` (Python `aletheia.from_decimal` → `Fraction`; C++
  `Rational::from_decimal`; Go `aletheia.FromDecimal`; Rust `Rational::from_decimal`)
  which delegates to the Phase 0 kernel export `aletheia_parse_decimal` and decodes
  via each binding's existing wire decoder — so the accepted grammar
  (`-?digits[.digits+]`, no `'+'`/leading-`.`/exponent) and the exact rational it
  denotes are identical everywhere and cannot drift. The float principle is now
  enforced end-to-end: numeric API parameters take an exact type (Python
  `int | Fraction`; Go check builders take `Rational`; C++/Rust unchanged — already
  `Strong<Rational>` / `impl Into<Rational>`), a bare `float`/`f64` is no longer
  accepted, and a float survives only at print-out (`to_double`/`Float64`/
  `format_rational`). Decimal parsing is **RTS-gated and vocal**: it requires a live
  backend (an `FfiBackend`/`Client` is the sole RTS initialiser) and returns a typed
  runtime-not-initialised error rather than self-initialising — so the previously
  pure YAML/Excel loaders now require a backend before loading a file with numeric
  fields. Go additionally drops the error return from its now-infallible check
  terminals (`NeverExceeds`/`NeverBelow`/`NeverEquals`, `Equals(...).Always()`),
  matching Python/Rust, and gains an overflow-safe `lo > hi` range comparator
  (`math/big`, replacing a cross-multiply that overflowed `int64`). YAML keeps
  accepting integer literals (exact); a YAML decimal scalar is read as its original
  text and parsed exactly (Python's loader disables the implicit-float resolver).
  Python further rejects a `bool` at the exact-numeric boundary (a `bool` is an
  `int` subclass, so `Fraction(True)` would silently become `1`): the DSL predicate
  path and the client's signal-value path share a single `to_exact_fraction`
  validator that rejects both `float` and `bool`, matching the statically-typed
  bindings that reject `bool` for free.
- **Excel loaders adopt an all-text contract across all four bindings (BREAKING).**
  A spreadsheet number cell stores a lossy IEEE-754 double, so every *numeric* field
  must now be a **text-formatted** cell, parsed exactly via `from_decimal`; a
  number-typed cell — integer or decimal — is rejected with a message naming the
  row, the column, the offending value and the reason (`"… is a number cell (got X);
  format it as TEXT …"`), so a single stray number cell in a column of text is
  locatable from the error alone. Booleans (the `Signed` column) and the hex
  `Message ID` are exempt (a boolean accepts native/`1`/`0`/`TRUE`/`FALSE`; the ID
  keeps its hex/decimal parse). The shared `examples/demo/demo_workbook.xlsx`
  fixture (loaded by every binding's tests) is regenerated all-text accordingly.
- **DBC decode-validation tightened to lockstep across all four bindings**
  (`go/aletheia/json.go`, `python/aletheia/client/_helpers/dbc_normalize.py` +
  `_client_bin.py`, `rust/src/{dbc,types}.rs`, `cpp/src/{json_parse,client}.cpp`).
  The DBC-response and binary-extraction decoders now reject malformed core output
  uniformly, instead of each binding accepting a different subset — closing a gap
  where the same wire bytes could decode in one binding yet be rejected (or
  silently mis-decoded) in another. Not API-breaking: the public surfaces are
  unchanged and well-formed core output is unaffected; only adversarial/corrupted
  input is now rejected. The unified contract:
  - **Signal `presence` is read from the explicit discriminator** (`"always"` /
    `"multiplexed"`) the core emits for every signal, rather than inferred from a
    bare `multiplexor` field. Go and C++ previously inferred; both now read
    `presence` (matching Rust and Python). A `"multiplexed"` signal requires a
    non-empty `multiplexor` and a non-empty `multiplex_values` array.
  - **`multiplex_values` selectors are bounded to u32** in every binding. Go
    already enforced this; Rust and Python previously accepted out-of-range values
    and C++'s `get<uint32_t>` silently truncated them.
  - **CAN id** is range-checked per the `extended` flag (11-bit / 29-bit) and
    **DLC** must be a valid CAN/CAN-FD byte count — Rust gained a public
    `Dlc::from_bytes` for this (the inverse of `Dlc::to_bytes`, the wire-symmetric
    mirror of Go's `BytesToDLC` / C++'s `bytes_to_dlc`). A present `extended` flag
    must be a JSON boolean (Go/Rust previously treated a non-boolean as `false` and
    Python coerced it — e.g. the string `"false"` became `True`; C++ already
    rejected). **`startBit`** is 0–511, bit **`length`** 1–64, and
    environment-variable **`varType`** is 0–2. Each binding that lacked one of these
    gained it (Go and C++ id/DLC were already strict).
  - **The binary signal-extraction buffer must be consumed exactly** — Python and
    C++ now reject trailing bytes past the computed layout (Go already did; the
    Rust binding decodes extraction via the JSON path).
- **BREAKING (Go): the Check API and the signal-extraction read path now carry /
  render exact rationals through the kernel `formatℚ`** (`go/aletheia/{check,result,enrich,json,client}.go`,
  `go/cmd/aletheia`). The Go part of the render-delegation pass,
  bringing Go in line with Python's `Fraction` and C++'s `Rational`-backed value.
  Two coupled changes:
  - **Check descriptions → kernel.** `CheckResult.ConditionDesc()` now returns
    `(string, error)` and renders thresholds via the kernel `formatℚ` lazily
    (mirroring Rust's `DescPart` / C++'s deferred builder / Python's `_desc_parts`),
    so it requires a live GHC RTS and reports an error when the runtime is down.
    Construction stays infallible. This removes the local `fmt.Sprintf("%g", …)`
    descriptions, which diverged from the kernel for values `%g` renders in
    scientific notation (`1e+06` vs the canonical `1000000`).
  - **Extraction value type `float64` → `Rational`.** `SignalValue.Value` is now
    an exact `Rational` (shared by the `BuildFrame` / `UpdateFrame` INPUT and the
    extraction OUTPUT, matching C++'s shared `SignalValue`); `ExtractionResult.Get`
    returns `(Rational, bool)`; `ViolationEnrichment.Signals` is
    `map[SignalName]Rational`; and the observed values in enriched violation
    reasons render via the kernel (eval-path degrade on failure, parity with
    Python / C++). The binary and JSON extraction decoders now carry the exact
    `numerator`/`denominator` the kernel sends instead of collapsing to
    `float64(num)/float64(den)` (so e.g. `1/3` is preserved exactly, not
    `0.333…`); a non-positive denominator is rejected on both paths. Migration:
    build input signals with `RationalFromFloat(…)` (e.g.
    `SignalValue{Name: "Speed", Value: RationalFromFloat(120.5)}`); read extracted
    values as `Rational`. The `aletheia` CLI's `extract --json` now emits each
    value as a bare integer or `{"numerator","denominator"}` object (matching the
    Python CLI's `FractionJSONEncoder`), where it previously emitted a lossy float.
- **The `mutation testing` lane is now diff-scoped per binding** (`tools/mutation_run.py`,
  `.github/workflows/pr-heavy-lanes.yml`). On a PR, only the binding engine(s) whose
  directory the branch diff vs `main` touches are run — a Go-only PR runs `gremlins`
  alone instead of also paying for `mutmut` (Python) and `Mull` (C++): a go-only PR's
  lane drops ~24→~16 min (gremlins is the slow ~12.5 min engine + ~4 min setup), a
  Python-only or C++-only PR wins more by skipping gremlins, and a docs-only PR runs
  no engine (~4 min setup only — measured on the UPD PR). Skipping an
  unchanged binding is coverage-neutral: its survivor count is unchanged from its
  baseline by construction. The scoping fails SAFE to the full run — a change under
  a shared artifact (the Agda `src/` → `.so` every binding dlopens, this harness, or
  `docs/MUTATION_BENCH.yaml`), an empty diff (push:main / the post-merge backstop), a
  missing `main` ref, or `ALETHEIA_MUTATION_NO_DIFF_SCOPE=1` all run every binding.
  Per-binding scoping maps the *whole* binding directory (source, tests, and config),
  since mutation tools kill mutants by running that binding's tests — so a test-only
  edit still scopes its binding in (under-scoping would silently skip a regression;
  over-scoping only costs time). The required `mutation testing` check still reports
  green on a docs-only PR (zero engines run, exit 0). CI/tooling only — no runtime or
  API change.
- **BREAKING (Python): `CheckResult.condition_desc` now renders its rational
  thresholds through the kernel `formatℚ` (cross-binding-canonical) and is a lazy
  property rather than a stored string** (`python/aletheia/checks.py`,
  `python/aletheia/client/_enrichment.py`). The Check-API part of the
  render-delegation pass, bringing Python in line with Go / C++ / Rust,
  all of which already route check descriptions through the kernel. Previously the
  description was an eager construction-time f-string of the *raw* value, so a
  float threshold rendered with Python's `repr` — `signal("Speed").never_exceeds(120.0)`
  gave `"<= 120.0"` — diverging from the kernel-canonical `"120"` that the other
  bindings (and the predicate pretty-printer) produce. Now each threshold is
  coerced with `to_predicate_fraction` (the same coercion the LTL predicate value
  uses) and rendered on read via the kernel, so the description and the predicate
  agree exactly and match the peers byte-for-byte. Two consequences: (1) the
  rendered string changes for non-integer-valued float inputs (`120.0` → `"120"`);
  (2) reading `condition_desc` now requires a live GHC RTS — like
  `format_formula` / `build_diagnostic` since the point-2 vocal change, it raises
  `FFIError` when no client/backend has initialised the runtime (construction
  stays infallible; the structured parts are captured eagerly). The internal
  renderer `_format_rational` is renamed `format_rational` (a public-named
  function in the still-private `_enrichment` module), now shared by the
  enrichment and check layers — mirroring Rust's `pub(crate) format_rational` and
  C++'s `detail::format_rational_ffi`. Migration: read `condition_desc` only with
  a live `AletheiaClient` (or `FFIBackend`); expect kernel-canonical threshold
  strings.
- **BREAKING (Go): the rational renderer no longer self-initialises the GHC
  runtime (it is vocal — returns an error — when the runtime is down), and the
  enrichment helper *functions* `FormatFormula` / `BuildDiagnostic` /
  `CollectSignals` are now package-private**
  (`go/aletheia/{renderer,ffi,enrich,client}.go`). First step of the
  cross-binding "whine if the runtime is uninitialised" pass. The renderer is the
  only FFI entry point not routed through `FFIBackend`; it used to `dlopen` +
  `hs_init` the `.so` itself on first use, which could latch a default `-N` and
  squander the `FFIBackend`'s bus-count `-N` (the RTS is one-shot per process). It
  now checks `hsInitialized()` and returns an error rather than self-initialising
  or panicking, so an `FFIBackend` (via a `Client`) is the sole runtime
  initialiser. Consequently `formatRationalFFI` / `formatRational` / the formula
  printer / `buildDiagnostic` became fallible, and `Client.SetProperties` now
  propagates a runtime-not-initialised error (it builds per-property diagnostics,
  which render predicate thresholds). The three *functions* were exported only so
  external-package tests could reach them — the peers keep them internal (Rust
  private, Python underscore module) and only the `PropertyDiagnostic` *type* is
  public — so they are now lowercase, with the main-module tests reaching them via
  `export_test.go` and `go/excel`'s loader tests comparing formulas structurally
  (`reflect.DeepEqual`) instead of by rendered string. Migration: rendering a
  formula now requires a live `Client`; compare `Formula` values directly.
- **BREAKING (C++): the rational renderer no longer self-initialises the GHC
  runtime — it is vocal (throws `AletheiaException(Ffi)`) when the runtime is
  down — and a null kernel return now throws instead of fabricating `"0"`**
  (`cpp/src/{rational_renderer,client}.cpp`, `cpp/src/detail/rts_init.{hpp,cpp}`).
  The C++ part of the cross-binding "whine if the runtime is uninitialised" pass
  (after Go). Like Go's, the renderer is the only FFI entry point not routed
  through `FfiBackend`; it used to `dlopen` + `hs_init` the `.so` itself on first
  use, latching a default `-N1` that squandered the `FfiBackend`'s bus-count `-N`
  (the RTS is one-shot per process). It now reads the shared
  `detail::rts_initialized()` and throws rather than self-initialising, so
  `make_ffi_backend` is the sole runtime initialiser; the previous silent `"0"`
  null-fallback (the same anti-pattern the pass exists to remove) is now a throw,
  matching Go/Rust. Consequently the render paths react per the established
  render-fail contract: `Check::condition_desc()` and `Client::set_properties`
  *propagate* the runtime-not-initialised error (reachable, pre-backend), while
  `format_enriched_reason` (the eval path, where the runtime is necessarily up
  because the frame was just processed) *degrades* to the formula description
  rather than ever sinking an already-processed frame. The renderer-first
  `rts.cores_mismatch` warning path is therefore gone (the renderer never inits).
  Migration: rendering (a check description or an observed value) now requires an
  `FfiBackend` to exist in the process — create one via `make_ffi_backend` first.
  - **CI (`tools/_ci_steps.py`): the C++ `ctest` + `ubsan ctest` steps now pin
    `ALETHEIA_LIB`** to `<repo>/build/libaletheia-ffi.so`, exactly as the Go and
    Rust steps already do, so every test resolves the one `.so` deterministically
    rather than via the renderer's cwd-relative probe — uniform, cwd-independent
    resolution (the C++ harness was the lone outlier). The relative heuristic stays
    as the bare-`ctest` local-dev fallback.
  - **Tests**: a Catch2 listener (`cpp/tests/rts_setup_listener.cpp`, the C++
    analogue of Go's package `TestMain`) brings the runtime up once per process for
    the render-dependent mock-backend binaries (`unit_tests`, `log_events_tests`)
    that create no real backend; real-backend binaries do not link it. The former
    renderer-first cores-mismatch test is replaced by
    `rts_init_renderer_uninitialized_tests.cpp`, asserting a pre-backend render
    throws the runtime-not-initialised error (its own process, RTS deterministically
    down).
- **BREAKING (Python): the rational renderer no longer self-initialises the GHC
  runtime — it is vocal (raises `FFIError`) when the runtime is down — and a null
  kernel return now raises instead of fabricating `"0"`**
  (`python/aletheia/client/{_enrichment,_ffi,_backend}.py`). The Python part of
  the cross-binding "whine if the runtime is uninitialised" pass (after Go and
  C++). The renderer is the only FFI entry point not routed through `FFIBackend`;
  `_get_or_load_renderer_lib` used to `hs_init` the `.so` itself on first render,
  latching a default `-N1` that squandered the `FFIBackend`'s bus-count `-N` (the
  RTS is one-shot per process) and tracking init state disjointly from `RTSState`.
  The two init paths are now unified behind a single `_ffi.hs_initialized()` source
  of truth; `_get_or_load_renderer_lib` loads symbols only (never `hs_init`), and
  `_format_rational` checks `hs_initialized()` and raises rather than
  self-initialising, so an `FFIBackend` (via an `AletheiaClient`) is the sole
  runtime initialiser. The previous silent `"0"` null-fallback is now a raise,
  matching Go/C++/Rust. Per the established render-fail contract: reachable paths
  (`format_formula` / `build_diagnostic`, which render predicate thresholds)
  *propagate* the runtime-not-initialised error, while `format_enriched_reason`
  (the eval path, runtime necessarily up because the frame was just processed)
  *degrades* to the formula description (still appending `[core: ...]`) rather than
  sinking an already-processed frame. The enrichment helpers were already
  binding-internal (the private `aletheia.client._enrichment` module), so no
  privatisation was needed — already at parity with Go's now-private functions.
  Migration: rendering a formula or an observed value now requires a live
  `AletheiaClient` / `FFIBackend`.
- **BREAKING (Rust): the rational renderer no longer self-initialises the GHC
  runtime — it is vocal (returns the new `Err(Error::RtsNotInitialized)`) when the
  runtime is down** (`rust/src/backend.rs`, `rust/src/error.rs`). The final part of
  the cross-binding "whine if the runtime is uninitialised" pass (after Go #104, C++
  #105, Python #106). The renderer is the only FFI entry point not routed through
  `FfiBackend`; `format_rational` used to call `ensure_rts_for_render` (a self-init
  via the default `-N`) on first use, which could latch GHC defaults and squander the
  `FfiBackend`'s bus-count `-N` (the RTS is one-shot per process). It now checks the
  one-shot `RTS_INIT` latch — `Some` exactly when a real `FfiBackend` has run
  `ensure_rts` — and returns `Error::RtsNotInitialized` rather than self-initialising,
  so a `Client` / `FfiBackend` is the sole runtime initialiser. The error is returned
  *before* the FFI call, because invoking the MAlonzo export with the RTS down is
  undefined behaviour. **A new public `Error::RtsNotInitialized` variant** carries
  this — distinct from `Error::Protocol` (a wire/ABI malfunction) so callers can tell
  a local precondition failure from an actual core problem; this is the additive but
  source-breaking part for exhaustive matchers on `Error`. (The null-return path
  already returned `Err(Error::Protocol)` since an earlier delegation, and the eval
  path already degrades via `reason_without_values` at the caller, so neither
  changed.) Consequently `format_rational` / `Check::condition_desc` /
  `build_diagnostic` / `set_properties` surface `Error::RtsNotInitialized` when no
  backend exists. Migration: rendering a check description, a formula, or an observed
  value now requires a live `Client` / `FfiBackend`; match `Error::RtsNotInitialized`
  (not `Error::Protocol`) for the runtime-down case.
- **BREAKING (Rust): all rational *display* rendering now delegates to the verified
  kernel's `formatℚ` (the `aletheia_format_rational` FFI), and
  `Check::condition_desc()` returns `Result<String, Error>`** (was `&str`)
  (`rust/src/{check,enrich,backend,lib}.rs`). The Rust binding previously rendered
  thresholds and observed signal values with a local reduced-fraction helper
  (`rat_str`), so a threshold of `1/4` printed as `"1/4"`; it
  now renders through the proven kernel — terminating fractions as decimals
  (`"0.25"`), non-terminating as `"p/q"` (`"1/3"`) — byte-identical to the Python,
  Go, and C++ bindings by construction (no local fallback). This covers all three
  rational-rendering surfaces: check-builder condition descriptions, enrichment
  predicate thresholds, and enrichment observed values. Because the kernel renderer
  is a fallible FFI (it needs `libaletheia-ffi.so`), descriptions render *lazily*
  at read-time, so building a check stays infallible (`never_exceeds(v)` etc. keep
  returning `Check`; the fluent `when().then()…within()` chain stays `?`-free) and
  only *reading* `condition_desc()` can fail. `set_properties` propagates a render
  failure (a setup error), while the streaming enrichment path degrades
  best-effort — it never fails an already-processed frame (and the render is
  unreachable there anyway: the values came from an extraction that already loaded
  the library). `rat_str` is retained only for inverted-range *validation error
  messages*, which must report a bad range without depending on a fallible FFI
  load. Migration: `check.condition_desc()` → `check.condition_desc()?` (or
  `.unwrap()`); fractional thresholds/values now print as decimals where they
  terminate. Renderer correctness and canonicality are proven once in Agda
  (`formatℚ-chars-represents` faithfulness + the decimal/fraction shape lemmas +
  `formatRational-canonical`), so redundant per-value rendering tests were removed
  rather than re-asserted per binding.
- **BREAKING (C++): `ExtractionResult::errors` is now `std::vector<SignalError>`**
  (was `std::vector<std::pair<SignalName, std::string>>`)
  (`cpp/include/aletheia/response.hpp`). A new `struct SignalError { SignalName
  name; std::string reason; }` replaces the anonymous pair, matching Go's
  `SignalError{Name, Error}`, Rust's `SignalError{name, reason}`, and Python's
  `errors: Mapping[str, str]` — and the project's no-anonymous-composite-types
  rule (`.first`/`.second` were non-self-documenting). Migration: `err.first` →
  `err.name`, `err.second` → `err.reason`.
- **C++ clang-tidy gate now lints every TU under `cpp/src` (was: a hand-maintained
  glob that silently skipped `src/detail/`)** (`tools/_ci_steps.py`). The gate ran
  `clang-tidy-22 -p build src/*.cpp src/cli/*.cpp` — a non-recursive glob that
  never matched `cpp/src/detail/`, so three files (`loader_utils.cpp`,
  `ffi_logic.cpp`, `rts_init.cpp`) were never linted and accumulated violations
  that passed CI. It now runs `run-clang-tidy-22 -p build cpp/src/`, driven by
  `compile_commands.json`, so the build system is the single source of truth for
  coverage and no subdirectory can be silently dropped again. A new
  `tools.check_clang_tidy_coverage` guard additionally fails CI if any
  `cpp/src/**/*.cpp` is absent from the compile DB (a file forgotten in
  CMakeLists would otherwise be silently unbuilt and unlinted). Fixes the
  previously-unlinted violations this surfaced: `loader_utils.cpp` (5 ZIP-walker
  functions moved from an anonymous namespace to `static`, per the adopted style)
  and `ffi_logic.cpp` (missing direct `#include`s). Internal only — no behavior
  change.
- **Dependency maintenance (Dependabot batch)** — raised dependency floors and a
  CI action major: `actions/checkout` v6 → v7 (all 8 workflow refs), and in
  `python/pyproject.toml` `ruff` ≥0.15.18, `basedpyright` ≥1.39.8, `hypothesis`
  ≥6.155.7, `python-can` ≥4.6.1, `atheris` ≥3.1.0. All patch/minor bumps; the two
  linter floors (ruff, basedpyright) were verified against the full tree
  (`ruff check`/`format`, `basedpyright` 0/0/0, `pytest`, `pylint` 10.00) at the
  new versions before merge. Supersedes Dependabot PRs #88–93.
- **BREAKING (C++): the `ltl::` ≤/≥ predicate builders are renamed
  `at_most` → `less_than_or_equal` and `at_least` → `greater_than_or_equal`**
  (`cpp/include/aletheia/ltl.hpp`). This aligns the C++ builder verbs with the
  Agda `ValuePredicate` constructors (`LessThanOrEqual` / `GreaterThanOrEqual`)
  and with the Python / Go / Rust builders, which already used those names — the
  last cross-binding builder-verb divergence (`predicate_dsl` parity). The
  underlying `Predicate` variant structs were already named `LessThanOrEqual` /
  `GreaterThanOrEqual`; only the free-function builders change. Migration:
  `ltl::at_most(s, v)` → `ltl::less_than_or_equal(s, v)`, `ltl::at_least(s, v)`
  → `ltl::greater_than_or_equal(s, v)`. (`never_exceeds` / `never_below` and the
  wire shape are unaffected.)
- **BREAKING (all bindings): `never_exceeds(v)` is now inclusive — `G(s <= v)`,
  not `G(s < v)`.** A frame with `signal == v` no longer reports a violation. This
  aligns the check vocabulary with the Agda core (`LessThanOrEqual` evaluates
  `x <= v`) and with its dual `never_below` (`>=`) and `stays_between` (inclusive
  on both ends); "never exceeds 220" now correctly lets 220 km/h pass. The
  builders emit the `LessThanOrEqual` predicate instead of `LessThan`, and the
  rendered condition is `"<= v"`. Affects `checks.signal(...).never_exceeds` (Python),
  `CheckSignalBuilder.NeverExceeds` (Go), `check::signal(...).never_exceeds` (C++),
  and `signal(...).never_exceeds` (Rust). To keep the old strict semantics, build
  the predicate directly (`less_than` / `LessThan{}` / `ltl::less_than` /
  `Predicate::LessThan`).
- **BREAKING (Rust): `ExtractionResult.errors` is now `Vec<SignalError>`**
  (was `Vec<String>`). The previous type dropped the per-signal *reason* the core
  emits as `{"name", "error"}`, losing diagnostic information the Python
  (`errors: Mapping[str, str]`) and Go (`SignalError{Name, Error}`) bindings
  retain — a cross-binding parity gap. The new public
  `aletheia::SignalError { name, reason }` carries both. *Migration:* read
  `err.name` (was the bare `String`); the reason is now available as `err.reason`.
- **BREAKING (Rust): `ValidationIssue.severity` and `.code` are now typed enums**
  (`IssueSeverity` / `IssueCode`), were `String`. New public
  `aletheia::IssueSeverity` (`Error`/`Warning`) and `aletheia::IssueCode` (the 21
  Agda `IssueCode` members + `Unknown(String)`), mirroring the Python/Go/C++ typed
  vocabularies. `IssueCode` decoding is lenient (unknown wire codes →
  `IssueCode::Unknown`); `IssueSeverity` decoding is strict (an unrecognised
  severity is a protocol error, matching the peers). *Migration:* match the enum
  instead of comparing strings; `issue.code.as_str()` / `issue.severity.as_str()`
  recover the wire string.
- The review-findings archive (`tools/review_db.py` + `.archive/reviews/schema.yaml`)
  now accepts `rust` as a finding language, for the Rust-binding review round.
- **Mutation testing is promoted to a required (merge-blocking) check, and its CI
  lane is cached.** Previously the `mutation testing` lane in `pr-heavy-lanes.yml`
  ran on every PR but was *advisory* — so a PR could merge with mutation red (a new
  survivor / test gap). This change makes it *ready to require*: the job is renamed
  `mutation testing (advisory)` → `mutation testing`, and it is activated by adding
  that check to the `main` branch ruleset — a follow-up repo-settings step, gated on
  the cache-seeding proof in `docs/development/BRANCH_PR_HYGIENE.md` (not active at
  merge time). Once active it blocks merge: the drift gate is baseline-relative
  (fails only on a collection crash or `observed > baseline`) and the suite is
  deterministic, so it is a stable signal; the lane already ran on every PR, so
  advisory merely discarded a signal we already paid to compute. **Caching** removes
  the two big setup costs that made cold runs ~33 min: the workflow now also runs on
  `push: [main]` so the Mull-from-source build cache (318s) and the FFI build tree
  are written under the default branch where every PR branch can read them
  (feature-branch caches don't cross-pollinate), and the mutation job restores the
  shared build-tree cache so the `.so` build (338s) becomes a Shake no-op when no
  Agda source changed. The C++ `-fpass-plugin` mutation compile is deliberately left
  un-ccache'd (ccache cannot content-hash the Mull plugin, which would risk stale
  mutation objects on a required gate). `push: [main]` runs are exempt from
  `cancel-in-progress` so a rapid second merge cannot kill a cache-seeding run
  before it saves; stability bench stays advisory (genuinely timing-flaky).
- **Unified Excel column handling across all bindings** (Python / Go / C++ / Rust).
  A design review found the loaders had drifted on two axes, both latent (no gated
  test loaded the demo workbook's DBC sheet). **(1) Column presence:** the contract
  is now uniform — lookup is by header name, all columns are read, and an *absent
  column behaves exactly like an empty cell* (required fields error, optional fields
  default). The `Extended` column is now optional everywhere (**BREAKING (Go)** —
  `excel.LoadDbc` previously *required* it and errored on its absence; C++ now reads
  all columns rather than only the first *N*). **(2) Cell coercion:** all bindings
  are now strict like the Python reference — a number stored as *text* (an Excel
  column formatted as Text) is rejected for a numeric field rather than silently
  parsed (**BREAKING (Go, C++)** — their loaders previously stringified every cell
  and parsed leniently; they are now type-aware via `excelize.GetCellType` /
  OpenXLSX `XLValueType`). `Message ID` keeps accepting a hex string (`0x100`). Every
  binding gains a gated test that loads the shared `examples/demo/demo_workbook.xlsx`
  DBC sheet (locking the optional-`Extended` contract) and a number-as-text rejection
  test (locking strict coercion).
- **BREAKING (Go).** The check-builder value methods now return `(CheckResult, error)`
  and reject non-finite / overflowing values instead of silently clamping them to
  `0/1`. `CheckSignalBuilder.NeverExceeds` / `NeverBelow` / `NeverEquals` and
  `CheckSignalPredicate.Always` previously returned a bare `CheckResult` and routed
  their value through the clamping `RationalFromFloat`, so a `NaN` / `±Inf` /
  int64-overflowing value produced a silent `0/1` predicate — a cross-binding
  parity bug, since the Python (`to_predicate_fraction`) and C++ (`Rational::from_double`)
  check paths raise/throw on such input. All terminal check builders are now
  uniformly fallible (matching `StaysBetween` / `SettlesBetween().Within()` /
  the when/then `.Within()`, which already returned errors): the value methods
  funnel through the error-returning `FloatToRational`, and the fluent chains
  capture a conversion failure (a new `valueErr`, sibling to `rangeErr`) and
  surface it at their terminal `(CheckResult, error)` method. This fixes both the
  YAML and Excel check loaders, which dispatch through these builders. The dead
  internal `physicalAsRational` helper is removed; `RationalFromFloat` (the
  manual-construction convenience for compile-time literals) now **panics** on a
  non-finite / int64-overflowing value instead of clamping to `0/1` (the
  `regexp.MustCompile` convention), removing the last silent-clamp path while
  keeping its bare-value signature for inline struct-literal use.
- `check-changelog` now also watches `rust/src/` (the Rust binding's public
  surface), so Rust public-API changes require a `CHANGELOG.md` entry like the
  other bindings — closing a gap left by the original G.2 broadening.
- **`check-changelog` now covers build, CI, and tooling changes, not just the
  public API.** `tools/check_changelog.py` previously required a `CHANGELOG.md`
  entry only when `python/aletheia/`, `go/aletheia/*.go`, `cpp/include/aletheia/`,
  or the FFI export snapshot changed. It now also requires one for changes under
  `Shakefile.hs`, `shake.cabal`, `aletheia.agda-lib`, `haskell-shim/`, `tools/`,
  and `.github/workflows/` (Agda `src/` is excluded — behavioral changes there
  reach users via the bindings; Markdown docs and test files are exempt). For a
  routine infra edit or a bot dependency bump with no observable behavior change,
  a one-line `### Changed` note ("internal — no behavior change") satisfies the
  gate. (DEFERRED_ITEMS G.2.)
- **The build-staleness self-test is scheduled on build-graph changes, not every
  PR.** `tools/run_ci.py`'s `build` step previously always ran
  `check_build_incremental`, which forces two `.so` relinks (an edit probe and its
  revert) — fast locally but ~260s on a 4-core CI runner, dominating an otherwise
  warm build. That gate verifies the build *graph* (can a source change reach the
  `.so`?), which only build-graph files (`Shakefile.hs`, `shake.cabal`, the
  `haskell-shim/` incl. its `.cabal`, `aletheia.agda-lib`) can regress. The
  `build` step now runs the gate only when the diff vs `main` touches one of those
  (the local `main` ref, matching the IWYU convention) (`--build-staleness=auto`, the
  default), always on `push:main` (the backstop, `--build-staleness=always`), or
  never (`--build-staleness=never`); otherwise it runs a plain
  `cabal run shake -- build` (a warm cache → near no-op). Trade-off: a build-graph
  regression that bypasses the PR check (e.g. a `--no-verify` push) is caught
  post-merge on `main` rather than on the PR — acceptable because a plain
  incremental build is content-hash-driven and self-corrects a bad cache; only a
  build-*system* change defeats that, and that is exactly what re-arms the gate.
- **The build-staleness gate is stronger.** `tools/check_build_incremental.py`
  now probes **two** structurally distant runtime modules
  (`Protocol/ResponseFormat` + `DBC/Formatter`) rather than one — a graph bug that
  breaks change-propagation for only one subtree is caught because both distinct
  probe tokens must reach the `.so` — and adds an **incrementality** assertion: a
  no-op build must not relink the `.so` (mtime stable). The staleness-only check
  would have passed a regression back to the always-full-rebuild sledgehammer;
  this catches it, structurally (was the artifact rewritten?), never by wall-clock.
- **CI caches compiled C++ objects with `ccache`.** `cpp/CMakeLists.txt`
  auto-enables ccache via `CMAKE_CXX_COMPILER_LAUNCHER` wherever it is on `PATH`
  (a no-op otherwise, so local builds are unaffected), and `pr-full-ci.yml`
  persists `~/.ccache` across runs. The C++ lanes reconfigure a fresh build dir
  each run (`ctest` ~394s, the UBSan lane ~689s), recompiling the same
  translation units cold; a warm ccache makes those recompiles near-instant. The
  build-tree cache (above) handles Agda/Haskell; this handles C++.
- **CI restores an incremental build tree, so a re-push is no longer a cold
  rebuild.** `.github/workflows/pr-full-ci.yml` now caches `build/` (Agda
  `.agdai` + generated MAlonzo `.hs`) and `dist-newstyle/` (the cabal
  foreign-library build) across runs, keyed on the GHC / Agda / stdlib versions.
  Restoring the prior tree lets the staleness-safe incremental build rebuild only
  what a commit changed — the cold `build` step (~384s) drops to ~23s on a cache
  hit (measured), and the `agda gates` / `iwyu` steps reuse warm interface files.
  Safe because the build keys on content, not mtime: `actions/cache` resets every
  file's mtime on restore, which Shake (`ChangeModtimeAndDigest`) and GHC
  (`mi_src_hash`) defeat via content hashing, with the build's own staleness gate
  as the backstop (a stale `.so` fails the run). A same-branch re-push restores
  its own cache immediately; a brand-new PR warms up after one `push:main` run
  seeds the tree. (C++ `ccache` and finer step parallelism are tracked as
  follow-ups.)
- **The local pre-push hook runs the CI sweep in parallel.** `tools/install_hooks.py`
  now generates a pre-push hook that invokes `tools/run_ci.py --parallel` (the
  memory-safe `heavy_limit=2` default; tune with `ALETHEIA_CI_HEAVY_LIMIT`), so the
  pre-push gate uses the lane scheduler instead of running serially. Re-run
  `python tools/install_hooks.py` to update an already-installed hook — the
  installer is now content-aware (it refreshes a hook whose template changed,
  rather than skipping whenever its marker is merely present).
- **`tools/run_ci.py` split along the catalog seam.** The step catalog — the
  registration helpers (`_run_agda_gates` / `_run_binding_tests` / `_run_lints` /
  `_run_gha_checks` / `_run_opt_in_lanes`, behind a public `register_all_steps`)
  plus the constants that classify them (`AGDA_SHAKE_TARGETS`, `HEAVY_STEPS`,
  `build_prereq_cmd`) — moved to a new `tools/_ci_steps.py`, leaving `run_ci.py`
  as the orchestration core (`Runner`, `RunContext`, options, `main`). No
  behavior change: same steps, same lanes, same exit codes. It takes `run_ci.py`
  from 999 to 616 lines (clear of the 1000-line pylint `max-module-lines`
  ceiling, which the next gate addition would otherwise have tripped) and moves
  the part that grows with every new gate out of the core.
- **C++ `IBackend` streaming endpoints are now pure-virtual.**
  `send_error_binary`, `send_remote_binary`, `start_stream_binary`,
  `end_stream_binary`, `format_dbc_binary`, and `extract_signals_binary`
  (`cpp/include/aletheia/backend.hpp`) previously carried base-class defaults
  that routed through the JSON `process()` path. That path mirrored streaming
  commands the Agda core no longer accepts (and `send_error` / `send_remote`
  never had a core JSON command at all), so the defaults were dead — and, for
  `send_error` / `send_remote`, emitted a wire shape the core rejects. They now
  have no default: every backend states how it streams, via the binary FFI
  (`FfiBackend`) or test sentinels (`MockBackend`). **Migration**: a custom
  `IBackend` implementation that relied on the JSON-fallback defaults must now
  implement these six methods.

### Added

- **`tools/check_docs.py` — a documentation-accuracy gate, wired into
  `tools/run_ci.py` as `check-docs`.** It scans every tracked Markdown file and
  fails on: broken relative links (`[text](target)` whose target is missing),
  broken header anchors (`#slug` with no matching header, using GitHub's
  slug rules), and transient/internal labels or links into the private agent
  memory store in the living docs (`docs/` + the READMEs; the historical logs
  CHANGELOG / PROJECT_STATUS are link-checked but not label-scoped). Code
  fences are skipped so a `[](const T& e)` lambda is not mistaken for a link.
- **Byte-exact furthest-failure parser positions.** The verified
  parser combinators now thread a *failure watermark* — the deepest
  position any parse attempt reached — through every parse
  (`Parser A = Position → List Char → Position × Maybe (ParseResult A)`;
  `<|>` merges failed alternatives' depths via the new `Position.maxₚ`,
  `many` keeps the depth of the element attempt it swallowed). Every DBC
  text/JSON parse error now pinpoints the exact offending byte:
  - `dbc_text_parse_failure` carries structured `line`/`column` (the
    watermark) and its message reads `DBC text parse failed at line N,
    column M`.
  - `dbc_text_trailing_input` reports the watermark in `line`/`column`
    (byte-exact *inside* the first unparseable statement — previously it
    could only name the statement's first character) plus new
    `statement_line`/`statement_column` for the statement start; message:
    `parse failed at line X, column Y (first unparseable statement starts
    at line N, column M)`.
  - `dispatch_invalid_json` gains the same `line`/`column` extras (the
    JSON protocol parser shares the combinators); message: `invalid JSON:
    parse failed at line N, column M`.
  Live acceptance: `validate` on a DBC whose `BO_` line has a corrupted
  DLC now reports the corrupted byte itself (`line 40, column 22`) instead
  of the statement start (`column 1`); the CLI parity scenario pins the
  full positioned message across all three CLIs. Error *codes* are
  unchanged, extras are additive, and no binding API changes — the
  ~100-module proof-tree restatement moves every parser-result lemma to
  the outcome level (`proj₂`), with the universal roundtrip theorem
  (`parseText (formatText d) ≡ inj₂ d`) surviving verbatim.
  Measured cost (paired, same host, back-to-back): `parseDBCText`
  200-msg 1.113s→1.149s (+3.2%), 1000-msg 28.907s→30.381s (+5.1%) —
  confined to the DBC-text cold path; the streaming hot path is
  untouched. PROTOCOL.md documents the watermark semantics.

- **`check-install-freshness` — a `run_ci` gate that makes deployed-kernel
  rot loud** (`tools/check_install_freshness.py`). Both deployment surfaces
  copy `build/libaletheia-ffi.so` out of the tree and then rot silently as
  the tree moves on (the release-packaging `dist/` sat three weeks stale
  after v2.0.0; the local install was partial for five months, above). The
  gate verifies any existing copy is the *same build* as `build/`'s
  library — compared by GNU build-id (strip/patchelf legitimately change
  the deployed bytes; the build-id note survives both; SHA-256 fallback
  when absent) — and that an installed library has its completed
  `_install_config.py`. The install target now writes a repo-local,
  gitignored `.install-receipt` (prefix, library path, config path) that
  the gate reads instead of *guessing* the prefix — a custom-`PREFIX`
  install stays under watch even when `PREFIX` is no longer exported;
  `uninstall` clears the receipt. Absent artifacts skip (CI runners have
  neither). 12 hermetic tests (both polarities per artifact class,
  receipt-precedence discriminator included).

- **Two Agda leaf modules decouple the error/serializer closure from the
  parser combinators (prep for the parser-position redesign) — pure code
  motion, no behavior change.** `Aletheia.Parser.Position` (the Position
  record + advance functions) and `Aletheia.Parser.CharClass`
  (`isUpper` / `isAlphaNum`) move out of `Aletheia.Parser.Combinators`,
  which re-exports both so parser-side importers are unaffected. Four
  imports narrow to break the remaining transitive routes:
  `Aletheia.Error` and `Aletheia.DBC.Identifier` to the new leaves, and
  `Aletheia.Protocol.ResponseFormat` + `Aletheia.Protocol.Message` from
  the `Protocol.JSON` umbrella (which re-exports the JSON *parser*) down
  to `Protocol.JSON.Types` — they only build JSON values. Verified by
  transitive import walk: the closures of `Error` (17 modules),
  `ResponseFormat` (34, was 39), and `Message` (24) no longer contain
  the combinator library, so the upcoming combinator result-type work
  stops re-checking the whole error/response vocabulary on every
  iteration. Module count 275 → 277 (both new modules
  `--safe --without-K`; counts synced in CLAUDE.md).

- **Go: `DispatchThen` — the third exported loader-dispatch helper**
  (`go/aletheia/loader.go`), completing the family started by
  `DispatchSimple` / `DispatchWhen`: maps a then-condition keyword
  (`equals` / `exceeds` / `stays_between`) to the bounded-obligation builder
  call. The YAML and Excel loaders' previously copy-pasted three-arm switches
  now delegate to it (presence checks and value extraction stay
  loader-specific; the Excel loader is a separate Go module, which is why the
  helper is exported — the same reason the other two are). Direct unit tests
  cover all three arms plus the unknown-condition reject
  (`go/aletheia/loader_test.go`).

- **CI: a `check-proof-coverage` gate makes the Agda proof checker provably
  exhaustive — internal, no behavior change.** `check-properties` walks a
  hand-maintained `proofModules` list (Shakefile.hs); a proof module missing
  from it was type-checked only as a side effect of the whole-tree `iwyu --all`
  pass, so `cabal run shake -- check-properties` (the documented proof gate)
  silently skipped it. Two such modules existed — `DBC.TextFormatter.Properties`
  and `Protocol.Adequacy.StreamingWarm` (the lemma that discharges
  `warm-cache-agreement`'s `AllCached` premise) — and are now added to
  `proofModules`. The new gate (`tools/check_proof_coverage.py`, folded into
  `run_ci`'s Agda-gate step and a `cabal run shake -- check-proof-coverage`
  target) asserts that `closure(proofModules) ∪ closure(build)` covers every
  `src/**.agda`, failing CI the instant a future proof module is not wired into
  a dedicated gate. It reads `proofModules` from Shakefile.hs (single source of
  truth — no second copy to drift).
- **`aletheia_parse_decimal` FFI export — the kernel single source of truth for
  decimal→rational.** A new Agda module `Aletheia.DBC.TextParser.DecimalEntry`
  (`parseDecimal : String → Maybe ℚ`) parses a decimal string into the exact
  rational it denotes by delegating wholesale to the verified `parseDecRat`
  grammar (`-?digits[.digits+]`; no `'+'`, no leading `'.'`, no exponent) and
  requiring full consumption (trailing input is rejected, unlike the library
  `runParser`). The Haskell shim (`aletheia_parse_decimal`) returns the bindings'
  wire shape — bare `{"numerator":N,"denominator":D}` on success (the exact form
  `decode_wire_rational` consumes), a `{"status":"error",...}` envelope keyed by
  `message` with code `decimal_parse_failed` / `decimal_overflow` and the
  offending `input` echoed on failure — catching Int64 overflow at the marshaling
  boundary via `toIntegralSized` (the kernel rational is unbounded). This is the
  input half of the float principle: a decimal is an exact `DecRat`
  (denominator `2^a·5^b`), never a float. The accepted grammar now lives once in
  the verified kernel, so it cannot drift between bindings. Phase 0 ships the
  export + a proof; the per-binding rewire (deleting the float→rational
  heuristics) follows. (`src/Aletheia/DBC/TextParser/DecimalEntry.agda`,
  `haskell-shim/src/AletheiaFFI.hs`, `haskell-shim/src/AletheiaFFI/Marshal.hs`.)
- **`parseDecimal` is proven a weak inverse of the decimal emitter**
  (`src/Aletheia/DBC/TextParser/DecimalEntry/Properties.agda`):
  `parseDecimal-chars (showDecRat-dec-chars d) ≡ just d` (every `DecRat` recovered
  from its canonical decimal text), a `map toℚ` corollary at the ℚ layer the FFI
  returns, and `parseDecimal-chars (showInt-chars z) ≡ just (fromℤ z)` (the
  common user-typed bare integer the emitter never prints as `"42"`). Both
  discharge from the already-proven suffix-aware roundtrips in
  `…DecRatParse.Properties.Phase6Suffix` specialised to full consumption; the
  module is registered in `Shakefile.hs` `proofModules` so `check-properties`
  gates it. A raw-ctypes smoke test (`python/tests/test_parse_decimal_ffi.py`)
  covers the shim marshaling path end-to-end (success / parse-failure / Int64
  overflow). Module count 273 → 275.
- **Rust binding now emits `extraction.process_failed` / `extraction.parse_failed`**
  (`rust/src/lib.rs`), closing a logging-parity gap with Go/Python/C++. The public
  `extract_signals` — and, through it, the violation-enrichment loop (`extract_all`
  funnels through `extract_signals`, mirroring Go's shared `extractSignalsLocked`
  primitive) — now logs a `Warn` event with `canId` + `error` fields when the
  backend call fails at the FFI/process boundary, and when a well-formed response
  cannot be decoded; the single pair of emit sites covers both the public API and
  enrichment. The `rust/src/log.rs` event-vocabulary doc is corrected to match
  reality: the two enrichment events and the two extraction events are marked
  emitted (the enrichment pair was already wired but still filed under "not
  emitted"), leaving only the three `cache.*` events un-emitted — those instrument
  an extraction-result memoization cache this binding deliberately does not
  implement (a perf optimization, not part of the cross-binding contract; see
  FEATURE_MATRIX `violation_enrichment`). The Go package doc (`go/aletheia/doc.go`)
  is likewise corrected to list all 16 events (it had omitted
  `endstream.uncached_atom`). New Rust behavioural tests assert each extraction
  event fires (process vs parse) without the other; the `log_events` parity gate's
  emitted-set is extended in lockstep.
- **Rust documentation is now gated in CI** (`tools/_ci_steps.py`): the rust lint
  section runs `RUSTDOCFLAGS="-D warnings" cargo doc --no-deps
  --document-private-items` for both the main crate (with `--all-features`) and the
  `rust/excel/` crate, so broken or redundant intra-doc links fail the build
  instead of accumulating silently (the gap that let several warnings pile up
  unnoticed). The pre-existing warnings this surfaced are fixed in the same change:
  `log.rs` (`[Client]` and `[ALL]` now link via their paths), `yaml.rs`
  (`MAX_INPUT_BYTES` demoted from a public→private link to a plain code span), and
  `async_client.rs` (a redundant explicit `[Client]` target dropped; the
  `AsyncClient` link in `lib.rs` resolves once `--all-features` is on). Doc/CI only
  — no runtime or API change. `cargo doc --no-deps` runs no doctests, so the gate
  needs no `.so`.
- **Async backend dependency-injection seam for the Rust binding** (`rust/`,
  feature `async`): `ClientBuilder::build_async_with_backend(Box<dyn Backend +
  Send>)` builds an `AsyncClient` over an injected `Backend` without loading
  `libaletheia-ffi.so` — the async analogue of the sync
  `ClientBuilder::build_with_backend` shipped earlier. The injected backend is
  moved to the async worker thread (where the `!Send` sync `Client` lives), so it
  carries a `+ Send` bound — the only difference from the sync seam; the
  `Backend` trait itself stays unbounded (the box coerces, dropping the marker).
  Both async builders now route through a single client-factory `spawn`, so
  `build_async` is behaviour-unchanged. This closes the sync↔async injection
  asymmetry and lets the in-flight cancellation contract be tested
  deterministically with a `Send` gating backend (no `.so`, no sleeps): the test
  drives a call to the point the worker is mid-FFI — past the queued-cancel guard
  — then drops the future and asserts the worker is not wedged and a fresh call
  still succeeds. (FEATURE_MATRIX `backend_di_seam` Rust note extended; the
  public `MockBackend` is `Rc`-based and intentionally `!Send`, so the gating
  double is test-local.)
- **Fluent comparison-predicate builders for the full Agda comparison family,
  Go + Rust** (`go/`, `rust/`; new FEATURE_MATRIX `predicate_dsl` row →
  `implemented` ×4). Python (`aletheia.dsl.Signal`) and C++ (`ltl::`) already
  exposed the full `ValuePredicate` comparison family —
  `equals` / `less_than` / `greater_than` and the at-or-below / at-or-above pair
  (`src/Aletheia/LTL/SignalPredicate/Types.agda`) — as a fluent surface; Go and
  Rust did not, so the cross-binding contract was never pinned. Now:
  - **Go** — `aletheia.Signal("X").LessThanOrEqual(v)` etc. via a new
    `SignalBuilder` (`Signal(name) SignalBuilder` + the five comparison methods),
    the formula-level predicate DSL, distinct from the higher-level check-DSL
    (`CheckSignal`).
  - **Rust** — `Predicate::less_than_or_equal(sig, v)` etc., five `#[must_use]`
    associated constructors taking `impl Into<String>` / `impl Into<Rational>`
    (mirroring C++'s free-function shape; Go/Python mirror each other's method
    chain — same capability, native idiom per binding).

  Each is sugar over the existing predicate structs/variants (a struct-equality
  test in each binding guards against a method being wired to the wrong
  constructor), so the wire shape and `FormatFormula` rendering are unchanged.
  The matrix row pins the `less_than` representative; the gate fails on its
  silent removal in any binding. The ≤/≥ builders are now spelled
  `less_than_or_equal` / `greater_than_or_equal` uniformly across all four
  bindings — the C++ `at_most` / `at_least` builders were renamed to match (see
  the BREAKING entry under Changed).
- **Lazy batch frame send across Go, C++, and Rust** (`go/`, `cpp/`, `rust/`;
  FEATURE_MATRIX `lazy_streaming_batch` → `implemented` ×4, joining Python — and
  emptying the matrix of its last `not_applicable` cell). A streaming variant of
  the eager batch send that pulls one frame from the source and yields one
  outcome at a time, materializing neither the whole input nor the whole response
  set — for large or live sources (a log reader, a socket) where full
  materialization is wasteful or impossible. Each binding presents it
  idiomatically:
  - **Go** — `Client.SendFramesSeq(ctx, iter.Seq[Frame]) iter.Seq2[FrameResponse, error]`,
    a Go 1.23 range-over-func (the lazy variant of `SendFrames`, as
    `strings.SplitSeq` is of `Split`; wrap a slice with `slices.Values`). It
    locks per frame rather than holding the eager batch-atomic lock, so a slow
    consumer never starves `Close`.
  - **C++** — `AletheiaClient::send_frames_lazy(stop, R) -> std::generator<Result<FrameResponse>>`,
    a C++23 coroutine over any `std::ranges::input_range` of `Frame`; it yields
    `std::expected`, forwarding cancellation as-is and prefixing the frame index
    on other errors (mirroring `send_frames`).
  - **Rust** — sync `Client::send_frames_iter(impl IntoIterator<Item = Frame>) -> impl Iterator<Item = Result<FrameResponse, Error>>`
    and async `AsyncClient::send_frames_stream(impl IntoIterator<Item = Frame>) -> impl Stream<Item = Result<FrameResponse, Error>>`
    (built on `futures-util`'s `unfold`, added under the existing runtime-agnostic
    `async` feature; the input iterator is `Send`-bound so the returned stream
    stays `tokio::spawn`-able). The async form is named `send_frames_stream`, not `_iter`,
    because a `Stream` is the async-iterator trait, not `core::iter::Iterator` —
    the `_iter` suffix is reserved for `Iterator`-returning methods.

  All three reuse the per-frame `send_frame` primitive that the eager form uses
  (an eager-vs-lazy equivalence test in each binding guards against drift), yield
  one success-or-error per frame and fuse after the first error, and honor the
  commit-prefix-and-report cancellation contract — stop pulling and the remaining
  frames are never sent while the yielded prefix stays committed (see
  `docs/architecture/CANCELLATION.md` §3.2–§3.4). The terminal error is tagged
  with the failing frame's 0-based batch index so the caller can locate it (Go /
  C++ via a `frame N:` message prefix; Rust via a new structured
  `Error::Frame { index, source }` variant; Python via `BatchError.frame_index`).
  Python's eager *raise* stays the one idiomatic divergence; the other three
  yield the error in-band (`std::expected` / `(T, error)` / `Result`).
- **Rust batch error now carries the frame index** (`rust/`). `Client::send_frames`
  and `AsyncClient::send_frames` (the eager forms) now wrap a per-frame failure in
  the new `Error::Frame { index, source }` variant — previously the raw
  underlying error, which dropped the batch position. This aligns Rust with the
  Go / C++ eager forms (which already prefixed `frame N:`) and with the new lazy
  forms. Behavior change: matching the specific inner variant now goes through
  `Error::Frame.source`.

- **Rust backend dependency-injection seam + test mock** (`rust/`; `mock_backend` + `backend_di_seam` →
  rust **36/40**). A public, open `trait Backend` (`rust/src/backend.rs`) is the
  FFI-boundary abstraction the `Client` is built on; the `Client` now holds a
  `Box<dyn Backend>`, injected via `Client::with_backend` or
  `ClientBuilder::build_with_backend`. The production `FfiBackend` (loads the
  `.so`) and a new public, `Clone`-able `MockBackend` (`rust/src/mock.rs`) both
  implement it; the mock queues responses (`respond_json` / `respond_bytes` /
  `respond_err`) and records the cross-binding `<binary:OP>` sentinels for
  inspection via `captured()`, so the `Client` can be unit-tested without loading
  `libaletheia-ffi.so` (`rust/tests/mock_backend.rs`). Mirrors the Go / Python
  `Backend` + `MockBackend` and the C++ `IBackend`, in idiomatic Rust form:
  **RAII** (the backend owns its session handle and closes it in `Drop`, so the
  trait has no `init`/`close`/`state` and never traffics in a raw pointer);
  **shared interior-mutable mock state** (`Rc<RefCell<…>>` + `Clone`, so a test
  keeps one clone to assert on while the `Client` owns another); and
  **error-on-exhaustion** (matching Go, vs the Python/C++ default-response — no
  fabricated mock behavior). The behavior-preserving extraction of the FFI
  machinery into `FfiBackend` leaves the existing public `Client` API unchanged.
- **Always-on gate: tools-importing tests must be mutmut-ignored.**
  `tools/check_mutation_setup.py` (in the required Shake `check` sweep, not the
  advisory mutation lane) now also verifies that every `python/tests/test_*.py`
  importing the repo-root `tools` package appears as `--ignore=tests/<name>` in
  `[tool.mutmut].pytest_add_cli_args`. This catches the exact drift that crash-
  killed the Python mutation lane (see Fixed) — a new `tools`-importing test
  landing without its ignore — at PR time in a required check, instead of in the
  advisory lane where it went unnoticed for days. Forward-revert verified.
- Rust async client (`rust/`) — `AsyncClient`, a
  runtime-agnostic async mirror of `Client`, behind the opt-in `async` cargo
  feature. The sync `Client` is `!Send` (a thread-pinned `StreamState`), so
  `AsyncClient` owns it on a dedicated **worker thread** and dispatches jobs over
  a channel: each `async` method sends a closure (capturing its owned arguments
  and a `oneshot` reply sender) and `.await`s the reply. The handle is a
  `Mutex`-wrapped channel sender, so `AsyncClient` is `Send + Sync` — its
  borrowing futures are `Send`, so it can be `tokio::spawn`ed on a multi-thread
  runtime (`mpsc::Sender` is `Send` but `!Sync`, hence the `Mutex`). It is
  runtime-agnostic — only the reply `oneshot` (from `futures-channel`) is used,
  never a runtime — so it works under tokio / async-std / smol. **Cancellation** = dropping a method's future
  (the idiomatic Rust cancel; no `ctx`/`stop_token` first parameter): a queued
  (not-yet-started) job is skipped via a `Sender::is_canceled()` self-guard with
  no FFI call (no frame committed); an in-flight FFI call runs to completion and
  advances `StreamState` (commit-prefix, no rollback) — honoring the
  `docs/architecture/CANCELLATION.md` contract (now with a Rust §2.4). `Drop`
  closes the channel then joins the worker, so the `Client`'s `aletheia_close`
  runs on its own thread. Built via `ClientBuilder::build_async()` /
  `AsyncClient::new()`. Flips the `cancellation_contract` `rust` row to
  `implemented` (rust 34/40).
- Rust violation enrichment (`rust/`) — violations now
  carry a client-side `Enrichment` (referenced signals + values, formula
  description, and a combined `enriched_reason`). The verified core emits only a
  raw reason, so — like the Go (`enrich.go`) and Python (`_enrichment.py`)
  bindings — each registered formula yields a per-property diagnostic (signals it
  references + a human-readable description) cached at `set_properties`; on a
  violation the signals are paired with their last-known values (extracted from
  the violating frame during streaming, or from the last frame seen per CAN id at
  end-of-stream) to build the `Enrichment` on `PropertyResult`. Emits the
  `enrichment.property_index_oob` / `enrichment.extraction_failed` log events.
  Rational values render via the same local renderer as the check DSL's
  `condition_desc` (its reduced-fraction form), keeping the two surfaces
  consistent. Removes the previously-dormant wire-`enrichment` decode (the core
  never sent that field). The extraction cache / `cache.*` events are
  deliberately not implemented (an internal perf optimization, not part of the
  enrichment contract — mirroring the Go/C++ scope). Flips the
  `violation_enrichment` `rust` row to `implemented` (rust 33/40).
- Rust ergonomics & runtime infra (`rust/`) — a
  `Client::builder()` adding **structured logging** and **RTS-cores
  configuration**. `.logger(...)` takes a callback `Logger` (a bare
  `Fn(&LogRecord) + Send + Sync` works via a blanket impl; level + event +
  typed fields), with `.min_level(...)` filtering; the client emits the shared
  cross-binding event vocabulary (`docs/LOG_EVENTS.yaml`), enforced by the new
  `rust/tests/log_events.rs` parity gate. `.rts_cores(k)` passes `+RTS -N<k>
  -RTS` to `hs_init`; the RTS is process-global, so the first client latches the
  count and a later mismatching request is a no-op plus a `rts.cores_mismatch`
  warning (mirrors Go `WithRTSCores` / C++ `make_ffi_backend`). Flips the
  `structured_logging` and `rts_cores_config` `rust` rows to `implemented`
  (rust 32/40); `lazy_streaming_batch` is recorded `not_applicable` for Rust
  (the existing `send_frames(&[Frame])` already delivers commit-prefix-and-report
  over a caller-materialized slice, mirroring the Go / C++ disposition).
- Rust Excel check + DBC loader (`rust/excel/`) — a separate
  `aletheia-excel` crate (mirroring Go's `go/excel/` module) so the `.xlsx`
  dependency chain (calamine + rust_xlsxwriter + zip) stays optional for core users.
  `load_checks_from_excel` / `load_dbc_from_excel` / `create_template` read the
  `Checks` / `When-Then` / `DBC` sheets and compile each row through the `check` DSL
  (checks) or into a typed `Dbc` (signals), matching the Python (`excel_loader`) and
  Go (`excel`) loaders so a workbook is portable across bindings — proven by a test
  that loads the shared `examples/demo/demo_workbook.xlsx` fixture. At the trust
  boundary it enforces the shared 64 MiB bound (raw size + a ZIP-bomb guard summing
  uncompressed entry sizes with a saturating add) and rejects symlink / non-regular
  paths. The `feature_matrix` parity gate now resolves a `pkg:symbol` entry against
  `rust/<pkg>/src` (mirroring the Go gate), flipping the `excel_check_loader` `rust`
  row to `implemented` (rust 30/40).
- Rust YAML check loader (`rust/`) — `load_checks_from_yaml`
  and `load_checks_from_yaml_file` parse a set of named checks from a YAML document
  into typed `Check`s, behind the default-on `yaml` cargo feature (disable with
  `--no-default-features`). The schema matches the Python (`load_checks`) and Go
  (`LoadChecksFromYAML`) loaders — a single `checks:` list of single-signal
  (`signal` + `condition` + operands) or causal `when`/`then` entries (with a
  top-level `within_ms`) — so a check file is portable across bindings (proven by a
  test that loads the shared `go/aletheia/testdata/doc_examples/checks.yaml`
  fixture). Decimal values go through a new `Rational::from_f64`, which replicates
  the cross-binding `round(v × 10⁹), 10⁹` convention (reduced to lowest terms) and
  fails on a non-finite / overflowing value rather than clamping — matching the
  Python and C++ loaders. Unknown YAML keys are ignored, as in the peers. At the
  trust boundary it enforces the shared 64 MiB input-length bound (on both inline
  content and files, checked before reading) and rejects symbolic-link / non-regular
  file paths — matching the Go and Python loaders' adversarial-input hardening. Flips
  the `yaml_check_loader` `rust` row to `implemented` (rust 29/40).
- Rust check DSL (`rust/`) — a fluent `check` module that
  compiles domain-friendly checks to LTL `Formula`s plus display metadata:
  `check::signal("Speed").never_exceeds(120)` (+ `never_below`/`stays_between`/
  `never_equals`/`equals().always()`/`settles_between().within()`) and the causal
  `check::when("Brake").exceeds(50).then("Light").equals(1).within(100)`. Numeric
  values take `impl Into<Rational>` (an `i64` literal works directly; fractions via
  `Rational::new`). `Check` carries `name`/`severity`/`condition_desc` metadata
  (`named`/`with_severity`, immutable). `Client::add_checks(&[Check])` binds the
  checks' formulas (the verdict `property_index` is the check's position; metadata
  stays client-side). The raw LTL combinators remain on `Formula` for power users.
  Flips the `check_dsl` / `add_checks` `rust` rows to `implemented` (rust 28/40).
- Rust frame construction (`rust/`) — `Client::build_frame`
  and `Client::update_frame` encode named signal values into a CAN payload via the
  binary build/update FFI (`aletheia_build_frame_bin` / `aletheia_update_frame_bin`);
  they take a typed `&DbcMessage` (from a parsed `Dbc`) and resolve signal
  names→indices against it — the idiomatic-Rust surface (no hidden client-side DBC
  cache, unlike the stateful peers) for the same capability. Adds
  `Client::send_frames(&[Frame])` for batch submission, returning
  `(Vec<FrameResponse>, Option<Error>)` — all responses processed plus the first
  transport error if it stopped early (partial results preserved). `extract_signals`
  is confirmed mux-aware (the core selects mux-dependent signals by the frame's mux
  value). Flips the `build_frame` / `update_frame` / `mux_extraction` /
  `batch_frame_send` `rust` rows to `implemented` (rust now 26/40).
- Rust DBC serialize side (`rust/`, write side) — `Client::parse_dbc` (load a typed `Dbc` via the JSON path),
  `Client::validate_dbc` (→ `ValidationResult { has_errors, issues }`), and
  `Client::format_dbc_text` (render a `Dbc` to `.dbc` text), backed by a
  `Dbc` → canonical-JSON serializer (the inverse of the read-side decoders;
  `Rational` int-when-den=1, flat presence, `extended` emitted only when true).
  Verified by end-to-end round-trips against the comprehensive `kitchen_sink`
  fixture (`parse_dbc_text` → `parse_dbc` and → `format_dbc_text` → `parse_dbc_text`
  are both the identity). Flips the last 3 `rust` rows (`parse_dbc_json`,
  `validate_dbc`, `dbc_text_format`) to `implemented` — the Rust binding now
  covers all 11 DBC-document rows.
- Rust typed DBC attribute vocabulary (`rust/`, tier-2) —
  `Dbc.attributes` is now the typed `Attribute` enum (`Definition` / `Default` /
  `Assignment`) over `AttrType` (`Int` / `Float` / `String` / `Enum` / `Hex`),
  `AttrValue`, `AttrScope` (7), and `AttrTarget` (7, with `extended` on the
  CAN-id-bearing targets), replacing the raw-JSON pass-through — mirroring the
  Go `DBCAttr*` / Python `DBCAttr*` models (`Int`/`Hex` bounds are integers,
  `Float` bounds rational). Flips the `dbc_metadata_tier2` `rust` row to
  `implemented`.
- Rust typed DBC document model (`rust/`, read side) — a
  typed `Dbc` / `DbcMessage` / `DbcSignal` family (with `Presence`, `ByteOrder`,
  `ValueDescription`, `Node`, `ValueTable`, `SignalGroup`, `EnvironmentVar`,
  `Comment` / `CommentTarget`) deserialized from the core's canonical JSON, plus
  `Client::format_dbc` (export the loaded DBC) and mux-query / lookup helpers
  (`DbcMessage::is_multiplexed` / `multiplexor_names` / `multiplex_values` /
  `signal_by_name`; `Dbc::message_by_id` / `message_by_name`). The `attributes`
  vocabulary is carried as raw-JSON pass-through pending a typed model (a
  follow-on commit). **Breaking:** `Client::parse_dbc_text` now returns
  `(Dbc, Vec<ValidationIssue>)` rather than just the warnings. Flips 7 `rust`
  `docs/FEATURE_MATRIX.yaml` rows to `implemented` (`format_dbc`,
  `dbc_metadata_tier1`, `dbc_signal_receivers`, `dbc_signal_value_descriptions`,
  `dbc_message_senders`, `dbc_queries_mux`, `dbc_lookup`).
- Rust binding (`rust/`) — loads `libaletheia-ffi.so` at runtime via `dlopen`
  (the `libloading` crate), mirroring the Go and C++ `.so`-consumer model. It
  enforces the GHC-allocated-memory ownership rules cgo hides (responses copied
  out and released with `aletheia_free_str` via a RAII guard; the RTS started
  once and latched in a `OnceLock`). The typed surface validates input at
  construction — `CanId` (`Standard`/`Extended` enum), `Dlc`, `Rational`,
  `Timestamp`, `TimeBound` return `Result` — and models LTL `Predicate` /
  `Formula` as native, exhaustively-matchable enums that serialize to the core's
  exact wire shape. `Client` loads a DBC (`parse_dbc_text`), binds properties
  (`set_properties`), and streams frames through the **binary FFI**
  (`start_stream` / `send_frame` / `send_error` / `send_remote` / `end_stream`,
  plus `extract_signals`) — the same fast path the other bindings use; `process`
  remains a raw JSON escape hatch. A `rust` column was added to
  `docs/FEATURE_MATRIX.yaml` (honest implemented/planned across all 40 rows) with
  a fourth structural parity gate (`rust/tests/feature_matrix.rs`); the existing
  Python/Go/C++ gates now validate the `rust` column too. Gated by a required
  `cargo test` / `cargo fmt --check` / `cargo clippy -D warnings` lane in
  `tools/run_ci.py`. The typed DBC document model, Check DSL, client-side
  violation enrichment, and CLI remain `planned`.
- **Incremental, staleness-safe build of `libaletheia-ffi.so`, plus build
  tooling.** A single changed Agda module now rebuilds the shared library in ~12s
  (one regenerated MAlonzo module recompiled + relink) and a no-op
  `cabal run shake -- build` in ~0.1s, instead of a full ~280-module recompile on
  every invocation. New developer targets and gates:
  - `cabal run shake -- gen-ffi-modules` regenerates the foreign library's
    `other-modules` list (every generated MAlonzo module), making cabal's
    dependency graph complete; `-Werror=missing-home-modules` is the drift gate —
    adding an Agda module without re-listing it fails the build, naming the
    module.
  - `cabal run shake -- iwyu` regenerates the relevant `.agdai` (via Agda's own
    incremental interface cache) and runs the import-usage analysis without a full
    `.hs`/`.so` rebuild.
  - `tools/check_build_incremental.py` (run as `tools/run_ci.py`'s `build` prereq)
    edits a source, rebuilds, and asserts the change reaches the `.so`, then
    reverts — a behavioral gate that the build can never silently ship a stale
    artifact.
  - A Shake oracle on `agda --version`, plus a dependency on `aletheia.agda-lib`,
    rebuild when the Agda toolchain (binary version, stdlib pin, or flags) changes
    even with no `.agda` source change.

### Removed

- **Two unreachable defensive branches in the Go JSON decoder — internal, no
  behavior change.** `parseRational` and `parseNumberAsInt64`
  (`go/aletheia/json.go`) each had a `case intParseNotNumber:` arm inside their
  `json.Number` switch, but `decodeJSONInt` applied to a `json.Number` can only
  return OK/fractional/overflow — never `notNumber` (that classification fires
  only for the dict components `rawNum`/`rawDen`, which the map arm already
  handles). The dead arms are removed and replaced with a comment noting why the
  switch is non-exhaustive on the classification. Found by a coverage audit while
  closing the decoder reject-branch test gap; no `exhaustive` linter depended on
  them.
- **The floating-point member of the typed log-value (C++ + Rust; BREAKING).**
  The user-facing Logger value type carried a float case — C++ `LogValue`'s
  `double` arm (`cpp/include/aletheia/log.hpp`) and Rust `LogValue::F64`
  (`rust/src/log.rs`) — that **no binding ever constructs**: every numeric log
  field is an exact integer (counts, indices, CAN IDs, µs timestamps) and the
  only exact rationals (enrichment observed values) reach logs as
  kernel-`format_rational`-rendered strings, never as a numeric log value. The
  float principle bars a float on every surface including the user-facing log
  boundary, so the float case is removed; both typed log-values are now the
  symmetric set `{string, i64, u64, bool}`. Also deletes the dead `static
  format_value(double)` overload in `cpp/src/enrich.cpp` (zero callers — every
  call site renders a `Rational` through the live `format_value(const Rational&)`
  → kernel `format_rational`). Go (`slog.Attr`) and Python (`object`) log values
  never carried a float, so they are unchanged. An exact rational that ever needs
  logging should be carried exactly and rendered to a string at the sink via the
  verified `format_rational`. **BREAKING**: a `LogValue` `double`/`F64` no longer
  exists.
- **Dead native-type arms in the Go JSON decoders (internal, no behavior
  change).** The Go binding's sole *production* decode entry (`parseResponse`)
  uses a `UseNumber` decoder, so on the production path every wire number arrives
  as a `json.Number`; the four rational/int decoders (`decodeJSONInt`,
  `parseRational`, `parseNumberAsInt64`, `jsonNumberToUint64`) therefore only ever
  see a `json.Number` in production, yet each still carried a `case float64:`
  (plus `int`/`int64`/`uint64` in `jsonNumberToUint64`) whose stated rationale
  ("mirrors the old `json.Unmarshal` FFI path") went stale when production
  switched to `UseNumber` in #116. Those arms were unreachable on the production
  path — only a test or fuzzer decoding via a plain `json.Unmarshal` could supply
  a `float64` — and are removed; any non-`json.Number` value now uniformly falls
  to the existing reject path (still total: rejected, never a panic). This
  aligns the Go decoder's contract with the float principle and with the
  Python/C++/Rust decoders, which already reject a float on inbound rational
  decode. The round-trip property test is retargeted to the production
  `json.Number` path and redundant native-`float64` reject tests are dropped (the
  wire-path cases in `json_precision_test.go` cover them). (`go/aletheia/json.go`,
  `go/aletheia/json_precision_test.go`, `go/aletheia/property_test.go`.)
- **The per-binding float→rational heuristics (BREAKING).** Deleted
  in favour of the kernel SSOT `from_decimal`: Python `float_to_rational` /
  `coerce_to_rational` / `to_signal_fraction` (`rational.py`, `types.py`); C++
  `Rational::from_double` (`types.hpp`/`types.cpp`); Go `PhysicalValue` (the
  `float64` newtype), `RationalFromFloat`, `FloatToRational`, `floatToRational`
  (`types.go`/`client.go`); Rust `Rational::from_f64` (and the now-dead `gcd`
  helper) (`types.rs`). Python's `fraction_to_rational` was **kept but renamed**
  `fraction_to_wire_pair` — it does the exact int64 numerator/denominator
  extraction the binary-frame FFI needs, which is unrelated to decimal *input*.
- Dead JSON **streaming** commands from the Agda core's command protocol —
  `startStream`, `sendFrame`, `extractAllSignals`, `endStream`, and `formatDBC`
  (their `StreamCommand` constructors, `Routing.agda` parsers, and
  `processStreamCommand` dispatch cases). Production streaming has always run
  through the binary FFI (`aletheia_send_frame` … via `Main/Binary.agda`'s
  `process*Direct`); these JSON mirrors were test-only and unreachable in
  production. The DBC/property JSON commands (`parseDBC`, `setProperties`,
  `validateDBC`, `parseDBCText`, `formatDBCText`) — the live JSON path every
  binding uses — are retained, as are all binary FFI handlers. The matching dead
  binding-side serializers (C++ `detail::serialize_*` for the removed commands
  plus the former default `IBackend` impls; Python's JSON-command ack-default
  markers) were removed too.

### Security

- Rotated the release-signing cosign key to a passphrase-protected key.
  The prior key (active 2026-05-08 – 2026-06-12) had no passphrase, so the
  key file alone could produce signatures; it is **retired, not
  compromised**. `keys/cosign.pub` now holds the new public key.
- Re-signed the v2.0.0 release artifacts with the new key. The release's
  primary `aletheia-2.0.0-linux-x86_64.tar.gz.sig` now verifies against the
  current `keys/cosign.pub`; the original retired-key signature is retained
  on the release as `aletheia-2.0.0-linux-x86_64.tar.gz.legacy-key.sig`.
  Each release publishes its signing key's SHA-256 fingerprint in the
  release notes; verifiers confirm the key against that immutable
  fingerprint rather than trusting a key by location (see `keys/README.md`
  § Key history).
- Added a published key-fingerprint trust anchor: release verification is
  anchored on the signing key's SHA-256 fingerprint (in the release notes
  and `keys/README.md`), so the public key may be fetched from any source
  and confirmed before use — closing the earlier reliance on the mutable
  `main` copy (PR #20 review).

## [2.0.0] — 2026-06-11

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

- EndStream `uncached_atom` warnings — `end_stream()` (Python
  `CompleteResponse.warnings`, Go `StreamResult.Warnings`, C++
  `StreamResult::warnings`) now surfaces one warning per property atom
  whose target signal never appeared in trace.  Disambiguates the
  Unresolved verdict (sound Kleene Unknown vs cache-miss diagnostic).
  Wire field `{kind, property_index, detail}`; the only kind today is
  `"uncached_atom"` (future kinds are additive).
- `endstream.uncached_atom` structured log event — each binding's
  `end_stream` / `EndStream` / `end_stream` now emits one warn-level
  structured log event per `CompleteWarning` carried on the response,
  in addition to the existing `stream.ended` lifecycle event's
  `numWarnings` aggregate.  Per-warning records carry
  `property_index` and `detail` fields so operators can grep for
  specific properties.  Cross-binding canonical event count bumped
  15 → 16; new "End-of-stream diagnostics" section in
  `docs/LOG_EVENTS.yaml`.  Documented in PROTOCOL.md
  § End-of-stream Warnings (wire shape + evolution rule for adding
  new kinds) and RUNBOOK.md § End-of-stream diagnostics (operator
  symptom/cause/action).
- `format_dbc_text` Client method — emit a DBC definition (Python
  `DBCDefinition`, Go `DBCDefinition`, C++ `DbcDefinition`) as canonical
  DBC text via the verified Agda formatter.
- `parse_dbc_text` Client method — parse DBC text directly through the
  verified Agda kernel. Replaces the previous
  `cantools`-based path on Python.
- DBC message `senders` round-trip on the **text** path — `format_dbc_text`
  emits `BO_TX_BU_ <id> : n1,n2,…;` lines for each message's extra
  transmitters and `parse_dbc_text` reads them back into `DBCMessage.senders`
  (keyed by CAN ID). The universal text round-trip
  `parseText (formatText d) ≡ inj₂ d` now holds with senders preserved —
  wired as an 8th synthesized top-level section mirroring VAL_, with
  `WellFormedTextDBCAgg`'s `senders-empty` precondition removed (strictly
  weaker). Senders were already on the binary/JSON path; this closes the
  text-surface gap (DEFERRED_ITEMS A.2). `parse_dbc_text` now attaches
  `BO_TX_BU_` transmitters instead of dropping them (corpus parity snapshot
  `kitchen_sink.json` regenerated to match).
- `send_error` and `send_remote` Client methods — emit CAN error and
  remote frames.
- DBC signal `value_descriptions` field (Python `DBCSignal.value_descriptions`,
  Go `DBCSignal.ValueDescriptions`, C++ `DbcSignal::value_descriptions`) —
  VAL_ entries promoted onto the owning signal.
- DBC signal `receivers` field — per-signal receiver-node list from `SG_`
  lines.
- DBC definition Tier 1 metadata fields (`signal_groups`, `environment_vars`,
  `value_tables`) on Python `DBCDefinition` / Go `DBCDefinition` /
  C++ `DbcDefinition`.
- DBC definition Tier 2 metadata fields (`nodes`, `comments`, `attributes`)
  on Python `DBCDefinition` / Go `DBCDefinition` / C++ `DbcDefinition`.
- DBC definition `unresolved_value_descriptions` field (same naming
  rule as Tier 1/2) — VAL_ lines that did not resolve to a signal on the
  text-parse path.
- `IssueCode.UnknownSignalReceiver` (Python `UNKNOWN_SIGNAL_RECEIVER`)
  — CHECK 21 warning surfaced on the typed binding API as a named
  constant.
- `IssueCode.UnknownValueDescriptionTarget` (Python
  `UNKNOWN_VALUE_DESCRIPTION_TARGET`) — CHECK 23 warning for VAL_
  lines whose target signal does not exist.
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
  row must resolve to a real symbol or the build fails.
- `docs/LOG_EVENTS.yaml` SSOT for the 16-event structured-log
  vocabulary plus three per-binding parity-gate tests
  (`python/tests/test_log_events_parity.py`,
  `go/aletheia/log_events_test.go`,
  `cpp/tests/test_log_events_parity.cpp`) — captures every event
  emitted by a comprehensive workflow and asserts membership in the
  canonical YAML name set, so a future binding-side emit-call that
  drifts from the cross-binding vocabulary fails the build.
- Doc-example harnesses across all three bindings: Python
  `pytest --markdown-docs`, Go `TestDocExamples`, C++
  `doc_example_tests` Catch2 binary. Every fenced ```python``` /
  ```go``` / ```cpp``` block in the documented file set runs against
  the real FFI.
- `tools/check_changelog.py` offline gate enforcing Universal Rule
  UR-1 (Public API stability and CHANGELOG discipline). Detects
  public-API drift since merge-base with `main` and fails if
  `CHANGELOG.md` was not also modified; wired into the Shake target
  `check-changelog` so the same gate runs from the build system, the
  pre-push hook (Phase 3), and from local CI without rebuilding the
  Shake binary. Branch-level granularity for v0; gate-shape verified
  by forward-revert test in a detached worktree.
- `tools/check_gate_claim.py` offline enforcer for the gate-claim
  integrity rule. Detects
  commits whose message asserts "all gates clean" / "gates green" /
  similar and verifies that `build/libaletheia-ffi.so` mtime postdates
  every build-relevant staged source file's mtime — i.e., the gates
  the commit claims to have run on actually observed the post-edit
  state. Three modes: `pre-commit` (read `.git/COMMIT_EDITMSG`),
  `HEAD` / `post-commit`, and explicit commit-hash for audit. Wired
  into Shake as `phony "check-gate-claim"`. Conservative claim
  detection — only "all gates" / "gates green" / "All N gates"
  patterns trigger; per-gate status lines do not.
- `tools/run_ci.py` offline CI orchestrator chaining the full 17-step
  gate sweep that commit messages have historically asserted "all
  gates clean" against. Steps: 8 Agda gates (build /
  check-properties / check-invariants / check-no-properties-in-runtime
  / check-erasure / check-fidelity / check-ffi-exports / count-modules)
  + 2 offline enforcers (check-changelog / check-gate-claim) + 3
  binding tests (Python pytest / Go test -race / C++ ctest) + 4 lints
  (basedpyright / pylint / gofmt + go vet / clang-format). Captures
  all output to `tools/ci-output/ci-<branch>-<timestamp>.log` (gitignored)
  for use as falsifiable gate-claim-integrity evidence. Total ~12-15 min
  on a warm system. Invoked directly (not via Shake) to avoid
  `cabal run` flock recursion.
- `tools/install_hooks.py` idempotent installer for Aletheia's git
  hooks. Currently installs a `pre-push` hook that invokes
  `tools/run_ci.py` before allowing push, refusing the push on any
  non-zero exit. Skip with `git push --no-verify` for incident
  response. Backs up any existing pre-push hook to
  `pre-push.aletheia-backup-<timestamp>`.
- `tools/ci-output/` directory with `.gitignore` reserving the
  directory for runtime CI logs while keeping logs themselves out
  of source tracking.
- `.actrc` configuration for [`act`](https://github.com/nektos/act),
  the local-GHA-replay tool. Pins `ubuntu-latest` to
  `catthehacker/ubuntu:act-latest` (~5 GB curated image) and
  `--container-architecture linux/amd64` for cross-platform
  reproducibility. Used by devs to validate workflow changes before
  pushing, without consuming GitHub Actions minutes.
- `docs/development/CI_LOCAL.md` documenting the local-first CI
  architecture: offline correctness sweep via `tools/run_ci.py`
  (pre-push hook), push-time meta-gates via `.github/workflows/`,
  and `act` Docker pairing for local GHA replay. Includes install
  / usage / troubleshooting.
- `.github/workflows/gha-checks.yml` push-time meta-gate workflow,
  three jobs running in parallel: `actionlint` (workflow YAML lint),
  `action-pins` (verify SHA-pinning policy via `tools/check_action_pins.py`),
  `permissions-check` (verify minimal permissions via
  `tools/check_workflow_permissions.py`). actionlint v1.7.7 installed
  via direct release download (no third-party action dependency).
  Triggers on every push and PR; wall-clock ~1-2 min on `ubuntu-latest`.
  `permissions: contents: read` default.
- `tools/check_action_pins.py` offline gate enforcing action-pin policy:
  GitHub-owned actions (`actions/*`, `github/*`) accept `@v<n>` tags;
  third-party actions must be SHA-pinned (40-char hex). Branch refs
  (`@main`, `@master`, etc.) are rejected even for GitHub-owned to
  defend against tag-mutability supply-chain attacks. Gate-shape
  verified inline via synthetic violation worktree.
- `tools/check_workflow_permissions.py` offline gate verifying that
  every workflow declares a top-level `permissions:` mapping or every
  job declares its own. Uses python3 + yaml for proper parsing.
  Rejects `read-all` / `write-all` defaults. Gate-shape verified
  inline.
- `.github/dependabot.yml` weekly dependency-update schedule covering
  Python (`pip` in `python/`), Go (`gomod` in `go/` and `go/excel/`),
  and GitHub Actions. Cabal not covered (dependabot-core does not
  support Hackage); GHC toolchain manual via the Phase 6 `--bignum=native`
  rebuild deliverable. Per-ecosystem `commit-message.prefix` and
  `labels` set for traceability.
- Optional GHA toolchain documented in `CLAUDE.md § Development
  Environment` — `actionlint` and `act` install commands. Both are
  optional locally; `tools/run_ci.py` step 18 (actionlint) skips
  gracefully if not installed.
- `tools/run_ci.py` extended from 17 to 20 steps, adding GHA meta-checks
  18-20 (actionlint with skip-if-missing, check-action-pins,
  check-workflow-permissions) so the offline pre-push hook now covers
  the same surface as the GHA workflow.
- `tools/run_ci.py` extended from 20 to 21 steps with the addition of
  `clang-tidy -p build src/*.cpp` (canonical invocation per AGENTS.md
  L580) — mandatory correctness gate per AGENTS.md L494,
  missing from Phase 3 / Phase 6 ships and revealed by the
  first end-to-end run.
- `docs/operations/RUNBOOK.md` — operations runbook keyed on operator
  symptoms.  Per AGENTS.md cat 22, every one of the 15 structured log
  events from `docs/LOG_EVENTS.yaml` has a `symptom / cause / action`
  entry, and every failure mode documented elsewhere (BUILDING.md
  troubleshooting, CANCELLATION.md edge cases, PROTOCOL.md
  `InputBoundExceeded` bounds, OOM / heap pressure, DBC validation
  rejection) is captured in one operator-facing reference.
- `tools/check_runbook_coverage.py` offline gate enforcing AGENTS.md
  cat 22.  Parses `docs/LOG_EVENTS.yaml` for event names and verifies
  every event appears as a `#### `<name>`` heading in
  `docs/operations/RUNBOOK.md`; missing entries fail the gate.  Wired
  as Shake `phony "check-runbook"` and as step 11 of `tools/run_ci.py`
  (which moves to 22 always-on steps total).  Forward-revert verified:
  deleting a heading fires the gate with a precise diagnostic;
  restoring it returns to exit 0.
- Long-run stability bench harnesses across all three bindings, with a
  GHC RTS heap-typed profile capture for the Agda kernel.  Per AGENTS.md
  cat 16 / 25 / 26 / 27 each binding now exercises ≥ 1M frames in a
  multi-cycle Init/Close pattern and asserts no per-iteration drift on
  RSS / FD count / binding-specific resource accounting.
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
  need to call this.
- `ALETHEIA_RTS_OPTS` env-var path in the Python binding's
  `RTSState.acquire` — additional RTS flags (e.g., `-hT` for heap
  profiling, `-p` for time profiling) are appended to the argv passed
  to `hs_init_with_rtsopts`.  Lets the stability bench drive the GHC
  RTS heap profile without rebuilding the `.so`.
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
  hard-zero gate with a precise `delta=N` diagnostic.
- `Aletheia.Limits` Agda module + `docs/architecture/PROTOCOL.md § Limits`
  documenting the compile-time adversarial-input bounds enforced at every
  parser at a trust boundary (Universal Rule UR-2). 11
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
  `frame_input_bound_exceeded` (Universal Rule UR-2).

#### Python

- `aletheia.Backend` Protocol — FFI-boundary
  abstraction promoted to the public surface alongside `aletheia.FFIBackend`
  (production wrapper around `libaletheia-ffi.so`) and `aletheia.MockBackend`
  (canned-response replay for tests).  Cross-binding parity with Go
  `aletheia.Backend` interface (`go/aletheia/backend.go`) and C++
  `aletheia::IBackend` (`cpp/include/aletheia/backend.hpp`).
  `AletheiaClient.__init__` accepts a new `backend=` kwarg; when omitted
  an `FFIBackend` is constructed on `__enter__` from the resolved .so
  path. Client-constructed backends are torn down on `close()`;
  caller-injected backends persist (cross-binding ownership parity).
- `aletheia.MockBackend` — drop-in mock
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
  `asyncio.CancelledError`.
- `AletheiaClient.send_frames_iter()` — lazy generator yielding
  `FrameResult` per committed frame; consumer-driven cancellation via
  `break` / `gen.close()`.
- `aletheia.validation` module exposing `IssueSeverity`, `IssueCode`,
  `ValidationIssue` — extracted from `protocols.py` to keep that file
  under the pylint 1000-line gate. Importable from the
  package root: `from aletheia import IssueCode, ValidationIssue`.
- `aletheia.limits` module mirroring `Aletheia.Limits` (Agda) — bound
  constants (`MAX_JSON_BYTES`, `MAX_DBC_TEXT_BYTES`, etc.) and bound-kind
  wire codes (`BOUND_KIND_INPUT_LENGTH_BYTES`, etc.) for use at FFI
  entries and in user code.
- `aletheia.InputBoundExceededError` exception class, subclass of
  `AletheiaError`, carrying `kind` / `observed` / `limit` fields.
  Raised by `_send_command` when a JSON payload exceeds `MAX_JSON_BYTES`
  before marshaling across ctypes; raised by `dbc_to_json` when a DBC
  file exceeds `MAX_DBC_TEXT_BYTES`; raised by `yaml_loader.load_checks`
  when a YAML file/string exceeds `MAX_DBC_TEXT_BYTES`. Importable as
  `from aletheia import InputBoundExceededError` (Universal Rule UR-2).
- `CANFrameTuple` gains `brs` / `esi` fields — pass-through CAN-FD
  Bit Rate Switch (ISO 11898-1:2015 §10.4.2) and Error State Indicator
  (§10.4.3) metadata. Both default to `None` for CAN 2.0B frames where
  the bits do not exist; `AletheiaClient.send_frame` / `send_frames`
  accept matching kwargs and `iter_can_log` / `load_can_log` surface
  them per-frame from python-can readers. The Aletheia kernel does
  NOT consume these bits — pass-through metadata only.
- Loader path-hardening: `excel_loader.load_checks_from_excel`,
  `load_dbc_from_excel`, and `yaml_loader.load_checks(Path(...))` now
  refuse symbolic links outright with `ValidationError`. Mirrors the
  same C++ rejection so cross-binding semantics stay aligned.
- `aletheia.client._ffi.find_ffi_library` extends the earlier
  symlink + group/world-writable check from the `ALETHEIA_LIB` env
  path to every fallback resolution path (`_install_config`,
  `build/`, `dist-newstyle/`); a tampered fallback can no longer
  bypass the gate.

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
  bound-kind wire-code constants (`BoundKindInputLengthBytes`, ...).
- `*aletheia.InputBoundExceededError` typed error in `error.go` with
  `BoundKind` / `Observed` / `Limit` / `Code` fields. Returned by
  `FFIBackend.Process` when input exceeds `MaxJSONBytes` before the
  cgo `aletheia_process` call. Discoverable via `errors.As`. New
  `Code*` error codes: `CodeParseInvalidIdentifier`,
  `CodeParseInputBoundExceeded`, `CodeDBCTextParseFailure`,
  `CodeDBCTextTrailingInput`, `CodeDBCTextAttributeRefinementFailed`,
  `CodeDBCTextInputBoundExceeded`, `CodeFrameInputBoundExceeded`
  (Universal Rule UR-2).
- Loader hardening: `excel.LoadChecks`, `excel.LoadDbc`,
  `excel.CreateTemplate`, `aletheia.LoadChecksFromYAMLFile`, and the
  file-branch of `aletheia.LoadChecksFromYAML` now reject symbolic
  links outright; the excel entry points additionally enforce a
  64 MiB raw file-size cap and walk the ZIP central directory via
  stdlib `archive/zip`, returning `*InputBoundExceededError`
  (`BoundKind="input_length_bytes"`) when the sum of uncompressed
  entry sizes exceeds the cap (ZIP-bomb defence).
  `excel.CreateTemplate` validates the destination's parent dir.
  Cross-binding mirror of the C++ and Python hardening.

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
  umbrella header `<aletheia/aletheia.hpp>`.
- New `ErrorCode` enumerators: `ParseInvalidIdentifier`,
  `ParseInputBoundExceeded`, `DBCTextParseFailure`,
  `DBCTextTrailingInput`, `DBCTextAttributeRefinementFailed`,
  `DBCTextInputBoundExceeded`, `FrameInputBoundExceeded` — plus
  matching `error_code_from_string` table entries (51 → 58 entries).
  `FfiBackend::process` synthesizes a `parse_input_bound_exceeded`
  error response when input exceeds `max_json_bytes` before
  calling the dlopen'd `aletheia_process` (Universal Rule UR-2).
- `error.hpp` — `AletheiaException` class deriving from
  `std::runtime_error` and carrying an `AletheiaError` value
  accessible via `kind()` / `code()` / `error()`. Used for FFI
  boundary failures (`dlopen` / `dlsym` / `aletheia_init() → null`)
  that emit `ErrorKind::Ffi`, plus `ErrorKind::Protocol` for
  runtime `aletheia_*() → null` cases and `ErrorKind::Validation`
  for caller-argument rejections (`rts_cores < 1`, oversize
  payload). Mirrors Python `FFIError` / `ProtocolError` /
  `ValidationError` and Go `ErrFFI` / `ErrProtocol` /
  `ErrValidation`. Previously these paths threw `std::runtime_error`;
  existing `catch (const std::exception&)` blocks keep working via
  the base, new code can `catch (const AletheiaException&)` to
  recover the kind tag.
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
  exception.
- `aletheia::Logger::enabled(LogLevel) const noexcept` — fast-path
  predicate letting hot-path callers short-circuit before
  constructing `std::initializer_list<LogField>`. Mirrors Go
  `slog.Logger.Enabled(ctx, level)` and Python
  `logging.Logger.isEnabledFor(level)`. Hot-path Debug call sites
  in `AletheiaClient` (`frame.processed`, `error_event.sent`,
  `remote_event.sent`, `cache.hit`, `cache.miss`) now guard with
  `enabled(LogLevel::Debug)` before building the field list, so a
  disabled-Debug logger never pays the per-frame `LogField`
  construction cost.

#### Build / release tooling

- `cabal run shake -- dist` now records SHA-256 hashes for the source
  and post-strip artifacts in `dist/aletheia/MANIFEST.txt`, generates
  a CycloneDX 1.5 SBOM at `dist/aletheia/aletheia-sbom.cdx.json`,
  produces a sidecar `dist/aletheia.tar.gz.sha256` for
  `sha256sum -c`, and signs the tarball with cosign at
  `dist/aletheia.tar.gz.sig` when `$ALETHEIA_COSIGN_KEY` is set.  The
  tarball is built reproducibly (`tar --sort=name --mtime=@<commit-epoch>
  --owner=0 --group=0 --numeric-owner --use-compress-program='gzip -n'`)
  — two `dist` runs of the same commit produce bit-identical
  `aletheia.tar.gz` (Universal Rule UR-3).
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
  can pin to a specific build (CICD-5.5).
- `dist/aletheia/README.txt` — deterministic in-tarball consumer entry
  point: file inventory, quick-start gcc command, verify-then-trust
  order, and cross-references to `DISTRIBUTION.md` / `RELEASE.md`.
  Content derived from commit time only — no wall-clock — so the
  tarball stays bit-reproducible (CICD-5.7).
- **Cross-binding integration tests** in all three bindings
  (`python/tests/test_cross_binding_integration.py`,
  `go/aletheia/cross_binding_integration_test.go`,
  `cpp/tests/test_cross_binding_integration.cpp`).  Each binding
  constructs identical canonical inputs and asserts the response shape
  matches the documented PROTOCOL.md invariants — no shared corpus, no
  golden output to diff against.
- **Sanitizer build matrix.**
  `cpp/CMakeLists.txt` adds `-DALETHEIA_SANITIZER=address|undefined|thread`
  for opt-in ASan / UBSan / TSan lanes; `cpp/sanitizer-ignorelist.txt`
  filters vendored third-party UB in OpenXLSX.  Requires clang for the
  ignorelist feature; `tools/run_ci.py` step 26 (`ALETHEIA_SAN_CHECK=1`)
  wires the canonical UBSan ctest battery.
- **`docs/architecture/CGO_NOTES.md`** documents the GHC RTS / cgo /
  sanitizer interaction surface — the AST→compile→link path, sanitizer
  blind spots, the rationale behind each lane decision, and the
  compiler requirement.
- **Native fuzz harnesses** in all three bindings:
  - Go: `aletheia/fuzz_test.go` adds `FuzzParseResponse`,
    `FuzzMarshalCommand`, `FuzzDecodeBinaryFrame`,
    `FuzzParseRationalNumber`, `FuzzParseDBCJSON`.
  - C++: `cpp/tests/fuzz/` ships 4 libFuzzer harnesses behind the
    `-DALETHEIA_FUZZ=ON` clang+`-fsanitize=fuzzer` opt-in.
  - Python: `python/tests/fuzz/` ships 3 atheris harnesses behind the
    new `aletheia[fuzz]` extra.
- **Property tests** in all three bindings:
  - Go: `aletheia/property_test.go` adds 5 `testing/quick` properties
    (rational round-trip, parser totality, command round-trip, rational
    monotonicity, mock/real shape parity).
  - C++: `cpp/tests/unit_tests_property.cpp` adds 5 Catch2 GENERATE
    properties.
  - Python: `python/tests/test_property_hypothesis.py` adds 8
    hypothesis property tests; `aletheia[dev]` extras gain
    `hypothesis>=6.0,<7`.
- **Python `-X dev` lane** at `tools/run_ci.py` step 14 — surfaces
  `ResourceWarning`, debug asyncio warnings, deprecation noise that
  the standard pytest lane silently masks.
- **`aletheia.asyncio.AletheiaClient(sync_client=…)`** — public
  dependency-injection seam.  When provided, the AsyncClient wraps the
  pre-built sync client instead of constructing one internally; enables
  test scaffolding (and downstream advanced uses) to interpose on the
  sync layer without touching private attributes.
- **`aletheia.asyncio.testing.gate_send_frame(sync, after_n)`** —
  public testing helper for deterministic async-cancellation contracts.
  Wraps the public ``send_frame`` method on a sync client to block the
  worker thread after frame ``after_n`` commits; pairs with the new
  ``sync_client=…`` injection seam so tests need no protected-access
  suppressions.  Used by
  ``python/tests/test_cancellation.py`` to verify the cancellation
  contract with no physical-time dependence — pytest's session timeout
  is the only safety net for genuine hangs.
- **Python `--random-order` lane** at `tools/run_ci.py` step 15 —
  exercises the `pytest-random-order` plugin per AGENTS.md cat 14(f);
  the dep was pinned in `pyproject.toml [dev]` extras when the cat
  landed but the lane never followed.  Both deterministic and
  randomized-order lanes must stay green.
- **Python doc-example harness lane** at `tools/run_ci.py` step 13 —
  the `pytest --markdown-docs` invocation was silently absent from the
  orchestrator before C5; recovering it adds 114 doc-fence executions.

#### Mutation testing infrastructure

Per AGENTS.md cat 14(g): per-binding mutation testing on hot-path
modules.  Infrastructure shipped; per-binding survivor baselines
established post-merge.

- **`docs/MUTATION_BENCH.yaml`** — single source of truth: per-binding
  tool, hot-path module list (mapped to actual on-disk paths after the
  protocols split and module extraction), baseline survivor count.
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

#### `tools/run_ci.py` CLI overhaul

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
step 13; `check-stability-bench` at step 12 was added earlier).

#### `tools/check_limits_parity.py` + Shake `check-limits-parity` gate

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

#### Changed — Python: mutation-lane hardening (internal; no behavior change)

The Python mutation lane (`mutmut`) was driven from 215 survivors to 1 by
closing real test gaps in the under-tested error/edge branches of
`aletheia.client._client` (`format_dbc` / `format_dbc_text` / `validate_dbc` /
`_send_command` guards + lifecycle), `aletheia.yaml_loader` (check-validation
branches), `aletheia.dbc._converter` (file wrappers), and `aletheia.types`
(`dump_json` / encoder).  The only source-visible changes are
behaviour-preserving simplifications (`to_signal_fraction` drops a redundant
integer branch; `_populate_signal_lookup` drops a redundant `False` default;
`str.encode`/`bytes.decode` drop the explicit `"utf-8"` default) and
`# pragma: no mutate` annotations on genuine equivalents / unreachable
defensive guards.  The internal stub `aletheia.client._client._send_frame_unbound`
was renamed to `send_frame_unbound` (still module-private — not exported).  No
observable behaviour or public-API change.  The one remaining survivor is a
documented genuine equivalent (`dump_json`'s `ensure_ascii=False`→`None`); see
`docs/MUTATION_BENCH.yaml`.

#### Added — Python: `aletheia.types.JSONValue` type alias; loaders typed against it

A canonical `JSONValue` alias (`str | int | float | bool | None | list[JSONValue]
| dict[str, JSONValue]`) is exported from `aletheia.types` for JSON-/wire-derived
data. The loader field accessors (`aletheia._loader_utils.get_str` / `get_int` /
`get_number` / `get_bool` / `get_dict`) and `is_str_dict` now use it (covariant
`Mapping[str, JSONValue]` inputs / `dict[str, JSONValue]` narrowing) instead of
`dict[str, object]`, removing the lazy `object` annotations from the loader +
JSON-dict surface (Excel cells keep the precise `CellValue`). Internal typing
precision; no behaviour change.

#### BREAKING — Python: `RationalNumber` dropped; `property_index` / `timestamp` are now `int`

The `aletheia.types.RationalNumber` TypedDict (the wire `{numerator,
denominator}` shape) is removed. The two response fields that used it —
`PropertyResultEntry.property_index` and `.timestamp` — are now parsed to
`int` at the response boundary, matching what the Go and C++ bindings already
expose (Python was the outlier, carrying the raw dict). The wire JSON is
unchanged — the Agda kernel still emits the rational form; only the parsed
Python shape changes. The now-redundant helpers `aletheia.checks_runner.
rational_to_int` and the internal `validate_integer_rational` are removed
(the boundary parser `validate_integer_field` returns `int` directly).

Caller migration:

```python
# before
idx = entry["property_index"]["numerator"] // entry["property_index"]["denominator"]
# after
idx = entry["property_index"]   # already an int
```

#### BREAKING — Python: `aletheia.protocols` renamed to `aletheia.types`

The wire-format type namespace (the response/command TypedDicts, the LTL
formula and predicate types, the DBC structure types, the `DLCCode` /
`ByteOrder` enums, `RationalNumber`, …) is renamed from `aletheia.protocols`
to `aletheia.types` — the name now reflects its contents (type definitions)
rather than reading like `typing.Protocol`. `from aletheia.protocols import …`
no longer resolves; use `from aletheia.types import …`. The handful of names
already mirrored at top-level (`DBCDefinition`, `PropertyResultEntry`) are
unchanged.

Caller migration:

```python
# before
from aletheia.protocols import DBCDefinition, DLCCode, LTLFormula
# after
from aletheia.types import DBCDefinition, DLCCode, LTLFormula
```

#### BREAKING — Python: `aletheia.error_codes` + `aletheia.issue_codes` unified into `aletheia.codes`

The two code-enumeration submodules are merged into a single `aletheia.codes`
namespace: `ErrorCode` (runtime error codes) and `IssueCode` / `IssueSeverity`
/ `ValidationIssue` (DBC validation issues). `from aletheia.error_codes import
…` and `from aletheia.issue_codes import …` no longer resolve; use
`from aletheia.codes import …`. The top-level convenience aliases are unchanged
— `from aletheia import ErrorCode, IssueCode, ValidationIssue` still works
(`IssueSeverity` remains available as `aletheia.codes.IssueSeverity`).

Caller migration:

```python
# before
from aletheia.error_codes import ErrorCode
from aletheia.issue_codes import IssueSeverity, ValidationIssue
# after
from aletheia.codes import ErrorCode, IssueSeverity, ValidationIssue
```

#### BREAKING — Python: `aletheia.dbc_converter` + `aletheia.dbc_queries` unified into `aletheia.dbc`

The two DBC submodules are merged into a single `aletheia.dbc` namespace
covering both conversion (`dbc_to_json`, `dbc_to_text`, `convert_dbc_file`)
and structural queries (`message_by_id`, `signal_by_name`, `is_multiplexed`,
…). `from aletheia.dbc_converter import …` and `from aletheia.dbc_queries
import …` no longer resolve. The top-level convenience aliases are unchanged
— `from aletheia import dbc_to_json, message_by_id` still works.

Caller migration:

```python
# before
from aletheia.dbc_converter import dbc_to_json
from aletheia.dbc_queries import message_by_id
# after
from aletheia.dbc import dbc_to_json, message_by_id
```

#### Added — Python: namespace hygiene via `__all__` on public submodules

`aletheia.can_log`, `aletheia.dsl`, `aletheia.excel_loader`, `aletheia.checks`,
and `aletheia.yaml_loader` now declare `__all__`, so each module exposes only
its intended public surface instead of leaking internal helpers (e.g.
`can_log.convert_message`, `dsl.require_non_negative_time_ms`,
`excel_loader.CellValue`, the `checks` fluent-builder intermediates). Explicit
imports of those helpers still work; only `*`-import and tooling/doc surface
narrow.

#### BREAKING — Python: `aletheia` is the sole public package; `aletheia.client` re-exports removed

The `aletheia.client` sub-package no longer re-exports any public name. The
client surface — `AletheiaClient`, the exception hierarchy (`AletheiaError`,
`ValidationError`, `FFIError`, `ProtocolError`, `StateError`, `BatchError`,
`InputBoundExceededError`), `Backend` / `FFIBackend` / `MockBackend` /
`BinaryPathUnsupportedError`, `RTSState`, the response TypedDicts, and the
`bytes_to_dlc` / `dlc_to_bytes` converters — is now importable **only** from the
top-level `aletheia` package, the single canonical public surface.
`aletheia.client` and its `_`-prefixed modules are internal implementation
detail and may change between releases.

Caller migration:

```python
# before
from aletheia.client import AletheiaClient, AletheiaError, ValidationError
# after
from aletheia import AletheiaClient, AletheiaError, ValidationError
```

This closes the long-standing dual public import path — every client name was
previously reachable from both `aletheia` and `aletheia.client`. Documentation
and examples already used the top-level form exclusively, so user-visible
breakage is limited to code that imported straight from `aletheia.client`.

#### Changed — Build: `check-properties` type-checks proof modules in one warm agda process

`cabal run shake -- check-properties` previously spawned one `agda Module.agda`
subprocess per proof module (~45 processes, each reloading the standard library
and shared interfaces). It now type-checks every module in a single warm
`agda --interaction-json` process (`tools.warm_check_properties`), loading the
stdlib once — roughly 13× faster (629s → ~48s) with identical verdicts: a
proof-obligation failure still surfaces as `Status{checked:false}`, and the run
writes `.agdai` so the downstream build reuses the interfaces. The former cold
batch and the separate `check-properties-warm` target are removed (folded in);
the `proofModules` list in `Shakefile.hs` remains the single source of truth.

#### Changed — Python + C++: Check entry points migrated from class statics to free functions

**BREAKING** — The `Check` class (Python `aletheia.Check`, C++ `aletheia::Check`)
is removed.  Its two static factories `Check.signal(...)` / `Check.when(...)`
are now module-level free functions in `aletheia.checks` (Python) and
namespace-level free functions in `aletheia::check` (C++).

Caller migration:

```python
# Before
from aletheia import Check
Check.signal("Speed").never_exceeds(220)
Check.when("Brake").exceeds(50).then("Light").equals(1).within(100)

# After
from aletheia.checks import signal, when
signal("Speed").never_exceeds(220)
when("Brake").exceeds(50).then("Light").equals(1).within(100)
```

```cpp
// Before
aletheia::Check::signal("Speed").never_exceeds(...);
aletheia::Check::when("Brake")...;

// After (using namespace aletheia; in scope)
check::signal("Speed").never_exceeds(...);
check::when("Brake")...;
```

Go is unaffected — package-level `aletheia.CheckSignal(...)` /
`aletheia.CheckWhen(...)` already used the free-function shape.

Why: the `Check` class-with-statics shape was Python-mirror legacy
(`Check.signal` mirrored Python's `Check.signal`).  C++ idiom prefers a
namespace with free functions for stateless factories; Python aligns by
exposing the same factories as module-level functions in `aletheia.checks`.
The `Check` class was a single-purpose factory holder with no state — the
class container added no value over the namespace form.  Not re-exported
at top level (`aletheia.signal` / `aletheia.when`) because both names are
generic and would shadow the stdlib `signal` module or local `signal`
parameters; use `from aletheia.checks import signal, when` (no shadow at
call sites) or `from aletheia import checks; checks.signal(...)` (no shadow
where `signal` is a local).

#### Changed — Go: `BuildFrame` argument order aligned to `(id, dlc, signals)`

**BREAKING** — Go `Client.BuildFrame` changed from
`BuildFrame(ctx, id, signals, dlc)` to `BuildFrame(ctx, id, dlc, signals)`.

Caller migration:

```go
// Before
payload, err := c.BuildFrame(ctx, id, signals, dlc)
// After
payload, err := c.BuildFrame(ctx, id, dlc, signals)
```

Why: `BuildFrame` was the lone outlier placing `signals` before `dlc`.
`UpdateFrame(ctx, id, dlc, data, signals)` and both other bindings'
`build_frame(id, dlc, signals)` (Python kwargs / C++ positional) already
used `(id, dlc, …)`; Go now matches.  Reordered pre-release (no external
users) per the no-backward-compat policy, closing the in-source
DEFERRED block on `client.go`.

#### Changed — Parsers: LittleEndian `bitLength = 0` now rejected at parse time

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

#### Changed — LTL metric operators: `window` parameter typed as `Timestamp μs` instead of raw `ℕ`

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

#### Changed — Agda kernel: `injectHelper` lifted to top-level + Bool fast-path via `Reflects`

Internal Agda kernel + proof refactor — no binding, wire, or runtime
behavior change.  Three coordinated changes ship together to close two
deferrals that an earlier four-approach probe had deferred
again on grounds of an Agda elaboration barrier:

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
   ↔ outer-with-abstraction trap the four-approach probe hit.
   Reduction equation `mkBoundedBitVec-just` lets consumers compose into
   `trans`/`with … | reduction` chains without crossing the barrier.
3. `injectHelper`'s Dec dispatch (`_<?_`) swapped for `mkBoundedBitVec`.
   MAlonzo output confirmed: the Dec constructor and `<?` are gone from
   `MAlonzo.Code.Aletheia.CAN.Encoding`.

The four-approach probe's framing ("the barrier is structural to
Agda's `with ... in eq` elaboration mechanism") is empirically correct
— `mkBoundedBitVec-just` written with `with ... in eq` still triggers
the exact `[UnequalTerms]` "ill-typed with-abstraction" error in a
17-line minimal reproduction.  But the conclusion ("workaround: keep
`Dec`") was over-strong: the `Reflects` two-with pattern is the
structural escape hatch the four-approach probe didn't try.

**Perf:** no measurable Frame Building gain over the post-`@0` baseline
(an earlier `@0`-erasure of `ℕToBitVec`'s bound slot already
captured the throughput win).  Benchmark deltas across all three
bindings are within WSL2 session-distant ±10% jitter.  Reason: MAlonzo emits
`Reflects.fromEquivalence` for `mkBoundedBitVec`, which allocates a
Reflects wrapper via `du_of_30` + two closures per call — one heap
cell, structurally similar to post-`@0` Dec.  The architectural win is
proof clarity (no 3-deep `with`-mirror, no where-bound runtime helper,
helper-level lemmas readable in isolation) and the reopening of the
"closed by upstream Agda fix" framing — `Reflects` is a stdlib-available
escape hatch that should be the first choice when a Bool fast-path needs
to bridge to a proof witness.

The `nothing = nothing` arm on `mkBoundedBitVec`'s
result stays DEFERRED — the branch is now via `Maybe` instead of `Dec`,
still structurally required by coverage and still provably dead.  An
in-source note at the branch documents the rationale.

#### Changed — All bindings: predicate pretty-printer renders Rationals via cross-binding-identical exact-decimal algorithm

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

#### Changed — Python: DSL float-input conversion now mirrors Go/C++ `from_double`

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

#### BREAKING — Go and C++: `mux_values` field + method renamed to `multiplex_values` for cross-binding parity

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
`mux_values` identifier.

#### BREAKING — C++: `StrongString<Tag>` merged into `Strong<Tag, T>`

The previously-separate `StrongString<Tag>` template is removed. `Strong<Tag, T>`
now exposes a concept-gated `operator std::string_view()` when `T == std::string`,
so existing `std::string_view{name}` direct-init sites for `SignalName` /
`MessageName` / `NodeName` / `Unit` continue to work unchanged. The four name
aliases now read `Strong<..., std::string>` instead of `StrongString<...>`.
Out-of-tree consumers that referenced the `StrongString` template name must
substitute `Strong<Tag, std::string>`.

#### BREAKING — C++: g++ dropped; latest stable Clang only (currently 22)

The C++ binding is now built and tested only against the **latest stable
Clang** (currently **Clang 22**). g++ is no longer supported (dropped
2026-06-09), and the previously-documented "Clang ≥ 19" floor is retired —
older Clang releases may still compile but are not supported. The project
tracks the latest stable toolchain and moves forward (e.g. to Clang 23 when it
ships) rather than promising a minimum-version range; UB can differ between
compiler versions, so the shipped compiler is pinned. Consumers building the
C++ binding from source with g++ or an older Clang must switch to clang-22
(`-DCMAKE_C_COMPILER=clang-22 -DCMAKE_CXX_COMPILER=clang++-22`); the
libstdc++/libc++ must provide C++23 (`<expected>` / `<format>`). CI (ctest /
clang-tidy / ubsan / mutation) and `tools/run_ci.py` build with clang-22, and
the mutation lane builds Mull 0.34.0 from source against LLVM-22. See
docs/development/BUILDING.md § Toolchain support policy.

#### Added — C++: `Strong<Tag, T>::of(...)` perfect-forwarding factory

New static factory: `PhysicalValue::of(1, 10)` constructs a `PhysicalValue`
from `Rational{1, 10}` without the explicit inner-type call site. Works for
every `Strong<Tag, T>` instantiation (numeric, string, bit-position). Chosen
over per-tag free `make_*` factories so the convenience scales without N new
symbols. Old `PhysicalValue{Rational{1, 10}}` form continues to compile.

#### Changed — C++: `LtlFormula` switched from `std::variant` inheritance to composition

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

The "Visitor pattern for binary-compat extension" alternative
(virtual-dispatch class hierarchy) is intentionally
**not pursued**: header-only template consumption + 1:1 Agda kernel ADT
mapping means virtual dispatch would lose constexpr and break the lambda
idiom for no architectural gain. Documented in `cpp/include/aletheia/ltl.hpp`.

#### BREAKING — Python: `aletheia.asyncio.testing.gate_send_frame` replaced by `gated_backend`

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
`send_frame_binary` calls only. Closed naturally with the Backend DI
seam.

#### BREAKING — Python: `aletheia.load_checks` dispatch is now strict by argument type

`load_checks(source: str | Path)` previously auto-promoted any string that
matched an existing file path to a file load (path-confusion vector). The dispatch is now strict: `pathlib.Path` → file load,
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

#### Changed — Python: `ALETHEIA_LIB` now rejects group/world-writable paths

`AletheiaClient` startup raises `PermissionError` if the path resolved
from `ALETHEIA_LIB` is writable by anyone but its owner (mode bits
`S_IWGRP | S_IWOTH`). Defense against the case where an unprivileged
third party who cannot set the env var poisons an existing legitimate
path. Owner-of-file ≠ current uid is still allowed (a shared
`/usr/local` install with root-owned `.so` loaded by a non-root user
remains a supported deployment). Owner-only writes are accepted (mode
`644` / `600`); fix with `chmod go-w $ALETHEIA_LIB` if rejected.

#### BREAKING — Go: `ctx context.Context` is now the first parameter on every Client operation method

Affects `SendFrame`, `SendFrames`, `StartStream`, `EndStream`,
`SendError`, `SendRemote`, `LoadDBC`, `ParseDBC`, `ParseDBCText`,
`FormatDBC`, `FormatDBCText`, `SetProperties`, `AddChecks`,
`ExtractSignals`, `BuildFrame`, `UpdateFrame`, `ValidateDBC`.
Migration: pass `context.Background()` to recover prior behavior, or
thread a real `ctx` through to enable cancellation. `Close()` and
`NewClient(...)` deliberately do not take `ctx` (mirrors `db.Close()`
/ `sql.Open(...)` precedent).

#### BREAKING — C++: `std::stop_token` is now the first parameter on every Client operation method

Affects `parse_dbc`, `parse_dbc_text`, `format_dbc`, `format_dbc_text`,
`extract_signals`, `build_frame`, `update_frame`, `send_frame`,
`send_frames`, `send_error`, `send_remote`, `start_stream`,
`end_stream`, `set_properties`, `add_checks`, `validate_dbc`.
Migration: pass `std::stop_token{}` to recover prior behavior.
`~AletheiaClient()` and `make_ffi_backend(...)` deliberately do not
take a stop_token (mirrors stdlib container constructor conventions).

#### BREAKING — Python: `ProcessError` removed in favor of kind-tagged hierarchy

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

#### BREAKING — Go: `Dbc*` → `DBC*` and `CanID` → `CANID` rename across exported surface

Go's acronym-casing convention (per `golangci-lint revive var-naming`)
calls for fully-capitalised initialisms in exported names.  The sweep
renamed 52 distinct `Dbc*` identifiers to
`DBC*` and ~40 `CanID` references to `CANID`.  Affected names include
the public types `DBCDefinition`, `DBCMessage`, `DBCSignal`,
`DBCAttribute`, `DBCComment`, `DBCNode`, `DBCSignalGroup`,
`DBCEnvironmentVar`, `DBCValueTable`, `DBCValueEntry`, and the
identifier-type alias `CANID`.  Constructor functions retained the
old `Dbc` casing (`NewDbcMessage`, `NewDbcDefinition`) and are
themselves a follow-up rename pending.

Migration: mechanical sed/perl rename on the consumer side
(`s/\bDbc/DBC/g` on type references, `s/\bCanID\b/CANID/g`); no
behavioral change.  C++ keeps the `Dbc*` form (its idiom); Python
already had `DBCDefinition` as the canonical name.

#### BREAKING — Go: `Dbc*` → `DBC*` rename completion + `DBCRawValueDesc.CANID` stutter fix

Closes the follow-up flagged in the entry above.
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

#### BREAKING — Go: predicate value fields are now `Rational`

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

#### BREAKING — Go: `Client.SendFrame` adds trailing `brs, esi *bool` parameters

The `Backend.SendFrameBinary` interface and `Client.SendFrame` /
`Client.SendFrames` method-set now accept CAN-FD BRS (bit-rate-switch)
and ESI (error-state-indicator) metadata per ISO 11898-1:2015 §10.4.2
/ §10.4.3.  Migration: pass `nil, nil` to recover prior CAN-2.0B
behaviour; pass `&trueVal` / `&falseVal` for CAN-FD frames where the
controller emitted the bits.  The Aletheia kernel does NOT consume
these bits — pass-through metadata only.

#### BREAKING — Python: `CANFrameTuple` is now a 7-tuple (`brs` / `esi` appended)

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
  Agda kernel. User-visible behavior is byte-identical on
  the test corpus; round-trip warnings now surface through
  `ValidationIssue` rather than `cantools` exceptions.
- Agda kernel facade `Aletheia.Main` re-exports five additional
  `Aletheia.Protocol.Message` constructors that had drifted out of the
  `using` list: `SendFrame` / `ParseDBCText` / `FormatDBCText` /
  `DBCTextResponse` / `ParsedDBCResponse`.  No runtime change — the FFI
  dispatcher (`processStreamCommand`) was already handling them; the
  facade now matches the actual protocol surface.
- Go `Backend` interface docstring at `go/aletheia/backend.go` gains
  structured grouping (session lifecycle + JSON command bus; binary-FFI
  send / event / state-transition endpoints; binary-FFI bidirectional
  endpoints) mirroring C++ `IBackend`'s [MANDATORY] / [OPTIONAL] split
  at `cpp/include/aletheia/backend.hpp`.  Doc-only; method signatures
  and behaviour unchanged.
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
  shapes documented in-source and carried to a tracked deferral.
  No runtime change.
- `Aletheia.DBC.JSONParser._≟-LC_` (decidable `List Char` equality)
  renamed to `_≟ₗᶜ_` (subscript-ell + superscript-c) to match the prior
  convention referenced in `Aletheia.LTL.SignalPredicate.Cache`; 8 use
  sites in JSONParser.agda updated.  `Aletheia.Parser.Combinators.elem`
  (private `Char → List Char → Bool` membership test) replaced with a
  point-free `elem c = any (c ≈ᵇ_)` over stdlib's `Data.Bool.ListAction.any`
  (≡ `or ∘ map p`); behaviour preserved, definition is no longer
  hand-rolled.  No runtime
  semantics change.
- `AGENTS.md` § CI/CD final paragraph rewritten from future-tense ("the
  first review round under this section will surface...") to past-tense
  reflecting current state: the three audit scripts and `dependabot.yml`
  are in place (2026-05-09); subsequent rounds maintain them (a cat 1 audit
  surfaced `CICD-1.2 / 1.3 / 2.3 / 3.2 / 5.1` against the scripts
  themselves); action references in `.github/workflows/` are still
  tag-pinned (`@v4`), SHA migration remains the next reviewable cat 1
  change.
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
  into the helpers.  Module count **247 → 248**.  No runtime semantics change.
- Doc-fence harness defense-in-depth: new autouse `_sandbox_cwd` fixture
  in the repo-root `conftest.py` pins every fence's cwd to a per-test
  `tmp_path` via `monkeypatch.chdir`.  Defense on top of the existing
  `pytest_sessionstart` loader patches: even if a future regression
  removes a `create_template` / loader patch or adds a new
  file-emitting fence, writes land in pytest's auto-cleaned `tmp_path`
  rather than the repo root.  Doc fences are cwd-independent (loader
  fakes ignore path args), so the chdir is invisible to fence
  behaviour.
- Streaming runtime now drops a property from the active iteration set
  when its `stepL` returns `Satisfied`, instead of re-evaluating the same
  proc on subsequent frames.  `Aletheia.Protocol.Iteration.StepOutcome`
  gains a parameterless `complete : StepOutcome S E` constructor;
  `iterateImpl` skips the property on `complete`; `length-specResult-≤`
  proves active-set monotonicity.  Internal kernel change — no
  binding-side API surface change.  See the corresponding § Fixed entry
  for the observable behaviour change.

- `cantools` is no longer a Python runtime dependency. The verified
  Agda DBC text parser replaces every code path that previously
  delegated to it. `python-can` remains an optional
  dependency under the `can` extra for log-file readers (ASC / BLF /
  MF4 etc.); replacing it is a Phase 6 goal.

### Fixed

- **Python async cancellation use-after-free.**
  Cancelling or timing out an async streaming / iter operation
  (`aletheia.asyncio.AletheiaClient.send_frames_iter`, batch `send_frames`,
  etc.) could **SIGSEGV** the process: the cancelled coroutine's
  `asyncio.to_thread` worker — which cannot be interrupted — kept running
  inside an `aletheia_*` FFI call while the client tore down (`__aexit__`
  → `aletheia_close` frees the `StreamState` `StablePtr`), so the
  abandoned worker dereferenced freed memory. Order/timing-dependent
  (surfaced by `pytest --random-order`, ~12% per full-suite run, in
  `test_timeout_during_iter`). Fixed by serialising every FFI call on the
  `StreamState` **and** `close()` through one per-client `threading.Lock`:
  teardown now blocks until any in-flight — even abandoned — call completes
  before freeing the pointer, honouring the cancellation contract's
  "in-flight runs to completion; next call after" for the Python binding
  (Go already serialised via its channel-token semaphore; C++ is
  single-client-per-thread). Verified by 60 consecutive clean
  `--random-order` runs of the reproducer that previously crashed at
  iteration 8.
- **Streaming runtime soundness.**
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
  `Always`-wrapped formulas are unaffected (per the
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
  by the first end-to-end run.  (1) `total_steps`
  default bumped from 25 to 26 to reflect the addition of
  `check-stability-bench` at step 12 (and opt-in bumps shifted +1 to
  preserve relative offsets).  (2) pylint command switched from bare
  `pylint` (system-wide pylint, no visibility into venv-only packages)
  to `<venv-python> -m pylint` so the `hypothesis` import in
  `tests/test_property_hypothesis.py` resolves and stops emitting
  E0401 (the system pylint was scoring 9.98/10 from import-error,
  blocking the gate).  (3) `clang-format` find-prune list extended
  with `./build-asan` and `./build-ubsan` so the sanitizer build
  trees' CMake-generated test files don't trip the lint.
- DBC `CM_` / `BU_` / `EV_` / `BA_*` / `VAL_TABLE_` / `VAL_` /
  `BO_TX_BU_` round-trip parity is now provable: the universal
  theorem `parseText (formatText d) ≡ inj₂ d` holds for every
  `WellFormedTextDBCAgg d` in the verified kernel
  (`Aletheia/DBC/TextParser/Properties/Substrate/Unsafe.agda`,
  closure `bca99f2`). This eliminates several silent-drop
  pathways present in the prior `cantools`-based round-trip.
- **Go**: `Client.ParseDBCText` previously emitted a non-canonical
  `"dbc.text_parsed"` log event, diverging from the `"dbc.parsed"`
  event used by `Client.ParseDBC` and the Python / C++ bindings'
  matching paths. Renamed to `"dbc.parsed"` so all DBC parse paths
  in all bindings emit a single canonical event name.
  Affects log collectors, dashboards, or alerting rules that filter
  by event name on Go logs from the text-parse path.
- **Go**: `parseValidationResponse` and `parseParsedDBCResponse`
  previously emitted `nil` slices for empty `Issues` / `Warnings`,
  diverging from Python's `[]` (empty list) default.  JSON-marshaling
  the responses produced `null` rather than `[]`.  Now initialized as
  empty slices.  Surfaced by the cross-binding integration test.
- **Python**: 3 cancellation tests (`test_timeout_mid_batch_raises_cancelled`,
  `test_explicit_task_cancel`, `test_timeout_during_iter`) intermittently
  failed under `python -X dev` due to `asyncio.timeout(0)` / `asyncio.sleep(0)`
  races in the test scaffolding.  Replaced with the public
  `aletheia.asyncio.testing.gate_send_frame` helper (paired with the
  `AsyncClient(sync_client=…)` injection seam) using `threading.Event`
  primitives without timeouts; cancellation point is pinned between
  committed frames purely via synchronization, no physical time
  involved.  50/50 runs under `-X dev` pass.
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
  imports / class names fail the build.
- **C++**: JSON parser previously dropped the `unresolvedValueDescs`
  field on the parse path even though the serializer emitted it. A
  `DbcDefinition` carrying unresolved VAL\_ entries (from the
  text-parse path) would survive the serializer round-trip on Python
  (`_helpers.py::_normalize_raw_value_desc`) and Go
  (`json.go::parseUnresolvedValueDescs`) but lose them on C++. Added
  `parse_raw_value_desc` to `json_parse.cpp` mirroring
  `raw_value_desc_to_json` in `json_serialize.cpp`; cross-binding wire
  parity restored. Three regression tests pin the parse arm + the
  serialize→parse roundtrip in `cpp/tests/unit_tests_json.cpp`.
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
  fence-execution time.
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
  in the proof tree, not the binding surface.
- **Tooling**: `tools/run_ci.py` orchestrator defects revealed by the
  first end-to-end run — fixed in a follow-up. (a) Steps
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
  separate concern, tracked as a deferral). Total step count 20→21. First genuine end-to-end pass
  logged at `tools/ci-output/ci-review-r18_-2026-05-08T*.log` (18m38s
  wall, ALL 21 STEPS PASSED). Forward-revert gate-shape verified for
  steps 15/16/17/18.

---

## [1.1.1] — 2026-04-03 and earlier

This file was bootstrapped at v2.0.0; pre-v2.0.0 history is not
retroactively documented here. Tag history (`git tag -l`): `v1.1.1`,
`v1.0.0`, `v0.3.2`, `v0.3.1-beta`, `v0.3.0-alpha`,
`v0.1.0-proof-research`, `v0.1.0-alpha`. Use `git log <tag>` for the
historical record.
