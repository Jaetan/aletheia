# Aletheia Project Status

**Last Updated**: 2026-05-26 (R23 ✅ MERGED to main at `4cb5220` + finalize `f6025e8`; current work: CI-speed gate optimization on branch `ci-speed`, not yet merged).  R22 ✅ merged to main at `3ebfc37` + clang-format follow-up `ce7bbcc`; main pushed to `origin`.

**Recent rounds**: R20 ✅ merged 2026-05-17 (`2477d5c`), R21 ✅ merged 2026-05-18 (`315c1a3`), R22 ✅ merged 2026-05-22 (`3ebfc37`).  R22 closed: AGDA-A-1.1 dead-import campaign (sweep #4 `56ac3d6` + two-tier gates `403555b`); AGDA-D-12.1 end-of-stream warnings (`d51cdb1`); Assign.agda b15 marker (`57ad862`); review-process meta-review (`80e3d2a` / `36fc47b` / `9f7d38e` / `b98661e` / `92bb3ae`).  R23 launched on the new protocol — delta scope on Step 1A/1B (saved 6 agents); whole-program on Step 1C + Step 2; cat 1 Agda graduated.

**R23**: all 57 findings status:closed (54 FIX + 3 FP-VERIFIED).  AGDA-D-10.1 — `SignalPredicate.signalName : List Char → Identifier`; JSON parser made reason-carrying (`ParseFail ⊎ _`, forked validity walk removed); handler verdict→wire-error routing PROVEN in new `Protocol/Handlers/Properties.agda` — closed at `050ba2f` (YAML `0f101be`); redundant per-binding behavior tests dropped (routing binding-independent — proven once kernel-side).  Earlier closes: AGDA-C-5.1 (`165de76`), CPP-D-15.1/15.2 (`8aff66b` / `e15d7d8`), CPP-D-17.1 (`c348317`), AGDA-D-12.1 (`7dc4fcb`).  Critical (XDOC-15.1 module count drift) raised AND closed in-round at `66cf92b` cluster A doc-sync; no carry-forward criticals.  **✅ MERGED to main** (merge `4cb5220` + finalize `f6025e8`, 2026-05-26).

**CI-speed gate optimization** (post-R23 user directive, branch `ci-speed`, NOT merged): make the verification gates fast enough that every contributor runs them manually + often.  Core insight — ONE warm `agda --interaction-json` process loads stdlib + interfaces once (vs ~14s per-invocation reload × N), attacking "calling Agda too often".  **Step 9** dead-import gate (was ~hours) → `tools/warm_dead_imports.py`: warm candidate-sieve + brute-force-confirm-*only-candidates* (~64× for a batch; filters the inferred-type-use FP class).  **Steps 1-8** check-properties (629s) → `tools/warm_check_properties.py` + Shakefile `check-properties-warm` (one process for all 45 proof modules, **~13×**: 629s→47.6s; batch-equivalence verified).  **#1 production-usability** done (`1312115`): portable (no hardcoded paths; `tools/` package; `python -m tools.X`) + pylint 10.00 / basedpyright 0/0/0.  Roadmap: wire `run_ci` (batch authoritative until weeks of agreement), land 5 confirmed dead imports, steps 10-30, merge.  Detail + roadmap: `memory/project_ci_speed_optimization.md`.

**Closure narratives**: per-round detail in `memory/project_review_round{18,19,20,21}.md`; structured per-finding YAML at `.archive/reviews/r{20,21,22,23}/findings/` (queryable via `tools/review_db.py`); historical PROJECT_STATUS narrative paragraphs preserved verbatim in [`docs/archive/PROJECT_STATUS_HISTORY.md`](docs/archive/PROJECT_STATUS_HISTORY.md).

---

## Current Position

**Phase 5.1 - Proof Gaps & Spec Observations** ✅ COMPLETE. **Track A (matrix + structural gates)** + **Track B.1 / B.1.x (DBC metadata Tier 1 + Tier 2 + signal receivers + message senders)** + **Track B.2 (mux query helpers — audit-closed)** + **Track B.3.a (corpus baseline) / B.3.b (Agda skeletons) / B.3.c (incremental construct implementation)** ✅ COMPLETE, following the [Cross-Binding Parity Plan](docs/development/PARITY_PLAN.md) locked 2026-04-20.

Phases 1-5.1 complete. Phase 5 delivered optional extensions driven by user feedback: CAN-FD, multi-language bindings (C++, Go), binary FFI, formal verification completion, benchmarks. Phase 5.1 closed all 2026-04-07 system-review items. All provable correctness properties are proven.

Post-R17 work now follows the parity plan rather than the generic "Phase 6" label. Active tracks:
- **Track A** ✅ — `docs/FEATURE_MATRIX.yaml` is the authoritative parity source (40 rows × 3 bindings); structural gates in Python / C++ / Go fail CI on any unresolved `implemented` entry.  Row count is live in the YAML — do not duplicate inline.
- **Track B.1 / B.1.x** ✅ — DBC metadata Tier 1 + Tier 2 + signal receivers + message senders (`BO_TX_BU_`) flow end-to-end through Agda core → FFI → bindings with roundtrip proofs.
- **Track B.2** ✅ — Mux query helpers + DBC lookups, closed via audit (binding surface pre-existed client-side); matrix rows `dbc_queries_mux` + `dbc_lookup` both `implemented` × 3.
- **Track B.3** ✅ COMPLETE 2026-05-03 — Agda-core DBC text parser bound across all three bindings (R17-DEF-4 closed).  Final ship sequence: B.3.d universal roundtrip theorem `bca99f2` (Layer 4c task E; proof in `Substrate/Unsafe.agda` per Unsafe-module-policy) → B.3.e/h/i `bc7a5fc` (JSON binding + `ParsedDBCResponse` envelope + C++/Go bindings) → B.3.j `3673cd2` + `3404dec` (cross-binding corpus parity gate + native canonical wire form) → B.3.f `019d014` (Python `dbc_to_json` flipped to verified Agda parser; surfaced + fixed two Python-side parity asymmetries — `parse_parsed_dbc_response` runs `normalize_dbc` so callers see `Fraction` rationals; `FractionJSONEncoder` canonicalised to "emit int when denominator=1") → B.3.g `2daa2fb` (cantools fallback dropped outright; ~3,560 net LOC removed; `[dbc]` extra retired from `pyproject.toml`).  All three bindings (Python `dbc_to_json` / `parse_dbc_text`, C++ `parse_dbc_text`, Go `ParseDBCText`) now run on the verified Agda parser with B.3.d's universal roundtrip underwriting them.  LGPL contingency for cantools fully realised.
- **Track C** ✅ — Idiomatic cancellation across all three bindings shipped 2026-05-03 (C.0 `docs/architecture/CANCELLATION.md` SSOT + C.1+C.2 Python `aletheia.asyncio.AletheiaClient` + sync `send_frames_iter` + C.3 Go `context.Context` + C.4 C++ `std::stop_token`). FEATURE_MATRIX `cancellation_contract` × 3 + `lazy_streaming_batch` × 3 rows all flipped to `implemented` (or `not_applicable` for cpp/go on lazy-iter where the language idiom already covers the case). See `memory/project_track_c_cancellation.md` for design + implementation post-mortem.
- **Track D** ✅ COMPLETE 2026-05-04 — doc-example harness mirror of R17 C6 (R17-DEF-6) bound across all three bindings; **R17-DEF-6 fully closed**. **D.2 (Go) ✅** shipped 2026-05-04 (`d0ae26b`): every ```go``` fence in 5 tracked markdown files extracted, wrapped, and executed via `go run` in `go test ./aletheia/`; structural gate via `TestNoNotestGoFences` + `TestEveryDocFileHasAtLeastOneGoFenceCollectively`; FEATURE_MATRIX `doc_example_gate_checks.go` flipped `planned` → `implemented` (entry: `Client`); 4 dead doc references caught + fixed (`PITCH.md` L45/L166, `CANCELLATION.md` L66/L182, `INTERFACES.md` L66/L77/L101). **D.1 (C++) ✅** shipped 2026-05-04 (`82d0347`): every ```cpp``` fence in 5 tracked markdown files compiled via `popen()` to `${CMAKE_CXX_COMPILER}` + executed via `ctest` (`doc_example_tests`, ~500 LOC, registered alongside the existing 7 ctest targets); static-archive paths for `aletheia-cpp` + `yaml-cpp` + `OpenXLSX` wired through `target_compile_definitions` using `$<TARGET_FILE:...>` generator expressions; structural gate via `TestNoNotestCppFences` + `≥6` collective cpp fence floor; FEATURE_MATRIX `doc_example_gate_checks.cpp` flipped `planned` → `implemented` (entry: `aletheia/client.hpp#AletheiaClient`); 4 dead doc references caught + fixed (`PITCH.md` L42/L157 — `PhysicalValue{220}` → `PhysicalValue{Rational{220, 1}}` since ctor takes `Rational`; `CANCELLATION.md` L84/L228 — signature-only fence + illustrative streaming worker referencing undefined symbols flipped ```cpp``` → ```text```; `INTERFACES.md` L52/L63/L74/L86/L99/L665 — `Check` namespace correction, missing `ltl::atomic` wrap, top-namespace YAML/Excel loaders, missing `std::stop_token{}` first arg post-Phase-C.4 (parallel to Go's L101 fix), `LogField` structured binding + `std::visit` for variant printing).
- **Track E** ✅ COMPLETE 2026-05-08 on branch `b3d-3d5-format-dsl` — VAL_ promotion to `DBCSignal.valueDescriptions`.  E.1 (record-field cascade) + E.2 (JSON wire layer) + E.3 (binding-side JSON unwrap) + E.4 (text-parser flip) + E.5α/E.5β (aggregator + per-section Format DSL roundtrip) + E.6 (Refine `attachValueDescs` + inverse-bridge) + E.7 (text formatter wiring + vacuous closure under `MessageWF.vds-empty`) + E.8 (`WellFormedText.ValueDescResolves` predicate) + E.9a (relax `vds-empty` interim clauses + non-vacuous `tvd-WF` via `clearVdsMsg` cascade through `liftTopStmt` — universal now holds for arbitrary DBCs modulo other `WellFormedDBC` fields) + **E.10 (FFI command `formatDBCText` + Python/C++/Go `format_dbc_text` Client method + Agda-handler `deriveNodesIfEmpty` for uniform sender→nodes derivation across bindings + Python wire-shape symmetry fix `normalize_dbc_for_wire` + JSON formatter escape pass closing serializer/parser inverse-pair gap; 1 NEW module `Aletheia/Protocol/Handlers/FormatDBCText.agda` + ~14 modified across 4 layers; closes the C3 deferral) + **E.11 (Validator CHECK 23 `UnknownValueDescriptionTarget` walking `DBC.unresolvedValueDescs` flat per Plan B; CHECK 21 `UnknownSignalReceiver` binding-mirror gap fix; `python/aletheia/validation.py` NEW splitting `IssueSeverity`/`IssueCode`/`ValidationIssue` out of `protocols.py` to clear pylint C0302; Agda module count unchanged at 244, +1 NEW Python module)** + **E.12 (FEATURE_MATRIX +2 rows `dbc_signal_value_descriptions` + `dbc_text_format`; per-binding tests Python `TestDBCSignalValueDescriptions` × 4 cases + Go `TestParseDBCText_ValueDescriptionsRoundTrip` + `_UnknownValueDescriptionTargetWarning` + C++ integration `VAL_ value descriptions round-trip via real FFI` + `CHECK 23 unknown_value_description_target warning via real FFI`; INTERFACES.md `format_dbc_text` doc-example fences (Python/C++/Go); Plan-A bundled ship commit)** all shipped per `feedback_no_unilateral_deferral`'s self-contained-commit principle.  Module count 237 → 240 → 242 → 243 → **244** at E.10 (E.11/E.12 unchanged on Agda side; +1 NEW Python module `aletheia/validation.py`).  Full session detail in `memory/project_track_e_val_promotion.md`.

**Status**: Phase 5.1 + Track A + Track B.1/B.1.x + Track B.2 + **Track B.3 (Agda-core DBC text parser, all of B.3.a–B.3.j) ✅ COMPLETE 2026-05-03** + **Track C (cancellation contract across all three bindings) ✅ COMPLETE 2026-05-03** + **Track D (cross-binding doc-example harness, R17-DEF-6) ✅ COMPLETE 2026-05-04** + **Track E (VAL_ promotion to `DBCSignal.valueDescriptions`) ✅ COMPLETE 2026-05-08** on branch `b3d-3d5-format-dsl`: E.1–E.12 shipped as the Plan-A bundled commit; Agda module count 237 → 240 → 242 → 243 → **244** at E.10 (E.11/E.12 modify-only on Agda side; +1 NEW Python module `aletheia/validation.py`).  Full plan in `memory/project_track_e_val_promotion.md`.

---


## Project Phases

All Phases 1 through 5.1 are ✅ COMPLETE.  Phase-by-phase detailed narrative is in [`docs/archive/PROJECT_STATUS_HISTORY.md`](docs/archive/PROJECT_STATUS_HISTORY.md); a one-line summary table follows.  Phase 6 (planned) detail is preserved in full below.

| Phase | Title | Status | Key deliverables |
|---|---|---|---|
| 1   | Core Infrastructure                  | ✅ | Agda → MAlonzo → Haskell → Python pipeline; baseline CAN frame analysis. |
| 2A  | LTL Core + Real-World Support        | ✅ | LTL syntax + semantics + coalgebra; signal predicates; DBC integration. |
| 2B  | Streaming Architecture               | ✅ | Incremental LTL stepping; warm-cache reachability; protocol layer. |
| 3   | Verification + Performance           | ✅ | Soundness/adequacy proofs; binary FFI; Bool fast-path. |
| 4   | Production Hardening                 | ✅ | Cross-binding parity; mock backends; error taxonomy; structured logging. |
| 5   | Optional Extensions                  | ✅ | CAN-FD; C++ binding; Go binding; cross-language benchmarks; DBC text parse. |
| 5.1 | Proof Gaps & Spec Observations       | ✅ | Closes Phase 4/5 review carryover; eight observation items resolved. |
| 6   | Extensions & New Protocols           | Planned | See dedicated section at end of file. |

### Post-R17 parity tracks

Tracks A–E ✅ all complete (R17 deferral closure path):

| Track | Scope | Status |
|---|---|---|
| A    | Feature matrix + structural gates                       | ✅ 2026-04-28 |
| B.1  | DBC metadata Tier 1                                     | ✅ 2026-04-20 |
| B.1.x| DBC metadata Tier 2 + signal receivers + senders        | ✅ 2026-04-20 |
| B.2  | Mux query helpers + DBC lookups                         | ✅ (audit) |
| B.3  | Agda-core DBC text parser (universal roundtrip)         | ✅ 2026-05-03 |
| C    | Cancellation contract bound across all 3 bindings       | ✅ 2026-05-03 |
| D    | Cross-binding doc-example harness                       | ✅ 2026-05-04 |
| E    | VAL_ promotion to `DBCSignal.valueDescriptions`         | ✅ 2026-05-08 |

Track narratives and per-step detail live in `memory/project_track_{c,e}_*.md`, `memory/project_b3{d,e}_*.md`, and `docs/development/PARITY_PLAN.md` (the live roadmap).

## Key Metrics

**Codebase**:
- Agda modules: **264** (259 `--safe --without-K` + 4 `--safe --without-K --no-main` + 1 allowlisted `--without-K`-only `Substrate.Unsafe`).  Per-round evolution detail in `memory/project_review_round{18,19,20,21}.md` and `docs/archive/PROJECT_STATUS_HISTORY.md`.
- Python modules: 32 (19 top-level + 10 in `aletheia/client/` subpackage + 3 in `aletheia/asyncio/`)
- C++ files: 54 (15 public headers + 1 public detail header + 11 source + 3 internal detail headers + 23 test `.cpp` + 1 `test_helpers.hpp`)
- Go files: 23 source + 28 test (in `go/aletheia/`); separate `go/excel/` package for the optional Excel loader. Source-file count includes 6 `*_string.go` files generated by `stringer` (R19 cluster 14 / GO-A-6.2).
- Lines of code: ~15,500 Agda + ~5,300 Python + ~4,000 C++ + ~4,400 Go (source only)

**Testing**:
- Python tests: 872 collected (via FFI) + 1 expected-skip (`test_lazy_import_boundary.py` skips when `_install_config.py` isn't present — guards the dev-checkout vs installed-wheel boundary); additionally doc-example `python` fences executed end-to-end by `pytest --markdown-docs` via the repo-root `conftest.py` harness (R17 C6). Includes cross-binding parity tests (`tests/test_feature_matrix_parity.py`) that validate `docs/FEATURE_MATRIX.yaml` schema (40 rows live; row count tracked in the YAML, not duplicated inline) + every Python `implemented` entry
- C++ tests: 198 unit + 39 integration + 33 YAML + 47 Excel + 2 parity TEST_CASEs + 3 log-events + dbc-corpus + 9 cross-binding-integration (331 total) across 8 runtime ctest binaries (`unit_tests`, `integration_tests`, `yaml_tests`, `excel_tests`, `feature_matrix_tests`, `log_events_tests`, `dbc_corpus_parity_tests`, `cross_binding_integration_tests`) + 1 compile-time binary (`static_tests`); `feature_matrix_tests` reads `docs/FEATURE_MATRIX.yaml` and verifies every C++ `implemented` entry resolves to a header + whole-word symbol under `cpp/include/`
- Go tests: 283 listed in `go/aletheia` across 28 test files (mock backend, `-race` clean); the optional `go/excel` package is a separate Go module and is not counted in the total. Includes 2 parity tests (`feature_matrix_test.go`) that validate the matrix schema + every Go `implemented` entry via `go/ast` source parsing (handles `Type.Method` receivers and `excel:<ident>` sub-package references)
- Total: 1480 tests (live aggregate; C++ + Go subtotals approximate post-R20/R21 — Python is the authoritative count refreshed every closure)

**Performance** (canonical source — other docs may round or summarize these numbers):

*Benchmarks: 10,000 frames × 5 runs, AMD Ryzen 9 5950X, Linux 6.6 (WSL2). C++ g++-15 -O3, Go 1.26.1 (benchmark host; required floor is Go 1.24+ per BUILDING.md / `go.mod`), Python 3.13.12.*

| Benchmark | C++ (fps) | Go (fps) | Python (fps) | Measured |
|---|---:|---:|---:|---|
| CAN 2.0B: Stream LTL (2 props) | **109,345** | 97,082 | 70,917 | 2026-04-06 |
| CAN 2.0B: Signal Extraction | **212,857** | 166,527 | 87,424 | 2026-04-06 |
| CAN 2.0B: Frame Building† | **76,469** | 71,692 | 55,093 | 2026-04-06 |
| CAN-FD: Stream LTL (3 props) | **48,248** | 47,516 | 34,737 | 2026-04-06 |
| CAN-FD: Signal Extraction | **14,930** | 14,493 | 12,143 | 2026-04-06 |
| CAN-FD: Frame Building† | **20,567** | 20,052 | 17,830 | 2026-04-06 |

† Frame Building rows have an additional post-fix 2026-04-08 measurement documented in the note immediately below the table; those numbers are not the canonical ones and are deliberately not substituted here.

> **Frame Building regression resolved (2026-04-08).** An earlier 30–65% regression on Frame Building rows (commit `5aa345e`, introduced by the `physicallyDisjoint?` Dec-valued check in `BatchFrameBuilding.hasOverlaps`) was traced via `git worktree` bisection and fixed by a Bool-valued fast path with formal equivalence proofs in `DBC/Properties.agda` (`signalsPhysicallyOverlapᵇ`, `physicallyOverlapᵇ-sound`, `physicallyOverlapᵇ-complete`). Per-signal physical bit lists are precomputed once in `hasOverlaps` and the O(m²) pair loop runs over cached lists with primitive ℕ equality — no `Dec` allocations on the hot path. See `project_frame_building_regression_2026_04_07.md` and AGENTS.md Category 16 for the cost-model lesson. The canonical numbers above still reflect the 2026-04-06 steady state; post-fix measurements (10000 frames × 5 runs, 2026-04-08) show Frame Building at C++ 58,712 / Go 65,106 / Python 47,789 (CAN 2.0B) and C++ 15,226 / Go 17,181 / Python 14,858 (CAN-FD) — a full +107–147% recovery on CAN-FD vs the regression state. The remaining gap (~10–25%) vs canonical reflects system noise plus residual list-representation overhead; further optimization is not blocked.

> **Note on C++ vs Go on Frame Building.** Frame Building is the only benchmark where Go can overtake C++, and the 2026-04-08 run does show Go +11% on CAN 2.0B and +13% on CAN-FD. This is not a C++ vs Go performance truth — it is benchmark geometry. Frame Building does the *least* Agda work per call and the *most* binding-side work, so per-call glibc `malloc` for the three scratch `std::vector`s in `AletheiaClient::build_frame` plus `std::unordered_map<SignalKey, uint32>` lookups become visible relative to Go's per-P bump allocator and built-in map. Stream LTL and Signal Extraction remain clearly C++-dominant. Future C++ optimizations (thread-local scratch buffers, small-vector, `ankerl::unordered_dense` / `absl::flat_hash_map`) would likely recapture the Frame Building lead but are not scheduled. See `project_cpp_vs_go_frame_building.md` for details.

- Build time: 0.26s (no-op), ~11s (incremental)
- Per-frame latency: ~9 us (CAN 2.0B streaming, C++)
- Memory: O(1) verified (1.08x growth across 100x trace increase)
- **Binary FFI**: All hot-path operations use binary FFI (no JSON parsing): `aletheia_send_frame` (streaming), `aletheia_extract_signals_bin`, `aletheia_build_frame_bin`, `aletheia_update_frame_bin`. All three bindings call the binary endpoints directly.
- **Single-threaded runtime**: Deployable to minimal containers (1 vCPU) with headroom over a 500 kbit/s CAN bus (~4,000 frames/sec). CAN-FD at 5 Mbit/s requires ~6,000 fps — all operations exceed this across all bindings (minimum: 12,143 fps Python CAN-FD extraction, 2x headroom).
- **Multi-bus scaling**: Each `AletheiaClient` has independent state (`StablePtr`). Multiple Python threads can monitor separate CAN buses in parallel. ctypes releases the GIL during FFI calls. For N buses on N vCPUs, pass `-N` to `hs_init` for parallel GHC capabilities.

**Verification**:
- 263 of 264 Agda modules use `--safe --without-K` (4 also use `--no-main`; 1 allowlisted `--without-K`-only `Substrate.Unsafe` hosts the two stdlib-equivalent `String ↔ List Char` bridging axioms + the universal `parseText (formatText d) ≡ inj₂ d` consumer)
- Zero postulates in production code
- All provable correctness properties proven (LTL adequacy, DBC validation, signal roundtrip, frame processing, predicate table, signal cache, response formatting, initial state, metric operator window bounds)
- **Pipeline soundness proven**: 8 unsound absorption rules removed, 4 remaining guarded with `finalizesHolds`, 2 structural idempotency rules added. `absorb-runL`, `simplify-runL`, `pipeline-adequate`, `production-adequate` all proven in `Adequacy/Pipeline.agda`
- **All verification suites green**: Python (basedpyright 0 errors, pylint 10.00/10), C++ (clang-format clean, clang-tidy clean, all ctest suites pass), Go (go test -race, go vet, gofmt all clean)

---

### Phase 6: Extensions & New Protocols (Planned)

**Scope**: Binding feature gaps, dependency cleanup, and automotive Ethernet support.  Goal-set refreshed 2026-05-07 after R17 fully closed.

**Binding feature gaps** (closed en route — kept for archaeology):
- ~~DBC `.dbc` text file parsing for C++ and Go~~ ✅ Closed by Track B.3 2026-05-03 (`bca99f2`).
- ~~Go multiplexing query helpers~~ ✅ Closed by Track B.2 audit 2026-04-XX (helpers were already shipped client-side).

**Binding feature gaps** (active):
- **CLI parity for C++/Go (stretch goal, 2026-05-07)** — Python ships `python -m aletheia` with six subcommands: `check` / `validate` / `extract` / `signals` / `format-dbc` / `mux-query`.  C++ and Go are currently `not_applicable` in the FEATURE_MATRIX with reason "library bindings; CLI tools are a host-application concern."  Stretch-goal flip: rebuild the same subcommand surface in each language as a thin host binary dispatching to the existing client API.  Estimate ~300-500 LOC per language (CLI is glue, not parser, so the estimate is honest).  No Agda or FFI changes.  Drives a `cli` matrix row flip from `not_applicable` to `planned` × 2.

**Toolchain upgrades**:
- Upgrade `basedpyright` and `pylint` to the latest stable releases, re-verify the 0/0/0 + 10.00/10 gates on the updated versions, and bump the upper pins in `python/pyproject.toml` (`basedpyright>=1.0,<2`, `pylint>=3.0,<4`) accordingly.

**LGPL contingency** (refreshed 2026-05-07):
- ~~cantools (transitively LGPL via python-can)~~ ✅ Closed by Track B.3.g (`2daa2fb`).  Verified Agda DBC text parser replaces it.
- **python-can replacement (Phase 6 goal)** — `python/aletheia/can_log.py:22` imports `python-can` for ASC/BLF/MF4/etc. log file readers; declared as optional `can = ["python-can>=4.0"]` extra in `pyproject.toml:58`.  **Estimate is open, not "~300 LOC"**: per project rule "parsers are Agda + proof" (`feedback_parsers_are_agda_with_proof.md`), each log format goes through the verified kernel — Agda implementation + roundtrip proof + binding wire layer per format (ASC text, BLF binary; MF4 deferred to `asammdf` BSD-3 if needed).  Track B.3 (DBC text parser) is the closest precedent: ~6 weeks of Agda + universal roundtrip theorem.  The 2026-03-22 ~300 LOC memo was based on a Python glue assumption that is invalid for this project.
- **GHC `--bignum=native` rebuild (Phase 6 goal)** — `libgmp` (LGPL-3.0) currently links into `libaletheia-ffi.so` because GHC defaults to `integer-gmp`.  Replacement: rebuild GHC with `--bignum=native` (BSD-3, pure Haskell).  **Deliverable is a step-by-step + tested procedure**, not just a config flip — script + verified commands on a clean machine, with before/after FFI .so hash + benchmark snapshot to confirm no regression.  Lives in `docs/development/` alongside BUILDING.md.

**SOME/IP support**:
- Extend Aletheia to automotive Ethernet via SOME/IP (Scalable service-Oriented MiddlewarE over IP)
- SOME/IP is fundamentally different from CAN: service-oriented rather than signal-based, with a 16-byte header and variable structured payloads
- Requires new frame model, extraction logic, and LTL atomic predicates (service-level: response timing, subscription freshness, method sequencing)
- Existing LTL engine is reusable; also covers CAN-over-Ethernet (DoIP/ISO 13400)

**Status**: Not started.  Goal-set locked 2026-05-07; no commitments to a phase ordering yet.

---

**End of Status Report**
