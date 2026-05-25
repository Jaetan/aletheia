# R23 — Review findings (working draft)

**Branch**: `review-r23` forked from `main@ce7bbcc` 2026-05-22.
**Round shape**: first full review under the R22 meta-review protocol (delta scope on Step 1A/1B; whole-program on Step 1C + Step 2; cat 1 Agda graduated; tighter agent reporting).
**Agents launched**: 11 (Step 1: agda-C, cpp-A, cpp-B, docs-A, docs-B, cicd-A; Step 2: agda-D, go-D, cpp-D, python-D, cross-doc).
**Total raw findings**: ~219 (Step 1: ~109; Step 2: ~110).

This file is round-scope working state per `memory/feedback_review_branch_workflow.md`. At round close it is either archived to `.archive/reviews/r23/working.md` or deleted; the durable record is per-finding YAML at `.archive/reviews/r23/findings/*.yaml`.

---

## Severity distribution (across all findings)

| Severity | Count (approximate) |
|---|---:|
| Critical | 1 (cross-doc 15.1: module count drift) |
| High | ~25 |
| Medium | ~60 |
| Low | ~95 |
| Info | ~38 |

No HIGH/CRITICAL regressions of prior closures (re-raise count = 0).

---

## Cluster proposal

Findings group naturally into 7 clusters. Each cluster maps to one or more closure commits per the user-redirect protocol.

### Cluster A — Doc-sync sweep (stale numeric facts)

The dominant finding cluster: R22's PROJECT_STATUS.md compression + CHANGELOG / BUILDING / CLAUDE drift left ~15 inline numbers stale. Single-commit fix possible if user approves.

| Finding | File:line | Severity | What |
|---|---|---|---|
| XDOC-15.1 | PROJECT_STATUS.md:68,107 | **critical** | Agda module count says 250; actual = 263 (CLAUDE correct) |
| XDOC-15.2 | CLAUDE.md:167,171 + CHANGELOG.md:86 + COOKBOOK.md:447 | high | Log event count 15; actual = 16 (R22 D-12.1 added the 16th) |
| XDOC-15.3 | AGENTS/docs.md:39 | high | Cat 22 rubric says "the 15 shared events"; meta-rule itself is stale |
| XDOC-15.4 | PROJECT_STATUS.md:20,75 | high | FEATURE_MATRIX rows said 35 / 38; actual = 40 |
| XDOC-15.5 | CLAUDE.md:171 + go/README.md:57 | high | Go concurrency primitive said `sync.Mutex`; actual = `lockCh chan struct{}` |
| XDOC-15.6 | INTERFACES.md:38 vs :55 + PITCH.md | high | C++ Check namespace casing inconsistent (`check::` vs `Check::`) |
| XDOC-15.7 | BUILDING.md:180 vs PROJECT_STATUS.md:82 | high | Go version: 1.24+ (floor) vs 1.26.1 (benchmark headline) — pick one or label both |
| XDOC-15.8 | BUILDING.md:124-125 vs pyproject.toml | medium | "Minimum 3.12" but pyproject says `>=3.13` |
| XDOC-15.9 | PROJECT_STATUS.md:75 | medium | Python tests claim 866; actual ~872p+1s |
| XDOC-15.10 | BUILDING.md:125 vs 301 vs 332 | medium | Same file internal inconsistency on Python version floor |
| XDOC-15.11 | CHANGELOG.md:42 vs :86 | medium | Same file internal inconsistency on 15→16 event count |
| XDOC-15.12 | PROJECT_STATUS.md:76 vs CLAUDE.md:264 | medium | C++ "8 runtime ctest binaries" vs "ctest 10/10" — disambiguate labels |
| DOCS-A-1.16 | PROJECT_STATUS.md:3 | low | "R22 ready to merge" is now historical — R22 merged at 3ebfc37 |
| XDOC-5.1–5.10 | (across docs) | medium-low | 10 fact duplications between PROJECT_STATUS, README, PITCH, CLAUDE, CANCELLATION, AGENTS — consolidate to canonical source + link |

**Disposition**: FIX (single doc-sync commit).

### Cluster B — Agda hygiene + proof-tree cleanup

| Finding | File:line | Severity | What |
|---|---|---|---|
| AGDA-C-3.1 | TextParser/Properties/Aggregator/Universal.agda:140-190 | medium | `-WF` naming uppercase vs project-wide `-wf` lowercase (60+ uses); rename to lowercase |
| AGDA-C-5.1 | DBC/JSONParser.agda:139,148 | medium | Literal "non-integer in multiplex_values" duplicated; centralise or split into typed ctor |
| AGDA-C-5.2 | TextParser.agda:238 + Error.agda:351 | low | `AttributeRefinementFailed : String → DBCTextParseError` payload is single-valued; drop payload, inline in formatter |
| AGDA-C-6.1 | Validity/Composition.agda:94-148 | medium | 6 pairs of `requireDec`/`rejectDec` boilerplate; add `-allE` lemmas to `Validity.Combinators` |
| AGDA-C-6.2 | CAN/Encoding/Properties/Arithmetic/Integer.agda | low | 13 scattered local imports; consolidate to module-top |
| AGDA-C-6.3 | DBC/Properties/Disjointness.agda | low | 3 scattered local imports; consolidate |
| AGDA-C-27.1 | TextParser/Properties/Aggregator/Universal.agda:127-138 | medium | `all-map` / `all-++` re-implement stdlib; use `Data.List.Relation.Unary.All.Properties.{map⁻,++⁺}` |
| AGDA-A-1.1 / 1.2 | Aletheia.Main facade | low | `open import M public using ()` re-exports nothing; either real public surface or doc comment |

**Disposition**: FIX (cluster commit; rename + dedup + stdlib lift).

### Cluster C — C++ delta-region cleanup

| Finding | File:line | Severity | What |
|---|---|---|---|
| CPP-A-4.1 | json_parse.cpp:151-156 | medium | Stale "three codes" comment on `is_input_bound_exceeded_code` (only 1 code checked) |
| CPP-A-1.1 | json_parse.cpp:157-159 | low | `is_input_bound_exceeded_code` is trivial 1-line helper; inline at single call site OR keep with refreshed comment |
| CPP-B-12.1 | json_parse.cpp:917-927 | medium | Warnings loop `w.at("property_index")` no `contains()` guard; protocol-vs-bound-exceeded shape |
| CPP-B-12.2 | json_parse.cpp:131-140 | low | `parse_bounded` throws runtime_error; wrap as typed `InputBoundExceeded` or document as defense-in-depth |
| CPP-A-5.1 | json_parse.cpp:373,630 | low | Error message "exceeds uint16 range" leaks impl type; should say "11-bit standard-frame range" |
| CPP-A-6.1 | json_parse.cpp:364-380 vs :621-637 | medium | Byte-identical 17-line CanId-construction lambda duplicated; extract `json_to_can_id` helper |
| CPP-A-6.2 | json_parse.cpp:193-297 | low | Three parsers share `{numerator, denominator}` decoding; extract `parse_rational_dict` helper |
| CPP-A-6.3 | json_parse.cpp:214-258 | low | 21-entry `if/else if` chain; use the same table pattern as `error_code_table` |
| CPP-A-6.4 | json_parse.cpp:501-517 | low | 7-entry `if/else if` chain for attribute scopes; use table pattern |
| CPP-A-4.2 | json_parse.cpp:142-150 vs :161 | low | `///` doc block separated from `make_json_error` by unrelated helper |
| CPP-B-26.2 | json_parse.cpp:902-911 | low | Two-step empty-or-assign of `reason`; explicit form is correct but document why over `value("reason", string{})` |

**Disposition**: FIX (cluster commit on cpp delta).

### Cluster D — Agda system-level

| Finding | File:line | Severity | What |
|---|---|---|---|
| AGDA-D-17.1 | haskell-shim/ffi-exports.snapshot:36-49 + BinaryOutput.hs:93 | high | `d_extractionErrorCodeToℕ_148` missing from "Indirect helper accessors" section; add `F:` line |
| AGDA-D-10.1 | LTL/SignalPredicate/Types.agda:69-88 | medium | `signalName : List Char` carries no DBC-identifier witness; unify with `Identifier` |
| AGDA-D-32.1 | LTL/JSON.agda:37-95 | high | `parseSignalPredicate` accepts unbounded signal names; add `IdentifierLength` bound OR promote field to `Identifier` |
| AGDA-D-11.2 | Protocol/Handlers.agda:278-284 | medium | `handleSetProperties` accepts unbounded property count; add `max-properties-per-stream` to BoundKind |
| AGDA-D-10.2 | Protocol/StreamState.agda:77-80 | low | `handleTraceEvent` (Error/Remote) accepts events in any state; should reject in WaitingForDBC / ReadyToStream |
| AGDA-D-11.1 | Protocol/StreamState.agda:77-80 | medium | Error/Remote events skip `checkMonotonic`; cross-event-type monotonicity uncovered |
| AGDA-D-12.1 | Protocol/StreamState/Internals.agda:259-266 | medium | Properties that reach `Satisfied` mid-trace silently absent from `Complete.results` |
| AGDA-D-12.2 | Protocol/Handlers.agda:330-348 | low | `collectUncachedWarnings` walks only active props; misses warnings from `complete`d properties |
| AGDA-D-15.1 | Aletheia/Main.agda facade | low | Same as AGDA-A-1.1 (facade `using ()` empty) |

**Disposition**: FIX (D-17.1 fast; D-10.1/32.1 paired with Identifier refactor; D-11.2 add BoundKind ctor; D-10.2/11.1 paired state-machine refactor; D-12.1/12.2 paired Complete-results refactor).

### Cluster E — Cross-binding parity (R22 first-test surface)

| Finding | File:line | Severity | What |
|---|---|---|---|
| CPP-D-15.3 + GO equivalent | cpp/include/aletheia/ltl.hpp:188-194 + go/aletheia/ltl.go:92-97 | medium | `ltl::next`/`weak_next` (C++/Go) lack the "Discouraged on CAN" annotation Python documents at dsl.py:809+ |
| CPP-D-22.3 | cpp/src/client.cpp:69-82 | medium | `rts_cores_mismatch` warning silently dropped when no logger wired; Python+Go emit unconditionally |
| CPP-D-22.2 | cpp/include/aletheia/client.hpp:57-73 | low | Adequacy doc-comment doesn't reference `StreamWarning{kind:"uncached_atom"}` mechanism |
| GO-D-22.3 | go/aletheia/client.go:752 | high | `parseEventAck` checks `"ack"`; Python+C++ also accept `"success"` — verify symmetry |
| GO-D-17.1 | go/aletheia/renderer.go:69 | medium | `RegisterDefaultLibPath` is public in Go; C++ keeps in `detail::` namespace |
| GO-D-17.2 | go/aletheia/ffi.go:173 | low | `StablePtrCount` is public in Go; C++/Python have no equivalent exposed |
| GO-D-31.1 | multiple test files | medium | Test files calling `NewFFIBackend` lack `//go:build cgo && linux` tags |
| GO-D-31.2 | go/aletheia/renderer.go vs enrich.go | low | `formatRationalFFI` no-cgo stub panics on call; document loud-failure behaviour |
| PY-D-22.6 | python/aletheia/client/_enrichment.py:138-201 | medium | `_format_rational` module-global `_renderer_lib` lazy-load lacks `threading.Lock` (Go uses `sync.Once`, C++ `std::call_once`) |

**Disposition**: FIX (cross-binding cluster — touches all 3 bindings).

### Cluster F — Structural / architecture-scale

| Finding | File:line | Severity | What |
|---|---|---|---|
| PY-D-16.1 | python/aletheia/client/_helpers.py:1-12 | medium | 798+ LOC, multiple concerns; R19 DEFER condition now met (coherent sub-modules emerged); split into `_helpers/{rational,dbc_normalize,json_codec}.py` |
| PY-D-16.2 | dsl.py:27 + cli.py:39 + excel_loader.py:89 + dbc_converter.py:19 | high | 4 non-client modules reach into `aletheia.client._helpers` (private); promote public surface |
| PY-D-16.3 | python/aletheia/asyncio/_client.py:28-30 | medium | Async sibling reaches across into peer's private modules; either move into client/ or promote dependencies |
| CPP-D-17.1 | cpp/src/rational_renderer.cpp + ffi_backend.cpp | medium | Two independent `dlopen` + `hs_init` sites; cross-singleton ordering undocumented; renderer-first construction silently drops `rts_cores` |
| CPP-D-17.2 | cpp/src/rational_renderer.cpp:100-104 | low | Heuristic relative paths only; add `dlopen(nullptr, ...)` fallback for system-installed `.so` |
| CPP-D-18.1 | cpp/CMakeLists.txt:377-446 | medium | Test binaries bake `CMAKE_CURRENT_SOURCE_DIR` absolute paths into compile-time defines; undermines reproducible-build invariant |
| CPP-D-19.1 | cpp/include/aletheia/types.hpp:88-138 | low | `Rational` uses `int64_t`; Agda kernel + Python `Fraction` + Go `big.Rat` are arbitrary precision — domain fidelity gap |
| CPP-D-20.2 | cpp/include/aletheia/backend.hpp:42-120 | low | `[OPTIONAL]` group conflates JSON-fallback defaults with sentinel-default mocks; split annotations |
| GO-D-15.2 | go/aletheia/client.go:518,542 | medium | `BuildFrame`/`UpdateFrame` parameter order divergence with C++/Python (R19P2-CL10-2 DEFER tracked) |
| PY-D-17.3 | python/aletheia/checks.py:80-298 | medium | 7 builder classes per chain; consider single `ConditionBuilder` with state-machine |
| PY-D-17.1 | python/aletheia/dsl.py:86-105 | medium | Three-point coupling (Agda + protocols.py + dsl.py); registry-driven dispatch via `PredicateType` enum |

**Disposition**: mostly DEFER (structural refactors); PY-D-16.2 (private-surface violation) is FIX.

### Cluster G — DEFER carry-overs (R19P2-CL10-4 / -CL10-5)

| Finding | File:line | What | Disposition |
|---|---|---|---|
| CPP-D-15.1 | cpp/include/aletheia/types.hpp:76-86 | R19P2-CL10-4 in-source DEFERRED — TRACKED on `struct Rational`. Conditions still hold (no C++ ergonomics cluster opened; no factory-bypass observed). | RE-DEFER explicitly in R23 plan |
| CPP-D-15.2 | cpp/include/aletheia/check.hpp:309-316 | R19P2-CL10-5 in-source DEFERRED — TRACKED on `Check` static-method idiom. Same conditions hold. | RE-DEFER explicitly |

### Cluster H — CI/CD + reproducibility

| Finding | File:line | Severity | What |
|---|---|---|---|
| CICD-1.1 | .github/workflows/gha-checks.yml + AGENTS/cicd.md L31 | low | Policy / guideline divergence on action pinning: AGENTS/cicd.md says "40-char SHA never tag" but `check_action_pins.py` carves out `actions/*` + `github/*`. Reconcile texts or land the SHA migration. |
| CICD-1.2 | .github/workflows/gha-checks.yml:13-15,23-25 | medium | Unfiltered `on: push:`/`pull_request:` + `cancel-in-progress: true` can silently cancel mainline build. Restrict cancellation to PR refs OR filter push triggers. |
| CICD-1.3 | .github/workflows/gha-checks.yml:66,77 | low | Audit scripts run via shebang-resolved `python3`; prefer explicit `python3 tools/...` for chmod robustness. |
| CICD-5.2 | Shakefile.hs:878 | medium | `dist` rule only depends on runtime build; doesn't chain `check-properties` / `check-invariants` / etc. Tighten dependencies. |
| CICD-5.4 | Shakefile.hs:1153-1179 | low | `docker` rule doesn't produce SBOM for the image (only for `dist` tarball). |
| CICD-pre-push | core.sshCommand / pre-push hook | low | The R22 SSH-keepalive incident shows the pre-push hook needs awareness of remote-side timeouts. Either document in install_hooks.py / CI_LOCAL.md, OR set `ServerAliveInterval` programmatically at hook install. |

**Disposition**: FIX (CI/CD cluster).

### Cluster I — Documentation depth (low-priority structural)

Findings from Docs B (~36): structure suggestions for DESIGN.md (missing trust-boundary policy, multi-binding split rationale, navigation hierarchy); QUICKSTART onboarding friction (toolchain prereqs vs "5-minute" claim); README async example uses undefined symbols; CANCELLATION example 4.3 is "sketch with undefined symbols" admittedly; runbook gaps (handler_non_monotonic_timestamp, monotonic-across-event-kinds, DBC text parse rejection); etc.

**Disposition**: FIX for the runbook gaps (operational); DEFER the structural DESIGN.md rewrite (out-of-scope for one round); FIX the example-runnability issues.

### Cluster J — Suspected FP / NO-FIX

| Finding | File:line | Disposition rationale |
|---|---|---|
| CPP-D-16.1 | cpp/include/aletheia/detail/cache_keys.hpp | FP-VERIFIED — documented exception (no-pImpl hot-path inlining); existing IWYU + header WARNING block + cpp/CMakeLists comment |
| CPP-A-3.1 | cpp/src/rational_renderer.cpp:32-34 | FP — included for coverage only; PascalCase matches project convention |
| CPP-A-1.1 | cpp/src/json_parse.cpp:157-159 | borderline; choose between "inline" and "keep + refresh comment" |
| AGDA-A-1.x, GO-A-x.x, PY-A-1.x | various Aletheia.Main facade lines | low impact; could DEFER to a dedicated facade-policy decision |
| GO-D-15.1 (R19P2-CL10-3) | `FormatDBC` vs `FormatDBCText` naming asymmetry | DEFER — in-source TRACKED block, same trigger conditions |
| GO-D-32.2 | go/aletheia/json.go:30-40 | cross-binding parity confirmation: verify Python+C++ JSON encoders also use insertion order (likely they do); FP-VERIFY |

---

## Verification carry-over

- **Critical-high trend** (`tools/review_db.py --report critical-high-trend`): R20=1/22, R21=0/17, R22=0/1. R23 raises 1 critical (XDOC-15.1, module count drift) and ~25 high. The critical is a doc-state drift, fixable in a single sweep; once fixed, R23 closes at 0 critical, preserving the "0 critical stays 0" invariant.
- **Graduation check**: cat 1 (Agda Dead code) had 0 findings in R23 (gate working); no new graduation candidates surfaced.
- **Re-raises**: 0 (no carry-over closures from R22 to re-raise).

---

## Proposed implementation order

1. **Cluster A** (doc-sync sweep) — single commit, low risk, closes 1 critical + ~7 high
2. **Cluster B** (Agda hygiene + stdlib lift) — single commit, proof-only changes
3. **Cluster C** (C++ delta region) — single commit, small surface
4. **Cluster H** (CI/CD hardening) — single commit
5. **Cluster D** (Agda system-level) — multi-commit (Identifier refactor is largest)
6. **Cluster E** (cross-binding parity) — multi-commit (touches all 3 bindings)
7. **Cluster I** (doc depth + runbook gaps) — single commit
8. **Cluster F** (structural refactors) — DEFER unless user prioritises
9. **Cluster G** (R19 carry-over re-DEFERs) — comment-only; bundle with another commit
10. **Cluster J** (FP-VERIFY annotations) — comment-only; bundle

**Total estimate**: 6-8 closure commits + 2-3 deferral/FP commits.
