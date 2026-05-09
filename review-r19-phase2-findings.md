# R19 Phase 2 Review Findings

**Branch**: `review-r19`
**Started**: 2026-05-10
**Tip at round start**: `7972c08` (post Phase-1 carry-over closure + post-UPD doc sync)
**Mode**: Phase 2 — fresh agent-driven review on the post-R19-carry-over tip. Phase 1 (R18 carry-over deferral cleanup) closed 2026-05-09 across clusters A-G; see [review-r19-findings.md](review-r19-findings.md). Per `.session-state.md` next-session entry-point option 2 ("Phase 2 (new agent-driven review on the post-R19 tip)").
**Tree state at round start**: clean. No uncommitted work. `git status` confirms working tree clean.

This file aggregates findings from 17 review agents per the AGENTS.md § Review Procedure protocol (mirrors R18 structure):
- 12 step-1 per-file agents (3 Agda + 2 Go + 2 C++ + 2 Python + 2 Documentation + 1 CI/CD)
- 4 step-2 system-level agents (Agda D + Go D + C++ D + Python D)
- 1 cross-document pass

Findings get unique IDs (`<lang>-<agent>-<cat>.<n>`). Disposition legend per AGENTS.md Step 3: `[ ]` TBD · `[FIX]` accepted this round · `[FP]` suspected false positive · `[DEFER-<reason>]` deferred with pointer.

---

## Step 0: Carry-over reconciliation

Per AGENTS.md "Step 0: Carry-over review":

> Every deferred finding from prior rounds is automatically a carry-over candidate for this round. If the conditions that justified deferral still hold, re-defer explicitly in this round's plan; if they no longer hold, the finding is live again and must be fixed.

### From R19 Phase 1 (`review-r19-findings.md` 2026-05-09)

| ID | Site | Phase 1 disposition | Phase 2 candidate disposition |
|---|---|---|---|
| **R19-CARRY-1** ← AGDA-A-16.4 | `src/Aletheia/CAN/Encoding.agda:122` Bool fast-path on `injectHelper` | RE-DEFER (4 probes failed at `with...in eq` outer-abstraction barrier; `@0` ℕToBitVec ship is the partial closure that DID land) | **RE-DEFER pending** — same condition holds (Agda elaboration mechanism, not effort); revisit only viable via Agda upstream fix or eliminating Dec dispatch. Confirm during Step 0. |

### From R18 (`review-r18-findings.md` 2026-05-07-09)

R18 closed all 17 hard clusters + end-of-round basedpyright `benchmarks/` promotion (per CLAUDE.md / `memory/project_review_round18.md`). Two explicit DEFER carry-ins remain that R19 Phase 1 did NOT enumerate:

| ID | Site | R18 deferral rationale | Condition still holds? | Phase 2 candidate disposition |
|---|---|---|---|---|
| **R19P2-CARRY-1** ← GO-B-28.3 | `go/aletheia/ffi.go:690-700` `outSize` bounded only by `MaxInt32` | Return-value size, not input; covered by upstream `MaxJSONBytes` cap | Likely still YES — return value not input. To verify in Step 0. | RE-DEFER probable; if Step 0 surfaces a tighter bound (`MaxFrameByteCount` style) is cheap, FIX. |

R18 also had ~445 `[ ]` TBD checkboxes in the file that were closed via cluster batches (cluster 15 mechanical, cluster 14 invariants, cluster 1 phases, etc.) but never had their individual TBD markers flipped. Per CLAUDE.md narrative R18 is fully closed; per `feedback_review_round_dispositions.md` "DEFER means end-of-round sequencing not rejection" — the cluster-level closure narrative is authoritative. **No action required** for the unflipped TBD markers; this Phase 2 round will write its own dispositions.

### Other deferral surfaces to walk

Per AGENTS.md Step 0 (1) the most recent round's plan file in `~/.claude/plans/`: 5 plan files exist (`deep-giggling-valiant.md` 2026-04-16, `foamy-sleeping-blanket.md` 2026-04-16, `magical-kindling-ritchie.md` 2026-04-14, `toasty-yawning-pine.md` 2026-05-07, `vivid-strolling-gizmo.md` 2026-04-14). Most-recent is `toasty-yawning-pine.md` 2026-05-07 — pre-R18-merge plan. To walk in Step 0.

Per AGENTS.md Step 0 (2) `MEMORY.md` `project_*_deferred*` / `project_system_review_deferred*` entries: closed per-item, archived to [project_spec_observations_index.md](memory/project_spec_observations_index.md). All Phase 5.1 spec observations resolved; no live deferrals.

Per AGENTS.md Step 0 (3) in-source deferral comment blocks: per `feedback_in_source_deferral_notes.md` deferrals must be written as comment blocks in source. To walk via `grep -rn 'DEFER' src/ python/aletheia/ go/aletheia/ cpp/include/ cpp/src/` in Step 0.

---

## Wire-boundary audit (per `feedback_audit_all_wire_boundaries.md`)

R19 Phase 1 cluster A + cluster G closed every parser-surface wire boundary identified at `e37e6ea` 2026-05-09. To re-verify at the post-carry-over tip 2026-05-10:

| Boundary | Site | Phase 1 status | Phase 2 verification target |
|---|---|---|---|
| Python YAML loader | `yaml_loader.py:154,160,164` (3 `safe_load` callsites) | ✅ Bounded via `_check_input_bound` (R18 cluster 2) | Confirm path-confusion fix (R19-CARRY-7 cluster B) preserves bound |
| Python CAN-log iterator | `can_log.py:57` `iter_can_log` | streaming reader; per-frame surface bounded by python-can + CAN spec (R19 cluster G reasoning correction) | Re-verify per-frame bound is real (DLC ≤ 15 → bytes ≤ 64) |
| Python Excel loader | `excel_loader.py:214` `load_dbc_from_excel` | ✅ Bounded R19 cluster A (R19-CARRY-9 partial) | Confirm sibling `load_checks_from_excel` also bounded |
| Python DBC text → JSON | `dbc_converter.py` `dbc_to_json` | ✅ Bounded via `_check_input_bound` (R18 cluster 2) | — |
| Python `float_to_rational` | `_helpers.py` | ✅ Bounded (NaN/Inf/int64-overflow guards) — pre-existed | Cross-binding: confirm Go + C++ all match (R19 cluster G fixed C++) |
| Go YAML loader | `yaml.go:38` `loadYAMLData` | ✅ Bounded R19 cluster A (R19-CARRY-4) | — |
| Go `serializeDBC` defense-in-depth | `go/aletheia/json.go:103` | ✅ Bounded R19 cluster E (R19-CARRY-3 reopen) | — |
| Go `floatToRational` / `doubleToRational` | `go/aletheia/yaml.go` | Pre-existed | Confirm parity with C++ post-cluster-G fix |
| C++ JSON parser | `cpp/src/json_parse.cpp` 10 sites | ✅ Depth bound R19 cluster A (R19-CARRY-5) | — |
| C++ `Rational::from_double` | `cpp/src/rational.cpp` | ✅ NaN/Inf/scaled-overflow guards R19 cluster G | — |
| C++ FFI entry | `cpp/src/ffi_backend.cpp` `FfiBackend::process` | ✅ `max_json_bytes` size cap (R18 cluster 2) | — |
| Tools / tests | `tools/check_*.py`, `python/tests/`, `go/aletheia/*_test.go`, `cpp/tests/*.cpp` | N/A — internal | — |

**Hypothesis going into Phase 2**: post-R19 wire-boundary surface is fully covered. Step 0 confirmation is a re-walk; new wire boundaries surface only if Phase 2 system-level agents identify a new I/O entry that didn't exist when R18 cluster 2 + R19 cluster A/E/G enumerated the surface.

---

## Coverage check

| Agent | Categories owned | Status |
|---|---|---|
| Agda Agent A (Hygiene) | 1, 2, 4, 16, 21, 28, 29 + G-A1, G-A8 | TBD |
| Agda Agent B (Semantics) | 7, 8, 9, 18, 20, 22-26 + G-A2-A6, A9, A10, A12 | TBD |
| Agda Agent C (Cross-file) | 3, 5, 6, 27 + G-A14, A15, A16 | TBD |
| Agda Agent D (system-level) | 10-13, 19, 32 + 14, 15, 17, 30, 31 + G-A7, A11, A13, A17-A20, A23 | TBD |
| Go Agent A (Hygiene & Style) | 1-6, 30 | TBD |
| Go Agent B (Correctness & Runtime) | 7-14, 23-29, 33 | TBD |
| Go system-level | 15-22, 31, 32 | TBD |
| C++ Agent A (Hygiene & Style) | 1-6, 30 | TBD |
| C++ Agent B (Correctness & Runtime) | 7-14, 23-29, 33 | TBD |
| C++ system-level | 15-22, 31, 32 | TBD |
| Python Agent A (Hygiene & Style) | 1-6, 27, 28, 32, 33 | TBD |
| Python Agent B (Correctness & Runtime) | 7-14, 23-26, 29-30, 34 | TBD |
| Python system-level | 15-22, 31 | TBD |
| Docs Agent A (Hygiene) | 1-9 | TBD |
| Docs Agent B (Deep) | 10-22 | TBD |
| Docs cross-doc pass | 5, 15-18 | TBD |
| CI/CD Agent | 1-5 | TBD |

**Coverage gate**: 0 of 17 agents launched. To proceed to Step 1.

---

## Universal Rules tracking

R18 introduced 3 universal rules (UR-1 CHANGELOG, UR-2 adversarial bounds, UR-3 reproducible build / SBOM / signing). Per AGENTS.md "the first review round under this rule must surface findings". Phase 2 carry-in surface:

- **UR-1 CHANGELOG discipline**: `CHANGELOG.md` exists at repo root with `[2.0.0] — Unreleased` section seeded R18 cluster 8. Phase 2 must verify entries reflect every public-API change since (R19 Phase 1 introduced typed error `InputBoundExceededError` cross-binding, `aletheia.testing` Python module, `aletheia.is_closed` property, etc. — entries should already be present from R18 cluster 8 + R19 closure UPDs; verify completeness).
- **UR-2 adversarial-input bounds**: closed at the parser surface (R18 cluster 2 + R19 cluster A/E/G). Phase 2 must verify NO new wire boundary has been introduced since 2026-05-09.
- **UR-3 reproducible build**: `tools/check_reproducible_build.py` exists; tarball-level repro verified. Phase 2 must confirm it still passes against current `7972c08` `.so` (procedurally on the opt-in lane via `ALETHEIA_REPRO_CHECK=1`).

---

## Findings — TBD

Per-agent findings sections will be written here as agents return. R18 model: each agent's section has per-category subsections, "No findings" allowed but mandatory.

### Agda findings — TBD

#### Agda Agent A (Hygiene)
TBD

#### Agda Agent B (Semantics)
TBD

#### Agda Agent C (Cross-file comparison)
TBD

#### Agda Agent D (system-level)
TBD

### Go findings — TBD

#### Go Agent A (Hygiene & Style)
TBD

#### Go Agent B (Correctness & Runtime)
TBD

#### Go system-level
TBD

### C++ findings — TBD

#### C++ Agent A (Hygiene & Style)
TBD

#### C++ Agent B (Correctness & Runtime)
TBD

#### C++ system-level
TBD

### Python findings — TBD

#### Python Agent A (Hygiene & Style)
TBD

#### Python Agent B (Correctness & Runtime)
TBD

#### Python system-level
TBD

### Documentation findings — TBD

#### Docs Agent A (Hygiene)
TBD

#### Docs Agent B (Deep)
TBD

#### Docs cross-document pass
TBD

### CI/CD findings — TBD

#### CI/CD Agent
TBD

---

## Step 3: Coverage reconciliation and planning — TBD

Per AGENTS.md Step 3, after all 17 agents return:

1. **Coverage check** — all categories received exactly one report; gaps re-run before proceeding.
2. **Collate** — merge findings into a single numbered plan; suspected FPs presented with justification for user adjudication.
3. **Disposition per finding** — every entry labeled `FIX` / `FP` / `DEFER-<reason>` before step 4 starts. No bare `[ ]` allowed at step 4.
4. **Cluster ranking** — FIX-early / FIX-middle / DEFER-end-of-round per `feedback_review_round_dispositions.md`.
5. **No deferrals** — findings fixed in current round unless user explicitly defers after reviewing (per AGENTS.md L181).

---

## Action plan — TBD

After Step 3 dispositions are marked, this section will hold the per-cluster plan with FIX/FP/DEFER labels and FIX-early/middle/late ranking, mirroring R18's "Cluster ranking" structure (cf. `review-r18-findings.md` § Cluster ranking).

---

## Round state

| Phase | Status | Notes |
|---|---|---|
| Step 0 — Carry-over reconciliation | TBD | Reconcile R19-CARRY-1 + R19P2-CARRY-1 + walk plan files / in-source DEFERs |
| Step 1 — Per-file review (12 agents in parallel) | TBD | Agda A/B/C + Go A/B + C++ A/B + Python A/B + Docs A/B + CI/CD |
| Step 2 — System-level (4 agents after step 1) | TBD | Agda D + Go D + C++ D + Python D |
| Step 2.5 — Cross-document pass | TBD | Docs cats 5, 15-18 |
| Step 3 — Coverage reconciliation + plan | TBD | All TBDs labeled before step 4 |
| Step 4 — Implement and verify | TBD | Per-cluster commits + 4-gate verification (Agda → unit tests → lint → bench) |

**Branch commit chain (Phase 2)**: TBD; will be appended as commits land, mirroring R18's Round table format.
