# R19 Review Findings

**Branch**: `review-r19`
**Started**: 2026-05-09
**Mode**: Phase 1 — R18 carry-over deferral cleanup (per AGENTS.md "Step 0: Carry-over review"). Phase 2 (new agent-driven review) TBD.
**Tree state at round start**: clean post-R18 merge (`4518fef`). Branch forked from `main` at `e37e6ea`.

---

## Step 0: R18 carry-overs

Per AGENTS.md "Step 0: Carry-over review":

> Every deferred finding from prior rounds is automatically a carry-over candidate for this round. If the conditions that justified deferral still hold, re-defer explicitly in this round's plan; if they no longer hold, the finding is live again and must be fixed.

Eight R18 deferrals + cluster 2 partial-scope items (verified against `e37e6ea` 2026-05-09):

| ID | Site | R18 deferral rationale | Condition still holds? | R19 disposition |
|---|---|---|---|---|
| **R19-CARRY-1** ← AGDA-A-16.4 | `src/Aletheia/CAN/Encoding.agda:122` | `_<?_` Dec-valued bounds check inside `injectHelper`; Bool-fast-path documented but no benchmark threshold for the flip stated | Adjudicated 2026-05-09 — implement Bool fast-path | **FIX** (cluster D, bench mandatory per AGENTS.md cat 16) |
| **R19-CARRY-2** ← GO-B-14.8 | `go/aletheia/cancel_test.go:99-105` | `defer close(release)` then `defer c.Close()` — reverse-execution-order subtle | No (trivial reorder) | **FIX** (cluster C) |
| **R19-CARRY-3** ← GO-B-28.4 | `go/aletheia/json.go:103` `serializeDBC` | Serializer-side, internal to a parsed `DbcDefinition` that already passed parse-time bound | Yes — serializer not parser; covered by upstream cap | **RE-DEFER** with rationale (defense-in-depth optional, not a parser surface per AGENTS.md L40) |
| **R19-CARRY-4** ← GO-B-28.5 | `go/aletheia/yaml.go` `LoadChecksFromYAML` / `loadYAMLData` | Go YAML loader entry-point cap not yet wired; Python equivalent IS wired | No (cross-binding asymmetry per `feedback_cross_binding_wire_symmetry.md`) | **FIX** (cluster A) |
| **R19-CARRY-5** ← CPP-B-28.3 | `cpp/src/json_parse.cpp` 10 callsites | `Json::parse(input)` no depth/size limit; nlohmann default. `max_json_bytes` cap fires first as size guard | Partial — size guard upstream, but depth-bound at parse-form deferred | **FIX** (cluster A; switch to bounded `parse(input, callback)`) |
| **R19-CARRY-6** ← PY-B-26.11 | `python/aletheia/client/_ffi.py:224` | `ALETHEIA_LIB` honored without permission/owner check; orthogonal to UR-2 input bounds | Yes (orthogonal) but FIX is cheap | **FIX** (cluster B) |
| **R19-CARRY-7** ← PY-B-26.12 | `python/aletheia/yaml_loader.py:156-158` | String → `Path(source).exists()` dispatch — path-confusion vector; orthogonal to UR-2 input bounds | Yes (orthogonal) but small breaking API change is OK per `feedback_no_backward_compat.md` | **FIX** (cluster B) |
| **R19-CARRY-8** ← CICD-3.1 | `Shakefile.hs:972 phony "install-python"` | `pip3 install -e .` would inherit ambient `GITHUB_TOKEN` if CI invoked it. DEFER until CI runs install paths | YES — verified no `.github/workflows/*.yml` invokes `install-python` (grep clean) | **RE-DEFER** with explicit rationale (track for the cycle that wires CI install paths) |
| **R19-CARRY-9** ← R18 cluster 2 partial scope (Python) | `python/aletheia/{can_log,excel_loader,cli,_helpers}.py` | Inner loaders deferred; covered transitively by FFI-entry `MAX_JSON_BYTES` cap | Partial — covered transitively but cross-binding parity wants explicit caps on parser surfaces | **FIX** (cluster A) on `iter_can_log` + `load_dbc_from_excel`; **DROP** `_helpers.float_to_rational` (not a parser surface — accepts a Python float, not raw bytes); CLI is protected via underlying loaders, no direct surface |

**Doc nit (out-of-band, fold into closure UPD):**
- DOC-X-18.3 PROJECT_STATUS.md L450 LOC totals lack scope qualifier — minor doc sweep, fold into R19 closure UPD.

---

## Wire-boundary audit (per `feedback_audit_all_wire_boundaries.md`)

Verified 2026-05-09 by `grep -rn 'loadYAMLData\|safe_load\|json::parse\|json\.Unmarshal\|yaml\.NewDecoder\|yaml\.Unmarshal' --include='*.go' --include='*.cpp' --include='*.hpp' --include='*.py'`:

| Boundary | Site | Status |
|---|---|---|
| Python YAML loader | `yaml_loader.py:154,160,164` (3 `safe_load` callsites) | ✅ Bounded via `_check_input_bound` (R18 cluster 2) |
| Python CAN-log iterator | `can_log.py:57` `iter_can_log` | ❌ No size cap — R19-CARRY-9 fix scope |
| Python Excel loader | `excel_loader.py:214` `load_dbc_from_excel` | ❌ No size cap — R19-CARRY-9 fix scope |
| Python DBC text → JSON | `dbc_converter.py` `dbc_to_json` | ✅ Bounded via `_check_input_bound` (R18 cluster 2) |
| Go YAML loader | `yaml.go:38` `loadYAMLData` | ❌ No size cap — R19-CARRY-4 fix scope |
| Go JSON FFI response | `json.go:756` `json.Unmarshal` | ✅ Receives bounded FFI response, not user input |
| C++ JSON parser | `cpp/src/json_parse.cpp` 10 sites | ❌ No depth bound — R19-CARRY-5 fix scope |
| C++ FFI entry | `cpp/src/ffi_backend.cpp` `FfiBackend::process` | ✅ `max_json_bytes` size cap (R18 cluster 2) |
| Tools / tests | `tools/check_*.py`, `python/tests/`, `go/aletheia/*_test.go`, `cpp/tests/*.cpp` | N/A — internal, not user wire boundary |

No new wire boundaries surfaced beyond what R18 cluster 2 + this carry-over closes. Audit clean.

---

## Action plan

Single bundled commit per cluster (per `feedback_no_unilateral_deferral.md` + `feedback_pre_commit_scope_check.md` 2-question gate before each).

### Cluster A — UR-2 bound-check parity completion (FIX-early)

Closes R19-CARRY-4, R19-CARRY-5, R19-CARRY-9 (subset).

**Targets:**
1. Go `loadYAMLData` (`go/aletheia/yaml.go:38`) — add size cap returning `*InputBoundExceededError` mirroring Python's `_check_input_bound`. Both file-path and inline-string forms.
2. C++ `cpp/src/json_parse.cpp` 10 callsites — switch from `Json::parse(input)` to depth-bounded `Json::parse(input, callback, allow_exceptions)` with `MAX_JSON_DEPTH` constant added to `Aletheia.Limits` + binding mirrors. New `BoundKind` `JsonNestingDepth` already exists in `Aletheia.Limits.agda`.
3. Python `iter_can_log` (`python/aletheia/can_log.py:57`) — add file-size cap mirroring `_check_input_bound` shape; new `MAX_CAN_LOG_BYTES` constant or reuse existing.
4. Python `load_dbc_from_excel` (`python/aletheia/excel_loader.py:214`) — add file-size cap; new `MAX_EXCEL_BYTES` constant.
5. Cross-binding regression tests mirroring R18 cluster 2's `python/tests/test_input_bounds.py` shape.

**Drop from scope** (reclassification, document inline):
- Go `serializeDBC` — serializer not parser per AGENTS.md L40 "Adversarial-input bounds at parser surfaces". Covered by upstream parse-time bound.
- Python `_helpers.float_to_rational` — accepts numeric, not raw bytes. Not a parser surface.

**Re-defer** (condition still holds):
- CICD-3.1 — `install-python` not invoked from any workflow; track until that changes.

### Cluster B — Python security hygiene (FIX-middle)

Closes R19-CARRY-6, R19-CARRY-7.

**Targets:**
1. `python/aletheia/client/_ffi.py:224` `ALETHEIA_LIB` env-var — owner check (refuse if file owner ≠ current uid) OR docs-only annotation if security model assumes trusted env.
2. `python/aletheia/yaml_loader.py:156-158` path-confusion — split API into `load_checks_from_file(path)` and `load_checks_from_string(text)` with explicit-Path-vs-string disambiguation. Breaking API change is OK per `feedback_no_backward_compat.md`.

### Cluster C — Trivial (FIX-early or fold into A)

Closes R19-CARRY-2.

**Target:** `go/aletheia/cancel_test.go:99-105` — reorder defers so close-order matches construction-order intent, or document the reverse-order rationale inline. ~3-line edit.

### Cluster D — AGDA-A-16.4 Bool fast-path (FIX-late)

Closes R19-CARRY-1. Adjudicated 2026-05-09: just implement.

**Target:** `src/Aletheia/CAN/Encoding.agda:122` — replace `_<?_` (Dec-valued, allocates proof per call) with a Bool-valued fast-path predicate plus an equivalence lemma so `Dec` callers are preserved by name. Pattern is `extractSignalCoreFast` (CLAUDE.md § Performance Considerations).

**Acceptance:** bench mandatory per AGENTS.md cat 16 + `feedback_hot_path_refactor_benchmark.md`. Compare CAN-FD Frame Building vs `benchmarks/results/*_baseline.json` (last refreshed 2026-04-19, `774c6c8`). Direction: improvement or unchanged ≥ noise floor; regression > 3% triggers root-causing.

---

## Round 1 progress

(empty until first commit lands)

---

*R19 carry-over scoping completed 2026-05-09. R18 deferrals + cluster 2 partial scope mapped to R19-CARRY-1 through R19-CARRY-9. Ready to begin cluster A.*
