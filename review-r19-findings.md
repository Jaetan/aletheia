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
| **R19-CARRY-9** ← R18 cluster 2 partial scope (Python) | `python/aletheia/{can_log,excel_loader,cli,_helpers}.py` | Inner loaders deferred; covered transitively by FFI-entry `MAX_JSON_BYTES` cap | Partial — Excel is a real parser surface (xlsx = ZIP, openpyxl all-loads); `can_log` is a streaming reader (per-frame yield, no all-load); CLI is protected via underlying loaders; `_helpers.float_to_rational` accepts a Python float, not raw bytes | **FIX** (cluster A) on `load_dbc_from_excel` + `load_checks_from_excel` (Excel = parser surface per AGENTS.md L40); **DROP** `iter_can_log` / `load_can_log` (streaming reader, not in AGENTS.md L40 enumeration; legitimate CAN logs > 64 MiB are common, capping would break real-world usage); **DROP** `_helpers.float_to_rational` + CLI helpers (not parser surfaces) |

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
1. Go `loadYAMLData` (`go/aletheia/yaml.go:38`) — add size cap mirroring Python's `_check_input_bound`. Reuses `MaxDBCTextBytes` (YAML check-defs reference signal names from a parsed DBC, same family). Both file-path and inline-string forms; returns `*InputBoundExceededError`.
2. C++ `cpp/src/json_parse.cpp` 10 callsites — add a single `parse_bounded(string_view)` helper using nlohmann's SAX-callback `Json::parse(input, callback)` form to enforce `max_nesting_depth` (already in `aletheia/limits.hpp` from cluster 2). Migrate all 10 `Json::parse(input)` callsites + add `catch (const InputBoundExceededError&)` block.
3. Python `load_dbc_from_excel` + `load_checks_from_excel` (`python/aletheia/excel_loader.py:214` + sibling) — add inline `MAX_DBC_TEXT_BYTES` size cap (matching `dbc_converter.dbc_to_json`'s pattern; xlsx is a ZIP archive, openpyxl all-loads).
4. Cross-binding regression tests mirroring R18 cluster 2's `python/tests/test_input_bounds.py` / `go/aletheia/input_bounds_test.go` / `cpp/tests/unit_tests_input_bounds.cpp` shape.

**Drop from scope** (reclassification, documented inline):
- Go `serializeDBC` — serializer not parser per AGENTS.md L40 "Adversarial-input bounds at parser surfaces". Covered by upstream parse-time bound.
- Python `_helpers.float_to_rational` — accepts a numeric, not raw bytes. Not a parser surface.
- Python `iter_can_log` / `load_can_log` — streaming reader yielding per-frame; not in AGENTS.md L40 enumeration ("YAML check loaders, Excel loaders" listed but not CAN log readers); legitimate CAN log files > 64 MiB are common (multi-hour drives in BLF), capping would break real-world usage. Threat is mitigated by the per-frame DLC validation that fires on every yielded tuple.
- Python CLI helpers — `run_checks` / `main` orchestrate from already-loaded inputs (DBC, checks, frames); no direct user-input parsing.

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

### Cluster A — CLOSED 2026-05-09

Single bundled commit per `feedback_no_unilateral_deferral.md`.  Closes
**R19-CARRY-4** (Go YAML loader cap), **R19-CARRY-5** (C++ json::parse
depth bound), **R19-CARRY-9 partial** (Python `excel_loader` x2);
re-classifies `iter_can_log` / CLI helpers / `_helpers.float_to_rational`
as out-of-scope (not parser surfaces).

**Production code:**
- `cpp/src/json_parse.cpp` — `parse_bounded(string_view)` helper using
  nlohmann's SAX-callback `Json::parse(input, callback)` form to enforce
  `max_nesting_depth` (64); migrates 10 callsites from `Json::parse(input)`
  to `parse_bounded(input)`.  Throws `std::runtime_error` on depth
  exceedance; the existing `catch (const std::exception&)` block at every
  parse_* callsite converts it to a `Result<>` error via `make_error`.
- `go/aletheia/yaml.go` — `loadYAMLData` + `LoadChecksFromYAMLFile`
  return `*InputBoundExceededError{BoundKind, Observed, Limit}` for
  inputs > `MaxDBCTextBytes` (64 MiB).  Mirrors Python's
  `_check_input_bound` shape; closes the cross-binding asymmetry.
- `python/aletheia/excel_loader.py` — `load_dbc_from_excel` +
  `load_checks_from_excel` reject files > `MAX_DBC_TEXT_BYTES`
  (Excel = ZIP archive, openpyxl all-loads = ZIP-bomb territory).

**Asymmetry-hygiene refactor** (per `feedback_no_subsumption_asymmetry.md`,
3 callsites of the same pattern across `dbc_converter` / `yaml_loader` /
`excel_loader` after this commit):
- NEW `python/aletheia/client/_types.py:check_dbc_text_size_bound(observed)`
  — single shared helper that raises `InputBoundExceededError` if observed
  > `MAX_DBC_TEXT_BYTES`.  All 3 loaders call it; `yaml_loader` drops its
  private `_check_input_bound` helper.

**Tests:**
- `python/tests/test_input_bounds.py` — new `TestPythonLoaderBoundChecks`
  class (5 tests): yaml_loader file-path / inline-string, dbc_converter,
  excel_loader x 2.  Inline-string test mocks `Path.exists` to bypass
  the orthogonal pre-existing path-confusion behavior tracked separately
  as **PY-B-26.12** (cluster B).
- `go/aletheia/input_bounds_test.go` — 3 new test funcs:
  `TestLoadChecksFromYAMLFile_RejectsOversize`,
  `TestLoadYAMLData_FilePathOversize`, `TestLoadYAMLData_InlineStringOversize`.
  Uses sparse-file `Truncate(MaxDBCTextBytes+1)` to avoid 64 MiB writes.
- `cpp/tests/unit_tests_input_bounds.cpp` — 2 new `TEST_CASE`s:
  depth bound rejection (65 nested arrays) + clean parse at safe depth.

**Gates:** pytest 795p+1s; go test -race ok 6.821s; ctest 10/10 (24.32s);
basedpyright 0/0/0; pylint 10.00/10; gofmt + go vet clean; clang-format
clean; clang-tidy clean (188,222 suppressed external-header / NOLINT, 0
user-code findings).

**Bench (vs 2026-04-19 baseline `774c6c8`):** Stream LTL across all 3
bindings +20-39% (cumulative R18 win); CAN-FD Frame Building -1.0%
(Go) / -0.7% (C++) / -0.3% (Python) — within WSL2 noise floor (~2-4%
steady-state, ±10% inter-run gate).  No regression from the SAX
callback overhead; baselines NOT refreshed per user "wait and see"
2026-04-28.

---

*R19 carry-over scoping completed 2026-05-09. R18 deferrals + cluster 2 partial scope mapped to R19-CARRY-1 through R19-CARRY-9. Cluster A closed; B / C / D pending.*
