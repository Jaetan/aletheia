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

### Cluster B + C — CLOSED 2026-05-09

Single bundled commit closes **R19-CARRY-2** (Go defer-ordering comment),
**R19-CARRY-6** (Python `ALETHEIA_LIB` permission hardening), and
**R19-CARRY-7** (Python `_load_yaml` type-based dispatch).

**Cluster C — Go defer-ordering hygiene:**
- `go/aletheia/cancel_test.go` — added a comment block above the two
  defers in `TestClient_CancelAtEntry` documenting the LIFO cleanup
  ordering (channel-close registered first / client-close second so
  client-close runs first).  Two-defer split is intentional: keeps the
  channel-close registered even if `NewClient` fails before the
  client-close defer can be set up.

**Cluster B — Python security hygiene (PY-B-26.11 + PY-B-26.12):**

PY-B-26.11 (`ALETHEIA_LIB` world-writable check):
- `python/aletheia/client/_ffi.py:find_ffi_library` — rejects an env-var
  path with `PermissionError` if `S_IWGRP | S_IWOTH` is set.  Defends
  against an unprivileged third party who cannot set the env var
  poisoning an existing legitimate path.  Owner-of-file ≠ current uid
  is still allowed (shared `/usr/local` install).
- NEW `python/tests/test_ffi_loader_security.py` — 4 test cases
  (world-writable / group-writable / owner-only-accepted / missing-path).
  Whitelist entry added to `tests/test_private_import_whitelist.py`
  for the `from aletheia.client._ffi import find_ffi_library` reach-through.

PY-B-26.12 (yaml_loader type-based dispatch):
- `python/aletheia/yaml_loader.py:_load_yaml` — dispatch strict by type
  (`Path` → file, `str` → inline YAML).  Removed the `Path(source).exists()`
  heuristic (path-confusion vector).
- BREAKING — call sites passing file path strings must wrap in `Path()`.
- `tests/test_yaml_loader.py` — replaced `test_load_from_path_string`
  with `test_string_path_now_treated_as_inline_yaml` (documents new
  behavior); updated `test_file_not_found` to use `Path` arg.
- Doc updates (PITCH.md / CANCELLATION.md / INTERFACES.md × 3 + prose /
  COOKBOOK.md / TUTORIAL.md / presentation/index.html) — examples now
  use `Path("checks.yaml")` / `pathlib.Path("checks.yaml")`.  Doc-example
  harness still passes (conftest fakes `load_checks` regardless of arg).
- CHANGELOG.md — `[2.0.0] [Changed] BREAKING` entries for both PY-B-26.11
  and PY-B-26.12 with migration guidance.

Asymmetry-hygiene refactor (cluster A landed `check_dbc_text_size_bound`
helper; cluster B benefits — `_load_yaml` dispatches via the helper after
type-narrowing, no duplicated bound-check code).

**Gates:** pytest 799p+1s; basedpyright 0/0/0; pylint 10.00/10; gofmt
+ go vet clean.  No Agda code touched (no Agda gates needed).  No runtime
hot-path effect (yaml_loader is a cold-start path; `_ffi` is once-per-
process at startup) — bench skipped.

### Cluster D — PARTIAL CLOSURE (@0 ships; Bool fast-path remains blocked) 2026-05-09

User initially adjudicated "FIX" cluster D 2026-05-09 ("just implement
Bool fast-path").  Three distinct implementation approaches probed;
two failed at Agda's with-abstraction elaboration layer (not the proof
body).  The third — `@0`-erase `ℕToBitVec`'s bound parameter —
succeeded as a standalone improvement and ships independently.

**Approach 1 — direct rewrite** (`with fromSigned ... <ᵇ 2 ^ bitLength in eq`
in `injectHelper` + cascade `Roundtrip.agda` `fits-check` + helper with-
patterns):

Type-check error in Roundtrip.agda's `helper`:
```
n <ᵇ 2 ^ SignalDef.bitLength sig != w of type Bool
when checking that the type ... | w | refl) ≡ just (injectedFrame n sig byteOrder frame n<2^bl)
of the generated with function is well-formed
```

**Approach 2 — helper restructure** (factor `mkBoundedBitVec : (n bl : ℕ)
→ Maybe (BitVec bl)` with reduction lemma; tried both `with ... in eq`
and `mkFromBool b refl` polymorphic variants):

Same error mode:
```
w != n <ᵇ 2 ^ bl of type Bool
when checking that the type ... mkFromBool n bl w refl ≡ just (...)
of the generated with function is well-formed
```

**Approach 3 — `@0`-erase `ℕToBitVec`'s bound parameter**: SHIPS.

Modified `Aletheia.Data.BitVec.Conversion`:
```agda
ℕToBitVec  : ∀ {n} (value : ℕ) → @0 (value < 2 ^ n) → BitVec n
ℕToBitVec' : ∀ {n} (value : ℕ) → ParityDecomp value → @0 (value < 2 ^ n) → BitVec n
```

`@0` propagates cleanly through Conversion.agda's recursive structure
(into `half-bound-even` / `half-bound-odd` via call-site modality).
**`check-properties` passes** (12m50s, all proof modules type-check).
**`check-erasure` passes** (CANId + Timestamp + stdlib invariants
intact + new ℕToBitVec erasure verified).

MAlonzo output verified: `d_ℕToBitVec_258 v0 v1 ~v2 = du_ℕToBitVec_258
v0 v1` — the bound proof `v2` is `~`-prefixed (erased), and the
`du_` (erasure-elaborated) variant has signature `Integer → Integer
→ T_Vec_28` (no proof slot).

Stand-alone runtime improvement: every existing consumer of
`ℕToBitVec` (e.g., `injectHelper`) now allocates the `Dec`-wrapped
proof from `_<?_` only at the `Dec` boundary; the proof witness inside
the `yes`-constructor flows into the `@0`-erased slot of `ℕToBitVec`
and is dropped by MAlonzo.  The dominant `_<?_` Dec wrapper allocation
remains (only the Bool fast-path would eliminate it), but the
proof-payload erasure is a clean win.

**Bool fast-path remains blocked**: Approaches 1 & 2 demonstrated that
`with ... in eq` in `injectHelper` creates a closed elaboration scope
that the proof's outer `with`-abstraction cannot penetrate, regardless
of whether the witness slot is relevant, `@0`-erased, or `.()`-irrelevant.
The mismatch is at Agda's elaboration mechanism (per `agda.readthedocs.io
/with-abstraction.html#ill-typed-with-abstractions`), not the witness
layer.  This is now empirically established; the in-source comment at
`Encoding.agda:102-115` (which predicted "a larger proof refactor than
the marginal `removeScaling`-dominated frame-build throughput gain
justifies") stays — the proof-side blocker is structural to Agda's
`with` mechanism, not to the proof effort estimate.

**State**: `Aletheia.Data.BitVec.Conversion` ships `@0`-erased
`ℕToBitVec`; `Aletheia.CAN.Encoding.injectHelper` keeps `_<?_` (Dec)
form unchanged.  In-source comment updated to note the @0 win on the
downstream slot.

**Cluster D disposition**:
- R19-CARRY-1 partial closure: @0-erasure of ℕToBitVec ships; Bool
  fast-path on top is RE-DEFER (Agda elaboration barrier, not effort).
- Future revisit only viable via either: (a) Agda upstream fix for
  `with ... in eq` + outer with-abstraction composition; or (b)
  removing the Dec dispatch entirely and accepting that the witness
  must be constructed via a different mechanism (none identified).

**Gates** (post-@0 ship):
- check-properties PASS (12m50s; all proof modules type-check)
- check-erasure PASS (CANId + Timestamp + ℕToBitVec invariants)
- check-fidelity PASS (11/11 FFI exports; constructor-fidelity test 1/1)
- check-invariants / check-no-properties-in-runtime / check-ffi-exports / count-modules PASS
- pytest 791p+1s; go test (race) ok 6.024s; ctest 10/10 (24.41s)

**Bench (vs 2026-04-19 baseline `774c6c8`):**
| Binding | Stream LTL | Signal Extraction | Frame Building |
|---|---|---|---|
| C++ (CAN 2.0B / FD) | +20.8% / +21.2% | -2.3% / -3.8% | -0.4% / +0.3% |
| Go (CAN 2.0B / FD)  | +43.5% / +23.6% | -2.5% / -2.7% | +6.4% / -0.4% |
| Python (CAN 2.0B / FD) | +17.0% / +15.9% | -0.8% / -1.8% | +1.8% / -2.5% |

Stream LTL +15-44% across bindings — cumulative R18 win confirmed.
Signal Extraction -0.8% to -3.8% — within WSL2 noise floor.  Frame
Building -0.4% to +6.4% — no regression across any binding; Go's
+6.4% is consistent with @0 erasure materializing on the binding with
highest per-frame overhead.  All deltas within the 5% gate per
AGENTS.md cat 16.  Baselines NOT refreshed per user "wait and see"
2026-04-28.

---

*R19 carry-over scoping Round 1 completed 2026-05-09.  Clusters A + B
+ C closed; cluster D PARTIAL (`@0` ships, Bool fast-path RE-DEFER).
Cumulative carry-overs closed: 7 of 9 (R19-CARRY-1 partial via @0 +
R19-CARRY-2 / 4 / 5 / 6 / 7 / 9-partial).  Round 1 re-deferrals
re-opened for Round 2 below.*

---

## Round 2 — RE-DEFER follow-ups (2026-05-09)

User direction 2026-05-09 post-Round-1: "save the RE-DEFER to the R19
plan and start working on them."  The three Round 1 RE-DEFERs have
distinct scopes and are tackled across two clusters.

### Cluster E — defense-in-depth + supply-chain hardening (FIX)

Closes **R19-CARRY-3** (Go `serializeDBC` defense-in-depth) and
**R19-CARRY-8** (Shakefile `install-python` ambient-token leak).
Both are orthogonal to UR-2 input bounds; both are small, cheap,
belt-and-suspenders fixes.  Single bundled commit.

**Targets:**
1. `go/aletheia/json.go:103` `serializeDBC` — add defense-in-depth
   bound check on the serialized output size before handing to FFI.
   Serializer-side rationale stays correct (parser bounds make it
   redundant in normal flow), but the cost is 5-10 LOC and an extra
   `len(json.Marshal(m))` pass; catches any internal-blowup regression.
2. `Shakefile.hs:972` `phony "install-python"` — use Cabal's
   `Env`-style invocation that strips `GITHUB_TOKEN` (and similar
   secret env vars) before calling `pip3 install -e .`.  Even though
   no current `.github/workflows/*.yml` invokes `install-python`,
   future CI wiring would inherit ambient secrets without this guard.

### Cluster E — CLOSED 2026-05-09

Single bundled commit closes **R19-CARRY-3** (Go `serializeDBC`
defense-in-depth) and **R19-CARRY-8** (Shakefile `install-python`
ambient-token leak).  Also folds in a pre-existing pylint W1309 fix
in `_ffi.py` (leftover from cluster B's f-string that lacked
interpolation).

**Production code:**
- `go/aletheia/json.go` `serializeDBC` — output bound check via
  `json.Marshal`-then-size pattern.  Returns
  `*InputBoundExceededError` when the marshaled DBC exceeds
  `MaxDBCTextBytes`.  Function-level comment documents that the cap
  is redundant in normal flow (parser cap fires first) and exists as
  a defense-in-depth guard against internal blowup or future bypass.
- `Shakefile.hs:972` `phony "install-python"` — strips secret env
  vars (`GITHUB_TOKEN`, `GH_TOKEN`, `GITHUB_API_URL`,
  `ALETHEIA_COSIGN_KEY`, `ALETHEIA_COSIGN_TLOG`, `TWINE_PASSWORD`,
  `NPM_TOKEN`) before invoking `pip3 install -e .` via Shake's
  `RemEnv` modifier.  Even though no current `.github/workflows/*.yml`
  invokes `install-python`, future CI wiring would inherit ambient
  secrets without this guard.
- `python/aletheia/client/_ffi.py:246` — drop `f` from a string
  literal that had no interpolation (pylint W1309).

**Tests:**
- `go/aletheia/input_bounds_test.go` — new
  `TestSerializeDBC_RejectsOversizeOutput` (single 64 MiB Version
  string drives marshaled JSON over the cap; verifies
  `*InputBoundExceededError` shape).

**Gates:** check-properties / check-fidelity / check-invariants /
check-no-properties-in-runtime / check-erasure / check-ffi-exports /
count-modules PASS; pytest 791p+1s; go test -race ok 7.642s; ctest
10/10 (24.62s); pylint 10.00/10; basedpyright 0/0/0 on `aletheia/ +
benchmarks/`.  No bench needed (Go output bound is cold-path init;
Shakefile change is build-time only).

### Cluster F — R19-CARRY-1 Bool fast-path remainder (investigation)

The Round 1 cluster D PARTIAL closure documented three approaches all
hitting Agda's `with ... in eq` + outer `with`-abstraction barrier.
Cluster F revisits with the @0-erasure now in place — the question is
whether the new `@0`-irrelevance of `ℕToBitVec`'s bound enables a
proof structure that wasn't tractable before.

**Probe scope:**
- Try `cong (...injectedFrame...) (<-irrelevant ...)` bridge in the
  proof helper after the Bool dispatch — `@0` may make the proof slot
  of `ℕToBitVec` (and hence `injectedFrame`) propositionally equal
  for any two `_<_` proofs without the `with`-abstraction needing to
  match.
- If that fails, investigate alternative dispatching mechanisms
  (e.g., `Decidable.does` with `@0`-erased `Reflects` — does this
  achieve Bool runtime + clean proof side?).
- If all probes fail, document finally as RE-DEFER (Agda upstream
  needed).

### Cluster F — FINAL RE-DEFER 2026-05-09

Probed a fourth distinct approach: promote `ℕToBitVec`'s bound from
`@0`-erasure (cluster D) to `.()`-irrelevance.  Hypothesis:
`.()`-irrelevance gives stronger guarantees than `@0` —
propositional equality of any two `_<_` proofs flows through the
bound slot via record-η on the irrelevant field — so the proof's
outer `with`-abstraction over `injectHelper`'s `with ... in eq`
might succeed where `@0`-only didn't.

**Probe shape** (3 files modified, all reverted):
1. `Aletheia.Data.BitVec.Conversion` — `@0` → `.(…)` on
   `ℕToBitVec` and `ℕToBitVec'` bound slots.
2. `Aletheia.CAN.Encoding.injectHelper` — `_<?_` Dec form → Bool
   fast-path: `with fromSigned ... <ᵇ 2 ^ bitLength in eq` + bridge
   `<ᵇ⇒< _ _ (subst T (sym eq) tt)` to lift Bool witness to the
   `_<_` proof needed by `ℕToBitVec`.  Local `.bounded` declaration
   makes the proof slot `.()`-irrelevant on consumption.
3. `Aletheia.CAN.Encoding.Properties.Roundtrip` — proof side updated
   to mirror the Bool dispatch in `injectHelper`'s reduction:
   imports `_<ᵇ_` / `T` / `tt` / `T-≡` / `Equivalence` / `<⇒<ᵇ`;
   adds `<→<ᵇ-≡true` bridge helper; updates
   `injectSignal-reduces-unsigned` and `injectSignal-reduces-signed`
   helpers.

**Result**: same elaboration error as cluster D approaches 1 & 2:
```
n <ᵇ 2 ^ SignalDef.bitLength sig != w of type Bool
when checking that the type ... | w | refl) ≡ just (...)
of the generated with function is well-formed
```

The outer `with`-abstraction over `n <ᵇ 2 ^ SignalDef.bitLength sig`
in `injectSignal-reduces-*` cannot abstract through the inner `with
... in eq` inside `injectHelper`, regardless of whether the witness
slot consuming the Bool result is relevant, `@0`-erased, or
`.()`-irrelevant.

**Conclusion**: cluster F probe confirms cluster D's analysis: the
with-abstraction barrier is at Agda's elaboration mechanism, not
the witness-slot semantics.  `.()`-irrelevance gives stronger
guarantees than `@0` (propositional equality of proof terms) but
does not change the inner-`with ... in eq` ↔ outer-`with`-abstraction
composition failure.  Four total approaches probed across cluster
D + F (direct rewrite, `mkBoundedBitVec` helper restructure,
`@0`-with-Bool, `.()`-with-Bool); all hit the same elaboration
mechanism barrier.

**Final RE-DEFER**: future revisit only viable via either:
- (a) Agda upstream fix for `with ... in eq` + outer
  `with`-abstraction composition (no specific issue tracked
  upstream as of 2026-05-09; structural to Agda's `with`); or
- (b) eliminating the Dec dispatch entirely and accepting that the
  bound witness must be constructed via a different mechanism (no
  mechanism identified that preserves the proof-side correctness
  guarantees).

The cluster D `@0`-erasure of `ℕToBitVec`'s bound slot remains in
place — it stands as a genuine runtime improvement (proof witness
inside `_<?_`'s `yes`-constructor flows into MAlonzo-erased slot)
independent of whether the Dec wrapper itself is later eliminated.

**Cluster F disposition**: probe complete, files reverted to
cluster D state.  `feedback_with_in_eq_outer_abstraction_barrier.md`
(written during cluster D) records the lesson; updated to cite
cluster F as the second empirical confirmation.

**Gates** (post-revert, identical to cluster E close):
- check-properties / check-fidelity / check-invariants /
  check-no-properties-in-runtime / check-erasure /
  check-ffi-exports / count-modules PASS (working tree at cluster
  E commit `7a541bd` + this docs-only update).

---

*R19 carry-over phase complete 2026-05-09.  All 9 carry-overs
addressed: 7 closed (R19-CARRY-2 / 3 / 4 / 5 / 6 / 7 / 9-partial)
+ 1 partial (R19-CARRY-1 via `@0`-erasure ship; Bool fast-path
final RE-DEFER per cluster F empirical) + 1 cleanly classified
DROP scope (R19-CARRY-9 streaming reader / numeric-only helpers /
CLI orchestrators).  R19-CARRY-8 closed via cluster E ambient-token
strip on `install-python`.*
