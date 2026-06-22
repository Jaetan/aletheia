# Aletheia Binding Review — Consolidated Final Report (R25, two rounds)

**Scope:** Python / Go / C++ / Rust API bindings. Round 1 = 71 proof-backed confirmed filings; Round 2 = a corrective re-verification sweep (dedicated safety, Python deep-probe, concurrency, consensus-wrong). **Round 2 wins on every overlap.** Per-round detail with full proofs: `round1_report.md`, `round2_report.md`; gap analysis: `round1_completeness_critique.md`; raw findings: `round1_findings.json`, `round2_findings.json`.

---

## 1. Executive summary

**Distinct-defect count.** Round 1's "71 confirmed" counts *filings*, not defects. Collapsing the four re-count clusters the completeness critic flagged — Go `Client.mu` (3 filings), Go "eight groups" (3), Go `MessageByID` deep-copy (3), C++ `ExtractionResult` anon-pair (3) — removes 8: **63 distinct from R1.** Round 2 added 2 net-new (`never_exceeds`; Python `end_stream property_index` cast); its other findings re-verify/refine R1 defects. **Net distinct ≈ 65.**

**Severity (corrected by R2):** **0 critical · 1 HIGH · ~5 medium · rest low.** R1's "0 high" is stale.

**The worst issues:**
- **`never_exceeds(v)` compiles to strict `G(s < v)` in all four bindings** and flags the in-bound value `s == v` as a violation — a silent correctness defect present consistently across Python/Go/C++/Rust, proven by internal contradiction (the same DSL defines `exceeds` as strict `>`, so the negation must be `<=`; the dual `never_below` correctly uses inclusive `>=`). Locked in by tests + docs. **HIGH, consensus-wrong, maintainer direction call.**
- **C++ `within(ms)` ms→µs `duration_cast` has no overflow guard → signed-int64 UB**, reachable from **untrusted YAML** (`within_ms: 9300000000000000`). Go + Rust guard it.
- **C++ truncated binary extraction buffer returns empty *success* instead of an error** — a truncated FFI response decodes as "zero signals"; callsite comments claim it "propagates as an error" (a lie). Go + Python error.
- **C++ `LazyIndex` stale positional index → unchecked `vector::operator[]` → OOB read UB** — reachable only via user misuse of the public-but-internal mutable vectors (no in-repo trigger).

**Safety verdict (R2's dedicated sweep).** Proved exactly **two C++ UB items** — `within()` (untrusted-input-reachable) and `LazyIndex` (misuse-only) — and **refuted** the one UAF candidate (Go `ExtractSignalsBin` missing `runtime.KeepAlive`: cgo implicitly pins a slice's backing array for a synchronous C call → style nit, not a UAF). Concurrency swept clean: **NO use-after-free, NO race, NO deadlock.** So "**0 critical / 0 high SAFETY defect**" holds — but it is **not "0 unsafe":** two real C++ UB mechanisms, stated honestly.

**Bottom line.** One HIGH consensus-wrong correctness bug (`never_exceeds`) across all four bindings; one untrusted-input-reachable C++ UB (`within()`); one misuse-only C++ UB (`LazyIndex`); plus C++'s truncation-as-success data-loss. No UAF, race, deadlock, hot-path regression, or valid-input memory bug on a normal path. Remaining work: **C++ parity hardening** (the repeat axis-2 outlier), a **truthful-comment sweep** (axis 3, mostly Go), and **Rust logging completeness** + DRY/dead-code cleanups.

---

## 2. Corrected 8-axis verdict

| # | Axis | Real proven defects? | How bad |
|---|------|---------------------|---------|
| 1 | Incomplete | Yes — 5 | Medium-capped. C++ truncation-as-success, Go 2^63→MinInt64 wrap, Rust 11/16 events + unwired extraction-failed. No missing core capability. |
| 2 | Inconsistent | Yes — ~11 (was 13; `within()`→axis 6) | C++ the dominant outlier. Mostly adversarial-wire reachability. Real parity gaps. |
| 3 | Lying comments | Yes — ~17 distinct (was 23 filings) | Pervasive, low-impact: stale names, wrong counts, false mechanisms. A few mislead about behavior/parity. |
| 4 | Unidiomatic / broken | **Yes — 1 HIGH** (R1 had 0) | `never_exceeds` strict-`<` boundary: silently broken semantics in all four. The worst single defect. |
| 5 | Inefficient | Yes — 9 | All **off** the per-frame hot path. No steady-state throughput impact. |
| 6 | Unsafe | **Yes — 2 C++ UB** (R1/R2 "0" corrected) | C++ `within()` int64-overflow UB — **untrusted-YAML-reachable**. C++ `LazyIndex` OOB UB — **misuse-only**. Refuted Go KeepAlive UAF is NOT here. No UAF/race/deadlock. |
| 7 | Low quality | Yes — ~11 distinct | Dead code, DRY breaks, stale comments. Hygiene. |
| 8 | Ill-designed | Yes — ~5 | C++ anon-pair errors, Rust `rational_le` dup, the lossy double-render (direction call), LazyIndex "const-safe" doc over-promise (no actual race). |

---

## 3. Prioritized fix list  (`binding · file:line · action`)

### P0 — correctness / UB (fix now)
1. **cross** · `checks.py:151` / `check.go:84` / `check.hpp:165` / `check.rs:142` · `never_exceeds`: strict `<` → inclusive `<=` in all four; retarget pinning tests (e.g. `rust/src/check.rs:469`), add an `s==v`-passes test, fix `TUTORIAL.md:219`. **(Direction call — confirm boundary first; see §4.)**
2. **cpp** · `check.hpp:141-144, 220-223` · guard the ms→µs multiply before `duration_cast` (reject `ms > INT64_MAX/1000`), mirror Go/Rust. Untrusted-YAML reachable.
3. **cpp** · `client.cpp:289-343` · replace every `return {};` in `parse_extraction_bin` with `return std::unexpected(Protocol, …)` (truncation must error); fixes the lying comments `:353-356,:870-873`.
4. **cpp** · `dbc.cpp:99,122,135` · bound-check before each cached `operator[]`, or drop the LazyIndex cache / make the vectors private+invalidating. (Go shares the frozen-index design → defined panic/wrong-element rather than UB; close that too.)
5. **go** · `types.go:84-86` · `FloatToRational`: add a post-cast round-trip check (`2^63` currently wraps to `MinInt64` with `err==nil`); mirror `cpp/src/types.cpp:27-29`.
6. **python** · `_streaming.py:550-558` · replace `cast("int", …)` on `property_index` with `validate_integer_field` (used for the identical field at `_response_parsers.py:233,:329`); Go raises.

### P1 — parity + comments that mislead about behavior
7. **cpp** · `yaml.cpp:259-266` · add the 64 MiB input bound to the inline-YAML loader (file loader + all peers enforce it; AGENTS.md trust boundary).
8. **cpp** · `json_parse.cpp:213-217` · reject negative-denominator rational on DBC decode (peers reject with an in-comment contract).
9. **cpp** · `response.hpp:41` · introduce `struct SignalError {…}`, change `errors` to `vector<SignalError>` (`client.cpp:331`, `json_parse.cpp:778`). **BREAKING — CHANGELOG.**
10. **go** · `dbc.go:670-675` · make `copyMessage` a true deep copy (Senders + per-signal slices + rebuild index) or downgrade the "deep copy" docs to "shallow."
11. **go** · `doc.go:65-86` · add `endstream.uncached_atom` to the 16-event vocabulary (emitted `client.go:964`).
12. **cpp** · `excel.hpp:39-43` · implement bold headers (Python+Go bold) or correct doc + FEATURE_MATRIX.
13. **rust** · `response.rs:451-471` · enforce the `status:"complete"` contract in `decode_stream` (Go/C++ enforce).
14. **rust** · `FEATURE_MATRIX.yaml:432` + `log.rs:146-154` + `lib.rs:328-336` · logging completeness: reword 11/16, move the two live enrichment events out of "not yet emitted," wire `extraction.{process,parse}_failed`.
15. **cpp** · `client.cpp:407-441` · add the "no DBC message for CAN ID" guard (Go/Python guard).
16. **cpp** · `json_parse.cpp:266-271,1036-1040` · preserve the wire code on `IssueCode::Unknown` (peers round-trip it).
17. **cross (decode-validation lockstep, converge on Go's stricter direction):** CAN-id/DLC on message decode (Rust `dbc.rs:474-484`, Python `dbc_normalize.py:489-523`); startBit/length (Python `:114-121`); `multiplex_values` empty/missing (Go rejects both, C++ missing-only, Rust+Python accept); env-var `varType` (Rust `dbc.rs:639`); multiplex discriminator on canonical `presence` (only Rust does).
18. **python** · `_client_bin.py:171-187` · reject trailing bytes in `parse_extraction_buffer`; add the `> expected` check to C++ for lockstep.
19. **Comment-truth sweep (mostly Go):** `enrich.go:296,303` (`Client.mu`→`lockCh`), `error.go:61-62` ("51"→57; same in `cpp error.hpp:39-40`), `error.go:64-65` ("eight groups" lists 7), `json.go:487-494` (bogus overflow clause), `mock.go:92-94` (`process`→`processLocked`), `dbc.go:193-195` (`ValueDescs`), `yaml.go:154-156`, `enrich.go:221,247`; Python `_converter.py:13-15,64-65`, `can_log.py:75-76,104-105`, `excel_loader.py:30-37`, `rational.py:176-189`, `types.py:600-601`, `_enrichment.py:388-393` (consistent-wrong across Go/C++/Rust); C++ `types.hpp:105-110`, `error.hpp:39-40`, `client.hpp:274-281`, `client.hpp:264-266`; Rust `async_client.rs:13-14,47-49,426-427` (`mpsc::Sender` is `Sync`).

### P2 — quality / efficiency / cosmetic
20. **go** · `ffi.go:782-835` · add `runtime.KeepAlive(data)` to `ExtractSignalsBin` for convention consistency. **NOT a UAF (refuted)** — style only.
21. **cpp** dead code: `enrich.cpp:20-22`, `types.cpp:58-61`; DRY: `json_parse.cpp:734-751` (extract `parse_issue_entry`), `json_parse.cpp:33` (drop array literal size).
22. **rust** DRY: `check.rs:39-42` (one inherent value-`le`, NOT `Ord`), `dbc.rs:772-773` (`set_extended`), `lib.rs:399-402` (`select_diag_values`).
23. **go** DRY: `mock.go:143-193`, `yaml.go:297-318`+`excel.go:497-537` (extract `DispatchThen`).
24. **Efficiency (all off the hot path):** Go CLI double-`ParseDBC` (`main.go:347,464`; C++ same); Go double-marshal (`json.go:219-231`); Go per-cell `GetCellType` (`go/excel/excel.go:247-285`); Go payload copy on cache hits (`client.go:1084-1085`); C++ P×F EOS re-extraction (`client.cpp:646-651,840-865`); C++ Excel copies (`excel.cpp:631,638-646`); Rust per-call dlsym (`backend.rs:438-440,…`); Rust O(N²) EOS dedup (`lib.rs:459-463`).
25. **go** · `json.go:652-679` · decode rational num/den via `UseNumber()` (float64 loses precision >2^53).
26. **rust** · `FEATURE_MATRIX.yaml` · note `build_frame`/`update_frame` take `&DbcMessage` by design (idiom-permitted). Doc-only.

---

## 4. Direction calls for the maintainer (do NOT auto-fix)
1. **`never_exceeds` boundary semantics** — the in-bound `s==v` flag is a clear bug vs the codebase's own `exceeds = strict >`, so the fix is in P0; but the exact boundary (and a symmetric audit of every comparison builder) is the maintainer's call. Must not be dropped from either §3 P0#1 or here.
2. **Lossy `enriched_reason` observed-value render (Python/Go/C++)** — the predicate ℚ renders exactly via the Agda kernel `formatℚ`, the observed value via lossy `%g` (`1234567`→`1.23457e+06`). Decide: document the approximation in all three, or route the observed render through `formatℚ` in all three. Rust is a separate divergence (`rat_str`→`1/2` not `0.5`) — fold in.
3. **Go `PhysicalValue = float64`** — Go's enrichment carries the observed value as `float64` (`json.go:1131`), structurally lossy. Aligning with (2) means carrying exact `(num,den)` through extraction decode — larger change. Maintainer call.

---

*Method: 24 round-1 finder cells (4 bindings × 5 lenses + 4 cross-binding) + 8 round-2 gap-closer cells, each finding independently adversarial-proof-verified (refute-by-default). Findings without a re-verifiable file:line + concrete trigger/spec proof were dropped; two over-claims (Go UAF, Rust byte-identical) were refuted and kept honestly at low. Per-round proofs in the sibling files.*
