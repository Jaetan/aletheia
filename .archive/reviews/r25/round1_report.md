The advisor caught a real bug: I conflated the table's *filing* count with the prose's *distinct-defect* count, producing two phantom medium entries (M11, M15) and one misplaced severity (M12 stale-index UB is low, not medium). Let me correct the medium section to list distinct defects once with multi-axis notes, matching how my low section already works. Here is the corrected, final report.

---

# Adversarial Binding Review — Final Report (proof-backed)

**Scope:** Python / Go / C++ / Rust API bindings. **71 confirmed findings** after independent proof-checking (each confirmed or downgraded; none invented). **0 critical, 0 high, 19 medium, 52 low.** No memory-unsafety with a reachable trigger on valid input was proven; no broken-idiomatic-API and no genuinely-unsafe-with-real-input defect was confirmed.

> The count table below counts **filings**; Section 3 lists **distinct defects**. A few defects are filed under more than one axis. The **19 medium filings are 16 distinct defects**: the Go `MessageByID` deep-copy is filed 3× (2 lying-comment + 1 ill-designed — 2 of those at medium), and C++ `ExtractionResult` anonymous-pair is filed 2× at medium (axis 8 + axis 2).

---

## 1. Executive summary

### Worst issues (the medium tier — there is no critical/high)

The review found **no critical or high defect**. Every confirmed bug is a documentation lie, a one-boundary-value edge case, a parity divergence reachable only on adversarial/hand-built wire input, or a quality/efficiency cleanup. The most consequential:

- **C++ `parse_extraction_bin` swallows truncated binary buffers as empty *success*** (`cpp/src/client.cpp:289-343`). Every short-buffer branch does `return {}`, which value-inits the `std::expected` *value* (`has_value()==true`), so a truncated FFI response decodes as "zero signals" instead of erroring. Go and Python both return a protocol error on every truncation. The function's own callsite comments claim truncation "propagates as an error" — a lie. (No OOB read — the bounds checks hold; it is a wrong *return value*.)
- **Go `FloatToRational` silently wraps `2^63` to `MinInt64` with `err==nil`** (`go/aletheia/types.go:84-86`). At exactly `v=2^63` the `v<=MaxInt64` float comparison passes (the cast of MaxInt64 rounds up to 2^63), and `int64(v)` yields `MinInt64` — violating its docstring and `NeverExceeds`' "raise rather than clamp" promise. Single boundary value; Python/C++ are correct.
- **C++ check `within(ms)` has no ms→µs overflow guard** (`cpp/include/aletheia/check.hpp:141-144,220-223`): `duration_cast<microseconds>` multiplies by 1000 in int64 — UB for `ms>INT64_MAX/1000`, reachable from public `settles_between(...).within(huge)`. Go and Rust both guard.
- **C++ inline-YAML loader has no input-length bound** (`cpp/src/yaml.cpp:259-266`) while the C++ *file* loader and all three peers' inline loaders enforce the 64 MiB cap — violating AGENTS.md's named trust-boundary rule.
- **C++ silently sign-flips a negative-denominator rational on DBC decode** (`cpp/src/json_parse.cpp:213-217`) where Python/Go/Rust each carry an *explicit in-comment reject contract* citing the wire-symmetry rule. 3-1 outlier.
- **C++ `ExtractionResult.errors` is an anonymous `std::pair`** (`cpp/include/aletheia/response.hpp:41`) — the lone binding without a named `SignalError` type; violates `feedback_no_opaque_composite_types` + the r24 precedent.
- **C++ `create_excel_template` documents bold/formatted headers but writes plain cells** (`cpp/include/aletheia/excel.hpp:39-43`) — Python *and* Go both bold them; C++ lone drop.
- **Go `doc.go` self-declared-exhaustive 16-event vocabulary lists only 15** (`go/aletheia/doc.go:65-86`), omitting `endstream.uncached_atom` which the code emits (`client.go:964`) and PROTOCOL.md mandates — in a comment saying "any drift here is a finding."
- **Go `MessageByID`/`MessageByName` document a "deep copy" that aliases** `Senders` and per-signal slices (`go/aletheia/dbc.go:635,653,670-675`); empirically confirmed mutation bleeds back. Python's docstring names Go as *the* deep-copy binding.
- **C++ `LazyIndex` const lazy-cache has an unsynchronized data race** behind a "const-safe" comment (`cpp/include/aletheia/dbc.hpp:29-51`): two threads first-calling `message_by_id` on a shared `const&` race on `cache_.emplace()`.
- **Rust over-claims structured logging.** FEATURE_MATRIX says Rust "emits the canonical event vocabulary" but it emits **11 of 16** (`docs/FEATURE_MATRIX.yaml:432`); `extraction.{process,parse}_failed` are never emitted (`lib.rs:328-336` swallows both via `.ok()?`); `log.rs:146-154` mislabels two *live* enrichment events as "not yet emitted"; `decode_stream` never enforces the `status:"complete"` contract its doc claims (Go + C++ do).

### Per-axis verdict (8 axes)

| # | Axis | Real proven defects? | How bad |
|---|------|---------------------|---------|
| 1 | **Incomplete** | **Yes — 5** | Medium-capped. Worst: C++ truncation-as-success, Go 2^63 wrap, Rust 11/16 events + unwired extraction-failure events. No missing core capability. |
| 2 | **Inconsistent** | **Yes — largest real-defect cluster, 13** | C++ the dominant outlier (7). Mostly adversarial-wire reachability → low/medium. Real parity gaps, not cosmetic. |
| 3 | **Lying comments** | **Yes — most numerous, 23** | Pervasive, low-impact: stale names, wrong counts, wrong tuple arity, false mechanisms. 4 medium because they also mislead about behavior/parity. |
| 4 | **Unidiomatic / broken** | **No — 0** | Closest candidates (Rust `&DbcMessage`, C++ visitor) judged principle-permitted idiom, not breakage. |
| 5 | **Inefficient** | **Yes — 9** | All proven, all **off the per-frame hot path** (CLI startup, file-load, EOS, control-plane). None affects steady-state throughput. |
| 6 | **Unsafe** | **No valid-input trigger — 0** | The two memory-adjacent items (LazyIndex UB on post-mutation lookup; within() int64 UB) live under axes 8/2 and need API misuse or an extreme argument. No use-after-free/OOB on a normal path. |
| 7 | **Low quality** | **Yes — 14** | Dead code (2 C++), DRY breaks (Go, C++, Rust), stale-identifier comments, an over-sized inert `std::array`. Hygiene, not correctness (2 Rust mediums). |
| 8 | **Ill-designed** | **Yes — 7** | Most structural: C++ LazyIndex stale-index (UB in C++ / silent-wrong-element in Go), C++ anon-pair errors, Rust `rational_le` duplication, cross-binding lossy double-render (a maintainer direction call). |

**Bottom line:** the bindings are sound at the core/runtime level — no crit/high, no hot-path regression, no valid-input memory bug. The work is (a) **C++ parity hardening** (the repeat axis-2 outlier), (b) a **truthful-comment sweep** (axis 3, mostly Go), (c) **Rust logging completeness** + DRY/dead-code cleanups.

---

## 2. Count table (confirmed filings)

Rows = the 8 axes; columns = binding. Findings filed under two axes are counted under each. Total = 71.

| Axis | python | go | cpp | rust | cross | **total** |
|------|:--:|:--:|:--:|:--:|:--:|:--:|
| 1 Incomplete | 1 | 1 | 1 | 2 | 0 | **5** |
| 2 Inconsistent | 0 | 1 | 7 | 3 | 2 | **13** |
| 3 Lying comments | 5 | 12 | 5 | 1 | 0 | **23** |
| 4 Unidiomatic / broken | 0 | 0 | 0 | 0 | 0 | **0** |
| 5 Inefficient | 0 | 4 | 3 | 2 | 0 | **9** |
| 6 Unsafe | 0 | 0 | 0 | 0 | 0 | **0** |
| 7 Low quality | 0 | 7 | 4 | 3 | 0 | **14** |
| 8 Ill-designed | 0 | 1 | 3 | 2 | 1 | **7** |
| **total** | **6** | **26** | **23** | **13** | **3** | **71** |

Severity split: **critical 0, high 0, medium 19, low 52.**

---

## 3. Findings by severity

### CRITICAL (0) — none.
### HIGH (0) — none.

### MEDIUM — 19 filings = 16 distinct defects

1. **C++ truncated binary extraction buffer returns empty SUCCESS, not error** · cpp · `cpp/src/client.cpp:289-343` (lying callsite comments 353-356, 870-873). Every short-buffer branch `return {}` value-inits the `expected` value; same fn returns `std::unexpected` on a bad rational (314-316) — within-fn inconsistency. **Diverges** (Go `json.go:1103-1169` + Python error on truncation). Fix: `return std::unexpected(Protocol,...)` matching peer messages — also makes the comments truthful.

2. **Go `FloatToRational` wraps 2^63 → MinInt64 with err==nil** · go · `go/aletheia/types.go:84-86`. Violates own docstring + `NeverExceeds`. **Diverges** (Python/C++ correct). Fix: post-cast round-trip `n:=int64(v); accept iff float64(n)==v`, else strict scaling path (mirror `cpp/src/types.cpp:27-29`).

3. **C++ check `within(ms)` lacks ms→µs overflow guard (int64 UB)** · cpp · `cpp/include/aletheia/check.hpp:141-144,220-223`. Reachable via public `settles_between(...).within(huge)`. **Diverges** (Go `check.go:200,344`, Rust `check.rs:45-49` guard). Fix: reject `ms.count()>millis::max()/1000` at both sites; add a test mirroring `rust/src/check.rs:597`.

4. **C++ inline-YAML loader has no input-length bound** · cpp · `cpp/src/yaml.cpp:259-266`. C++ file loader + all 3 peers enforce 64 MiB. **Diverges**; AGENTS.md trust-boundary violation. Fix: reject `yaml.size()>max_dbc_text_bytes` (InputBoundExceeded) before `YAML::Load`.

5. **C++ sign-flips negative-denominator rational on DBC decode** · cpp · `cpp/src/json_parse.cpp:213-217`. Python/Go/Rust each *reject* den<0 with an in-comment wire-symmetry contract. **Diverges** (3-1). Fix: throw on `den<0` like the existing `den==0` throw.

6. **C++ `ExtractionResult.errors` is an anonymous `std::pair`** *(filed twice at medium — axis 8 ill-designed + axis 2 inconsistent)* · cpp · `cpp/include/aletheia/response.hpp:41`. No `SignalError` type in C++; Go/Rust/Python all name it. **Diverges**; violates `feedback_no_opaque_composite_types` + r24 precedent. Fix: add `struct SignalError {SignalName name; std::string error;}`, update emplace sites (`client.cpp:331`, `json_parse.cpp:778`). BREAKING — CHANGELOG entry; align the field name across all four.

7. **C++ `create_excel_template` documents bold/formatted headers but writes plain cells** · cpp · `cpp/include/aletheia/excel.hpp:39-43`. **Diverges** (Python `excel_loader.py:394-399` + Go `excel.go:199,296` bold). Fix: implement bold via OpenXLSX, or correct the doc *and* flip the FEATURE_MATRIX expectation. Parity preferred.

8. **C++ `LazyIndex` const lazy-cache data race behind "const-safe" comment** · cpp · `cpp/include/aletheia/dbc.hpp:29-51`. `ensure()` writes `mutable cache_` with no synchronization; `const` `message_by_id`/`signal_by_name` invite the standard `const⇒concurrent-read-safe` expectation. Same at `check.hpp:96-102`. **Single-binding**. Fix: reword to "not thread-safe", or use `std::once_flag`/`call_once` (pattern already in `rational_renderer.cpp`).

9. **Go `MessageByID`/`MessageByName` "deep copy" aliases Senders + per-signal slices** *(filed 3× — 2 lying-comment medium + 1 ill-designed medium)* · go · `go/aletheia/dbc.go:635,653,670-675`. `copyMessage` shallow-copies the struct and reslices only `Signals`; empirically confirmed mutation bleeds back. Sibling `SignalByName` honestly documents shallow — the two doc surfaces contradict. Python names Go as *the* deep-copy binding. **Single-binding**. Fix: make `copyMessage` truly deep (Senders + per-signal slices + rebuild `signalIndex`) — parity-correct — or downgrade both docs to shallow.

10. **Go `doc.go` 16-event vocabulary lists only 15 (omits `endstream.uncached_atom`)** · go · `go/aletheia/doc.go:65-86`. Code emits it (`client.go:964`); PROTOCOL.md mandates it; C++/Python emit it. **Diverges**. Fix: add it (Python's 16-value `LogEvent` enum is the reference).

11. **Python `dbc_to_json ∘ dbc_to_text` documented roundtrip is not invocable** · python · `python/aletheia/dbc/_converter.py:13-15,64-65`. `dbc_to_json` consumes a *path* (`Path(dbc_path).stat()`), so passing DBC text raises FileNotFoundError. **Single-binding**. Fix: reword to the actual relationship (file-containing-text, or `client.parse_dbc_text(client.format_dbc_text(d))`).

12. **Python `load_can_log`/`iter_can_log` docstrings claim 5-tuple; yield 7-field `CANFrameTuple`** · python · `python/aletheia/can_log.py:75-76,104-105`. The module's own example unpacks 7. **Single-binding**. Fix: document all 7 fields (+brs, esi).

13. **Python Excel DBC-sheet column list omits the `Extended` column** · python · `python/aletheia/excel_loader.py:30-37`. `DBC_HEADERS` (145-162) has it 3rd; loader reads it (603-604); template writes it. A technician builds an off-by-one sheet. **Single-binding**. Fix: add `Extended` between `Message Name` and `DLC`, note it is optional.

14. **Rust FEATURE_MATRIX overstates structured-logging emission (11/16)** · rust · `docs/FEATURE_MATRIX.yaml:432`. Only 11 emit sites; the 5 absent sit under `log.rs`'s own "not yet emitted" header; the gate checks `emitted ⊆ vocabulary`, not full emission. Go/Python/C++ emit all 16. **Single-binding**. Fix: reword to "defines the full vocabulary; emits 11 of 16 today" + describe the subset gate.

15. **Rust `log.rs:146-154` mislabels two *live* enrichment events as "not yet emitted"** · rust · `rust/src/log.rs:146-154`. `ENRICHMENT_PROPERTY_INDEX_OOB`/`ENRICHMENT_EXTRACTION_FAILED` are emitted at `lib.rs:359,406,479`. **Single-binding**. Fix: move them to the emitted group; narrow the comment to the genuinely-unemitted cache.*/extraction.* events.

16. **Rust `decode_stream` never enforces the `status:"complete"` contract its doc claims** · rust · `rust/src/response.rs:451-471`. Go (`json.go:1260-1262`) and C++ (`json_parse.cpp:924-925`) both enforce it; the core emits `status:"complete"`. **Diverges**. Fix: match-and-error on non-complete status; surface the parallel `decode_extraction` leniency to the maintainer as the same direction call.

*(These 16 distinct defects = 19 filings: #6 counted twice, #9 counted twice at medium. Per the table: python 3, go 4, cpp 7, rust 5 = 19.)*

### LOW (52)

**Lying comments — stale identifiers / wrong counts / false mechanism (Go-heavy):**
- Go `extractCache` comments reference non-existent `Client.mu`; lock is `lockCh` semaphore · `enrich.go:296,303` (filed under axes 3 and 7). Fix: name `lockCh`.
- Go `error.go` "51 codes" but 57 constants · `error.go:61-62`. **consistent-wrong** with C++ `error.hpp:39-40`. Fix both; cite `std::size(...)` not a literal.
- Go `error.go` "eight groups" but parenthetical lists 7 (omits Input-bound) · `error.go:64-65` (multiple filings). Fix: add "Input bound."
- Go `validateTimeBound` doc claims int64-overflow rejection; body only checks `<0` (int64 field can't overflow int64) · `json.go:487-494`. Fix: drop the clause.
- Go `mockSentinel` names non-existent `Client.process` (actual `processLocked`) · `mock.go:92-94`.
- Go `SignalByName` names non-existent field `ValueDescs` (actual `ValueDescriptions`) · `dbc.go:193-195`.
- Go `parseYAMLChecks` cost comment says "per workbook" in a YAML-bytes fn · `yaml.go:154-156`. Fix: "per document."
- Go enrich exhaustiveness comments cite non-existent `sealedFormula`/`sealedPredicate` markers (actual `formula()`/`predicate()`) · `enrich.go:221,247`.
- Python `parse_rational` claims a "float-from-string heuristic"; code uses `Fraction(float).limit_denominator(1e9)` (no string) · `rational.py:176-189`.
- Python `PropertyResultEntry` docstring scopes it "end-of-stream" but it's also the mid-stream `property_batch` element · `types.py:600-601`.
- Python `build_diagnostic` "Always succeeds" but reachable `ValidationError` (nesting>64) + renderer-load failures · `_enrichment.py:388-393`. **consistent-wrong**: Go (`enrich.go:41`, panics on missing .so, caller undefended), C++ (`enrich.hpp:22`), Rust (`enrich.rs:33`) share the claim. Fix: accurate Raises across all; align caller defenses.
- C++ Rational static_assert/comment claims g++/clang-21 support the build hard-rejects (Clang-22-only) · `types.hpp:105-110`.
- C++ `ErrorCode` "51 codes / 6 families" → 57 codes / 7 families (omits DBC-text) · `error.hpp:39-40`. **consistent-wrong** with Go.
- C++ `signal_index_`/`signal_names_` "populated by parse_dbc()" but `parse_dbc_text` populates too · `client.hpp:274-281`. Fix: "by populate_signal_lookup()."
- C++ `last_frames_` "cleared by start_stream()" but `end_stream` clears it too · `client.hpp:264-266`.
- Rust async_client claims `mpsc::Sender` is `!Sync` (the stated `Mutex` rationale) — empirically false on rustc 1.96 (`Sender<T>:Sync` since 1.72); the `Mutex` is not what makes `AsyncClient: Sync` · `async_client.rs:13-14,47-49,426-427`. Fix all 3 sites; the `Mutex` simplification is a separate follow-up.

**Inconsistent — cross-binding parity (mostly adversarial-wire reachable):**
- Rust doesn't validate env-var `varType ∈ {0,1,2}` · `dbc.rs:639`. Peers reject. **Diverges.**
- Rust *and Python* don't validate CAN-id range / DLC byte-count on message decode (2-2 split; Go/C++ do) · `dbc.rs:474-484`. Fix in lockstep.
- multiplex_values empty/missing: Go rejects both, C++ throws-on-missing-only, Rust+Python accept (four-way) · `go/aletheia/json.go:2128-2130`. **Diverges**; adopt Go's reject-empty-and-missing.
- multiplexed discriminator: only Rust keys on canonical `presence`; C++/Go key on `multiplexor`; Python keys on neither (passthrough) · `cpp/src/json_parse.cpp:314-323`. **Diverges**; make all decode on `presence`.
- Go decodes rational num/den through float64 (precision loss >2^53); C++/Rust/Python exact · `go/aletheia/json.go:652-679`. Fix: `json.Decoder.UseNumber()`.
- C++ build_frame/update_frame lack the client-side "no DBC message for CAN ID" guard (empty-signals + unknown-id slips) Go/Python apply · `cpp/src/client.cpp:407-441`. Fix: lookup via existing `signal_names_`.
- Rust build_frame/update_frame take `&DbcMessage`; peers take CAN ID + internal index · `rust/src/lib.rs:794-841`. **Downgraded to doc-nit** (principle-permitted idiom; `message_by_id` expresses the diagnostic one call earlier; the r24-acceptance and structurally-precluded claims were *refuted*). Fix: FEATURE_MATRIX note only; no code change.
- C++ `IssueCode::Unknown` drops the original wire code; Python/Go/Rust preserve it · `cpp/src/json_parse.cpp:266-271,1036-1040`. **Diverges** (forward-compat claim not delivered). Fix: stash the raw string.
- C++ ExtractionResult anon-pair, axis-2 low filing · `response.hpp:41` (low duplicate of the medium #6 above; same defect).

**Low quality — dead code / DRY / drift hygiene:**
- C++ dead `format_value(double)` overload, zero callers · `enrich.cpp:20-22`. Delete.
- C++ dead `if(den<0)` in `Rational::from_double` (den provably ≥1) · `types.cpp:58-61`. Delete (`json_serialize.cpp` already removed the twin).
- C++ copy-paste severity-parse loop in `parse_validation`/`parse_parsed_dbc` · `json_parse.cpp:734-751`. Extract `parse_issue_entry`.
- C++ `error_code_table` declared size 59 with 57 initializers → 2 inert `{"",Unknown}` padding · `json_parse.cpp:33`. Drop the literal size (CTAD/`to_array`).
- Go `DispatchThen` not extracted (breaks DispatchSimple/DispatchWhen precedent; YAML+Excel duplicate) · `yaml.go:297-318` + `go/excel/excel.go:497-537`. **Downgraded** (in-sync today, different input shapes). Extract to loader.go.
- Go MockBackend binary shims pass `Process(nil,...)` vs `Process(state,...)` inconsistently (cosmetic; param discarded) · `mock.go:143-193`. Unify.
- Go `ExtractSignalsBin` omits the defensive `runtime.KeepAlive(data)` every sibling applies (not a live UAF — cgo pins arg) · `ffi.go:782-835`. Add it.
- Rust `rational_le` duplicated byte-for-byte in check.rs+ltl.rs (`Rational` has no comparison method) · `check.rs:39-42`. Fix: ONE inherent value-`le`/`cmp` method — **not** `Ord` (structural `Eq`: `1/2≠2/4` would break Ord/Eq consistency).
- Rust extended-flag encode copy-pasted across 7 sites while decode has `extended_flag` helper · `dbc.rs:772-773`. Add `set_extended`.
- Rust diag-signal filter predicate duplicated in `diag_values`/`enrich_eos` · `lib.rs:399-402`. Extract `select_diag_values`.

**Inefficient — all off the per-frame hot path:**
- Go CLI re-loads DBC via `ParseDBC` after `ParseDBCText` already loaded it · `go/cmd/aletheia/main.go:347,464`. **Diverges**: C++ does the same double-load; Python (reference) loads once. Fix Go+C++ in lockstep.
- Go `serializeDBC` marshals the whole DBC twice (throwaway size-probe + real) · `json.go:219-231`. **Downgraded** (control-plane O(N), not O(N²); the 51s/1000-msg figure misattributed to the Agda core). Reuse the bytes.
- Go `readTypedRows` issues one `GetCellType` per non-empty cell (2 mutex pairs + O(logN+M) each) after `GetRows` read all values · `go/excel/excel.go:247-285`. Single worksheet pass via `Rows()` (Python gets typed values free).
- Go `extractSignalValues` copies the full payload into a string cache key on every call incl. hits (the `m[string(b)]` elision doesn't apply when stored in a field) · `client.go:1084-1085`. **Diverges**: C++ uses a non-owning FrameKeyView on hits. Copy-free hit path.
- C++ `end_stream` re-extracts every last-known frame once *per failing property* (P×F FFI crossings) · `cpp/src/client.cpp:646-651,840-865`. **Diverges**: Rust (`lib.rs:435-488`) hoists-then-filters (F crossings) — the reference; C++/Go uncached, Python cached-but-per-P. Adopt Rust's shape.
- C++ `load_dbc_from_excel` deep-copies each dead-local `CellMap` into `data_rows` instead of moving · `excel.cpp:631`. `std::move`.
- C++ `load_dbc_from_excel` re-looks-up each group via `groups[key]` though grouping already populated the map · `excel.cpp:638-646`. Carry index-vectors in insertion order.
- Rust `FfiBackend` re-resolves FFI symbols via dlsym every call (2 dlsym + 2 dlerror/frame) · `backend.rs:438-440,476,565-567,607-609`. **Downgraded** (dominated by the RTS round-trip). **Diverges**: Go/C++ cache once at construction. Resolve once in `new`.
- Rust `enrich_eos` O(N²) linear-scan dedup where Go uses a hash set · `rust/src/lib.rs:459-463`. **Diverges** (EOS only, dominated by FFI extracts). Use `HashSet`.

**Ill-designed (low):**
- C++ `LazyIndex` populate-once-never-invalidated cache over public mutable `signals`/`messages`; three `operator[]` derefs (incl. `dbc.cpp:135`, missed by finder) → OOB UB when a fresh lookup uses a frozen index after `signals.clear()` · `cpp/src/dbc.cpp:89-135`, `dbc.hpp:29-51`. **Single-binding** for the UB, but Go (`dbc.go:84-89,196-211,612-661`) shares the frozen-index design and returns the *wrong element* (bounds-checked panic vs UB); Python/Rust linear-scan, immune. Fix: bound-check before each deref (`dbc.cpp:99,122,135`) and/or store key/pointer not positional index; close the Go silent-wrong-element bug too.
- cross: enriched reason mixes exact FFI-rendered formula text with a lossy double-rendered observed value (1/3 → "0.333333") · `cpp/src/client.cpp:713-714`. **consistent-wrong** across Go/Python/C++ — a maintainer **direction call** (AGENTS.md:31), *not* a unilateral fix: either document the observed-value approximation in all three or render observed values through the exact path in all three.

**Incomplete (low):**
- Rust never emits `extraction.process_failed`/`extraction.parse_failed` though its enrichment path hits both modes (`.ok()?` discards) · `rust/src/lib.rs:328-336`. **Diverges** (Go/Python/C++ emit both, distinct from the generic `enrichment.extraction_failed`). Match on the two error sites; add to the parity gate.

---

## Cross-binding scorecard (where the work is)

- **C++ is the repeat outlier in axis 2** — 7 of 13 inconsistencies (neg-denominator flip, anon-pair errors, within() overflow, inline-YAML bound, no-DBC guard, IssueCode-drops-code, multiplex-discriminator), plus the truncation-as-success (M1) and Excel-bold (M7) mediums. **Highest-leverage cleanup.**
- **Go owns axis 3** — 12 of 23 lying comments, all stale-identifier / wrong-count drift; a mechanical truthful-comment sweep clears most.
- **Rust** — logging completeness (FEATURE_MATRIX 11/16, two mislabeled events, unenforced `decode_stream` contract, unwired extraction-failure events) + a few DRY items; no structural problem.
- **Python** — cleanest binding (6 findings, all doc accuracy); no parity gap where it is the lone offender (it co-offends with Rust on CAN-id/DLC validation).
- **Consistent-wrong items (build_diagnostic, "51 codes", multiplex empty/missing, multiplex discriminator)** — fix ALL bindings in lockstep (consistency ≠ correctness). The lossy-render item is a maintainer **direction call**, not an autonomous fix.