# R19 Phase 2 Review Findings

**Branch**: `review-r19`
**Started**: 2026-05-10
**Tip at round start**: `7972c08` (post Phase-1 carry-over closure + post-UPD doc sync)
**Mode**: Phase 2 — fresh agent-driven review on the post-R19-carry-over tip. Phase 1 (R18 carry-over deferral cleanup) closed 2026-05-09 across clusters A-G.
**Tree state at round start**: clean.

---

## Step 0: Carry-over reconciliation

### From R19 Phase 1

| ID | Site | Phase 1 disposition | Phase 2 candidate disposition |
|---|---|---|---|
| **R19-CARRY-1** ← AGDA-A-16.4 | `src/Aletheia/CAN/Encoding.agda:122` Bool fast-path on `injectHelper` | RE-DEFER (4 probes failed at `with...in eq` outer-abstraction barrier) | **RE-DEFER pending** |

### From R18

| ID | Site | R18 deferral rationale | Phase 2 candidate disposition |
|---|---|---|---|
| **R19P2-CARRY-1** ← GO-B-28.3 | `go/aletheia/ffi.go:690-700` `outSize` bounded only by `MaxInt32` | Return-value not input; covered by upstream `MaxJSONBytes` cap | RE-DEFER probable |

R18 had ~445 unflipped `[ ]` markers but cluster narratives in CLAUDE.md confirm full closure; no action required.

---

## Wire-boundary audit

R19 Phase 1 closed every parser-surface wire boundary at `e37e6ea`. Phase 2 hypothesis confirmed: post-R19 surface is fully covered. **No new wire boundary surfaced; defense-in-depth gaps surfaced under cat 28 below.**

---

## Coverage check

| Agent | Categories owned | Status |
|---|---|---|
| Agda Agent A (Hygiene) | 1, 2, 4, 16, 21, 28, 29 + G-A1, G-A8 | ✓ returned (10 findings) |
| Agda Agent B (Semantics) | 7, 8, 9, 18, 20, 22-26 + G-A2-A6, A9, A10, A12 | ✓ returned (6 findings) |
| Agda Agent C (Cross-file) | 3, 5, 6, 27 + G-A14, A15, A16 | ✓ returned (19 findings) |
| Go Agent A (Hygiene & Style) | 1-6, 30 | ✓ returned (16 findings) |
| Go Agent B (Correctness & Runtime) | 7-14, 23-29, 33 | ✓ returned (30 findings) |
| C++ Agent A (Hygiene & Style) | 1-6, 30 | ✓ returned (8 findings) |
| C++ Agent B (Correctness & Runtime) | 7-14, 23-29, 33 | ✓ returned (55 findings) |
| Python Agent A (Hygiene & Style) | 1-6, 27, 28, 32, 33 | ✓ returned (30 findings) |
| Python Agent B (Correctness & Runtime) | 7-14, 23-26, 29-30, 34 | ✓ returned (36 findings) |
| Docs Agent A (Hygiene) | 1-9 | ✓ returned (40 findings) |
| Docs Agent B (Deep) | 10-22 | ✓ returned (40 findings) |
| CI/CD Agent | 1-5 | ✓ returned (6 findings) |
| Agda Agent D (system-level) | 10-13, 19, 32 + 14, 15, 17, 30, 31 | ✓ returned (25 findings) |
| Go system-level | 15-22, 31, 32 | ✓ returned (22 findings) |
| C++ system-level | 15-22, 31, 32 | ✓ returned (28 findings) |
| Python system-level | 15-22, 31 | ✓ returned (30 findings) |
| Docs cross-doc pass | 5, 15-18 | ✓ returned (38 findings) |

**Step 1 + Step 2 closure**: 17 of 17 agents returned. **~439 findings** total (296 step-1 + 143 step-2/cross-doc).

---

## Universal Rules tracking

- **UR-1 CHANGELOG**: surfaced in Docs (DOC-B-17.3 — two-SSOT problem with PROJECT_STATUS).
- **UR-2 adversarial-input bounds**: 6 limits.hpp constants unchecked at C++ parser (CPP-B-9.1 / CPP-B-28.4).
- **UR-3 reproducible build**: surfaced (CICD-2.2 Dockerfile libgmp10 unpinned; CICD-5.9 cosign binary unverified-fetch).

---

## Step 1 findings

### Agda Agent A — Hygiene (10 findings)

#### Cat 1: Dead code
- `[ ]` AGDA-A-1.1 [src/Aletheia/Limits.agda:138-143] `withinBound` defined but unreferenced; bound checks call `_≤ᵇ_` directly
- `[ ]` AGDA-A-1.2 [src/Aletheia/Protocol/Handlers.agda:11-12] Comment lists `handleDataFrame` as living in Internals; actually in `Protocol/StreamState.agda:62-72`
- `[ ]` AGDA-A-1.3 [src/Aletheia/CAN/DLC/Properties.agda:165] 16-deep `suc` chain in absurd pattern; G-A2 mandates `_≤?_` / `Fin n` / `toWitness`

#### Cat 2: Magic numbers
No findings.

#### Cat 4: Comment quality
- `[ ]` AGDA-A-4.1 [src/Aletheia/Protocol/Handlers.agda:11-12] (=1.2) stale handleDataFrame placement
- `[ ]` AGDA-A-4.2 [src/Aletheia/DBC/Validator/Checks.agda:5] Module says "16 DBC validity conditions"; actual count is 22 (CHECK 1-11, 13-23)
- `[ ]` AGDA-A-4.3 [src/Aletheia/DBC/Validator/Checks.agda:199-223] CHECK 17 sandwiched between 5 and 6, breaks doc reading flow
- `[ ]` AGDA-A-4.4 [src/Aletheia/CAN/Constants.agda:23] Comment hardcodes literal `512` rather than `max-physical-bits` symbol

#### Cat 16: Performance / stability artifacts
- `[ ]` AGDA-A-16.1 [benchmarks/stability/<commit>/] AGENTS.md cat 16 mandates `aletheia-ffi.hp` AND `aletheia-ffi.prof`; only `.hp` produced (RTS opts set `-hT` not `-p`)
- `[ ]` AGDA-A-16.2 [src/Aletheia/Protocol/StreamState/Internals.agda:88-135] Deferred `Fin (length atoms)` migration in-source — listed for review-trail completeness only

#### Cat 21: Safety flag & zero-postulate
No findings. `grep -L '^{-# OPTIONS --safe --without-K'` returns only Substrate.Unsafe (allowlisted).

#### Cat 28: Pragma abuse
No findings. Three `{-# CATCHALL #-}` in LTL/Simplify.agda are documented identity-pass-throughs.

#### Cat 29: Instance & reflection discipline
- `[ ]` AGDA-A-29.1 [src/Aletheia/DBC/DecRat/RationalRoundtrip.agda:1-17, 143-148, 390, 446, 472] 4 instance blocks; module header lacks `DEFER-stdlib-mandate` note
- `[ ]` AGDA-A-29.2 [src/Aletheia/DBC/DecRat.agda:251] `suc-pred ⦃ 2^a·5^b-NonZero a b ⦄`; header lacks DEFER note
- `[ ]` AGDA-A-29.3 [src/Aletheia/DBC/TextParser/DecRatParse/Properties.agda:1108-1239] 6 explicit witness sites; header lacks DEFER note
- `[ ]` AGDA-A-29.4 [src/Aletheia/DBC/TextFormatter/Emitter.agda:175-177] Local `instance scale-nonZero`; header lacks DEFER note

#### G-A1: Import hygiene
- `[ ]` AGDA-A-GA1.1 [src/Aletheia/Error.agda:22] `boundKindCode` imported but never used; only `boundKindLabel` used
- `[ ]` AGDA-A-GA1.2 [src/Aletheia/CAN/BatchExtraction.agda:28] `Error` and `MuxValueMismatch` imported — verify use; flagged as candidate

#### G-A8: Flag hygiene
No findings beyond Unsafe-allowlist already documented.

### Agda Agent B — Semantics (6 findings)

#### Cat 7: Type tightness
- `[ ]` AGDA-B-7.1 [src/Aletheia/Protocol/StreamState/Internals.agda:84-85] `lookupAtom : List SignalPredicate → ℕ → Maybe SignalPredicate` — raw `ℕ` index; deferral acknowledged in-source per `feedback_in_source_deferral_notes.md`
- `[ ]` AGDA-B-7.2 [src/Aletheia/CAN/DLC.agda:21-32] `dlcToBytes : ℕ → ℕ` exported; takes raw `ℕ` not `DLC`; external callers can pass raw

#### Cat 8: Proof simplification
No findings.

#### Cat 9: Proof soundness
No findings.

#### Cat 18: Dead-branch provability
- `[ ]` AGDA-B-18.1 [src/Aletheia/CAN/SignalExtraction.agda:80-81] `checkPresenceP zero _ _ (When _ _) = just MuxChainCycle` — defensive guard; G-A6 wants proof or type-tightening, comment alone insufficient
- `[ ]` AGDA-B-18.2 [src/Aletheia/DBC/Validator/Checks.agda:181] `walkMux | nothing = true` — cross-check pipeline contract not structural; document composition with check 4
- `[ ]` AGDA-B-18.4 [src/Aletheia/CAN/Encoding.agda:80-88] `extractSignal else nothing` — caller reachability documentation imprecise

#### Cats 20, 22, 23, 24, 25, 26 — clean
No findings.

#### Guidelines G-A2 / A3 / A4 / A5 / A6 / A9 / A10 / A12
- `[ ]` AGDA-B-GA6.1 = AGDA-B-18.1
- `[ ]` AGDA-B-GA6.2 = AGDA-B-18.2

### Agda Agent C — Cross-file (19 findings)

#### Cat 3: Naming consistency (5)
- `[FP]` AGDA-C-3.1 [src/Aletheia/DBC/TextFormatter/TopLevel.agda:76] `formatChars` breaks `emit*-chars` convention — **adjudicated FP** (2026-05-11, cluster 14 naming sub-batch): `formatChars : DBC → List Char` follows the `format*` API convention (parallels `formatText : DBC → String` in `Aletheia.DBC.TextFormatter`, both are the top-level whole-file emitters; one returns `List Char`, the other `String`).  The `emit*-chars` family is for per-section sub-emitters (`emitMessages-chars`, `emitAttributes-chars`, etc.) that `formatChars` composes.  Two distinct, internally-consistent conventions for two distinct roles (top-level vs. per-section).  Renaming `formatChars → emitDBC-chars` would also cascade through the universal-roundtrip proof aggregator (`formatChars-body`, `formatChars-body-bridge`, `parseTextChars-on-formatChars`, `parseDBCText-on-formatChars` — load-bearing theorem names with ~80 references).
- `[ ]` AGDA-C-3.2 [src/Aletheia/Limits.agda:49,62 + 116,128] `BoundKind` ctors mix `<noun>Length` / `<noun>Bytes` / `Byte+Count` suffix orderings
- `[x]` AGDA-C-3.3 [src/Aletheia/DBC/Validator.agda:35,46,51 vs :36-50] 3 `checkDuplicate*` exceptions break the `checkAll*` prefix convention — closed by cluster 14 naming sub-batch (51 sites across 6 files)
- `[x]` AGDA-C-3.4 [src/Aletheia/DBC/Formatter/MetadataRoundtrip.agda:153 vs :217,242] kebab `-list-` vs camelCase inconsistency in `*-go` helpers — closed by cluster 14 naming sub-batch (`valueEntryList-*` → `valueEntry-list-*`, 8 sites in MetadataRoundtrip.agda + SignalRoundtrip.agda)
- `[ ]` AGDA-C-3.5 [src/Aletheia/DBC/Formatter/MessageRoundtrip/{Standard,Extended}.agda] `-std`/`-ext` suffix doesn't match type-level `Standard`/`Extended`

#### Cat 5: Error message consistency (3)
- `[x]` AGDA-C-5.1 [src/Aletheia/Error.agda:333 vs :71,234,242,244] `formatDispatchError MissingTypeField` adds trailing `" in request"` no other "missing 'X' field" carries — closed by cluster 14 naming sub-batch (string text aligned)
- `[x]` AGDA-C-5.2 [src/Aletheia/Error.agda:188 vs :83-87,236] Range-violation strings split across `"out of range (max N)"` / `"DLC exceeds maximum value"` (no max) / `"<label> N exceeds limit M"` — closed by cluster 14 naming sub-batch (converged on `"<label> N exceeds limit M"`; SignalIndexOOB kept "out of range" — index, not value-range — and bound is contextual; `DLCExceedsMax` now uses `maxDLC-FD` literal)
- `[ ]` AGDA-C-5.3 [src/Aletheia/Error.agda:351 + 326] `DBCTextParseError` and `DispatchError` lack `InContext` ctor present on every other error ADT

#### Cat 6: Redundant patterns (6)
- `[ ]` AGDA-C-6.1 [src/Aletheia/Error.agda:67,148,184,224,288] `InContext` duplicated across 5 ADTs with identical shape — combinator candidate
- `[ ]` AGDA-C-6.2 [src/Aletheia/Error.agda:66,183,356] `InputBoundExceeded : BoundKind → ℕ → ℕ → X` duplicated across 3 ADTs — lift to top-level Error
- `[ ]` AGDA-C-6.3 [src/Aletheia/DBC/Validator/Checks.agda:506-541 + 551-567] 3 near-identical `checkUnknown*` functions — single helper
- `[ ]` AGDA-C-6.4 [src/Aletheia/DBC/Formatter/MessageRoundtrip/{Standard,Extended}.agda] 72-line mirror twins — parameterise over CANId ctor
- `[x]` AGDA-C-6.5 [src/Aletheia/DBC/Formatter/MetadataRoundtrip.agda:153,189,217,242] 4 `-list-go` helpers identical template — closed by cluster 14 / AGDA-C-6.5 — added `parseObjectList-roundtrip` combinator in MetadataRoundtrip.agda; 4 per-entity `*-list-go` helpers (signalGroup / environmentVar / valueEntry / valueTable) collapsed to one-line combinator calls; combinator takes `formatter-eq` witness that `formatter ≡ JObject ∘ fields` (always `λ _ → refl` when formatter is `formatX x = JObject (...)` syntactically)
- `[ ]` AGDA-C-6.6 [src/Aletheia/LTL/SimplifySound/Decomposition.agda] ≥5 And/Or-symmetric lemma pairs — extend `Aletheia.LTL.Semantics.Duality` (~150 LOC saving)

#### Cat 27: Stdlib coverage & dedup (5)
- `[ ]` AGDA-C-27.1 [src/Aletheia/DBC/Formatter/MetadataRoundtrip.agda:110-113] `map-∘-identifier` reproduces `Data.List.Properties.map-∘`
- `[ ]` AGDA-C-27.2 [src/Aletheia/Parser/Properties.agda:50,56] `monad-left/right-identity` may shadow stdlib `RawMonad.Laws`
- `[ ]` AGDA-C-27.3 [src/Aletheia/DBC/Formatter/MetadataRoundtrip.agda:91-94] `parseCharsList-roundtrip` — generalise via stdlib `cong-map`
- `[ ]` AGDA-C-27.4 [src/Aletheia/CAN/Endianness/Properties/WriteSet.agda:167 + Data/BitVec.agda:77] 2 hand-rolled `*-comm` lemmas — future dedup candidate
- `[ ]` AGDA-C-27.5 [src/Aletheia/Protocol/FrameProcessor/Properties/Step.agda:69-70] `mod-identity-byte` is one-line wrapper over stdlib `m<n⇒m%n≡m`

### Go Agent A — Hygiene (16 findings)

#### Cat 1: Hygiene
- `[ ]` GO-A-1.1 [go/aletheia/error.go:99-100, types.go:155-160] `CanID` mixed-case acronym vs `MessageID` / `ID` siblings; cross-binding parity touchpoint
- `[ ]` GO-A-1.2 [go/aletheia/types.go:209-211] `maxPayloadBytes = 64` duplicates `MaxFrameByteCount = 64` (limits.go:62)

#### Cat 2: Naming
- `[ ]` GO-A-2.1 [go/aletheia/dbc.go: 30+ ids] `Dbc*` prefix violates Go acronym capitalization (DBC). Internal asymmetry: methods use `DBC`, types use `Dbc`
- `[ ]` GO-A-2.2 [go/aletheia/types.go:137,155,171] `CanID` — `Can` is acronym; convention says `CANID` or `CANIdentifier`. Cross-binding parity may justify
- `[ ]` GO-A-2.3 [go/aletheia/json.go:119,237] `vds` vs `unresolvedVDs` — sibling-list var naming inconsistency

#### Cat 3: Doc strings on exported symbols
- `[ ]` GO-A-3.1 [go/aletheia/result.go:134-155] 22 `IssueCode` consts use trailing line-comments rather than leading godoc
- `[ ]` GO-A-3.2 [go/aletheia/error.go:68-134] 51 `Code*` error code constants lack godoc per-symbol
- `[ ]` GO-A-3.3 [go/aletheia/{dbc,ltl,result,mock,ffi,backend}.go] Sealing-marker methods (signalPresence/predicate/etc.) — surrounding type docs don't say "sealed" uniformly
- `[ ]` GO-A-3.4 [go/aletheia/dbc.go:237] `DbcVarType` const block lacks per-constant docs
- `[ ]` GO-A-3.5 [go/aletheia/dbc.go:357-364] 7 `DbcAttrScope*` const block lacks per-constant docs
- `[ ]` GO-A-3.6 [go/aletheia/types.go:75] `Frame` struct fields undocumented
- `[ ]` GO-A-3.7 [go/aletheia/error.go:48-53,198-209] Field doc comments asymmetric (some inline, some absent)

#### Cat 4: Style
- `[ ]` GO-A-4.1 [go/aletheia/dbc.go:357-364] `DbcAttrScope*` iota block lacks per-constant docs (cf. 3.5)
- `[ ]` GO-A-4.2 [go/aletheia/client.go:733-743] `c.logger.LogAttrs(context.Background(),...)` inside method that has `ctx` — should forward
- `[ ]` GO-A-4.3 [go/aletheia/client.go:798-839] `enrichViolation` and `enrichPropertyResult` use `context.Background()`
- `[ ]` GO-A-4.4 [go/aletheia/json.go:1093-1097] `maxFormulaDepth` grouped with unrelated string consts
- `[ ]` GO-A-4.5 [go/aletheia/json.go:1054-1057] Format inverted — happy path should be upper branch

#### Cat 5: Errors
- `[ ]` GO-A-5.1 [go/aletheia/error.go:155-167] `protocolError`/etc. constructors build *Error with `Code: ""`; no invariant test
- `[ ]` GO-A-5.2 [go/aletheia/json.go:1146] `protocolError(msg)` with empty msg renders `aletheia protocol error: ` — brittle sentinel
- `[ ]` GO-A-5.3 [go/aletheia/client.go:165-189] `resolveSignalIndices` mixes `validationError` and `fmt.Errorf %w` — uneven errors.Is/As
- `[ ]` GO-A-5.4 [go/aletheia/client.go:629] `fmt.Errorf("frame %d: %w", ...)` lacks method-name prefix others use
- `[ ]` GO-A-5.5 [go/aletheia/error.go:8-13] `ErrBinaryPathUnsupported` is the only sentinel; consider `ErrClientClosed` for discoverability

#### Cat 6: Redundant patterns
- `[ ]` GO-A-6.1 [go/aletheia/client.go: 15 sites] `c.lock(ctx); defer c.unlock(); if err := ctx.Err()...` boilerplate × 15 — `c.acquire(ctx, name)` helper
- `[ ]` GO-A-6.2 [go/aletheia/{dbc,error,result,types}.go] 6 iota-enum types each hand-roll `String()` — codegen candidate
- `[ ]` GO-A-6.3 [go/aletheia/json.go: 8 sites] Tier 1/2 array parsers share shape — generic `parseObjects[T any]`

#### Cat 30: Logging discipline
- `[ ]` GO-A-30.1 [docs/LOG_EVENTS.yaml:94] `cache.full` says "evicted oldest entry" — actual binding code REJECTS new entries (no eviction); cross-binding doc-vs-impl drift
- `[ ]` GO-A-30.2 [go/aletheia/client.go: 13 sites] `slog.LogAttrs(context.Background(),...)` discards caller ctx
- `[ ]` GO-A-30.3 [go/aletheia/client.go:251-578] 5 `c.logger.Info(...)` variadic-form vs LogAttrs elsewhere; convention asymmetric
- `[ ]` GO-A-30.4 [go/aletheia/client.go:251-253,286-288] `dbc.parsed` / `properties.set` field schema undocumented in LOG_EVENTS.yaml

### Go Agent B — Correctness (30 findings)

#### Cat 7: Type safety
- `[ ]` GO-B-7.1 [go/aletheia/dbc.go:602] `extendedIDFlag = 1 << 32` untyped — make `uint64`
- `[ ]` GO-B-7.2 [go/aletheia/types.go:73-80] `Frame{DLC: DLC{value: 99}}` zero-value escape; no `NewFrame` constructor
- `[ ]` GO-B-7.3 [go/aletheia/types.go:24,41,44] `PhysicalValue/Delta/Tolerance` are float64 aliases; NaN/Inf reach `serializePredicate` unchecked

#### Cat 8: Serialization
- `[ ]` GO-B-8.1 [go/aletheia/json.go:451-477] `serializePredicate` emits NaN/Inf as non-RFC8259 JSON tokens
- `[ ]` GO-B-8.2 [go/aletheia/json.go:633-660] `parseRational` accepts `den < 0` and rewrites; Python+Agda reject (cross-binding wire symmetry)
- `[ ]` GO-B-8.3 [go/aletheia/json.go:128-136] `serializeDBC` map-iter relies on json.Marshal sort — undocumented future-regression vector
- `[ ]` GO-B-8.4 [go/aletheia/json.go:705] `parseNumberAsInt64` boundary `n > MaxInt64` unreachable; comment about silent precision loss is wrong

#### Cat 9: Parsing
- `[ ]` GO-B-9.1 [go/aletheia/json.go:1980-1988] `startBit/length` validation uses literal `0-511`/`1-64` not `MaxBitPosition`/`MaxBitLength`
- `[ ]` GO-B-9.2 [go/aletheia/json.go:1015] `parseExtractionBin` no upfront cardinality × per-entry-size bound check before loop
- `[ ]` GO-B-9.3 [go/aletheia/yaml.go:122-128] No nesting-depth or alias-cycle limit on YAML parse (YAML bomb bypass)
- `[ ]` GO-B-9.4 [go/aletheia/json.go:262-276] `serializeDBC` defense-in-depth on output only; raw `parseDBCText` text not measured pre-FFI

#### Cat 10: FFI
- `[ ]` GO-B-10.1 [go/aletheia/ffi.go:99-111] `strdup` 4 strings on init never freed (intentional, matches Python/C++) — confirming
- `[ ]` GO-B-10.2 [go/aletheia/ffi.go:330-333] `rts.cores_mismatch` warning fires only when logger not nil; silently swallowed without
- `[ ]` GO-B-10.3 [go/aletheia/ffi.go:558-611] `BuildFrameBin`/etc. no `runtime.KeepAlive(...)` after `C.call_*`; defensive against future inliner
- `[ ]` GO-B-10.4 [go/aletheia/ffi.go:184-195] `loadSym` thread-locality assumes outer LockOSThread; future refactor risk

#### Cat 11: Tests
- `[ ]` GO-B-11.1 [go/aletheia/cancel_test.go:160-167] Polls `callCount() == 0` with `time.Sleep(time.Millisecond)` per `feedback_no_physical_time_in_tests.md`
- `[ ]` GO-B-11.2 [go/aletheia/cancel_test.go:181] `time.Sleep(50 * time.Millisecond)` flake source (same finding shape)
- `[ ]` GO-B-11.3 Fuzz coverage omits `parseFrameResponse`/`parseStreamResponse`/`parseDbcSignal`
- `[ ]` GO-B-11.4 [go/aletheia/mock.go:103-121] No "queue fully consumed" assertion helper

#### Cat 12: Error wrapping
- `[ ]` GO-B-12.1 [go/aletheia/error.go:198-209] `InputBoundExceededError` lacks `Unwrap()`; YAML loader paths populate `Code: ""` (cross-binding parity loss)
- `[ ]` GO-B-12.2 [go/aletheia/error.go:48-53] `Error.Code` not in `Error()` string; C++/Python format `[code] message`
- `[ ]` GO-B-12.3 [go/aletheia/error.go:144-146] `newCodedError` package-private; no `NewCodedValidationError` for external loaders

#### Cat 13: Nil discipline
- `[ ]` GO-B-13.1 [go/aletheia/dbc.go:191-207] `DbcMessage.SignalByName` silently falls back when `signalIndex == nil` — hides misuse of zero-value struct
- `[ ]` GO-B-13.2 [go/aletheia/result.go:18-23] `ExtractionResult.Get` returns silent `(0, false)` if `index == nil`; lazy-build or panic
- `[ ]` GO-B-13.3 [go/aletheia/client.go:48-50] `c.diags`/`c.cache` nil-before-SetProperties; defensive checks fine but tighter contract assertion would help

#### Cat 14: Context propagation
- `[ ]` GO-B-14.1-14.2 [go/aletheia/client.go:107-114, 88-101] `Close()` blocks unbounded on `lockCh`; documented in CANCELLATION.md but watchdog timeout safer
- `[ ]` GO-B-14.4 [go/aletheia/client.go:733,740,802,824,866,902,914] `slog.LogAttrs` with `context.Background()` — discards caller ctx (cross-ref GO-A-30.2)

#### Cats 23, 24: Channel / sync
No findings (correct double-close avoidance, mutex hygiene clean).

#### Cat 25: Hot-path perf
- `[ ]` GO-B-25.1 [go/aletheia/client.go:725-728] `dataCopy := make(...)` correct — verified guarded
- `[ ]` GO-B-25.2 [go/aletheia/json.go:42-69] `serializeDataFrame` builds `strings.Builder` per call; sync.Pool candidate
- `[ ]` GO-B-25.3 [go/aletheia/json.go:111-114,266] `serializeDBC` allocates `make([]map[string]any,...)` twice on parse + defense-in-depth probe
- `[ ]` GO-B-25.4 [go/aletheia/client.go:856-859] `extractLastKnownValues` allocates+sorts per call (cold path; OK)

#### Cat 27: cgo security
- `[ ]` GO-B-27.2 [go/aletheia/ffi.go:206-208] `libPath` user-supplied; `filepath.Clean` doesn't validate against NUL bytes — `C.CString` truncates
- `[ ]` GO-B-27.3 [go/aletheia/ffi.go:392-393] `cInput := C.CString(input)` NUL-byte truncation; `len(input) > MaxJSONBytes` is bytes-of-Go-string, divergent

#### Cat 28: File I/O
- `[ ]` GO-B-28.2 [go/aletheia/yaml.go:31-37] TOCTOU between `Stat` and `ReadFile`; cross-binding (Python same exposure)
- `[ ]` GO-B-28.3 [go/aletheia/yaml.go:60-83] `loadYAMLData` path-vs-inline precedence undocumented; semantic-hijack vector

#### Cat 29: Determinism
No findings (json.Marshal sorts; signalIndex map access via lookup not range).

#### Cat 33: Dynamic correctness
- `[ ]` GO-B-33.1 [go/aletheia/fuzz_test.go:56-73] `FuzzMarshalCommand` doesn't assert `parsed["type"] == "command"`
- `[ ]` GO-B-33.2 Verify `tools/run_ci.py` enforces `-race` on every CI lane
- `[ ]` GO-B-33.3 No property-based testing harness for `floatToRational` round-trip (Python uses hypothesis)
- `[ ]` GO-B-33.4 [go/aletheia/property_test.go] Verify it covers `floatToRational` round-trip + `serializeRational ∘ parseRational` + `serializeDBC ∘ parseDbcDefinition`

### C++ Agent A — Hygiene (8 findings)

#### Cat 1: Hygiene
- `[ ]` CPP-A-1.1 [cpp/src/ffi_backend.cpp:237-343] 8× repeated FFI-string deleter+guard+null-check pattern; extract `wrap_str_result(char*, std::string_view)` helper
- `[ ]` CPP-A-1.2 [cpp/include/aletheia/dbc.hpp:340 + cpp/src/json_parse.cpp:585] "Track E.8 (Plan B)" qualifier — Track E shipped; drop "(Plan B)" tag

#### Cat 2: Naming
No findings (`.clang-tidy` enforced uniformly).

#### Cat 3: Doc / comment quality
- `[ ]` CPP-A-3.1 [cpp/include/aletheia/excel.hpp:13-14] Pre-include comment names `load_dbc_from_excel` but not `create_excel_template`
- `[ ]` CPP-A-3.2 [cpp/src/json_parse.cpp:148-152] R-stamp surfaced in user-facing `///` doxygen comment; downgrade to `//`

#### Cat 4: Style
No findings.

#### Cat 5: Errors
- `[ ]` CPP-A-5.1 [cpp/src/ffi_backend.cpp:253-256, 331-334; cpp/src/yaml.cpp:32-61] `throw std::runtime_error` past the FFI boundary; sibling `update_frame_bin`/`extract_signals_bin` use `std::expected`. Asymmetric — uncaught exception unwinds through `AletheiaClient::send_frame`

#### Cat 6: Redundant patterns
- `[ ]` CPP-A-6.1 (= CPP-A-1.1) FFI-string deleter pattern × 8
- `[ ]` CPP-A-6.2 [cpp/src/client.cpp + dbc.cpp + json_serialize.cpp + ffi_backend.cpp] `std::visit([](const auto& v) → uint32_t { return v.value(); }, id)` + `holds_alternative<ExtendedId>(id)` ~12 sites; promote `can_id_value`/`can_id_is_extended` to `aletheia::detail::` or types.hpp

#### Cat 30: Logging discipline
- `[ ]` CPP-A-30.1 [docs/LOG_EVENTS.yaml:94 vs cpp/include/aletheia/client.hpp:167-172] `cache.full` description says "evicted oldest entry"; C++ implementation doesn't evict (= GO-A-30.1)
- `[ ]` CPP-A-30.2 [cpp/src/client.cpp:419,463,590] `properties.set`/`stream.ended` use camelCase keys (`numResults`, `numFails`, `numUnresolved`); other sites use snake_case (`active_cores`, `requested_cores`, `ts`)
- `[ ]` CPP-A-30.3 [cpp/src/client.cpp:419,590,657-660,678-681,720] `static_cast<std::int64_t>(size())` for `size_t` quantities; should be `std::uint64_t` for size-style

### C++ Agent B — Correctness (55 findings)

#### Cat 7: Type safety
- `[ ]` CPP-B-7.1 [cpp/include/aletheia/types.hpp:64-71] `Rational(n, d)` uses `assert(d > 0)` — disappears under `-DNDEBUG` (Release default); hot-path callers bypass `Rational::make`
- `[ ]` CPP-B-7.2 [cpp/src/json_parse.cpp:822/869] `parse_rational_as_int` int64→size_t narrowing; no upper bound check
- `[ ]` CPP-B-7.3 [cpp/src/client.cpp:267] Extraction-bin `Rational{num, den}` skips den-positive normalisation
- `[ ]` CPP-B-7.4 [cpp/src/ffi_backend.cpp:32 vs cpp/include/aletheia/limits.hpp:75] Two parallel `64`-byte constants (`max_can_fd_payload_bytes` anon-ns vs public `max_frame_byte_count`); SSOT violation

#### Cat 8: Serialization
- `[ ]` CPP-B-8.1 [cpp/src/json_serialize.cpp:34-38] `rational_to_json` no gcd normalisation (Python+Go normalize)
- `[ ]` CPP-B-8.2 [cpp/src/json_serialize.cpp:516-531] `serialize_send_frame` future-fragile — no JSON-escape audit on `std::format`
- `[ ]` CPP-B-8.3 [cpp/src/json_serialize.cpp:466-468] `serialize_parse_dbc_text` correctly uses `Json::dump`
- `[ ]` CPP-B-8.4 [cpp/src/json_serialize.cpp:394-456] `formula_to_json` `max_formula_depth = 100` not synced with `Aletheia.Limits` (`max_atom_count_per_property = 1024`, `max_nesting_depth = 64`)

#### Cat 9: Parsing
- `[ ]` CPP-B-9.1 [cpp/src/json_parse.cpp:122-141] `parse_bounded` only checks nesting; 6 limits.hpp bounds (messages_per_file, signals_per_message, atom_count, identifier_length, string_length_bytes, attributes_per_file, value_descriptions_per_file) NOT checked
- `[ ]` CPP-B-9.2 [cpp/src/json_parse.cpp:117-119] `make_error` redundant `static`+namespace
- `[ ]` CPP-B-9.3 [cpp/src/json_parse.cpp:251] `parse_extraction_bin` `expected_size` static_assert candidate
- `[ ]` CPP-B-9.4 [cpp/src/json_parse.cpp:165-184] `parse_signal_value` bare double `1.5` silently throws — clearer error wanted

#### Cat 10: FFI
- `[ ]` CPP-B-10.1 [cpp/src/ffi_backend.cpp:189-191] Constructor catch-all behavior documented; not actionable
- `[ ]` CPP-B-10.2 [cpp/src/ffi_backend.cpp:124-133] `dlerror()` race in pre-throw error message
- `[ ]` CPP-B-10.3 [cpp/src/ffi_backend.cpp:75-88] `start_lifetime_as_array<u8>` (C++23) UB-free alternative to reinterpret_cast (cosmetic)
- `[ ]` CPP-B-10.4 [cpp/src/ffi_backend.cpp:165-187] `rts.cores` records what we requested, not actual `GHCRTS=` env override
- `[ ]` CPP-B-10.5 [cpp/src/ffi_backend.cpp:171-179] hs_init may rewrite argv; argc not read back

#### Cat 11: Tests
- `[ ]` CPP-B-11.1 [cpp/tests/unit_tests_input_bounds.cpp:38-49] Constants test only asserts numeric — not cross-binding parity claim
- `[ ]` CPP-B-11.2 [cpp/tests/test_helpers.hpp] Verify mock-vs-real-FFI separation in shared header
- `[ ]` CPP-B-11.3 [cpp/tests/fuzz/] R19 cluster G's `Rational::from_double` should add NaN/Inf/overflow fuzz target

#### Cat 12: Exception safety
- `[ ]` CPP-B-12.1 [cpp/src/client.cpp:75-86] `~AletheiaClient` `static_cast<void>(std::current_exception())` is no-op; backend close failures silently lost — at least gate-log
- `[ ]` CPP-B-12.2 [cpp/src/client.cpp:101-124] Move-assign `noexcept` calls `backend_->close()` (can throw); container moves not noexcept on all stdlib configs
- `[ ]` CPP-B-12.3 [cpp/src/ffi_backend.cpp:236-238] Unique_ptr deleter pattern correct
- `[ ]` CPP-B-12.4 [cpp/src/json_parse.cpp:622-636] `j.at(...).get<>` raises nlohmann errors; safe but worth audit

#### Cat 13: UB hazards
- `[ ]` CPP-B-13.1 [cpp/src/client.cpp:235-237/268-271/278-282] `memcpy` reads native byte order — add `static_assert(std::endian::native == std::endian::little)`
- `[ ]` CPP-B-13.2 [cpp/src/json_parse.cpp:264] `INT64_MIN / -1` UB; ordering protects but brittle if reordered
- `[ ]` CPP-B-13.3 [cpp/src/ffi_backend.cpp:430] `out_size != 0` with `out_buf == nullptr` silently discards size-mismatch signal
- `[ ]` CPP-B-13.4 [cpp/src/excel.cpp:40-42] `sv_end_ptr` C++20 contiguous_iterator OK
- `[ ]` CPP-B-13.5 [cpp/src/types.cpp:35-43] `from_double` scaled `static_cast<double>(INT64_MAX)` rounds UP → boundary UB; cluster G hardened NaN/Inf but not full overflow corner

#### Cat 14: Data races
- `[ ]` CPP-B-14.1 [cpp/src/ffi_backend.cpp:90-99] `RTSState` Meyers singleton race-free
- `[ ]` CPP-B-14.2 [cpp/include/aletheia/dbc.hpp:32-50] `LazyIndex<...>` `mutable std::optional` NOT thread-safe; document single-thread restriction
- `[ ]` CPP-B-14.3 [cpp/include/aletheia/log.hpp:54-82] `std::function<void(...)>` copy-assignment not atomic; document Logger move-only

#### Cat 23: Resource discipline
- `[ ]` CPP-B-23.1 (= CPP-B-12.3) RAII helper consolidation candidate
- `[ ]` CPP-B-23.3 [cpp/src/excel.cpp:619-642] `XLDocument.save()` throw leaves partial file; remove-on-failure for atomicity

#### Cat 24: Sanitizer-clean
- `[ ]` CPP-B-24.2 [cpp/src/ffi_backend.cpp:189-192] On RTS init failure, `dlclose` may run while RTS-spawned threads live; verify under TSan

#### Cat 25: Hot-path perf
- `[ ]` CPP-B-25.1 [cpp/src/client.cpp:484-486] `last_frames_.insert_or_assign(...FramePayload(...))` per-frame allocation when diagnostics installed; reuse storage candidate
- `[ ]` CPP-B-25.4 [cpp/include/aletheia/log.hpp:54-62] `Logger::log()` short-circuits but `initializer_list<LogField>` allocates per callsite — outer `if (logger_)` gate inconsistent

#### Cat 26: Stability
- `[ ]` CPP-B-26.2 [cpp/src/client.cpp:172-173] `cache_` capped at `max_cache_size = 256`; no LRU eviction; long stream silently degrades

#### Cat 27: Stdlib idioms
- `[ ]` CPP-B-27.2 [cpp/src/json_parse.cpp:103-106] `error_code_from_string` linear scan over 58 entries; cold path acceptable
- `[ ]` CPP-B-27.3 [cpp/src/excel.cpp:122-124/144-147/172-176] 3 near-identical `transform`+`toupper` lambdas — `to_upper(std::string&)` helper
- `[ ]` CPP-B-27.4 [cpp/include/aletheia/types.hpp:213-236] `bytes_to_dlc` linear scan over 16-pair array; minor

#### Cat 28: Security & I/O
- `[ ]` CPP-B-28.1 [cpp/src/yaml.cpp:243-254] `load_checks_from_yaml` no path validation; document caller responsibility
- `[ ]` CPP-B-28.2 [cpp/src/excel.cpp:444-447/567-569] TOCTOU between exists+open
- `[ ]` CPP-B-28.4 [cpp/include/aletheia/limits.hpp:32-75] 6 limits.hpp constants have no enforcement code (cross-ref CPP-B-9.1)

#### Cat 33: Dynamic correctness
- `[ ]` CPP-B-33.1 [cpp/tests/fuzz/fuzz_parse_rational_number.cpp] Verify NaN/Inf/`std::nextafter(int64_max_d, INFINITY)` boundary inputs after R19 cluster G
- `[ ]` CPP-B-33.2 [cpp/tests/fuzz/fuzz_parse_response.cpp + fuzz_parse_dbc_json.cpp] R19 cluster A's `parse_bounded` depth limit — verify deep-nested JSON in fuzz dictionary

### Python Agent A — Hygiene (30 findings)

#### Cat 1: Hygiene
- `[ ]` PY-A-1.1 [python/benchmarks/violations.py:24] `os.path.join` use; should be `pathlib` (cross-ref Cat 28)
- `[ ]` PY-A-1.2 [python/aletheia/__init__.py:118,124,130] `_e` name non-idiomatic (read but underscored)
- `[ ]` PY-A-1.3 [python/aletheia/asyncio/_client.py:36,42] Annotation-only imports outside `TYPE_CHECKING`

#### Cat 2: Naming
No findings (PEP 8 conformant).

#### Cat 3: Doc strings
- `[ ]` PY-A-3.1 [python/aletheia/protocols.py:670-684] `SignalValue/SignalError` TypedDicts have one-line docstrings vs richer peers
- `[ ]` PY-A-3.2 [python/aletheia/cli.py:189] `_load_dbc` docstring doesn't document `_die`-on-missing-file branch
- `[ ]` PY-A-3.3 [python/aletheia/checks.py:101-113 + dsl.py:343/367/651/675] Missing `Raises:` sections
- `[ ]` PY-A-3.4 [python/aletheia/protocols.py:14-23] `is_str_dict`/`is_object_list` lack `Returns:` for TypeGuard
- `[ ]` PY-A-3.5 [python/aletheia/dbc_queries.py:13-96] 8 query fns one-line docstrings; Go richer
- `[ ]` PY-A-3.6 [python/aletheia/dsl.py:266-269] Internal-constructor docstrings don't document `_data` invariant

#### Cat 4: Style
- `[ ]` PY-A-4.1 [python/aletheia/dsl.py:46,52-58] Single-quoted dict keys (`'operator'`) vs project's double quotes elsewhere
- `[ ]` PY-A-4.2 [python/aletheia/dsl.py:90,109,128,...] All formula-builder methods use `'`; protocols.py and helpers.py use `"`
- `[ ]` PY-A-4.3 [python/aletheia/checks.py:72,93,180,234] 4× `# pylint: disable=too-few-public-methods` — review against fluent-builder protocol
- `[ ]` PY-A-4.4 [python/aletheia/cli.py:527] `# pylint: disable=too-many-locals` on `run_checks`; refactor candidate
- `[ ]` PY-A-4.5 [python/aletheia/client/_client.py:566 + asyncio/_client.py:159 + _signal_ops.py:144] `# pylint: disable=too-many-arguments`; FFI surface fixed
- `[ ]` PY-A-4.6 [python/aletheia/asyncio/testing.py:78,89,93] `# noqa: PLR0913` + `# type: ignore[method-assign]` — protocol typing could remove

#### Cat 5: Errors
- `[ ]` PY-A-5.4 [python/aletheia/excel_loader.py:295] `raise RuntimeError(...)` not typed AletheiaError subclass
- `[ ]` PY-A-5.6 [python/aletheia/client/_response_parsers.py:62-71] `ProtocolError` raises lack `code=` parameter

#### Cat 6: Redundant patterns
- `[ ]` PY-A-6.1 [python/aletheia/cli.py:131,197,221,629] 5 `_die(...)` paths share `not p.exists()` precondition
- `[ ]` PY-A-6.3 [python/aletheia/checks.py:144,171,226] 3 classes raise same `"<x>: lo must be <= hi"`
- `[ ]` PY-A-6.4 [python/aletheia/dsl.py:343,367,651,675 + checks.py:106,194] 6 `time_ms < 0` raises
- `[ ]` PY-A-6.5 [python/aletheia/client/_helpers.py:401-405 + _loader_utils.py:37 + _helpers.py:307,333] 4 sites duplicate `isinstance(v, bool) or not isinstance(v, int)`

#### Cat 27: Module organization
- `[ ]` PY-A-27.4 [python/aletheia/client/_client.py] 930 LOC near pylint cap
- `[ ]` PY-A-27.5 [python/aletheia/protocols.py] 976 LOC near cap

#### Cat 28: File I/O & encoding
- `[ ]` PY-A-28.1 [python/aletheia/yaml_loader.py:157] `open(source, encoding="utf-8")` not `source.open(encoding="utf-8")`
- `[ ]` PY-A-28.2 [python/benchmarks/violations.py:90,97,104,115] `os.path.join` not `Path / "x"`
- `[ ]` PY-A-28.3 [python/benchmarks/violations.py:327,328] `os.unlink/os.rmdir` not `Path.unlink/.rmdir`
- `[ ]` PY-A-28.4 [python/aletheia/dbc_converter.py:47,99] Mixed `'utf-8'` / `"utf-8"` quotes within file
- `[ ]` PY-A-28.5 [python/benchmarks/stability.py:38-40 vs throughput.py:21-25] sys.path injection asymmetric across benchmarks

#### Cat 32: Doctest validity
- `[ ]` PY-A-32.1 No `>>>` doctests in `aletheia/`; coverage via markdown-docs harness only
- `[ ]` PY-A-32.2 [python/aletheia/checks.py:7-15,274-277] Docstring examples lack `>>>` markers

#### Cat 33: CLI quality
- `[ ]` PY-A-33.4 [python/aletheia/cli.py:887,907] `--dbc` and `--excel` not in `add_mutually_exclusive_group`
- `[ ]` PY-A-33.5 [python/aletheia/cli.py:891-896] `format-dbc` lacks `--json` flag asymmetric with peers
- `[ ]` PY-A-33.7 [python/benchmarks/{stability,throughput,violations}.py] argparse vs env-var inconsistent across benchmarks

### Python Agent B — Correctness (36 findings)

#### Cat 7: Type safety
- `[ ]` PY-B-7.1 [python/aletheia/client/_helpers.py:92,111] `cast("list[dict[str, object]]", ...)` unverified casts on untrusted input
- `[ ]` PY-B-7.2 [python/aletheia/client/_response_parsers.py:241] `cast(list[dict[str, object]], results_raw)` not element-narrowed
- `[ ]` PY-B-7.3 [python/aletheia/client/_signal_ops.py:124] `cast(str, error_msg)` after `dict.get` without `isinstance` check
- `[ ]` PY-B-7.4 [python/aletheia/client/_enrichment.py:38-83] Repeated cast in `_walk_formula`/`_format_formula_inner` rely on caller invariants
- `[ ]` PY-B-7.5 [python/aletheia/client/_helpers.py:298] `_normalize_signal_group` contract self-consistent but undocumented vs `_normalize_optional_list`

#### Cat 8: Serialization
- `[ ]` PY-B-8.1 [python/aletheia/client/_helpers.py:43-61] `FractionJSONEncoder.default` doesn't handle Decimal/datetime
- `[ ]` PY-B-8.2 [python/aletheia/client/_helpers.py:64-66] `dump_json` doesn't pin `ensure_ascii`; cross-binding wire-byte parity risk
- `[ ]` PY-B-8.3 [python/aletheia/client/_response_parsers.py:118] `cast(list[ValidationIssue],...)` precedes severity validation; ordering OK but should follow

#### Cat 9: Parsing
- `[ ]` PY-B-9.2 [python/aletheia/client/_client_bin.py:118,140,164] `idx >= len(names)` masks index-OOB as synthetic name; should LogEvent
- `[ ]` PY-B-9.3 [python/aletheia/client/_helpers.py:262-273] `parse_rational` bare `except (ValueError, ZeroDivisionError): pass` — chain with `from exc`
- `[ ]` PY-B-9.4 [python/aletheia/client/_helpers.py:243 vs :209-211] `extract_rational_from_dict` doesn't reject bool numerators (asymmetric with `parse_rational`)
- `[ ]` PY-B-9.5 [python/aletheia/can_log.py:160] `bytearray(data[:dlc])` silently truncates; should LogEvent.warning

#### Cat 10: FFI
- `[ ]` PY-B-10.1 [python/aletheia/client/_ffi.py:88-93] `RTSState.acquire` warning fires after refcount=0 reuse; document
- `[ ]` PY-B-10.2 [python/aletheia/client/_ffi.py:96-101] `cls.lib` never cleared; stale-handle latent
- `[ ]` PY-B-10.3 [python/aletheia/client/_client.py:600,749] Per-frame `ctypes.c_uint8 * len(data))(*data)` allocation on streaming hot path
- `[ ]` PY-B-10.5 [python/aletheia/client/_ffi.py:233-249] `ALETHEIA_LIB` symlink-following gap; use `os.lstat` and reject symlinks

#### Cat 11: Tests
- `[ ]` PY-B-11.1 [python/tests/test_excel_loader.py:39-748] 30+ `# type: ignore[union-attr]` on `wb.active`; helper would close all
- `[ ]` PY-B-11.2 [python/tests/test_cancellation.py:50,302,303] 3 `# type: ignore` on async batch typing — narrow annotations
- `[ ]` PY-B-11.3 [python/tests/test_checks.py:226-241] `# type: ignore[operator]` on `not in d`; switch to `.get(...) is None`
- `[ ]` PY-B-11.4 [python/tests/test_cli.py:493-494] `# pylint: disable=import-outside-toplevel` — switch to `from aletheia.testing import run_checks`

#### Cat 12: Concurrency
- `[ ]` PY-B-12.1 [python/aletheia/asyncio/_client.py:107-109] `close()` not `asyncio.shield`'d; cancellation mid-close leaks RTS state
- `[ ]` PY-B-12.2 [python/aletheia/asyncio/_client.py:94] `__aenter__` similarly unshielded
- `[ ]` PY-B-12.3 [python/aletheia/asyncio/_client.py:188-194] `send_frames` partial-prefix semantics — clarify in docstring

#### Cat 13: Mutability
- `[ ]` PY-B-13.1 [python/aletheia/client/_types.py:222-244] `MappingProxyType(values)` no defensive `dict(values)` copy first

#### Cat 14: Hot-path perf
- `[ ]` PY-B-14.1 [python/aletheia/client/_log.py:106-116 + _client.py:621-625, 640-643] `log_event` short-circuits, but kwargs eval pre-call still allocates `**fields` dict
- `[ ]` PY-B-14.2 [python/aletheia/client/_client.py:563-564,620] `(_ACK_BYTES, _ACK_BYTES_SPACED)` tuple built per frame; hoist to class const

#### Cat 23: Security
- `[ ]` PY-B-23.1 (= PY-B-10.5) Symlink gap on ALETHEIA_LIB
- `[ ]` PY-B-23.2 [python/aletheia/client/_ffi.py:269-272] `cabal_dir.rglob(...)` first-match nondeterministic
- `[ ]` PY-B-23.4 [python/aletheia/excel_loader.py:201,251] No ZIP-bomb protection; cap is on outer file size only
- `[ ]` PY-B-23.5 [python/aletheia/yaml_loader.py:163] `len(source.encode("utf-8"))` allocates pre-check; use `len(source) * 4` upper bound

#### Cat 24: Exception chaining
- `[ ]` PY-B-24.1 (= PY-B-9.3) `from exc` missing in parse_rational

#### Cat 25: Stability
- `[ ]` PY-B-25.1 [python/aletheia/client/_client.py:519-525] `MAX_EXTRACT_CACHE = 256` first-256-win; no LRU; long stream degrades
- `[ ]` PY-B-25.2 [python/aletheia/client/_client.py:848] `last_frames.clear()` not in `close()`; minor leak window

#### Cat 26: Determinism
No findings.

#### Cat 29: Test access via interface/DI
- `[ ]` PY-B-29.2 (= PY-B-11.4) `aletheia.testing.run_checks` exists; tests should use it
- `[ ]` PY-B-29.3 [python/aletheia/asyncio/testing.py:42] `from ..client._client import AletheiaClient as _SyncClient` — should reach public

#### Cat 30: Mutation testing
- `[ ]` PY-B-30.1 mutmut survivors archive at `benchmarks/mutation/<short-sha>/python.raw.txt`; `_ACK_BYTES_SPACED` byte-equivalence not asserted

#### Cat 34: Dynamic correctness
- `[ ]` PY-B-34.3 [python/aletheia/client/_helpers.py:262-273 + tests/test_property_hypothesis.py] String-form `parse_rational` malformed-input property gap

### Docs Agent A — Hygiene (40 findings)

#### Cat 1: Accuracy
- `[ ]` DOC-A-1.1 [PROJECT_STATUS.md:489] "All 244 Agda modules use `--safe --without-K`" contradicts L450 (246); live count 246
- `[ ]` DOC-A-1.2 [PROJECT_STATUS.md:506-509] Phase 6 candidate list says `convert` (doesn't exist); missing `format-dbc`/`signals`/`check`
- `[ ]` DOC-A-1.3 [docs/reference/CLI.md:13] "Five subcommands" — actual is six (missing `format-dbc`)
- `[ ]` DOC-A-1.4 [docs/INDEX.md:33] Same omission of `format-dbc`
- `[ ]` DOC-A-1.5 [docs/reference/INTERFACES.md:38] `aletheia::check::signal(...)` lowercase — actual is `aletheia::Check::signal(...)`
- `[ ]` DOC-A-1.6 [docs/development/RELEASE.md:199] "21 steps, ~18 min" — actual `BASE_STEPS = 27`
- `[ ]` DOC-A-1.7 [python/README.md:35] 4-tuple `iter_can_log` unpack vs current 5-tuple (R18 cluster 11 fix didn't reach this README)
- `[ ]` DOC-A-1.8 [docs/development/BENCHMARKS.md:54] `_run_checks` private name; promoted to `aletheia.testing.run_checks`
- `[ ]` DOC-A-1.9 [docs/development/CI_LOCAL.md:218,248 vs L18,27-28] "17 steps, 12-15 min" vs "27 always-on steps, ~17-22 min" — same file
- `[ ]` DOC-A-1.10 [docs/development/CI_LOCAL.md:145] References `tools/run-ci.sh` which doesn't exist (migrated to Python)

#### Cat 2: Staleness
- `[ ]` DOC-A-2.1 [docs/PITCH.md:4] "Last Updated: 2026-04-15" — 25 days stale
- `[ ]` DOC-A-2.2 [python/README.md] No version marker; mtime 3 Apr 2026, 5 weeks of API changes since
- `[ ]` DOC-A-2.3 [docs/development/RELEASE.md:199] `21 steps, ~18 min` orphaned across two `run_ci.py` expansions
- `[ ]` DOC-A-2.4 [docs/operations/RUNBOOK.md, STABILITY.md, architecture/*.md, reference/*.md, guides/*.md, development/*.md] None carry "Last Updated"; PITCH sets pattern but isn't followed
- `[ ]` DOC-A-2.5 [docs/architecture/DESIGN.md:13,17,71] Phase 1→2/2A/2B references; reads as last refreshed during Phase 2/3

#### Cat 3: Consistency
- `[ ]` DOC-A-3.1 [CHANGELOG.md:27,34,37,39,41,43] CHANGELOG names `DbcDefinition`/`DbcSignal` (CamelCase); Python is `DBCDefinition`/`DBCSignal` (all-caps); cross-binding asymmetry
- `[ ]` DOC-A-3.2 [docs/reference/INTERFACES.md:599] `DBCDefinition` (all-caps) vs L112 `DbcDefinition` — internal inconsistency
- `[ ]` DOC-A-3.3 [docs/reference/INTERFACES.md:38 vs :55] `aletheia::check::signal` vs `Check::signal` same row
- `[ ]` DOC-A-3.4 [docs/development/CI_LOCAL.md] "27 always-on" vs "17-step" — same file, different numbers
- `[ ]` DOC-A-3.5 [docs/development/RELEASE.md:199 vs CI_LOCAL.md:18] "21 steps" vs "27 steps" cross-file
- `[ ]` DOC-A-3.6 (= DOC-A-1.1) Same-file 246-vs-244

#### Cat 4: Completeness
- `[ ]` DOC-A-4.1 [docs/INDEX.md] No reference to `CHANGELOG.md`
- `[ ]` DOC-A-4.2 [docs/INDEX.md] No reference to `docs/architecture/CANCELLATION.md`
- `[ ]` DOC-A-4.3 [docs/INDEX.md] No reference to `docs/architecture/CGO_NOTES.md`
- `[ ]` DOC-A-4.4 [docs/INDEX.md] No reference to `docs/development/CI_LOCAL.md`
- `[ ]` DOC-A-4.5 [docs/INDEX.md] No reference to `docs/development/RELEASE.md`
- `[ ]` DOC-A-4.6 [docs/INDEX.md] No reference to `docs/operations/MUTATION.md`
- `[ ]` DOC-A-4.7 [docs/INDEX.md] No reference to `docs/development/PARITY_PLAN.md`
- `[ ]` DOC-A-4.8 [docs/INDEX.md:96-143] Documentation Map tree omits the above 6+ docs
- `[ ]` DOC-A-4.9 [docs/reference/] No `GO_API.md` or `CPP_API.md`; PYTHON_API.md exists. Cross-binding asymmetry

#### Cat 5: Redundancy / single-source
- `[ ]` DOC-A-5.1 [PROJECT_STATUS.md:450 / :489] Module count 246/244 same file
- `[ ]` DOC-A-5.3 [docs/development/RELEASE.md:199 vs CI_LOCAL.md:18,218,248] Step count stated 4× with 3 different values; canonical lives in `tools/run_ci.py:235`
- `[ ]` DOC-A-5.4 [docs/PITCH.md:237 / QUICKSTART.md:9 / BUILDING.md:7] Toolchain pin loose (Python "3.12+" vs "3.13"); QUICKSTART vs BUILDING
- `[ ]` DOC-A-5.5 [docs/PITCH.md:298 / docs/reference/CLI.md:13 / docs/INDEX.md:33] CLI subcommand list 3× three different values

#### Cat 6: Commands
- `[ ]` DOC-A-6.1 [docs/guides/QUICKSTART.md:51-53,61-72] References `vehicle.dbc` (only at `examples/demo/`) and `drive.blf` (doesn't exist)
- `[ ]` DOC-A-6.2 [python/README.md:30-41] `can_trace` undefined in narrative example
- `[ ]` DOC-A-6.3 [docs/development/RELEASE.md:50-54] `tools/check_reproducible_build.py` invocation lacks repo-root resolution signal

#### Cat 7: Links
- `[ ]` DOC-A-7.1 [docs/PITCH.md:237] `[Building Guide § Prerequisites](../development/BUILDING.md#prerequisites)` — `..` resolves wrong
- `[ ]` DOC-A-7.2 [CLAUDE.md & docs/development/PARITY_PLAN.md] `memory/...` references; `memory/` doesn't exist in repo (lives in `~/.claude/projects/`); unresolvable for human readers

#### Cat 8: Audience
- `[ ]` DOC-A-8.1 [python/README.md:1-54] Audience scope unclear; near-duplicate Quick Start conflicts with `docs/guides/QUICKSTART.md`
- `[ ]` DOC-A-8.2 [docs/PITCH.md:140-205] "For Engineers" / "For Engineering Managers" persona switching distracts code-heavy reader

#### Cat 9: Precision
- `[ ]` DOC-A-9.1 [README.md:14] "Robust DBC Parsing" vague — replace with corpus stat
- `[ ]` DOC-A-9.2 [docs/PITCH.md:53] "real-world tested" unquantified
- `[ ]` DOC-A-9.3 [docs/PITCH.md:51] "gigabyte-scale" hand-wave; concrete "1M frames" or "8 GB BLF" preferred
- `[ ]` DOC-A-9.4 [docs/PITCH.md:316,318] "Real-world tested" vague
- `[ ]` DOC-A-9.5 [docs/architecture/DESIGN.md:71] "large CAN traces with O(1) memory" — "large" unbounded; cite 1.08× / 100× verified claim
- `[ ]` DOC-A-9.6 [docs/PITCH.md:184-197] Streaming workflow shows 8200-frame example; no scaling claim

### Docs Agent B — Deep (40 findings)

#### Cat 10: Structure
- `[ ]` DOC-B-10.1 [PROJECT_STATUS.md] 526 LOC monolithic; >25k token cap on Read
- `[ ]` DOC-B-10.2 [docs/architecture/PROTOCOL.md] 1209 LOC, no top-of-file TOC
- `[ ]` DOC-B-10.3 [AGENTS.md] 793 LOC, no TOC
- `[ ]` DOC-B-10.4 [CHANGELOG.md] 691 LOC for single Unreleased block; sub-TOC needed
- `[ ]` DOC-B-10.5 [docs/INDEX.md] Missing 8+ files in Documentation Map (cf. Cat 4 findings above)

#### Cat 11: Examples
- `[ ]` DOC-B-11.1 [docs/guides/COOKBOOK.md] 518 LOC Python-only fences; INTERFACES.md has Python+C+Go — cross-binding gap
- `[ ]` DOC-B-11.2 [docs/PITCH.md:42-46] Cross-binding API examples: Python `220`, C++ `PhysicalValue{Rational{220, 1}}`, Go `220` — verbose C++ unexplained

#### Cat 12: Rationale
- `[ ]` DOC-B-12.1 [docs/operations/MUTATION.md:4,55-58] "go-mutesting" mentioned twice; actual is `gremlins` — top of doc should state substitution
- `[ ]` DOC-B-12.2 [docs/architecture/DESIGN.md:67] One-sentence "why dual-protocol JSON+binary"; expand
- `[ ]` DOC-B-12.3 [docs/operations/RUNBOOK.md:216] `MAX_EXTRACT_CACHE = 256` cap — no rationale paragraph

#### Cat 13: Onboarding
- `[ ]` DOC-B-13.1 [docs/guides/QUICKSTART.md:9 vs BUILDING.md] Python ≥ 3.12 vs Python 3.13 — uniformity gap
- `[ ]` DOC-B-13.2 [README.md:156-167] "Getting Started" lists QUICKSTART → BUILDING; omits TUTORIAL despite INDEX.md saying TUTORIAL is the "start here" entry
- `[ ]` DOC-B-13.3 No onboarding doc for C++ or Go users; Python-first chain
- `[ ]` DOC-B-13.4 No top-level `cpp/README.md` or `go/README.md`; Python has 53 LOC `python/README.md`

#### Cat 14: Durability
- `[ ]` DOC-B-14.1 [docs/PITCH.md:4] Last Updated 2026-04-15 — 25 days stale
- `[ ]` DOC-B-14.2 [DEFERRALS.md:5] Last Updated 2026-04-14 (R10); R11-R19 absent
- `[ ]` DOC-B-14.3 [DEPENDENCIES.md:3] Last Updated 2026-04-19 — R18 added gremlins/mull-19/mutmut/actionlint/act unreflected
- `[ ]` DOC-B-14.4 [docs/development/BUILDING.md:11-12] References "Last Updated stamp at top" but BUILDING.md lacks one
- `[ ]` DOC-B-14.5 [PROJECT_STATUS.md:468] Benchmark date 2026-04-06 — 5 weeks old

#### Cat 15: Testability
- `[ ]` DOC-B-15.1 [docs/operations/MUTATION.md:4] Tool name drift "go-mutesting"; extend `tools/check_runbook_coverage.py`-style mechanical gate
- `[ ]` DOC-B-15.2 [docs/PITCH.md:42-46] Verify PITCH.md is in C++/Go doc-example harness `docFiles` lists
- `[ ]` DOC-B-15.3 [docs/architecture/DESIGN.md:53] "All production modules `--safe --without-K`" — claim verified by `check-invariants` but `Substrate.Unsafe` exception not surfaced inline
- `[ ]` DOC-B-15.4 [docs/operations/RUNBOOK.md:37-42] "Binding parity tests enforce this" — what specifically fails not surfaced

#### Cat 16: Qualifiers
- `[ ]` DOC-B-16.1 [docs/development/PARITY_PLAN.md:41] "currently-shipped capabilities (~15 rows)" — actual 34 rows
- `[ ]` DOC-B-16.2 [docs/development/PARITY_PLAN.md:67] "the Agda core does not currently carry" — post-B.1.x, time-anchor needed
- `[ ]` DOC-B-16.3 [docs/architecture/DESIGN.md:63] "currently enforced by runtime checks" — timestamp or remove hedge

#### Cat 17: Internal consistency
- `[ ]` DOC-B-17.1 [PROJECT_STATUS.md:450 vs :489] 246 vs 244 same file — canonical worked example per AGENTS.md L785
- `[ ]` DOC-B-17.2 [PROJECT_STATUS.md:401] Self-contradictory arithmetic in same paragraph
- `[ ]` DOC-B-17.3 [CHANGELOG.md:1-3 vs PROJECT_STATUS.md] Two SSOTs — UR-1 says CHANGELOG canonical; AGENTS says PROJECT_STATUS canonical

#### Cat 18: Scope labels
- `[ ]` DOC-B-18.1 [PROJECT_STATUS.md:450] LOC totals "(source only)" ambiguous — excludes tests? benchmarks? generated?
- `[ ]` DOC-B-18.2 [PROJECT_STATUS.md:460] "Total: 1263 tests" — does it include 103 doc-example markdown-docs? Sub-totals don't add

#### Cat 19: Missing content
- `[ ]` DOC-B-19.1 No FAQ document
- `[ ]` DOC-B-19.2 No `MIGRATION-2.0.md` despite breaking changes (Go ctx-first / C++ stop_token-first)
- `[ ]` DOC-B-19.3 [docs/operations/RUNBOOK.md] No performance-troubleshooting section
- `[ ]` DOC-B-19.4 No `cpp/README.md`, `go/README.md` — Python has one
- `[ ]` DOC-B-19.5 [CONTRIBUTING.md] No "Where to file bugs" / issue templates / commit-message conventions / branch-naming

#### Cat 20: Numerical correctness
- `[ ]` DOC-B-20.1 (= DOC-B-17.1) 244 vs 246
- `[ ]` DOC-B-20.2 [PROJECT_STATUS.md:451] "22 Python modules (13+9)" — verify via `find python/aletheia -name '*.py'`
- `[ ]` DOC-B-20.3 [PROJECT_STATUS.md:457] "34 rows" matrix; PARITY_PLAN.md L41 says "~15 rows"
- `[ ]` DOC-B-20.4 [docs/development/PARITY_PLAN.md:41] "~15 rows" vs PROJECT_STATUS L457 "34 rows" — mathematical inconsistency

#### Cat 21: Cross-language parity
- `[ ]` DOC-B-21.1 [python/README.md vs go/, cpp/] No equivalent at binding root for Go/C++ — asymmetric
- `[ ]` DOC-B-21.2 [docs/guides/COOKBOOK.md] Python-only; Track D harness covers all 3 — should mirror or label "Python only"
- `[ ]` DOC-B-21.3 [docs/PITCH.md:41-47] Cross-binding fence: C++ verbose `Rational{220, 1}` unexplained vs Python `220`

#### Cat 22: Operational runbook
- `[ ]` DOC-B-22.2 [docs/operations/RUNBOOK.md] No performance-troubleshooting / WSL2-noise-vs-real-regression entry; on-call would search RUNBOOK first
- `[ ]` DOC-B-22.3 [docs/operations/RUNBOOK.md:562-569] gate-failure mode for `tools/check_runbook_coverage.py` not documented

### CI/CD Agent (6 findings)

#### Cat 1: Workflow YAML hygiene
- `[ ]` CICD-1.6 [.github/workflows/gha-checks.yml:24,44,54] `runs-on: ubuntu-latest` violates AGENTS.md L732 (must be `ubuntu-22.04`)
- `[ ]` CICD-1.7 [.github/workflows/gha-checks.yml:34-36] `actionlint` tarball fetched without sha256 verify before extract+execute
- `[ ]` CICD-1.8 [.github/workflows/gha-checks.yml:22-60] No `timeout-minutes:` on any of 3 jobs; upstream curl/DNS hang pins runner
- `[ ]` CICD-1.9 [.github/workflows/gha-checks.yml:13-16] No `concurrency:` group; near-simultaneous pushes spawn duplicate runs

#### Cat 2: Cache discipline
- `[ ]` CICD-2.2 [Dockerfile.runtime:23-25] `apt-get install libgmp10` unpinned; breaks UR-3 reproducibility for docker artifact (only python:3.13-slim base layer is digest-pinned)

#### Cat 3-4: Permission scoping / Build isolation
No findings.

#### Cat 5: Artifact and release
- `[ ]` CICD-5.8 [docs/development/RELEASE.md:199] "21 steps, ~18 min" vs actual `BASE_STEPS = 27`
- `[ ]` CICD-5.9 [keys/README.md:13-15, docs/development/RELEASE.md:137-139] Cosign binary fetched via curl + chmod +x, no sha256 verify before execution; tool-of-trust unverified-fetch (same pattern at CI_LOCAL.md:118 for Mull-19 deb)

---

## Step 2 findings

### Agda Agent D — system-level (25 findings)

#### Cat 10: Domain model fidelity
- `[ ]` AGDA-D-10.1 [src/Aletheia/Trace/CANTrace.agda:42-43 + haskell-shim/src/AletheiaFFI.hs:78-95] CAN-FD BRS/ESI bits modeled as `Maybe Bool` in `TimedFrame` but binary FFI `aletheia_send_frame` HARDCODES both to `nothing` (line 95); no binding has BRS/ESI symbols. ISO 11898-1:2015 §10.4.2 (BRS) / §10.4.3 (ESI) silently dropped
- `[ ]` AGDA-D-10.2 [src/Aletheia/Trace/CANTrace.agda:69-72 vs ISO 11898-1:2015 §10.6] `TraceEvent.Error` carries only `Timestamp μs`; no error-passive vs error-active node state, no transmit/receive error counters
- `[ ]` AGDA-D-10.3 [src/Aletheia/Trace/CANTrace.agda:69-72] No constructor for overload frames or single-shot transmission fail events per CAN 2.0B §3.1.5

#### Cat 11: Invariant sufficiency
- `[ ]` AGDA-D-11.1 [src/Aletheia/Limits.agda] 9 of 11 declared bound constants never consumed by Agda code; documented as authoritative but not enforced inside the verified core (defense-in-depth gap)
- `[ ]` AGDA-D-11.2 [src/Aletheia/Protocol/JSON/Parse.agda:198-261] `parseJSONHelper` invoked with `length input` as fuel — bound is `max-json-bytes` not `max-nesting-depth = 64`; depth-bound never enforced
- `[ ]` AGDA-D-11.3 [src/Aletheia/DBC/JSONParser.agda:195-202, 290-296, 361] `parseObjectList`/`parseSignalList`/`parseMessageList` recurse without cardinality guards
- `[ ]` AGDA-D-11.4 [src/Aletheia/DBC/Identifier.agda:84-88] `Identifier.valid` enforces grammar but NOT length — 64 MiB-long valid identifier admitted
- `[ ]` AGDA-D-11.5 [src/Aletheia/LTL/JSON.agda:213] `parseProperty` no atom-count cap; `streaming-warms-cache` cost ∝ `length atoms × length σ`
- `[ ]` AGDA-D-11.6 [src/Aletheia/Protocol/StreamState/Types.agda Streaming ctor] `props : List PropertyState` no cardinality bound on protocol state
- `[ ]` AGDA-D-11.7 [src/Aletheia/Limits.agda:138-143] `withinBound` defined unused; returns `Bool` not refined-witness; SSOT-without-enforcement

#### Cat 12: Property completeness
- `[ ]` AGDA-D-12.1 [src/Aletheia/Trace/CANTrace.agda:36-44 + haskell-shim FFI] `TimedFrame.dlcValid` is `.()`-irrelevant + erased; FFI enforces empirically via `validateDLCAndLen`; no `WellFormedTimedFrame` propositional lemma
- `[ ]` AGDA-D-12.2 [src/Aletheia/Protocol/Adequacy/StreamingWarm.agda:359-368 + Main.agda:46] `AllObserved` user obligation not propagated to bindings; bindings have no `AllObserved`-style helper
- `[ ]` AGDA-D-12.3 [src/Aletheia/Trace/CANTrace.agda:93-96] No theorem stating `checkMonotonic` ENFORCED on every frame implies `Monotonic` on cumulative sequence into metric-LTL
- `[ ]` AGDA-D-12.4 [src/Aletheia/CAN/DLC.agda:21-32] No `dlcToBytes-image-bounded : ∀ d → dlcBytes d ≤ 64` theorem matching binding-side `MaxFrameByteCount = 64`

#### Cat 13: Assumption audit
- `[ ]` AGDA-D-13.1 (= AGDA-D-10.1) BRS/ESI hardcoding is unchecked coercion at FFI
- `[ ]` AGDA-D-13.2 [src/Aletheia/LTL/Semantics/MTL.agda:93-111] `met-*-go` uses `_∸_` truncated subtraction; relies on upstream `checkMonotonic` defensively
- `[ ]` AGDA-D-13.3 [haskell-shim/AletheiaFFI/Marshal.hs:70-84 vs BinaryOutput.hs:81-82] Stdlib bump renaming `denominator-1` → `denominator` would break input side without touching output (asymmetric path)
- `[~]` AGDA-D-13.4 [src/Aletheia/Protocol/JSON/Parse.agda:198-200] PHASE 2a + 2b SHIPPED 2026-05-11 (NestingDepth `8a81786` + AtomCount typed wire-errors at handler boundary + structured payload + cross-binding lifting); phase 2c (`IdentifierLength`, parser-monad rewrite) still pending — Fuel measure correct for termination but leaves nesting effectively unbounded
- `[ ]` AGDA-D-13.5 [src/Aletheia/Main.agda:34-50 adequacy comment] Implicit assumption "callers know which atoms are LTL-relevant"; no programmatic introspection in bindings

#### Cat 14: API surface
- `[ ]` AGDA-D-14.1 [src/Aletheia/Main.agda:89] `checkMonotonic` re-exported but unused in any binding code
- `[x]` AGDA-D-14.2 [src/Aletheia/Limits.agda:64-71] CLOSED 2026-05-11 via AGDA-D-13.4 phase 2a (`boundKindCode` is now consumed by `Protocol/ResponseFormat.errorExtras` to serialize the structured wire payload)
- `[ ]` AGDA-D-14.3 [src/Aletheia/Main.agda:131-147] Re-exports `Byte`, `bytesToDlc`, `maxDLC-2B`, `maxDLC-FD` — unused by FFI shim or any binding
- `[ ]` AGDA-D-14.4 [src/Aletheia/Main.agda:159-164] `TimeUnit; μs` exported alongside unused `ns/ms/s`; binding side hardcodes μs

#### Cat 15: Module structure
- `[ ]` AGDA-D-15.1 [src/Aletheia/DBC/Validator/Checks.agda 595 LOC] CHECK 17 sandwiched between 5 and 6; concern-mixing (predicates + formatter + IssueCode); split into `Checks/{Identity,Cardinality,Reference,Range}.agda`
- `[ ]` AGDA-D-15.2 [src/Aletheia/Protocol/StreamState/Internals.agda 255 LOC + 130-line in-source DEFER block] Mixes runtime helpers + indexing + proof exports; in-source DEFER consider `Internals/IndexingNotes.agda`
- `[ ]` AGDA-D-15.3 [src/Aletheia/Protocol/Adequacy/StreamingWarm.agda 367 LOC] Headline theorem co-located with helper definitions — split into `Adequacy/Observation.agda` + thin `Adequacy/StreamingWarm.agda`

#### Cat 17: Cross-layer
- `[ ]` AGDA-D-17.1 [haskell-shim/AletheiaFFI.hs:81-96] Binary FFI signature has NO BRS/ESI; either extend C signature or remove fields from `TimedFrame`
- `[ ]` AGDA-D-17.2 [haskell-shim/AletheiaFFI.hs:53,151,218 + Marshal.hs:67,92-93 + BinaryOutput.hs:36-57] 11 `unsafeCoerce` sites; `check-erasure` covers Vec/Sum/CANId/Timestamp but NOT Maybe (`AgdaMaybe.C_nothing_18`/`C_just_16`) or Sigma (`AgdaSigma.T_Σ_14`/`d_fst_28`/`d_snd_30`)
- `[ ]` AGDA-D-17.3 [haskell-shim/AletheiaFFI/Marshal.hs:81-84] `mkAgdaRational` bypasses stdlib smart ctor; loses witness if stdlib moves coprimality from compile-time field to runtime lemma
- `[ ]` AGDA-D-17.4 [bindings vs Main.agda:34-50] `AllObserved` user obligation has 0 references in python/go/cpp; bindings haven't propagated

#### Cat 30: MAlonzo export surface
- `[ ]` AGDA-D-30.1 (= AGDA-D-17.2) `check-erasure` Maybe/Sigma gap
- `[ ]` AGDA-D-30.2 [haskell-shim/ffi-exports.snapshot] Snapshot covers 11 entries; doesn't cover indirect helper accessors (`d_dlcToBytes_6`, `d_numerator_14`, etc.); drift detectable only via end-to-end check-fidelity

#### Cat 31: Stdlib version pinning
No findings. `aletheia.agda-lib:2` pins `standard-library-2.3`.

#### Cat 32: Parser resource bounds
No NEW findings beyond cat 11 reframing per advisor.

#### Guidelines G-A7/A11/A19/A23
- `[ ]` AGDA-D-GA7.1 (= AGDA-D-12.2) `AllObserved` doc-propagation gap
- `[ ]` AGDA-D-GA11.1 (= AGDA-D-11.4) `Identifier.valid` length missing
- `[ ]` AGDA-D-GA17.1 (cross-listed AGDA-C-6.2) `InputBoundExceeded` duplicated 3 ADTs
- `[ ]` AGDA-D-GA19.1 [haskell-shim/AletheiaFFI/BinaryOutput.hs:53-71] Wire format uses host-native byte order; cross-host parity nominal but undocumented
- `[ ]` AGDA-D-GA19.2 [haskell-shim/AletheiaFFI/BinaryOutput.hs:81-84] Numerator `Integer` cast to `Int64` silently wraps for VAL_TABLE_ rationals exceeding `Int64.MaxValue`
- `[ ]` AGDA-D-GA23.1 (= AGDA-D-10.1/13.1/17.1) BRS/ESI wire-boundary audit not applied
- `[ ]` AGDA-D-GA23.2 (= AGDA-D-30.1) Maybe/Sigma constructor wire boundary not in check-erasure

### Go system-level (22 findings)

#### Cat 15: API ergonomics
- `[ ]` GO-D-15.1 [go/aletheia/client.go:88-101] `Client.Close()` return type lies — always returns nil
- `[ ]` GO-D-15.2 [go/aletheia/client.go:733-743 + 13 LogAttrs sites] `context.Background()` discards caller's ctx
- `[ ]` GO-D-15.3 [go/aletheia/types.go:231 vs dbc.go:234,351] `ByteOrder/IssueSeverity/Verdict` have `String()`; `DbcVarType/DbcAttrScope` don't (Stringer asymmetric)
- `[ ]` GO-D-15.4 [go/aletheia/client.go: BuildFrame vs UpdateFrame vs SendFrame] inconsistent (ctx, id, dlc, …) ordering across siblings
- `[ ]` GO-D-15.5 [go/aletheia/client.go:325-340] `FormatDBC` returns `*DbcDefinition` but `ParseDBC*` return `*ParsedDBC` (with warnings); asymmetric

#### Cat 16: Boundaries
- `[ ]` GO-D-16.1 [go/aletheia/ffi.go:139-147 vs ffi_nocgo.go] `StablePtrCount() int64` only in cgo build; `go/benchmarks/stability/main.go:136` uses unconditionally — `CGO_ENABLED=0` build breaks
- `[ ]` GO-D-16.2 [go/aletheia/client.go:43-56] No `IsClosed()` predicate (Python ships `is_closed` for harnesses)
- `[ ]` GO-D-16.3 [go/aletheia/dbc.go:564-577] `DbcDefinition` mixes public fields with private `nameIndex/idIndex` populated only by `NewDbcDefinition`; literal-built struct silently O(N) scans

#### Cat 17: Extensibility
- `[ ]` GO-D-17.1 [go/aletheia/backend.go:33-72] `Backend` sealed; observability shims blocked; document rationale
- `[ ]` GO-D-17.2 [go/aletheia/backend.go:7-28] No `WithLibraryPath` / `WithDLClose` test option

#### Cat 18: Dependency discipline
- `[ ]` GO-D-18.1 [go/go.work:23-30 + excel/go.mod] `v0.0.0` placeholder requires manual rewrite at release; no static gate
- `[ ]` GO-D-18.2 [go/excel/go.mod:23] No `go mod verify` / `osv-scanner` lane

#### Cat 19: Domain model fidelity
- `[ ]` GO-D-19.1 [go/aletheia/dbc.go:259-282] `DbcRawValueDesc.SignalName` is plain `string`; everywhere else `SignalName` typed alias
- `[ ]` GO-D-19.2 [go/aletheia/dbc.go:319-340] `DbcCommentTargetMessage/Signal.ID uint32 + Extended bool` leaks wire discriminator; `CanID` sealed interface elsewhere
- `[ ]` GO-D-19.3 [go/aletheia/types.go:46-53] `Timestamp.Microseconds int64` accepts negative; field exposed; no `NewTimestamp` constructor

#### Cat 20: Design coherence
- `[ ]` GO-D-20.1 [go/aletheia/json.go:1094] `maxFormulaDepth = 100` belongs in `limits.go` next to `MaxNestingDepth = 64`
- `[ ]` GO-D-20.2 [go/aletheia/yaml.go:38-83] `loadYAMLData` content-based dispatch (`os.Stat(source)` then file/inline); same path-confusion vector Python migrated away from in R19 cluster B
- `[ ]` GO-D-20.3 [go/aletheia/client.go:107-114, 88-101] `Close` blocks unbounded on `lockCh`; ctx-aware `Close(ctx)` overload candidate

#### Cat 21: Use-case coverage
- `[ ]` GO-D-21.1 [docs/FEATURE_MATRIX.yaml:392-400] `mock_backend` Go status implemented; align with Python/C++ if/when they flip to `aletheia/testing` namespace
- `[ ]` GO-D-21.2 [docs/FEATURE_MATRIX.yaml:457-470] `can_log_reader` Go planned; Phase 6 architecture should be Agda kernel + Go thin client per `feedback_parsers_are_agda_with_proof.md`

#### Cat 22: Cross-layer alignment
- `[ ]` GO-D-22.1 [go/aletheia/ffi.go:222-304] No gate that Go-side `loadSym` symbol list matches `ffi-exports.snapshot`
- `[ ]` GO-D-22.2 [go/aletheia/yaml.go:39-44, 63-68, 77-82] `InputBoundExceededError` constructions in yaml.go don't set `.Code`; cross-binding parity loss
- `[ ]` GO-D-22.3 [go/aletheia/json.go:266-276] `serializeDBC` defense-in-depth marshals JSON twice (probe + caller's); doubled cost on every parse/validate/format

#### Cat 31: Build tag / module hygiene
- `[ ]` GO-D-31.1 [go/aletheia/ffi_nocgo.go:1] Filename misleading — `ffi_nocgo.go` chosen on `cgo && darwin/windows` too; rename `ffi_unsupported.go` or `ffi_stub.go`
- `[ ]` GO-D-31.2 (= GO-D-16.1) Stability harness lacks build tag for cgo-only symbol use

#### Cat 32: Determinism
- `[ ]` GO-D-32.3 [go/aletheia/mock.go:103-121] Document `Inputs()` ordering across goroutines is non-deterministic

### C++ system-level (28 findings)

#### Cat 15: API ergonomics
- `[ ]` CPP-D-15.1 [cpp/include/aletheia/types.hpp:64-72] `Rational(n,d)` debug-only `assert`; sibling validated factories return `std::expected` — asymmetric
- `[ ]` CPP-D-15.2 [cpp/include/aletheia/types.hpp:64] `Rational` `struct` with public mutable fields; invariant maintained only by ctor not accessor
- `[ ]` CPP-D-15.3 [cpp/include/aletheia/types.hpp:189-201,145-159,161-175] Mixed error vocabularies (`std::expected<X, std::string>` factories vs `std::expected<X, AletheiaError>` downstream)
- `[ ]` CPP-D-15.4 [cpp/include/aletheia/aletheia.hpp + client.hpp] Two umbrella headers (full vs core+detail) for one boundary
- `[ ]` CPP-D-15.5 [cpp/include/aletheia/check.hpp:259-266] `Check::signal()`/`when()` static methods on no-state class — namespace function more idiomatic

#### Cat 16: Boundaries
- `[ ]` CPP-D-16.1 [cpp/include/aletheia/client.hpp:19] `<aletheia/detail/cache_keys.hpp>` public-installed despite IWYU pragma; pimpl candidate
- `[ ]` CPP-D-16.2 Two `aletheia::detail::` namespaces (public vs private); rename internal one to `aletheia::internal::`
- `[ ]` CPP-D-16.3 [cpp/include/aletheia/dbc.hpp:24-52] `LazyIndex` template public-installed but documented "implementation detail"
- `[ ]` CPP-D-16.4 [cpp/include/aletheia/aletheia.hpp:38-46] `aletheia/log.hpp` and `aletheia/limits.hpp` always-imported but independent vocabulary

#### Cat 17: Extensibility
- `[ ]` CPP-D-17.1 [cpp/include/aletheia/backend.hpp:42-110] `IBackend` mixes pure virtual + 11 default-implementations; new backend implementations can't tell mandatory vs optional
- `[ ]` CPP-D-17.2 [cpp/include/aletheia/backend.hpp:106] `rts_mismatch_info()` returns `std::optional<std::pair<int,int>>`; struct with named fields would extend better
- `[ ]` CPP-D-17.3 [cpp/include/aletheia/backend.hpp:113] `make_ffi_backend(int rts_cores = 1)` positional; no extension point for future tuning
- `[ ]` CPP-D-17.4 [cpp/include/aletheia/log.hpp:46-89] `Logger` single-callback; multi-sink composition pushed to caller

#### Cat 18: Dependency discipline
- `[ ]` CPP-D-18.1 [cpp/CMakeLists.txt:148-150 + tests:323,351] Tests reach into `cpp/src/detail/json.hpp` via `target_include_directories(... PRIVATE src)` — public/private boundary breach
- `[ ]` CPP-D-18.2 [cpp/CMakeLists.txt:175] OpenXLSX pinned to master commit; add tracking issue + date for re-pin re-evaluation
- `[ ]` CPP-D-18.3 [cpp/CMakeLists.txt:184-194] yaml-cpp 0.8.0 + `CMAKE_CXX_STANDARD 20` workaround block; bite-the-bullet candidate
- `[ ]` CPP-D-18.4 [cpp/CMakeLists.txt:153] `nlohmann/json` v3.11.3 (2023); 3.12.0 (2024) exists — flag for cadence

#### Cat 19: Domain model fidelity
- `[ ]` CPP-D-19.1 [cpp/include/aletheia/types.hpp:177] `using CanId = std::variant<...>;` requires `std::visit(...)` 12+ sites
- `[ ]` CPP-D-19.2 [cpp/include/aletheia/types.hpp:115-119] `PhysicalValue` is `Rational`; `Delta`/`Tolerance` are `double` — Python+Go use Rational for all 3 (cross-binding parity)
- `[ ]` CPP-D-19.3 [cpp/include/aletheia/dbc.hpp:103-130] `DbcMessage.senders` is `vector<string>` (raw); `.sender` is `NodeName` (typed)
- `[ ]` CPP-D-19.4 [cpp/include/aletheia/dbc.hpp:191-193] `DbcNode { std::string name; }` — bare string not `NodeName`

#### Cat 20: Design coherence
- `[ ]` CPP-D-20.1 [cpp/include/aletheia/client.hpp:50-55] `stop_token` cancellation contract per-method (1-poll vs N-poll) not documented at signatures
- `[ ]` CPP-D-20.2 [cpp/src/client.cpp:75-86, 101-124] `static_cast<void>(std::current_exception())` no-op; backend close failures silent — at least gate-log
- `[ ]` CPP-D-20.3 [cpp/src/client.cpp:417, 460, 595] `cache_.clear()` in `set_properties/start_stream/end_stream` but NOT in `parse_dbc/parse_dbc_text` — re-parse leaves stale cache keyed by old DBC's signals
- `[ ]` CPP-D-20.4 [cpp/src/ffi_backend.cpp:194-197] `~FfiBackend = default;` — `dlopen` handle leaks per process; document "one .so per process" invariant
- `[ ]` CPP-D-20.5 [cpp/include/aletheia/response.hpp:83-91] `verdict = Verdict::Fails` default; default to `Unresolved` or require explicit init

#### Cat 21: Use-case coverage
- `[ ]` CPP-D-21.1 No equivalent of Python `iter_can_log`/`load_can_log` (cross-binding feature gap)
- `[ ]` CPP-D-21.2 No equivalent of Python `send_frames_iter` (per-frame yielding) (cross-binding gap)
- `[ ]` CPP-D-21.3 [cpp/src/ffi_backend.cpp:220-230] `max_dbc_text_bytes` not enforced at parse_dbc_text entry; only `max_json_bytes` covers wrapped JSON
- `[ ]` CPP-D-21.4 [cpp/include/aletheia/limits.hpp:90-94] `to_aletheia_error()` referenced in comment but not implemented
- `[ ]` CPP-D-21.5 [cpp/src/ffi_backend.cpp:220-230] Bound-error response uses `code: parse_input_bound_exceeded` only; missing `bound_kind/observed/limit` structured fields (cross-binding asymmetry)

#### Cat 22: Cross-layer alignment
- `[ ]` CPP-D-22.1 [cpp/src/client.cpp:225-249] `parse_extraction_bin` no `static_assert(std::endian::native == std::endian::little)`
- `[ ]` CPP-D-22.2 [cpp/include/aletheia/limits.hpp:32-38 vs python/aletheia/limits.py:36 vs Aletheia.Limits.agda] Wire codes pinned by comment only; no compile-time check ties C++ to Agda truth
- `[ ]` CPP-D-22.3 [cpp/src/ffi_backend.cpp:38-39] `AletheiaSendFrameFn` signature pinned only by tooling alignment; no C++-side `check-fidelity` counterpart
- `[ ]` CPP-D-22.4 [cpp/src/json_serialize.cpp:516-531 + 488-502] `serialize_send_frame` builds JSON via `std::format` bypassing nlohmann escapes; defensive route through `Json::array()` candidate
- `[ ]` CPP-D-22.5 [cpp/src/json_serialize.cpp:33-38] `rational_to_json` no GCD normalization (cross-ref CPP-B-8.1)

#### Cat 31: ABI & compiler portability
- `[ ]` CPP-D-31.2 [cpp/include/aletheia/log.hpp:55-61] `std::source_location` requires C++20+ for consumers — document
- `[ ]` CPP-D-31.3 [cpp/include/aletheia/error.hpp:124] `std::expected` is C++23; CMake correct; document why g++>=14 / clang>=21 specifically
- `[ ]` CPP-D-31.4 [cpp/include/aletheia/types.hpp:183] `Timestamp.count()` `int64_t` rep assumed; document or static_assert

#### Cat 32: CMake hygiene
- `[ ]` CPP-D-32.3 [cpp/CMakeLists.txt:233-237] Bare `dl` not `${CMAKE_DL_LIBS}` — Linux-only target acceptable, future portability snag
- `[ ]` CPP-D-32.6 [cpp/CMakeLists.txt:268] `install(DIRECTORY include/ ...)` exports `aletheia/detail/cache_keys.hpp`; pimpl long-term
- `[ ]` CPP-D-32.8 [cpp/CMakeLists.txt:239-241] `SOVERSION 1` hardcoded; PROJECT_VERSION is 1.1.1 — no auto-bump on 2.0.0

### Python system-level (30 findings)

#### Cat 15: API ergonomics
- `[ ]` PY-D-15.1 [python/aletheia/asyncio/_client.py:107] async client lacks `is_closed` (sync client has it at line 165) — sync↔async asymmetric
- `[ ]` PY-D-15.2 [python/aletheia/asyncio/_client.py:97-105] `__aexit__` close coroutine cancellable; `asyncio.shield` candidate
- `[ ]` PY-D-15.3 [python/aletheia/client/_client.py:88-112] `__init__` accepts `default_checks` and `rts_cores` positionally; keyword-only signature would match cross-binding ergonomics
- `[ ]` PY-D-15.4 [python/aletheia/dsl.py:266-269 / checks.py:42] `_data` vs `_property` field naming inconsistent
- `[ ]` PY-D-15.5 [python/aletheia/asyncio/_client.py:196-217] `send_frames_iter` async generator without `await` — docstring should clarify vs other coroutine methods
- `[ ]` PY-D-15.6 [python/aletheia/client/_client.py:728-815] `send_error/send_remote/send_frame` raise `ValueError` not typed `AletheiaError`

#### Cat 16: Boundaries
- `[ ]` PY-D-16.1 [python/aletheia/asyncio/testing.py:42] `from ..client._client import AletheiaClient` deep private path; should use public
- `[ ]` PY-D-16.2 [python/aletheia/excel_loader.py:84 + yaml_loader.py:63] Both import private `from .client._types import check_dbc_text_size_bound`; promote to `aletheia.limits`
- `[ ]` PY-D-16.3 [python/aletheia/client/__init__.py:60-69] `_types.py` mixes public (AletheiaError) and private (StreamCaches, MAX_EXTRACT_CACHE) — split `aletheia/types.py` from `_types.py`
- `[ ]` PY-D-16.4 [python/aletheia/__init__.py:66-81] 14 symbols re-exported from `client` subpackage; `aletheia.AletheiaError` and `aletheia.client.AletheiaError` both public — deprecate one
- `[ ]` PY-D-16.5 [python/aletheia/protocols.py:14-23] `is_str_dict`/`is_object_list` infrastructure helpers leaked into public surface — rename `_is_str_dict`/`_is_object_list`
- `[ ]` PY-D-16.6 [python/aletheia/client/_helpers.py:280] `normalize_signal` no underscore (sibling `_normalize_*` underscored)

#### Cat 17: Extensibility
- `[ ]` PY-D-17.1 [python/aletheia/client/_client.py:88-112] No `Backend`/`IBackend` abstraction (cross-binding parity gap with C++/Go); `aletheia.testing` punts the design
- `[ ]` PY-D-17.2 [python/aletheia/client/_log.py] `LogEvent` enum closed; new event types require core edit
- `[ ]` PY-D-17.3 [python/aletheia/dsl.py:61-80] Three-point coupling for adding predicates documented in dsl.py only; lift to `docs/architecture/PROTOCOL.md`
- `[ ]` PY-D-17.4 [python/aletheia/checks.py:271-289] `class Check` with two `@staticmethod` factories — module-level functions more idiomatic
- `[ ]` PY-D-17.5 [python/aletheia/client/_signal_ops.py:42-52] `SignalOpsMixin(ABC)` private + 1:1 binding; composition over MI

#### Cat 18: Dependency discipline
- `[ ]` PY-D-18.1 [python/pyproject.toml:10] `requires-python = ">=3.12"` vs CLAUDE.md/AGENTS.md "Python ≥ 3.13"; pin floor consistently
- `[ ]` PY-D-18.3 [python/pyproject.toml:81-99] Optional extras (pyyaml/openpyxl/python-can) only floor pins; match dev-tools `<X` pattern
- `[ ]` PY-D-18.5 [python/aletheia/can_log.py:22-23] `import can` raises bare ImportError if missing; replicate narrow-swallow pattern from `__init__.py`
- `[ ]` PY-D-18.6 [python/aletheia/client/_helpers.py 732 LOC] Mixed responsibilities (rationals + serialization + DBC normalization across tier-2); split per cat 27

#### Cat 19: Domain model fidelity
- `[ ]` PY-D-19.1 [python/aletheia/protocols.py:670-678] `SignalValue.value` `Fraction` but `EqualsPredicate.value` etc. `float` — IEEE-754 approx loss; align with DecRat universal principle
- `[ ]` PY-D-19.2 [python/aletheia/protocols.py:97-99] `DBCSignal = DBCSignalAlways | DBCSignalMultiplexed` — `DBCSignalAlways.presence: Literal["always"]` discriminator; `DBCSignalMultiplexed` lacks discriminator (key-presence narrowing)
- `[ ]` PY-D-19.3 [python/aletheia/protocols.py:678] Negative-denominator parse path Python-vs-Agda normalization unverified — roundtrip property test
- `[ ]` PY-D-19.4 [python/aletheia/protocols.py:106-117] `DBCMessage.dlc: int` ambiguous (byte count vs raw code); `NewType` distinct typing candidate
- `[ ]` PY-D-19.5 [python/aletheia/protocols.py:778-779] `PropertyViolationResponse.timestamp: RationalNumber` — assert `denominator == 1` for timestamps
- `[ ]` PY-D-19.6 [python/aletheia/protocols.py:432-449] `DBCDefinition` Tier 2 fields `NotRequired`; Go/C++ structs non-optional — collapse to required + `[]` default

#### Cat 20: Design coherence
- `[ ]` PY-D-20.1 [python/aletheia/client/_types.py:16-127] Flat `AletheiaError` hierarchy; caller can't distinguish "FFI null" from "Agda rejected"
- `[ ]` PY-D-20.2 [python/aletheia/asyncio/_client.py:97-109] `__aexit__/close` lack `asyncio.shield` (cross-ref PY-B-12.1)
- `[ ]` PY-D-20.3 [python/aletheia/cli.py:106-123 + testing.py:22] `run_checks` lives in `cli.py` — layering inversion; move to `aletheia/checks_runner.py`
- `[ ]` PY-D-20.4 [python/aletheia/validation.py] Module hosts only enum-types; rename `aletheia/issue_codes.py` or add thin `validate(dbc)` wrapper
- `[ ]` PY-D-20.5 [python/aletheia/dsl.py + checks.py] Two API surfaces; no `CheckResult.from_property(p)` inverse
- `[ ]` PY-D-20.6 [python/aletheia/cli.py:527 `run_checks`] Returns 3-tuple; `@dataclass(frozen=True) class CheckRunResult` candidate

#### Cat 21: Use-case coverage
- `[ ]` PY-D-21.2 [python/aletheia/__init__.py] `aletheia.limits.MAX_DBC_TEXT_BYTES` etc. not at top-level; Go/C++ surface them in their canonical packages
- `[ ]` PY-D-21.3 [python/aletheia/__init__.py] No mid-level `AletheiaError` taxonomy doc page
- `[ ]` PY-D-21.4 [python/aletheia/asyncio/__init__.py:9-26] Async/sync mutual cross-references missing in docstrings

#### Cat 22: Cross-layer alignment
- `[ ]` PY-D-22.1 [python/aletheia/client/_helpers.py:64-66] `dump_json` doesn't pin `ensure_ascii`; cross-binding wire-byte parity at risk (cross-ref PY-B-8.2)
- `[ ]` PY-D-22.3 [python/aletheia/client/_ffi.py:104-206] FFI binding by string lookup; renamed export silent until first call. `check-ffi-exports` Shake gate exists but type-stub wrapper would catch earlier
- `[ ]` PY-D-22.4 [python/aletheia/client/_client.py:563-564] `_ACK_BYTES`/`_ACK_BYTES_SPACED` not asserted byte-equivalent at test level; pin `json.dumps(separators=(",",":"))` candidate
- `[ ]` PY-D-22.5 [python/aletheia/client/_client.py:600,749,794] `(c_uint8 * N)(*data)` per-frame allocation; `(c_uint8 * N).from_buffer(bytearray(data))` zero-copy candidate

#### Cat 31: Packaging hygiene
- `[ ]` PY-D-31.2 [python/pyproject.toml:48-55] `_install_config.py` generated post-install; document in pyproject docstring or BUILDING.md
- `[ ]` PY-D-31.6 [python/aletheia/__init__.py:117-132] Optional-extras narrow-swallow at top-level only; direct `from aletheia.can_log import ...` raises bare ImportError without `pip install aletheia[can]` guidance

### Docs cross-document pass (38 findings)

#### Cat 5: Redundancy / single-source
- `[ ]` DOC-X-5.1 Module count "246" stated in CLAUDE.md:92, PROJECT_STATUS.md:450, CLAUDE.md:252, MEMORY.md, review-r19-findings.md; canonical: `count-modules`. PROJECT_STATUS.md L489 contradicts L450 (244 vs 246) — same file
- `[ ]` DOC-X-5.2 "binary FFI 4.3×/9.1×" stated in CLAUDE.md:212, DESIGN.md:67, PROJECT_STATUS.md:301; canonical: PROJECT_STATUS.md
- `[ ]` DOC-X-5.3 "C++23, g++>=14 / clang>=21, CMake 3.25+" stated in CLAUDE.md:138, DEPENDENCIES.md:73, BUILDING.md:514,621,614,171, cpp/CMakeLists.txt:1; canonical: BUILDING.md § Prerequisites
- `[ ]` DOC-X-5.4 "15 log event types" stated in CLAUDE.md:163,167; canonical: docs/LOG_EVENTS.yaml
- `[ ]` DOC-X-5.5 "Python ≥ 3.12" stated in PITCH.md:237, QUICKSTART.md:9,14, BUILDING.md:128,130,299,330,432, pyproject.toml:10, DEPENDENCIES.md; canonical: BUILDING.md
- `[ ]` DOC-X-5.6 CLI subcommand list 3× different counts (PITCH:298 6 vs CLI.md:13 5 vs INDEX.md:33 5)
- `[ ]` DOC-X-5.7 "ParseDBC required before StartStream" stated in PROTOCOL.md:36,413,1056, PYTHON_API.md, go/aletheia/client.go:166; canonical: PROTOCOL.md state machine
- `[ ]` DOC-X-5.8 Track A-E status stated in CLAUDE.md:212,280-282, PITCH.md:290,304, PARITY_PLAN.md:36,49,348-415, PROJECT_STATUS.md:443; canonical: PARITY_PLAN.md
- `[ ]` DOC-X-5.9 Frame Building canonical fps stated in PROJECT_STATUS.md:466-473 + L425 (R15 retro 109,345); R15 retro lacks "snapshot" qualifier
- `[ ]` DOC-X-5.10 "iter_can_log streaming design rationale" stated in CLAUDE.md:252, review-r19-findings.md, MEMORY.md; canonical: RUNBOOK.md or PYTHON_API.md
- `[ ]` DOC-X-5.11 DBC type naming `DbcDefinition` vs `DBCDefinition` — CHANGELOG.md (`DbcDefinition`) vs python (`DBCDefinition`); INTERFACES.md mixes both within itself
- `[ ]` DOC-X-5.13 Cancellation contract repeated 14× across go/aletheia/client.go method docs (intentional API mirror — Cat 5 noise)

#### Cat 15: Testability cross-doc
- `[ ]` DOC-X-15.1 PITCH.md:237 declares BUILDING.md SSOT for version pins but `QUICKSTART.md:9`, `DEPENDENCIES.md:18-20,73`, `CLAUDE.md:138`, `cpp/CMakeLists.txt:1` duplicate; no mechanical gate
- `[ ]` DOC-X-15.2 PROJECT_STATUS.md:462 says "canonical source — other docs may round" but DESIGN.md:67 quotes 4.3×/9.1× verbatim; "canonical" claim unenforced
- `[ ]` DOC-X-15.3 INDEX.md:33 vs CLI.md:13 vs PITCH.md:298 disagree on CLI subcommand count; no structural test cross-checks argparse against doc surface
- `[ ]` DOC-X-15.4 LOG_EVENTS.yaml is YAML SSOT; CLAUDE.md:163,167 quotes "15 event types" rather than deferring; no gate
- `[ ]` DOC-X-15.5 CLAUDE.md:212 quotes 4.3×/9.1× same as DESIGN.md:67 + PROJECT_STATUS.md:301; benchmarks/run_all.sh produces JSON but no cross-check vs doc literals

#### Cat 16: Qualifiers cross-doc
- `[ ]` DOC-X-16.1 "Phase 5.1 complete" — CLAUDE.md:212, PITCH.md:290, PROJECT_STATUS.md:443 — none with "as of [date]" qualifier
- `[ ]` DOC-X-16.2 "stable" applied to Agda 2.8.0 (PITCH.md:118) without timestamp; BUILDING.md:7 says "tested combination, not lower bound" — different attestation strength
- `[ ]` DOC-X-16.4 "Per-frame latency: ~9 μs" (PROJECT_STATUS.md:482) coupled with PITCH.md:234 "~8,000 fps" — these are coupled (1/9μs ≠ 8,000 fps)
- `[ ]` DOC-X-16.5 "WSL2 ±10% / ~2-4%" stated only in PROJECT_STATUS.md:425,427; BENCHMARKS.md doesn't surface stance

#### Cat 17: Internal consistency cross-doc
- `[ ]` DOC-X-17.1 (= DOC-X-5.1) Module count 246 vs 244 same file
- `[ ]` DOC-X-17.2 Step count: RELEASE.md:199 "21 steps", CI_LOCAL.md:18 "27", CI_LOCAL.md:218,248 "17"; authority `tools/run_ci.py:235` `BASE_STEPS = 27`
- `[ ]` DOC-X-17.3 (= DOC-X-5.6) CLI subcommand count
- `[ ]` DOC-X-17.4 [docs/operations/MUTATION.md:4 vs :55-58] "go-mutesting" vs `gremlins` — same file disagrees with itself
- `[ ]` DOC-X-17.5 GHC pin: QUICKSTART.md:9 "≥ 9.4" vs DEPENDENCIES.md:20 / BUILDING.md:7 "9.6.7"
- `[ ]` DOC-X-17.6 Last Updated stamps: PITCH.md (2026-04-15), DEFERRALS.md (2026-04-14, R10), DEPENDENCIES.md (2026-04-19), DISTRIBUTION.md (2026-04-15), PROJECT_STATUS.md (2026-05-09); 21-26 days stale
- `[ ]` DOC-X-17.7 Test count: PROJECT_STATUS.md:457 "735 + 1 skip + 103 doc-fences"; L427 R16 retro "624"; no qualifier
- `[ ]` DOC-X-17.8 ParseDBC API name: PROTOCOL.md:56 (`ParseDBC` wire), Python `parse_dbc`, Go `ParseDBC`, C++ `parse_dbc` — PROTOCOL.md should map upfront
- `[ ]` DOC-X-17.10 Track D fence count: PARITY_PLAN.md:382 (Go ≥8, C++ ≥6), PROJECT_STATUS.md:457 (103 Python); no summary table

#### Cat 18: Scope labels cross-doc
- `[ ]` DOC-X-18.1 Audience markers inconsistent: only RUNBOOK.md:20, PROTOCOL.md:7, INTERFACES.md:15 carry explicit Audience section; 25+ docs lack
- `[ ]` DOC-X-18.2 "Last Updated" pattern: 5 docs carry; 25+ docs lack; BUILDING.md:11 refers to a stamp that doesn't exist in BUILDING.md (self-contradiction)
- `[ ]` DOC-X-18.3 "Phase 6 candidate" / "stretch" / "deferred" labels inconsistent across CLAUDE.md, PITCH.md, PROJECT_STATUS.md, DEFERRALS.md (4 different scope verbs)
- `[ ]` DOC-X-18.4 STABILITY.md / MUTATION.md content stamps absent
- `[ ]` DOC-X-18.5 INTERFACES.md cross-binding parity table uses ✅ emoji without "as of [date]" row qualifier; no gate against FEATURE_MATRIX.yaml drift

---

## Step 3: Coverage reconciliation and planning

**Coverage gate**: 17 of 17 agents returned full reports across all assigned categories. No gaps. ✓

**False positives + reclassifications** (user adjudicated 2026-05-10):
- **AGDA-A-29.1-4**: ✅ **FP** — already documented at `DecRatParse/Properties.agda:1079-1090` (explanatory comment block). Strict-form header note not required; existing inline rationale satisfies AGENTS.md cat 29.
- **AGDA-D-10.3**: ❌ **NOT FP — reclassified FIX**. User direction: "do not defer". Domain-model gap on overload frames + single-shot transmission events; FIX as documenting comment-block addition to `TraceEvent` ADT explaining the omission (Phase 5.1 minimal-trace scope). Folded into Cluster 5.
- **CPP-B-12.4**: ✅ **FP — audit verified**. Every public `parse_*` (10 functions: parse_success / parse_event_ack / parse_validation / parse_extraction / parse_frame_data / parse_frame_response / parse_stream_result / parse_dbc_response / parse_parsed_dbc / parse_dbc_text_response) wraps body in `try { ... } catch (const std::exception& e) { ... }`. nlohmann's exceptions all inherit from `std::exception`. Containment confirmed.
- **GO-B-10.1**: ❌ **NOT FP — reclassified FIX**. User direction: "make sure there's a comment explaining why we strdup and not free". Existing comment at `go/aletheia/ffi.go:110` (`// Intentionally not freed — GHC RTS may retain argv pointers.`) is terse; strengthen to fully explain (a) why strdup vs stack — hs_init may retain argv across return per GHC docs; (b) why not free at process end — tiny one-shot leak, no harm; (c) cross-binding parity with Python `_ffi.py` and C++ `ffi_backend.cpp`. Folded into Cluster 5.

---

## Action plan

19 clusters. Mirroring R18's FIX-early / FIX-middle / DEFER-end-of-round structure per `feedback_review_round_dispositions.md`. Carry-overs (R19-CARRY-1, R19P2-CARRY-1) tracked separately.

### Carry-over dispositions

| ID | Site | Disposition | Rationale |
|---|---|---|---|
| R19-CARRY-1 | `src/Aletheia/CAN/Encoding.agda:122` Bool fast-path | **RE-DEFER** | Agda elaboration barrier (4 probes failed in R19 Phase 1); only viable revisit via Agda upstream fix or eliminating Dec dispatch |
| R19P2-CARRY-1 | `go/aletheia/ffi.go:690-700` `outSize MaxInt32` | **RE-DEFER** | Return-value bound (FFI output), not input; covered by upstream `MaxJSONBytes` cap |

### Clusters (FIX-early — mechanical, low-risk)

**Cluster 1 — Doc drift mechanical batch** (Themes A + parts H/Q)
- Findings: DOC-A-1.1-1.10, DOC-A-2.1-2.5, DOC-A-3.1-3.6, DOC-A-4.1-4.9, DOC-A-5.1/5.3-5.5, DOC-A-7.1-7.2, DOC-A-8.1-8.2, DOC-A-9.1-9.6, DOC-B-10.5, DOC-B-13.1-13.4, DOC-B-14.1-14.5, DOC-B-15.1, DOC-B-16.1-16.4, DOC-B-17.1-17.3, DOC-B-18.1-18.3, DOC-B-19.1-19.5, DOC-B-20.1-20.4, DOC-B-21.1-21.3, DOC-B-22.2-22.3, DOC-X-5.1-5.13, DOC-X-15.1-15.5, DOC-X-16.1-16.5, DOC-X-17.1-17.10, DOC-X-18.1-18.5, AGDA-A-4.2/4.3, GO-A-1.1, CICD-5.8.
- Disposition: **FIX-early**.
- Scope: PROJECT_STATUS.md L489 244→246 sync; `tools/run_ci.py` step count cited as 17/21/27 → cite `BASE_STEPS = 27` symbolically across docs; `MUTATION.md:4` "go-mutesting" → `gremlins`; CLI subcommand list 5 vs 6 (CLI.md/INDEX.md need `format-dbc`); `iter_can_log` 5-tuple in python/README.md; CHANGELOG type-naming `DbcDefinition` vs `DBCDefinition` cross-binding alignment; INDEX.md missing 6+ docs (CHANGELOG, CANCELLATION, CGO_NOTES, CI_LOCAL, MUTATION, PARITY_PLAN, RELEASE); "Last Updated" stamps refresh on PITCH/DEFERRALS/DEPENDENCIES/DISTRIBUTION; binding READMEs for go/cpp.
- Effort: ~80 doc-only edits across ~25 files; no source code changes.

**Cluster 2 — CICD supply-chain hardening** (Theme P)
- Findings: CICD-1.6/1.7/1.8/1.9, CICD-2.2, CICD-5.9.
- Disposition: **FIX-early**.
- Scope: `.github/workflows/gha-checks.yml` `runs-on: ubuntu-latest` → `ubuntu-22.04`; add `timeout-minutes: 5` per job; add `concurrency: { group: gha-checks-${{ github.ref }}, cancel-in-progress: true }`; sha256-verify actionlint tarball pre-extract; pin Dockerfile.runtime libgmp10 install via snapshot.debian.org; sha256-verify cosign binary fetch (keys/README.md + RELEASE.md).
- Effort: ~6 small workflow/Dockerfile/release-doc edits.

**Cluster 3 — Logger/event consistency mechanical batch** (Theme H)
- Findings: GO-A-30.1, CPP-A-30.1 (= shared `cache.full` description drift), GO-A-30.2, GO-A-30.3, GO-A-30.4, CPP-A-30.2, CPP-A-30.3.
- Disposition: **FIX-early**.
- Scope: `docs/LOG_EVENTS.yaml:94` `cache.full` description "evicted oldest" → "reached capacity bound; subsequent extractions bypass cache"; Go's 13 `slog.LogAttrs(context.Background(),...)` → forward caller `ctx`; CPP-A-30.2 camelCase→snake_case key normalization; CPP-A-30.3 `int64`→`uint64` for size-style fields; document `dbc.parsed` field schema in YAML SSOT.
- Effort: ~20 sites across 3 bindings; mechanical.

**Cluster 4 — Test-discipline cleanup** (Theme J)
- Findings: GO-B-11.1/11.2, PY-B-11.1/11.2/11.3/11.4, PY-A-4.6, PY-B-29.2.
- Disposition: **FIX-early**.
- Scope: Go cancel_test.go `time.Sleep` polling → channel-based synchronization (per `feedback_no_physical_time_in_tests.md`); python/tests/test_excel_loader.py `_active_sheet(wb)` helper to drop 30+ `# type: ignore[union-attr]`; test_cancellation.py narrow async-batch annotations to drop 3 `# type: ignore`; test_checks.py `not in d` → `.get(...) is None`; test_cli.py `from aletheia.testing import run_checks`.
- Effort: ~3 files modified; pattern repeats.

**Cluster 5 — Naming/hygiene Agda+Go mechanical batch** (Theme R + AGDA-D-10.3 + GO-B-10.1 reclassifications)
- Findings: AGDA-A-1.1 (Limits.withinBound dead), AGDA-A-1.2 (Handlers comment stale), AGDA-A-1.3 (DLC suc^16 absurd), AGDA-A-4.4 (Constants L23 magic 512), AGDA-A-GA1.1/GA1.2 (import hygiene), AGDA-D-10.3 (TraceEvent overload-frame/single-shot-tx omission comment), GO-A-1.2 (`maxPayloadBytes` vs `MaxFrameByteCount`), GO-A-2.1 (`Dbc*` → `DBC*` 30 IDs), GO-A-2.2 (`CanID` capitalization), GO-A-2.3 (`vds` vs `unresolvedVDs`), GO-A-3.1-3.7 (godoc on 70+ exported), GO-A-4.4-4.5 (json.go const grouping + format inversion), GO-A-5.4 (frame error wrap prefix), GO-B-10.1 (strdup-no-free comment strengthening).
- Disposition: **FIX-early**.
- Scope: `Limits.withinBound` either delete or thread through parser entries; AGDA-D-10.3 add comment block to `TraceEvent` ADT explaining overload-frame + single-shot-tx omission per CAN 2.0B §3.1.5 / ISO 11898-1 §6.6 (Phase 5.1 minimal-trace scope, signal-level LTL only); Go `Dbc*` → `DBC*` API rename (breaking — per `feedback_no_backward_compat.md` OK, no migration shim); 70+ Go godoc comments added; minor consts/format inversions; GO-B-10.1 strengthen `ffi.go:110` strdup-no-free comment to fully explain (a) hs_init retains argv per GHC docs; (b) one-shot per-process leak is tiny and harmless; (c) cross-binding parity with Python+C++.
- AGDA-A-29.1-4 dropped from scope per FP confirmation.
- Effort: large (Go API rename touches every consumer of `DbcMessage`/`DbcSignal`/etc.); mostly mechanical via grep+sed.
- Risk: Go API rename breaks downstream → call out explicitly.

**Cluster 6 — AllObserved doc propagation** (Theme G)
- Findings: AGDA-D-12.2, AGDA-D-13.5, AGDA-D-17.4, AGDA-D-GA7.1.
- Disposition: **FIX-middle** (doc-propagation across 3 bindings).
- Scope: Add docstring + binding-API doc on `AllObserved` user obligation in python/aletheia/client/_client.py docstring + go/aletheia/doc.go + cpp/include/aletheia/aletheia.hpp; cross-ref to `docs/architecture/CGO_NOTES.md` or new dedicated note; surface `Unsure` verdict semantics in PROTOCOL.md.
- Effort: ~5-8 doc edits across bindings + 1 architecture doc.

### Clusters (FIX-middle — moderate scope)

**Cluster 7 — Cross-binding wire-byte parity** (Theme B)
- Findings: PY-B-8.2 / PY-D-22.1 (Python `dump_json` `ensure_ascii` not pinned), GO-B-8.2 (Go `parseRational` accepts negative denom), CPP-B-8.1 / CPP-D-22.5 (C++ `rational_to_json` no GCD norm), CPP-D-19.2 (C++ Delta/Tolerance double, Python+Go Fraction), GO-B-8.1 (Go NaN/Inf to non-RFC8259 JSON).
- Disposition: **FIX-middle**.
- Scope: Pin `ensure_ascii=False` in `_helpers.py:dump_json`; Python+Go+C++ Rational normalization gate (cross-binding test asserting roundtrip emits canonical-form `{6,3}` → `{2,1}`); Python+Go reject NaN/Inf at predicate value boundary (typed `ProcessError`); C++ `Delta`/`Tolerance` migrate `double` → `Rational`.
- Effort: ~6 sites + 1 cross-binding test; needs cross-binding parity gate.

**Cluster 8 — Defense-in-depth bound checks at parser surfaces** (Theme D)
- Findings: AGDA-D-11.1/11.2/11.3/11.4/11.5/11.6/11.7, CPP-B-9.1 / CPP-D-21.3 / CPP-B-28.4 (6 limits.hpp unenforced), CPP-D-21.5 (bound-error response missing structured fields), AGDA-D-13.4 (fuel measure leaves nesting unbounded).
- Disposition: **FIX-middle** (sub-items split — see status below).
- Scope: Identifier length bound at `Aletheia.DBC.Identifier` validity record; atom-count cap at `parseProperty`; nesting-depth bound at `parseJSONHelper` (subtract on each Array/Object recursion); `parseObjectList`/`parseSignalList`/`parseMessageList` cardinality caps; C++ `parse_bounded` extended to messages_per_file/signals_per_message/atom_count/identifier_length/string_length/attributes_per_file/value_descriptions_per_file; structured `bound_kind/observed/limit` in C++ bound-error JSON.
- Effort: large — Agda kernel + C++ parser changes; needs proof updates for new validity record fields.

**Cluster 8 — Sub-item status (2026-05-11):**

| Sub-item | Status | Notes |
|---|---|---|
| **(a) `parseJSON` nesting-depth bound** (AGDA-D-11.2 partial / AGDA-D-13.4) | ✅ ROLLED BACK to post-parse 2026-05-11 (uncommitted) | Initial implementation set `fuel = max-nesting-depth` (depth bound conflated with the parser's recursion-termination measure).  Per user feedback "I generally am not a fan of fuel… arbitrary upper-bound", rolled back to `parseJSONHelper (length input) pos input` (original termination measure) + post-parse `jsonDepth tree <ᵇ suc max-nesting-depth` refinement.  Same wire surface (`DispatchErr InvalidJSON`); same bound enforcement; consistent with e.1 / e.2 post-parse-refinement pattern (no fuel anywhere).  New `jsonDepth` helper added to `Protocol/JSON/Types.agda` as `mutual` recursion with `listDepth` / `fieldsDepth`.  Trade-off: rejection on adversarial deep-nesting inputs now requires the full parse to run before the bound check fires.  Verified at JSON depth 62 (accept) / 65 (reject as `dispatch_invalid_json`). |
| **(b) `parse_dbc_text` inner cap** (CPP-D-21.3 + Python/Go mirrors) | ✅ In flight on `review-r19` | Each binding pre-checks input text size against `max_dbc_text_bytes` before wrapping in JSON command; rejection carries precise `dbc_text_input_bound_exceeded` wire code. 3 new tests (1 per binding). |
| **(c) Structured `bound_kind/observed/limit` in C++ AletheiaError + wire JSON** (CPP-D-21.5) | ✅ DONE 2026-05-11 (uncommitted) | `AletheiaError` gains `std::optional<InputBoundExceededError> bound_info_`; FFI backend emits structured fields; `make_json_error` lifts them via `is_input_bound_exceeded_code(code)` discriminator (kind override). 3 new tests (parse_dbc_text rejection / parsed-from-wire / nullopt-when-missing). 19 assertions / 3 test cases. |
| **(d) C++ `parse_bounded` extension to 6 schema-aware bounds** (CPP-B-9.1 / CPP-B-28.4) | ✅ DEFERRED — closed via (e) | Resolution: implementing item (d) creates the reverse asymmetry — C++ would be the only binding doing defense-in-depth on Agda's responses; Python and Go (which export the same constants for SSOT) trust the Agda kernel.  The right close is **kernel-level proof** so all 3 bindings inherit the guarantee.  This is what sub-item (e) accomplishes.  Transitional risk before (e) lands is bounded by the existing `max_json_bytes` FFI-entry cap (64 MiB) which transitively limits response size and cardinality. |
| **(e) Agda kernel work** (AGDA-D-11.1/3/4/5/6/7) — Identifier validity record + atom-count cap + cardinality caps + bounded-emission theorems | ✅ DONE 2026-05-11 (uncommitted) | e.1 + e.2 + e.3 + e.4 all shipped this session.  Closes item (d) — C++ binding-side defense-in-depth — via formal proof for all 3 bindings simultaneously. |
| **(e.1) Identifier length bound at the validity-record refinement** (AGDA-D-11.1) | ✅ DONE 2026-05-11 (uncommitted) | `validIdentifierᵇ (c ∷ cs)` extended with `length (c ∷ cs) <ᵇ suc max-identifier-length` as a third conjunct.  Construction paths (`mkIdentFromChars` / `mkIdentFromString`) inherit via existing `T?` decidable check; hard-coded `mkIdent (toList "<short>") tt` callsites still typecheck (the new conjunct reduces to `true` on every concrete short string).  Cascade through proof tree was small: only `Primitives.agda:decompose-valid` needed updating (single `T-∧-split` → two splits via Agda's inferred implicits).  All gates green: `cabal run shake -- build` 2m04s + `check-properties` 11m44s + Python 805p / Go ok / C++ ctest 10/10.  Cross-binding regression tests: Python 3 cases (`TestIdentifierLengthBound`), Go 2 cases (`TestCrossBinding_Identifier{AtMaxLength,OverMax}`), C++ 2 `[e1]` cases.  Wire surface for over-bound input is currently `dbc_text_trailing_input` rather than typed `InputBoundExceeded IdentifierLength` — the parser-monad position is past the consumed chars when `mkIdentFromChars` rejects, so the top-level parser eventually fails with "trailing input"; refining this is downstream plumbing tracked alongside AGDA-D-13.4. |
| **(e.2) Atom-count cap at `parseProperty`** (AGDA-D-11.6) | ✅ DONE 2026-05-11 (uncommitted) | New `atomCount : ∀ {A} → LTL A → ℕ` in `LTL/Syntax.agda` (alongside `mapLTL`).  `parseProperty` in `LTL/JSON.agda` now binds on `parseLTL` then checks `atomCount ltl <ᵇ suc max-atom-count-per-property`; over-bound trees return `nothing`.  Post-parse refinement, NOT fuel — `parseLTL` runs to structural completion on the input JSON value, then the bound check fires once.  Wire surface for rejection is `HandlerErr (PropertyParseFailed idx)` via `parseAllProperties` in `Protocol.Handlers`.  Tradeoff acknowledged in user feedback: rejection on a >1024-atom property pays the full parseLTL cost (~115s for a balanced 1025-atom And-tree empirically; manually verified to reject correctly).  Companion bound-soundness lemma `parseProperty-atom-bounded` deferred to e.4 where it composes with the formatter side.  Build 1m58s + `check-properties` 8m07s.  Python regression: `TestAtomCountBound::test_small_property_accepted` (100-atom balanced tree accepted in <1s); the over-bound case intentionally not exercised in CI (slow). |
| **(e.3) Cardinality caps at the DBC handler boundary** (AGDA-D-11.3/4/5) | ✅ DONE 2026-05-11 (uncommitted) | Post-parse refinement applied at the **handler boundary** (`Protocol/Handlers.agda` for `handleParseDBC`; `Protocol/Handlers/ParseDBCText.agda` for `handleParseDBCText`), NOT inside the parser itself.  First attempt wired checks inside `parseDBCWithErrors` + `parseMessageBody` and broke ~all DBC-roundtrip proofs (parseMessageList-roundtrip / parseDBCWithErrors-roundtrip / parse-format-parse) — `pattern refl` no longer matched because the new `if-then-else` bind disrupted the structural shape proofs depended on.  Reverted parser-level changes and moved to handler-level: parseDBCWithErrors / parseText stay unchanged so all roundtrip proofs preserve their existing shape; the bound check fires AFTER the parser returns a DBC, BEFORE `validateDBCFull` runs.  Helper functions `signalsBound : List DBCMessage → Maybe (ℕ × ℕ)` and `firstDBCOverBound : DBC → Maybe (...)` walk the DBC tree once, returning the first cardinality violation (messages → per-message signals → attributes); on violation, handler emits typed `InputBoundExceeded ArrayCardinality observed limit` wrapped in the appropriate ADT (`ParseError` for `handleParseDBC`, `DBCTextParseError` for `handleParseDBCText`).  Bounds covered: `max-messages-per-file` (10000), `max-signals-per-message` (1024 per message), `max-attributes-per-file` (10000).  Build 2m01s + `check-properties` re-run clean.  Python regression: `TestListCardinalityBound` with 3 acceptance tests (100 messages / 64 signals / empty lists).  Over-bound rejection NOT in CI — pre-existing O(N²) `parseDBC` scaling (~51s @ 1000 messages, >30min @ 10001 — see `feedback_parsedbc_quadratic_scaling.md`) makes canonical-limit tests impractical; bound is verified by code inspection. |
| **(e.4) Bounded-emission theorems for the DBC formatter** (load-bearing for binding-side trust) | ✅ DONE 2026-05-11 (uncommitted) | New module `src/Aletheia/DBC/Formatter/Bounded.agda` (3 lemmas, all proof-only).  Module count 246 → **247**.  Each lemma is a conditional length-preservation statement: `length input ≤ n → length (map format-… input) ≤ n`, with stdlib `length-map` as the underlying fact and `subst (_≤ n) (sym ...)` to transport the bound: <ul><li>`formatDBC-messages-bounded` — `messages` array of `formatDBC d`;</li><li>`formatDBC-attributes-bounded` — `attributes` array of `formatDBC d`;</li><li>`formatDBCMessage-signals-bounded` — per-message `signals` array of `formatDBCMessage msg`.</li></ul>  Wired into `Shakefile.hs` `check-properties` walk so the gate catches future drift.  Closes the cross-binding trust chain established by e.1 (Identifier length via validity record) + e.2 (Property atom count) + e.3 (per-handler cardinality caps): every DBC accepted by `handleParseDBC` carries the e.1/e.3 bounds, and `formatDBC` preserves them on emit.  Identifier-length bound is automatic from the e.1 validity-record invariant (Identifier carries the witness; emit just unpacks `Identifier.name` which is provably ≤ 128 chars).  `formatProperty-atomCount` not added because Property has no format-to-JSON path in the current protocol (properties are stored internally; only verdicts round-trip to wire); the e.2 parse-side bound is sufficient.  Closes item (d) for all 3 bindings by formal proof — Python / Go / C++ inherit the guarantee without per-binding defense-in-depth code. |

**Agda kernel plan for (e)** (added per user direction 2026-05-11 — "when planning for the larger Agda kernel work, add it to the existing R19 work"):

The kernel work has four sub-phases.  Each builds on the previous; gates between phases are `check-properties` + per-binding test sweep.

**Phase e.1 — Identifier length bound at the validity-record refinement** (AGDA-D-11.1)
- File: `src/Aletheia/DBC/Identifier.agda`
- Add a 2nd bool-witness slot to the `Identifier` record: `bounded : T (length chars <ᵇ suc max-identifier-length)`, mirroring the existing first-char/non-isHSpace witnesses (per `feedback_refinement_types_pattern.md`).
- The existing parser already produces `Identifier` via `Identifier.parse : List Char → Maybe Identifier`; parse rejects when the new witness fails — surfaces as a new `parseInvalidIdentifier` code variant or extends the existing one with bound context.
- Cascade: every Identifier construction site in TextParser proofs (~30 sites per past Identifier change rounds) plus the `_≟ᴵ_` decidable equality.  Per `feedback_data_ctor_irrelevance_cascade.md`, the new witness can be `@0`-erased (record has η; no MAlonzo runtime cell).
- Proof side: refresh `parseDBC-identifier-bounded : ∀ {input dbc} → parseDBC input ≡ inj₂ dbc → ∀ id ∈ identifiers(dbc) → length (Identifier.chars id) ≤ max-identifier-length` from refinement-record invariant.  ≤ 30 LOC, straightforward (`Identifier.bounded id` direct project).
- Effort: medium (cascade is mostly mechanical); 0 new modules.

**Phase e.2 — Atom-count cap at `parseProperty`** (AGDA-D-11.6 / AGDA-D-13.4 typed-error half)
- File: `src/Aletheia/LTL/PropertyParser.agda` (or wherever `parseProperty` lives) + `Aletheia/Protocol/JSON/Parse.agda` (atom dispatch).
- Refinement at the kernel: every parsed `Property` carries a witness `atom-bounded : T (atom-count prop <ᵇ suc max-atom-count-per-property)`.  Either (i) wrap `Property` in a refinement record, or (ii) prove the bound post-parse and surface as a `Refined` newtype.
- (ii) is cleaner — keeps `Property` shape unchanged; adds `refineProperty : Property → Maybe RefinedProperty` that fails with typed `InputBoundExceeded AtomCount`.
- Cascade: tighter — refinement happens at one point in `parseProperty`'s output; downstream consumers either accept `Property` (no change) or `RefinedProperty` (new type).
- Proof: `parseProperty-atom-bounded` via straightforward induction on the AST.
- Effort: small-medium; ~50-100 LOC.

**Phase e.3 — Cardinality caps at `parseObjectList`/`parseSignalList`/`parseMessageList`** (AGDA-D-11.3/4/5)
- Files: `src/Aletheia/DBC/Parser/*.agda` + the JSON-side equivalents in `src/Aletheia/Protocol/JSON/Parse.agda`.
- Per AGENTS.md "Adversarial-input bounds at parser surfaces": each list-cardinality parser refuses inputs that would push the resulting list size past the canonical bound.
- Implementation pattern: extend each `parseList`-style combinator with a fuel parameter capping list length:
  ```
  parseBoundedList : ℕ → Parser A → Parser (List A)
  parseBoundedList zero       _ = fail-with InputBoundExceeded ArrayCardinality observed limit
  parseBoundedList (suc fuel) p = ...
  ```
- Three call sites use different limits: `max-messages-per-file (10K)` / `max-signals-per-message (1024)` / `max-attributes-per-file (10K)` / `max-value-descriptions-per-file (1M)`.
- Proof: per-call-site `parseBoundedList-bounded : parseBoundedList n p input ≡ just xs → length xs ≤ n` from fuel-decrement invariant.
- Effort: medium-large; cascades into JSON parser proofs (Properties tree).

**Phase e.4 — Bounded-emission theorems** (the load-bearing part for binding-side trust)
- Files: new `src/Aletheia/Protocol/JSON/Properties/Bounded.agda` or extension of existing JSON/Properties.
- Theorems (one per bound kind):
  - `formatDBC-messages-bounded : ∀ d → length (DBC.messages d) ≤ max-messages-per-file → length (extract "messages" (formatDBC d)) ≤ max-messages-per-file`
  - Similar for signals_per_message, attributes_per_file, value_descriptions_per_file.
  - `formatDBC-identifier-bounded : every emitted "name" / "messageName" / "signalName" string ≤ max-identifier-length`.
  - `formatDBC-string-bounded : every emitted comment / attribute string value ≤ max-string-length-bytes`.
  - `formatProperty-atom-bounded : property AST count ≤ max-atom-count-per-property → emitted JSON atoms ≤ same`.
- These compose with phases e.1-e.3: parse rejects over-bound inputs → internal representation respects bounds → formatter preserves bounds → emitted JSON respects bounds → no binding-side check needed.
- Effort: small-medium per theorem; cumulative ~200-400 LOC; all proof-only (no runtime effect, walked by `check-properties` only).

**Closing sub-item (d) when (e) lands**: append a paragraph to AGDA-D-11.1 / 11.6 / etc. closures explicitly noting that CPP-B-9.1 / CPP-B-28.4 (item d) close as by-product, and add a cross-binding regression test that parses a hand-crafted-from-kernel response and asserts no bound is exceeded.

**Cluster 8 in-flight diff (uncommitted on `review-r19` as of 2026-05-11):**
- `src/Aletheia/Protocol/JSON/Parse.agda` (item a)
- `python/aletheia/client/_client.py` + `python/tests/test_input_bounds.py` (item b — Python)
- `go/aletheia/client.go` + `go/aletheia/input_bounds_test.go` (item b — Go)
- `cpp/include/aletheia/error.hpp` + `cpp/src/client.cpp` + `cpp/tests/unit_tests_input_bounds.cpp` (item b — C++)
- `cpp/include/aletheia/error.hpp` + `cpp/src/ffi_backend.cpp` + `cpp/src/json_parse.cpp` + `cpp/tests/unit_tests_input_bounds.cpp` (item c)

Per-binding green: Python 19/19, Go `TestParseDBCText_RejectsOversizeText` pass, C++ `[cluster8]` 3 tests / 19 assertions pass.  Agda runtime closure compiles (`cabal run shake -- build`, 1m42s, 272 MAlonzo modules).  `check-properties` not re-run yet — items (a) + (b) + (c) are all runtime/cold-path; proof side should be parametric.  Commit is held pending sub-item (e) scoping (per user direction "do not commit yet").

**Cluster 9 — Missing extension points** (Theme E)
- Findings: PY-D-17.1 (Python no IBackend), GO-D-16.2 (Go no IsClosed), CPP-D-17.4 (C++ Logger single-callback), CPP-D-17.1 (IBackend mixed pure/default).
- Disposition: **FIX-middle**.
- Scope: Define `aletheia.client.Backend(Protocol)` matching FFI surface; `AletheiaClient.__init__` accepts `backend: Backend | None` + default `_FFIBackend(...)`; Go `func (c *Client) IsClosed() bool` under lock; C++ `Logger::add_sink(LogCallback)` multi-sink composition; C++ `IBackend` annotate pure-vs-defaulted at declarations.
- Effort: medium per binding; cross-binding parity test for IBackend / IsClosed surface.

**Cluster 10 — API ergonomics asymmetries** (Theme F)
- Findings: GO-D-15.1 (Close lies about error), GO-D-15.3 (Stringer asymmetric), GO-D-15.4 (BuildFrame/UpdateFrame ctx ordering), GO-D-15.5 (FormatDBC vs ParseDBC*), PY-D-15.1 (async no is_closed), PY-D-15.3 (positional kwargs), PY-D-15.6 (send_frame ValueError not typed), CPP-D-15.1/15.2 (Rational invariant), CPP-D-15.5 (Check::signal namespace).
- Disposition: **FIX-middle**.
- Scope: Cluster of small fixes — Go `String()` for DbcVarType/DbcAttrScope; arg-order normalization across BuildFrame/UpdateFrame/SendFrame; FormatDBC return `*ParsedDBC`; Python async `is_closed`; Python `__init__` keyword-only; Python typed `InvalidArgumentError`; C++ `Rational::make` as only public + privatize 2-arg ctor; C++ Check namespace decision (preserve or migrate).
- Effort: medium; touches 3 bindings; some breaking (Python signature, Go arg order, C++ Check) per `feedback_no_backward_compat.md`.

**Cluster 11 — Async cancellation hardening** (Theme I)
- Findings: PY-B-12.1, PY-B-12.2, PY-D-15.2, PY-D-20.2.
- Disposition: **FIX-middle**.
- Scope: `asyncio.shield(asyncio.to_thread(self._sync.close))` in `__aexit__` + standalone `close()`; same pattern for `__aenter__` `init`; document `send_frames` partial-prefix behavior in docstring.
- Effort: small (~5 code changes); add cancel-during-close test.

**Cluster 12 — cgo / FFI safety hardening** (Theme L)
- Findings: GO-B-27.2/27.3 (NUL-byte truncation in CString), GO-B-10.3 (runtime.KeepAlive), CPP-B-13.1 (memcpy no endian static_assert), CPP-B-13.5 (Rational::from_double scaled overflow), CPP-B-7.1/7.3 (Rational invariant under NDEBUG / extraction-bin den<0), CPP-B-7.4 (`max_can_fd_payload_bytes` vs `max_frame_byte_count` SSOT violation), PY-B-23.1 / PY-B-10.5 (ALETHEIA_LIB symlink-following), PY-B-23.4 (Excel ZIP-bomb cap on outer file size only).
- Disposition: **FIX-middle**.
- Scope: Go `strings.ContainsRune(s, 0)` rejection at `C.CString` callsites; `runtime.KeepAlive(...)` after `C.call_*`; C++ `static_assert(std::endian::native == std::endian::little)`; tighten `Rational::from_double` overflow boundary at `std::nextafter(int64_max_d, 0)`; Python `os.lstat` reject symlinks for ALETHEIA_LIB; Python ZIP-bomb defense via `zipfile.ZipFile` central-dir size sum.
- Effort: medium; 8-10 sites across bindings.

**Cluster 13 — MAlonzo erasure surface extension** (Theme M)
- Findings: AGDA-D-17.2, AGDA-D-30.1, AGDA-D-30.2, AGDA-D-GA23.2.
- Disposition: **FIX-middle**.
- Scope: `Shakefile.hs check-erasure` add Maybe constructor checks (`AgdaMaybe.C_nothing_18`/`C_just_16`) + Sigma constructor checks (`AgdaSigma.T_Σ_14`, `C__'44'__32`, `d_fst_28`, `d_snd_30`); extend `ffi-exports.snapshot` to cover indirect helper accessors (`d_dlcToBytes_6`, `d_numerator_14`, `d_denominatorℕ_20`, etc.).
- Effort: small (Shakefile + snapshot file); proof-only.

**Cluster 14 — Combinator-first refactor batch** (Theme N)
- Findings: AGDA-C-6.1 (`InContext` × 5 ADTs), AGDA-C-6.2 (`InputBoundExceeded` × 3), AGDA-C-6.3 (`checkUnknown*` × 3), AGDA-C-6.4 (Standard/Extended twins), AGDA-C-6.5 (`*-list-go` × 4), AGDA-C-6.6 (And/Or-symmetric ≥5 in SimplifySound), AGDA-C-3.1 (`formatChars` naming), AGDA-C-3.3 (`checkAll*` prefix), AGDA-C-3.4 (`-list-` kebab inconsistency), CPP-A-1.1 / CPP-A-6.1 (FFI deleter × 8), CPP-A-6.2 (`can_id_value` × 12), GO-A-6.1 (lock pattern × 15), GO-A-6.2 (iota Stringer × 6), GO-A-6.3 (parseObjects × 8), AGDA-C-5.1 (DispatchError trailing "in request"), AGDA-C-5.2 (range-error phrasing), AGDA-C-5.3 (DBCTextParseError/DispatchError lack InContext).
- Disposition: **FIX-middle** (large scope, sub-cluster for parallel work).
- Scope: Lift `InContext` to top-level `Error.WithContext` (or factor `WithCtx` combinator); lift `InputBoundExceeded` to top-level Error; parameterize `MessageRoundtrip/{Standard,Extended}.agda` over CANId ctor; `parseObjectList-roundtrip` combinator; And/Or duality lift to `LTL.Semantics.Duality`; C++ `wrap_str_result(char*, std::string_view)` helper + `can_id_value`/`can_id_is_extended` promoted to types.hpp; Go `(c *Client) acquire(ctx, name) (release func(), err error)` helper + `parseObjects[T any]` generic.
- Effort: large; can be sub-clustered for parallel agent work.

**Cluster 15 — Stdlib dedup** (Theme S)
- Findings: AGDA-C-27.1-27.5.
- Disposition: **FIX-early** (small mechanical).
- Scope: Replace hand-rolled `map-∘-identifier` with stdlib `map-∘`; verify `monad-left/right-identity` against `RawMonad.Laws`; consolidate `*-comm` lemmas; inline `mod-identity-byte` rename wrapper.
- Effort: small; 5 sites.

**Cluster 16 — Python boundary cleanup** (Theme Q)
- Findings: PY-D-16.1-16.6, PY-D-18.1, PY-D-18.3, PY-D-18.5, PY-D-18.6, PY-D-31.6.
- Disposition: **FIX-middle**.
- Scope: Promote `check_dbc_text_size_bound` to public `aletheia.limits.check_dbc_text_size_bound`; split `_types.py` into `aletheia/types.py` (public) + `aletheia/client/_internals.py` (private); rename `is_str_dict`/`is_object_list` → `_is_str_dict`/`_is_object_list`; `aletheia.testing` use public path for `AletheiaClient` import; Python ≥ 3.13 floor consistency; optional extras upper-bound pins; ImportError narrow-swallow at submodule level.
- Effort: medium; some breaking changes per `feedback_no_backward_compat.md`.

### Clusters (FIX-middle — Domain Model)

**Cluster 17 — Python domain model coherence** (Theme N + part of E)
- Findings: PY-D-19.1-19.6, PY-D-20.1, PY-D-20.3, PY-D-20.4, PY-D-20.6, PY-D-15.4, PY-A-3.1-3.6, PY-A-5.4 (RuntimeError in excel_loader), PY-A-6.1, PY-A-6.3, PY-A-6.4, PY-A-6.5.
- Disposition: **FIX-middle**.
- Scope: Predicate values `float` → `Fraction` (per DecRat universal principle); `DBCSignal` add explicit `presence` discriminator; `DBCMessage.dlc` distinguish `DLCByteCount`/`DLCCode` newtypes; `DBCDefinition` Tier 2 fields required + `[]` default; flat `AletheiaError` → kind-tagged hierarchy; move `run_checks` from `cli.py` to `aletheia/checks_runner.py`; rename `validation.py` → `issue_codes.py` or add thin `validate(dbc)` wrapper; helper consolidation (`_require_existing_path`, `_require_lo_le_hi`, `_require_non_negative_time_ms`, `_is_pure_int`); typed `AletheiaError` subclass for excel_loader RuntimeError.
- Effort: large; touches several modules; some breaking (DBCSignal discriminator).

### Clusters (DEFER-end-of-round / requires-decision)

**Cluster 18 — BRS/ESI cross-binding plumbing** (Theme C)
- Findings: AGDA-D-10.1 / AGDA-D-13.1 / AGDA-D-17.1 / AGDA-D-GA23.1.
- Disposition: **FIX-late** (user adjudicated 2026-05-10: extend C signature + propagate through 3 bindings + JSON wire).
- Scope: extend `aletheia_send_frame` C signature to accept `brs_present u8`, `brs_value u8`, `esi_present u8`, `esi_value u8` (or equivalent encoding); thread through `haskell-shim/AletheiaFFI.hs` builder so it constructs `TimedFrame.brs/.esi` from real values instead of hardcoded `nothing`; surface `BRS`, `ESI` fields on Python `Frame` / Go `Frame` / C++ `Frame` types; propagate to JSON wire shape; documentation-comment per binding explaining ISO 11898-1:2015 §10.4.2 (BRS) and §10.4.3 (ESI) semantics.
- Cat 17 cross-layer: every wire boundary needs the new fields per `feedback_audit_all_wire_boundaries.md` — binary FFI signature, JSON wire, 3 binding type structs, doc surface.
- Effort: large (~4-6 weeks of cross-binding work). Best ordered AFTER Cluster 8 (defense-in-depth bounds) and Cluster 9 (extension points) so the new fields get bound checks + Backend-aware tests in one pass.

**Cluster 19 — Hot-path allocations** (Theme K)
- Findings: GO-B-25.2 (strings.Builder), PY-B-10.3 / PY-D-22.5 (ctypes per-frame), CPP-B-25.1 (last_frames per-frame copy), PY-B-14.1 (log_event kwargs eval), PY-B-14.2 (`_ACK_BYTES` tuple per-frame).
- Disposition: **DEFER-end-of-round** unless benchmarks show regression on cluster 17 ship.
- Rationale: per `feedback_in_source_deferral_notes.md` + `feedback_hot_path_refactor_benchmark.md`, hot-path optimizations need benchmark evidence; current numbers are within WSL2 ±10% gate.

### Clusters (DEFER-end-of-round / architectural)

**Cluster 20 — Module structure refactors** (Theme O)
- Findings: AGDA-D-15.1 (Validator/Checks.agda 595 LOC), AGDA-D-15.2 (StreamState/Internals.agda + DEFER block), AGDA-D-15.3 (StreamingWarm.agda 367 LOC), PY-A-27.4/27.5 (`_client.py` 930 LOC, `protocols.py` 976 LOC).
- Disposition: **DEFER-end-of-round** (benchmark-or-skip per AGENTS.md L244 facade pattern).
- Scope: split per `feedback_properties_facade_split.md`; Python `_client.py` candidate for further `_signal_ops.py`-style extraction.
- Effort: medium; mechanical; module count drift to track per `feedback_module_count_prose_audit.md`.

### Round summary

- 20 clusters identified (18 FIX [6 early + 11 middle + 1 late], 2 DEFER-with-rationale).
- 2 carry-overs RE-DEFER (R19-CARRY-1, R19P2-CARRY-1).
- 4 candidate FPs adjudicated 2026-05-10: 2 confirmed FP (AGDA-A-29.1-4, CPP-B-12.4); 2 reclassified FIX (AGDA-D-10.3, GO-B-10.1) folded into Cluster 5.
- Cluster 18 BRS/ESI: user adjudicated FIX-late (extend C signature + propagate).

---

## Round state

| Phase | Status | Notes |
|---|---|---|
| Step 0 — Carry-over reconciliation | ✓ done | R19-CARRY-1 + R19P2-CARRY-1 candidate dispositions in plan |
| Step 1 — Per-file review (12 agents) | ✓ done | 12 of 12 returned; ~296 findings |
| Step 2 — System-level (4 agents) | ✓ done | Agda D 25 + Go D 22 + C++ D 28 + Python D 30 |
| Step 2.5 — Cross-document pass | ✓ done | 38 findings across cats 5/15-18 |
| Step 3 — Coverage reconciliation + plan | ✓ done | 20 clusters; 18 FIX (6 early + 11 middle + 1 late), 2 DEFER; 2 carry-overs RE-DEFER; 4 FPs adjudicated (2 confirmed + 2 reclassified FIX) |
| Step 4 — Implement and verify | in flight | FIX-early first (Clusters 1-6, 15); then FIX-middle (7-14, 16-17); FIX-late Cluster 18 last; per-cluster commits + 4-gate verification |

**Total: 17 of 17 agents returned. ~439 findings.** Step 3 ✓; Step 4 starting FIX-early. **Pushes forbidden** per user direction 2026-05-10.
