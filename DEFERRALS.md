# Deferred & NO-FIX Review Items

Items explicitly declined or deferred during AGENTS.md review rounds. Each entry records **what**, **where**, **why deferred**, and **what would change the decision**. Resolved items stay in this file with a `✅ RESOLVED` annotation rather than being deleted — NO-FIX in a pre-user project is worth periodic re-audit (worked example: R6-B9.1 was filed NO-FIX 2026-04-10 with a "non-trivial proof effort" rationale; R20 cluster W shipped an operational fix in `c40e3ba` after cluster S discovered the original stability claim was empirically false on raw `Until`/`Release`/`Atomic` shapes).

**Last updated:** 2026-05-17 (R20 closed + R19 Phase 2 carry-overs formalised — see `memory/project_review_round{11..20}.md` for per-round closure narratives.  Recent revisions: 2026-05-15 — Phase C1 (R6-B7.2 ✅), LE bitLength=0 promotion (R5-B1 ✅ + R6-B7.1 ✅), R20-GO-A-4.10 ✅, plus pass-2 audit-trail closures (R5-A11 ✅ / R6-B9.1 ✅ / R6-P1.1 ✅ / R6-B7.3 🟢).  2026-05-16 — R20-AGDA-B-26.3 ✅ + R20-AGDA-B-GA9.1 ✅ via `Reflects` Bool fast-path + `injectHelper` lift (strengthens R20-AGDA-B-18.3 with in-source DO-NOT-RE-RAISE comment); R6-B8.2 `sound-or` half ✅ via De Morgan from `sound-and`.  2026-05-17 — R20-AGDA-C-27.1 re-audited DEFER → FIX-re-flip → DROP after empirical 5.69× slowdown on `parseDBCText`; in-source DO-NOT-RE-RAISE blocks added for R5-C2 / R6-B8.1 / R6-B8.2-sound-and / R20-AGDA-B-18.3.  R6-B7.3 🟢 → ✅ RESOLVED (`lastObserved` lifted to `Timestamp μs`, 7 files).  R6-B7.4 DEFER → ✅ RESOLVED (`PropertyState` parameterised by `(n : ℕ)` with `index : Fin n`, 8 Agda + 3 haskell-shim files).  Final pre-merge pass adds durable in-source DO-NOT-RE-RAISE blocks for R20-AGDA-D-19.3 / D-GA20.1 (above `nothing≢just` in `StreamingWarm.agda`), R20-GO-A-3.6 (above `StandardID` in `go/aletheia/types.go`), R20-GO-A-3.7 (above `Client` in `go/aletheia/client.go`) — every NO-FIX item now has its justification visible in source.  **R19 Phase 2 carry-over section added** below (Cluster 10 + 16 scope deferrals) — these are planned future work, not NO-FIX; verified status per item.  Per advisor: scope deferrals get DEFERRALS.md tracking but NOT in-source DO-NOT-RE-RAISE blocks (those are for rejected choices).)

---

## Permanently Deferred

### D1. `mkPredTable` atom index ℕ → Fin (length atoms)
- **Origin:** System review 2026-04-07 (item 11.1)
- **File:** `src/Aletheia/Protocol/StreamState/Internals.agda:91`
- **Finding:** `mkPredTable` returns `Unknown` when `n ≥ length atoms`. The branch is provably dead (Property 27 in `FrameProcessor/Properties.agda` proves `AllBelow` holds by construction). A `Fin (length atoms)` index would make the dead branch unrepresentable.
- **Why deferred:** **Performance hazard.** MAlonzo compiles `Fin n` as a unary Peano chain (`data T_Fin_10 = C_zero_12 | C_suc_16 T_Fin_10`) — k heap cells per value, one heap dereference per pattern match. The current `ℕ` compiles via BUILTIN to Haskell `Integer` with native `eqInt`/`subInt`. `mkPredTable` runs per frame and its closure is invoked by `stepL` for every Atomic cell (Stream LTL hot path). This is the same failure mode as the `Dec`-vs-`Bool` regression (commit `5aa345e`, 30-65% throughput loss). The refactor would also touch ~8 files, change the four-valued `agreement` theorem shape, and require FFI mangling re-verification.
- **In-source caution:** ~40-line comment block above `mkPredTable` in `StreamState/Internals.agda:91`.
- **Revisit when:** Someone proposes a MAlonzo compilation strategy for `Fin` that doesn't use Peano encoding, or benchmarks show the overhead is acceptable.

---

## NO-FIX Items by Round

### Round 5 (2026-04-10)

#### R5-B1. `bitLength` lacks positive type guarantee
**✅ RESOLVED 2026-05-15** — closed via BE-LE parity completion at BOTH parser surfaces rather than type-tightening.  `Aletheia.DBC.JSONParser.physicalGate` (JSON path) now rejects `bitLength = 0` for both byte orders with `ParseErr SignalBitLengthZero` (BE was already rejected since 2026-04-08); `Aletheia.DBC.TextParser.Topology.SignalLine.buildSignal` (text path) likewise returns `nothing` on `1 ≤ᵇ bl ≡ false`, which propagates through `buildAllRaw` → `resolveSignalList` → `buildMessage` (parser `fail`) and surfaces at the top level as `DBCTextParseError.ParseFailure` (wire code `dbc_text_parse_failure`).  `Aletheia.DBC.Formatter.WellFormed.PhysicallyValid.pv-LE` gains a `1 ≤ SignalDef.bitLength` argument parallel to `pv-BE`'s existing `len-pos`.  Python test `TestBitLengthZero` adapted: LE and BE both expect `ProtocolError` with `code = parse_signal_bit_length_zero` from `client.validate_dbc(dbc)` (was: `bit_length_zero` validation warning).  C++ added LE parity test mirroring the existing BE `[integration][parse_error]` case.  Go's MockBackend-based parse-error tests are byte-order-agnostic; the comment block was updated to note the parity.  The type-tightening `bitLength : ℕ⁺` cascade was rejected as too expensive and unnecessary — parser-surface rejection achieves the same external behaviour without touching CAN/Signal / CAN/Encoding / CAN/Batch.  The text-parser's error vocabulary is intentionally coarser than the JSON parser's (`DBCTextParseError` has three constructors; the functional outcome is identical — zero-length LE signals are rejected at parse time on every external entry point).  The validator's `checkBitLengthZero` remains in place as defense-in-depth but is unreachable from any parse-driven external entry point.  Audit-trail preserved below.

- **File:** `src/Aletheia/CAN/Signal.agda:22`
- **Finding:** `bitLength : ℕ` could be `ℕ⁺` to statically prevent zero-length signals.
- **Why NO-FIX (2026-04-10, since invalidated):** Type-tightening that cascades through CAN/Signal, CAN/Encoding, CAN/Batch, DBC modules. The DBC validator catches `BitLengthZero` at validation time, and `physicalGate` rejects bitLength=0 for BE signals at parse time. LE bitLength=0 produces a degenerate but non-crashing extraction (0 bits = 0 value). Cost far exceeds benefit.
- **Related:** Round 6 B7.1 (same underlying issue, different angle).

#### R5-A11. `M.map` closure on eval hot path
**✅ RESOLVED in `bf238b3`** (round 11) — the cache-fallback path was rewritten during the round-11 batch sweep that introduced `cachedSignalValue` / `lookupCacheValue`. `getTruthValue` now uses Maybe's `<∣>` alternative (`Evaluation.agda:103-104`) and `evalValuePredicateTV` / `evalDeltaPredicateTV` consume the result via `case … of λ where` (line 108), eliminating the `M.map` closures originally at lines 84/98. Verified 2026-05-15 against current source.

- **File:** `src/Aletheia/LTL/SignalPredicate/Evaluation.agda:84,98`
- **Finding:** `M.map` (Data.Maybe.map) creates a closure on the cache-fallback path of `evalPredicateTV`.
- **Why NO-FIX (2026-04-10):** Low severity — only fires on cache hits (not the primary extraction path). The closure is short-lived. Replacing with a pattern match would be a micro-optimization with no proof impact and would need benchmarking to confirm any improvement.

#### R5-C2. Validation issue codes lack `validation_` prefix
- **File:** `src/Aletheia/Protocol/ResponseFormat.agda:68-106` (definition `formatIssueCode` + 18-line in-source DO-NOT-RE-RAISE block above it, added 2026-05-17).
- **Finding:** Validation issue codes don't have a domain prefix like error codes do.
- **Why NO-FIX:** Validation codes live in `issues[].code` within `ValidationResponse` / `ParsedDBCResponse` — structurally nested, already namespaced by container. Error codes share a flat `("code", JStringS …)` JSON field with the response envelope (`formatResponse (Error err)` at this module's tail), so they need a domain prefix to disambiguate per Cat 5. Adding `validation_` would touch the 21 codes here + 21 mirrors in each of the three bindings (Python/Go/C++ `IssueCode` enum) for zero disambiguation benefit at the wire.
- **In-source DO-NOT-RE-RAISE block:** `ResponseFormat.agda` immediately above `formatIssueCode` (added 2026-05-17). Future review rounds that scan the source will see the rationale before considering a prefix-adding refactor.

---

### Round 6 (2026-04-10)

#### R6-B7.1. `bitLength` admits 0
**✅ RESOLVED 2026-05-15** — see R5-B1 (above) for the closure narrative.  Same fix: `physicalGate`'s `1 ≤ᵇ bl` check now fires for both byte orders.  The "defense in depth at the parse layer" framed as nice-to-have in the original NO-FIX rationale is now the actual behaviour.

- **File:** `src/Aletheia/CAN/Signal.agda:24`
- **Finding:** `bitLength : ℕ` allows 0, which is physically meaningless for a CAN signal.
- **Why NO-FIX (2026-04-10, since invalidated):** `physicalGate` in `DBC/JSONParser.agda` rejects bitLength=0 for BE signals at parse time. `handleParseDBC` always runs `validateDBCFull` after parsing (line 124), and `checkBitLengthZero` rejects bitLength=0 for ALL byte orders. A DBC with bitLength=0 never enters `ReadyToStream`. Defense in depth at the parse layer would be nice but the validator already gates the data path.
- **Related:** Round 5 B1 (same underlying issue).

#### R6-B7.2. Metric `window`/`startTime` raw ℕ
**✅ RESOLVED 2026-05-15** — Phase C1 cascade lifted `MetricEventually` / `MetricAlways` / `MetricUntil` / `MetricRelease` from `ℕ → ℕ → LTL → LTL` to `Timestamp μs → ℕ → LTL → LTL` (window phantom-typed μs; `startTime` stays ℕ as a suc-encoded sentinel). Files touched: `LTL/Syntax.agda`, `LTL/Coalgebra.agda`, `LTL/Coalgebra/Properties.agda`, `LTL/Simplify.agda`, `LTL/JSON.agda` (parser wraps `mkTs`), `LTL/JSON/Format.agda` + `Properties.agda` (formatter unwraps `tsValue`; roundtrip preserved via Timestamp record η), `LTL/Semantics.agda`, `LTL/Semantics/MTL.agda`, `LTL/Adequacy.agda`, `LTL/Adequacy/Agreement.agda`, `LTL/SimplifySound/Decomposition.agda` (new `≡ᵇ⇒≡-ts` private helper), `Protocol/Adequacy/WarmCache.agda`, `Protocol/FrameProcessor/Properties/Bounded.agda`. Gates: `check-properties` 8m17s clean; `cabal run shake -- build` 2m00s clean; Agda invariants/erasure/fidelity/ffi-exports/bound-enforcement/runbook/changelog all clean; `pytest tests/` 854 passed; check-fidelity 17/17 (FFI smoke through bindings exercises the new constructor types). The R6-B7.2 NO-FIX rationale ("number of frames, not wall-clock") was wrong on the facts — the values ARE microsecond timestamps used in `metricElapsed s curr ≤ᵇ tsValue w` window-check arithmetic. Audit-trail preserved below for future review-round visibility.

- **File:** `src/Aletheia/LTL/Syntax.agda:45`
- **Finding:** `MetricEventually`, `MetricAlways`, etc. use raw `ℕ` for window size and start time instead of `Timestamp` or a refined type.
- **Why NO-FIX (2026-04-10, since invalidated):** Approved NO-FIX from round 5 (item A21). Refining these would cascade through all metric operator proofs in `Coalgebra.agda`, `Coalgebra/Properties.agda`, `Semantics/MTL.agda`, `Adequacy.agda`, and `Agreement.agda`. The ℕ values represent "number of frames" (window) and "frame count since start" (startTime), not wall-clock timestamps — they are dimensionally distinct from `Timestamp μs`.

#### R6-B7.3. `CachedSignal.lastObserved` unrefined ℕ
**✅ RESOLVED 2026-05-17** — closed by user request to re-examine the hot-path concern.  The 2026-05-15 🟢 HELD disposition cited "the per-frame hot path benefits from the unwrap-avoidance" — that rationale was empirically wrong.  Verification via `grep -rn "\.lastObserved\|mkCachedSignal" src/`: zero runtime READ sites for `lastObserved`; the only read is `AllTimestamps≤` in `Cache/Properties.agda:47` (proof-only, not reached from Main).  All non-Cache.agda hits for `mkCachedSignal` are proof-side construction in `Adequacy/StreamingWarm.agda` (universally-quantified `ts`, never destructured-and-read on a runtime path).  The "unwrap at every cache lookup / update" claim was a phantom hazard: there are no consumers that DO the unwrap, because there are no consumers that READ the field.

  Refactor scope (7 files): `Cache.agda` (field type + `updateEntries` / `updateCache` signatures + proof helpers `updateEntries-All-neq` / `updateEntries-unique` parameter types + misleading rationale block replaced); `Cache/Properties.agda` (`AllTimestamps≤` bound type lifted from `ℕ` to `Timestamp μs`, comparison routed via `_≤ᵗ_` which unfolds to `tsValue _ ≤ tsValue _` so existing `≤-refl` proofs continue to discharge); `StreamState/Internals.agda` (`updateSignals` / `updateCacheFromFrame` signatures + `Timestamp` import); `StreamState.agda:71` (caller passes `timestamp tf` instead of `timestampℕ tf` — the actual perf win, ONE per-frame `timestampℕ` unwrap eliminated); `Adequacy/StreamingWarm.agda` (`timestamp` import added; `cacheAfter` body + `cacheAfter-monotone` + `cacheAfter-warms` proof bodies updated to pass `timestamp tf` to `updateCacheFromFrame`); `FrameProcessor/Properties/Step.agda` (3 `updateCacheFromFrame ... timestampℕ tf` → `timestamp tf` in proof statements); `FrameProcessor/Properties/Monotonic.agda` (2 similar updates).  No proof logic changed — all updates were type-level annotation adjustments + `timestampℕ`→`timestamp` substitution.  All Properties consumers' `ts` parameters infer the new `Timestamp μs` type from context.  `check-properties` passed 12m13s clean against the refactor; build clean 3m56s.

  Perf impact: removed one `timestampℕ` unwrap per frame in the streaming hot path.  Not benchmark-measurable (`Timestamp μs` MAlonzo-compiles to the same `Integer` as `ℕ` via the `@0 u : TimeUnit` phantom erasure, so the field-storage cost is unchanged; the eliminated `tsValue` projection is a single Haskell function call per frame).  Pitch is type-level annotation cleanup, not perf — the prior comment's "unwrap-avoidance" was a phantom benefit.

- **File:** `src/Aletheia/LTL/SignalPredicate/Cache.agda:27-37` (post-refactor).
- **Audit-trail preserved (original Why NO-FIX, since invalidated):** Round 5 item A23, "internal bookkeeping; refining would touch 9 files and reopen `Cache/Properties.agda` proofs for no new dimensional-analysis benefit." The "no dimensional-analysis benefit" claim was wrong on the facts — the dimensional tag now propagates from `TimedFrame.timestamp` directly into `CachedSignal.lastObserved`, making the cache's timestamp dimension type-checked rather than implicit.  The "touch 9 files" estimate was approximately correct (actual: 7 files).

#### R6-B7.4. `PropertyState.index` ℕ vs Fin
**✅ RESOLVED 2026-05-17** — `PropertyState` parameterised by `(n : ℕ)`; `index : Fin n`; `StreamState` constructors carry the matching `n` (`ReadyToStream : (n : ℕ) → DBC → List (PropertyState n) → SignalCache → StreamState`, similar for `Streaming`).  `Data.Fin.toℕ` runs only at the wire boundary (`PropertyResult.Violation`/`Satisfaction`/`Unresolved` in `verdictToResult`, and `dispatchIterResult`'s violation emit); the internal pipeline (`stepProperty` → `iterate` → `classifyStepResult`) keeps `Fin n` end-to-end.  `parseAllProperties` consumes a pre-tabulated `List (Fin n × JSON)` (helper `withIndices` in `Handlers.agda`) so each property's index comes from its input position with `length` definitional equality discharging the type — no counter-with-invariant threading.  Cascade: 8 files (`Types`, `Internals`, `StreamState`, `Handlers`, `Handlers/ParseDBCText`, `FrameProcessor/Properties/{Step,Monotonic,Handlers}`) + `haskell-shim/{src/AletheiaFFI.hs, test/ConstructorTest.hs}` MAlonzo-mangled name updates (`d_initialState_42` → `_50`, `T_StreamState_28` → `_32`) + `haskell-shim/ffi-exports.snapshot` `T:` line.  Gates clean: 12 Agda gates (build / check-properties 8m28s / check-invariants / check-no-properties-in-runtime / check-erasure / check-fidelity 17/17 / check-ffi-exports 45 entries / check-bound-enforcement 7 BoundKind ctors / count-modules 250 / check-runbook 15 events / check-changelog / check-limits-parity 14+7) + pytest 866p+1s + Go test -race ok + C++ ctest 10/10.

Perf impact: zero per-frame in the common no-violation case (`PropertyState.index` is a record-field projection threading the same `Fin n` value through the stream; no `toℕ` on the per-frame `Continue` path).  Worst-case violation path adds `toℕ : Fin n → ℕ` once per violation (Peano-chain unfold of depth `toℕ idx + 1`, ≤ `n` cells); for the canonical `n ≤ 1024` ceiling that's ≤ 1µs per violation, negligible at any realistic violation rate.  Distinct from the `Fin (length atoms)` concern in `Internals.agda`'s `DEFERRED REFACTOR` block (lines 98-136) — that one is about the per-step atom-table lookup (`lookupAtom`) which IS on the per-frame hot path and DOES warrant the MAlonzo-Peano warning; this one is about the property-identifier label, which is wire-only.

- **File:** `src/Aletheia/Protocol/StreamState/Types.agda:28-42` (`PropertyState n` + `StreamState` constructors carrying `n`).
- **Audit-trail preserved (original Why NO-FIX, since invalidated):** "Cold-path construction, but the index is read on the violation path in the stepping loop. `Fin → ℕ` conversion would be needed for JSON formatting (property index in violation responses). Cascade through 4+ files for marginal type safety gain. The index is always valid by construction (`initProperties` assigns sequential indices)." Three errors in this rationale: (1) `Data.Fin.toℕ` at the wire boundary is a single `toℕ` call per emission, not "JSON formatting needs conversion" per anything — the wire emit IS the only conversion site; (2) "marginal type safety gain" understated the value — the `Fin n` index makes "no out-of-bounds property identifier reaches the wire" structurally true rather than an `initProperties`-invariant claim; (3) the cascade was 8 files, not 4+, but most files needed only `{n}` implicit additions in proof signatures (refl-based proofs carry through unchanged).

#### R6-B8.1. SimplifySound truth-table helpers repetitive
- **File:** `src/Aletheia/LTL/SimplifySound/Decomposition.agda:325-373` (the `runL-and-right-*` / `-or-right-*` / `-cong-r` empty-trace helpers + 24-line in-source DO-NOT-RE-RAISE block above them, strengthened from prior A25 design note 2026-05-17).  SimplifySound was split from a monolith into `SimplifySound.agda` + `SimplifySound/Composition.agda` + `SimplifySound/Decomposition.agda` between this finding's filing and its re-audit — the helpers cited at the original `SimplifySound.agda:340-458` line range now live in `Decomposition.agda`.
- **Finding:** Per-verdict helper functions for empty-trace And/Or cases are repetitive (6 helpers, ~10 lines each, total ~60 lines).
- **Why NO-FIX (re-audited 2026-05-17):** In-source design note A25 already explained extraction-via-generic-dispatcher rejection (each helper calls different decomposition lemmas with different arity; And/Or have different K3 absorbers; a generic combinator would still need the same case split, just with more parameters).  Re-audit per `feedback_nofix_rationale_incomplete_axis.md` asked "what's a different axis?" — the R6-B8.2 De Morgan trick (`sound-or` via `sound-and`) does NOT translate here because `FinalVerdict`'s three-valued logic has asymmetric absorbers between And and Or (`Holds` transparent on And but absorbing on Or; `Fails` is the mirror), with no involutive operation on `FinalVerdict` that lets us derive Or helpers from And helpers via substitution.  Truth-table lookup, higher-order combinators, and macro-generated cases all regenerate the same case split with added indirection.  The repetition is the price of three-valued Kleene correctness at the FinalVerdict layer.
- **In-source DO-NOT-RE-RAISE block:** `Decomposition.agda` immediately above the empty-trace helpers (strengthened 2026-05-17 from the prior A25 design note with explicit DO-NOT-RE-RAISE tag + re-audit conclusion).
- **Revisit when:** Agda gains a tactics framework that mechanically generates the truth-table cases (current `unquoteDecl` / `macro` reflection is banned by Cat 29), OR the FinalVerdict type is refactored to admit an involutive operation that produces a clean dual between And and Or.

#### R6-B8.2. SoundOps `sound-and`/`sound-or` repetitive (380 lines each)
**✅ RESOLVED 2026-05-16** (`sound-or` half) — closed via De Morgan derivation: `sound-or sm sd ≡ subst₂ Sound _ _ (sound-not (sound-and (sound-not sm) (sound-not sd)))`, bridged by a one-line lemma `∨TV-via-De-Morgan : ∀ a b → a ∨TV b ≡ notTV (notTV a ∧TV notTV b)` added to `LTL/TruthVal/Properties.agda`. The required `notTV-involutive` and `deMorgan-∨` lemmas already existed in `TruthVal/Properties.agda` (used by `Semantics/Duality.agda`); A24's framing considered "generic combinator parameterized by op" but did NOT consider De Morgan reduction to the dual operator — same shape of incomplete-rationale gap as R20-AGDA-B-26.3 (`Reflects` was the unexplored escape hatch there). Net: `sound-or` 175 LOC → 6 LOC (−169 LOC); SoundOps total 515 → 349 lines (−166); +5 lines for the new lemma in TruthVal/Properties; net **−161 LOC** in the proof layer. Gates clean: `check-properties` 9m07s + `build` 1m58s + `check-no-properties-in-runtime` + `check-invariants` + `check-erasure` all green. Downstream consumers in `Adequacy.agda` (30+ call sites) all type-check unchanged — none pattern-match on the `Sound` constructor of the result, so the `subst₂`-bridged result type unifies cleanly. `sound-and` stays primitive (its `sound-ff _ = sound-ff` short-circuit handles 6 of 36 outer cases at the top); deriving both via De Morgan would create a definitional cycle. In-source A24 design note rewritten to document the new architecture.  **In-source DO-NOT-RE-RAISE block** for the `sound-and` primitive choice strengthened 2026-05-17 from prior A24 architecture note (`SoundOps.agda` immediately above `sound-not`/`sound-and`) — explicit DO-NOT-RE-RAISE tag added; rationale extended with "why deriving both creates a definitional cycle" + "why True-absorber on sound-or wouldn't short-circuit as cleanly as False-absorber on sound-and" + "revisit only if Agda gains a tactics framework" (current reflection is Cat 29 banned).

- **File:** `src/Aletheia/LTL/Adequacy/SoundOps.agda:92-444`
- **Finding:** `sound-and` and `sound-or` each have ~380 lines of similar structure.
- **Why NO-FIX (2026-04-10, since invalidated for sound-or):** In-source design note A24 explains why a generic `sound-binop` was rejected. The two functions differ in their Kleene truth-table entries, identity elements, and absorption rules. A generic version would need to be parameterized over 9 truth-table entries plus identity/absorption lemmas — the resulting type signature would be longer than the repeated code, and the proof would not be simpler.

#### R6-B9.1. `classifyStepResult` Satisfied stability argument hand-waved
**✅ RESOLVED 2026-05-15** — R20 cluster W (`c40e3ba`): `classifyStepResult Satisfied _ = complete` (was `advance prop`); satisfied properties drop from the active set instead of being re-stepped. Cluster S (`637b2e0`) surfaced that the original "stays satisfied" assumption was empirically false for raw `Until`/`Release`/`Atomic` shapes — the gap was real and produced two bugs (mid-stream false counterexamples; EndStream false `Fails` on satisfied `Eventually`/`Until`). The original NO-FIX rationale below was incorrect on its facts; preserved here for audit-trail.

- **File:** `src/Aletheia/Protocol/StreamState/Internals.agda:210`
- **Finding:** The Satisfied branch of `classifyStepResult` relies on an informal argument that a satisfied property stays satisfied.
- **Why NO-FIX (2026-04-10, since invalidated):** Non-trivial proof effort. `runL-stepL-satisfied` in `Coalgebra/Properties.agda` already covers the safety property (a trace that evaluates to True stays True). The gap is about inner-process stepping behavior (that `stepL` on a `Done True` process stays `Done True`), not trace-level correctness. The claim is true by inspection of `stepL`'s `Done` clause but formalizing it would require threading process-level invariants through the stepping loop.

#### R6-P1.1. `_client.py` 1030 lines (marginal overshoot)
**✅ RESOLVED 2026-05-15** — `wc -l python/aletheia/client/_client.py` reports **944** lines (under the 1000-line guideline by 56). The shrinkage came from cumulative round 11+ batch sweeps that hoisted helpers into `_response_dispatcher.py`, `_diagnostic_state.py`, `_request_state.py`, etc. The 30-line overshoot is gone without an explicit split commit — file growth has stalled below threshold organically. Re-audited 2026-05-15.

- **File:** `python/aletheia/client/_client.py`
- **Finding:** File is 1030 lines, exceeding the 1000-line guideline by 30 lines.
- **Why NO-FIX (2026-04-10):** The file was already decomposed in prior rounds (cache logic, types, protocols all extracted). Further splitting would require passing 4+ fields through a new module boundary (FFI handle, caches, logger, state) for marginal line-count improvement. The 30-line overshoot is from the GD22.1 cross-binding parity fix (sorted iteration).

---

### Round 20 (2026-05-15)

R20 closed clusters A-Y + GO-A-3.5. Entries below are the round's DEFER + FP-VERIFIED + DROP residuals; full per-cluster closure narrative in `memory/project_review_round20.md` and disposition logs in `review-r20-findings.md`. Round-merge to `main` follows once this file syncs.

#### R20-AGDA-B-26.3. `injectHelper` Dec on frame-build hot path [DEFER → ✅ RESOLVED 2026-05-16]
**✅ RESOLVED 2026-05-16** — closed via architectural refactor + Bool fast-path via `Reflects`.  Three coordinated changes shipped together:

1. **`injectHelper` lifted from where-bound to top-level** in `src/Aletheia/CAN/Encoding.agda`.  Top-level reduction lemmas `injectSignal-bounds-true` / `-false` dispatch the outer `inBounds` guard via single-line `rewrite`; proofs no longer need to mirror the full 3-deep `with`-chain.  Both `Roundtrip.agda` and `Disjoint.agda` proofs were decomposed: `injectSignal-reduces-{unsigned,signed}` and `injectSignal-preserves-disjoint-bits{,-physical}` now `trans`-compose a one-line outer-bounds lemma with a 2-deep helper-level lemma.

2. **New smart constructor `mkBoundedBitVec`** in `src/Aletheia/Data/BitVec/Conversion.agda`.  Uses `<ᵇ-reflects-<` from stdlib (two-with form `with n <ᵇ bl | <ᵇ-reflects-< n bl`) — Reflects' `ofʸ`/`ofⁿ` constructors carry the witness AS DATA, so the consumer's reduction lemma `mkBoundedBitVec-just` abstracts over a constructor-shaped scrutinee instead of an equation-shaped one.  This is the structural escape hatch the R19 cluster D + F four-approach probe didn't try.

3. **`injectHelper`'s Dec dispatch swapped for `mkBoundedBitVec`** — net wire of Bool-dispatch + `Maybe` constructor replaces yes/no Dec wrapper.  Verified at MAlonzo level: the Dec constructor and `<?` are gone from `MAlonzo.Code.Aletheia.CAN.Encoding`.

The original R19 cluster D + F probe's framing ("the barrier is structural to Agda's `with ... in eq` elaboration mechanism") is empirically correct — `mkBoundedBitVec-just` written with `with ... in eq` still triggers the exact `[UnequalTerms]` "ill-typed with-abstraction" error in a minimal 17-line reproduction.  But the conclusion ("workaround: keep `Dec`") was too strong: the `Reflects` two-with pattern provides a clean alternative that didn't appear in the four probed approaches.  See `memory/feedback_with_in_eq_outer_abstraction_barrier.md` (revised 2026-05-16) for the corrected guidance.

**Perf note:** No measurable Frame Building gain over the post-`@0` baseline (deltas within WSL2 session-distant ±10% jitter; Python 2.0B +4.9%, C++/Go 2.0B −3.1%/−3.9%).  Reason: MAlonzo emits `Reflects.fromEquivalence` for `mkBoundedBitVec`, which allocates a Reflects wrapper via `du_of_30` + two closures per call — one heap cell, structurally similar to post-`@0` Dec.  The original 30–65% throughput figure cited in the in-source comment was from commit `5aa345e` (pre-`@0`, pre-`extractSignalCoreFast`); cluster D's `@0` ship in `471a9ce` already captured the real perf gain.  The architectural win (proof clarity, eliminated where-block + 3-deep mirror) is real and standalone valuable.

- **File:** `src/Aletheia/CAN/Encoding.agda:108` (lifted `injectHelper`)
- **Original finding:** `Dec` dispatch on the per-frame inject path; MAlonzo allocates a Dec witness per call.
- **Why DEFER (2026-05-15, since closed):** R19 cluster D + F's four-approach probe (direct rewrite / `mkBoundedBitVec` helper restructure with `with ... in eq` / `@0`-with-Bool / `.()`-irrelevance) all hit the `with ... in eq` outer-abstraction barrier. Standalone `@0`-erasure on `ℕToBitVec`'s bound slot shipped in R19 cluster D `471a9ce`; the `Dec` wrapper allocation remainder appeared blocked at the Agda elaboration layer.
- **What broke the deadlock:** the four-approach probe used `with ... in eq` for the bound-check bridge.  Stdlib's `Reflects` data carrier sidesteps the trap entirely (constructor witness, not equation witness).  Not tried in cluster D/F.

#### R20-AGDA-B-18.3. `injectHelper` `nothing = nothing` dead branch [DEFER — DO NOT RE-RAISE]
- **File:** `src/Aletheia/CAN/Encoding.agda:114` (`mkBoundedBitVec`'s `nothing` arm)
- **Finding:** The `... | nothing = nothing` branch on `mkBoundedBitVec`'s result is structurally required by Agda's coverage checker but provably unreachable under the bound-injection invariant.
- **Why DEFER (stable, not waiting on anything):** Encoding the branch as unreachable at the type level requires either (a) a refined `Maybe`-with-conditional-emptiness type that no stdlib primitive consumes, or (b) threading a `WellFormedSignal` precondition through every call site of `injectSignal` (CAN/BatchFrameBuilding, Protocol/Handlers, ~30+ call sites).  Neither carries enough leverage to justify the cascade — GHC's strictness analyzer DCEs the branch already (returns `Nothing` without further work).
- **In-source DO-NOT-RE-RAISE block:** `CAN/Encoding.agda` immediately above the branch.  The block is marked with the AGDA-B-18.3 identifier in caps and an explicit "DO NOT RE-RAISE IN REVIEW" tag so future review-round agents that scan the source recognize the rationale and skip it.
- **Revisit when:** a separate refactor adds a `WellFormedSignal` precondition to `injectSignal` for an unrelated reason and the branch becomes provably dead as a side effect — OR a stdlib primitive emerges that lets the type carry the emptiness condition without proof-threading.

#### R20-AGDA-B-GA9.1. `injectHelper` canonical where-block on runtime path [DEFER → ✅ RESOLVED 2026-05-16]
**✅ RESOLVED 2026-05-16** — `injectHelper` lifted from where-bound to top-level in `src/Aletheia/CAN/Encoding.agda` (see R20-AGDA-B-26.3 closure narrative).  The where-block no longer exists; the runtime function is at module scope and proofs name it directly via the new `injectHelper-reduces-{unsigned,signed}` / `injectHelper-preserves-disjoint-bits{,-physical}` lemmas.

- **File:** `src/Aletheia/CAN/Encoding.agda:108` (now top-level)
- **Original finding:** Where-block hosted the `with` chain whose Dec dispatch + bounded-witness flow couldn't be promoted to the `_<ᵇ_` Bool fast path under the R19 four-approach probe's framing.
- **Why DEFER (2026-05-15, since closed):** Tied to R20-AGDA-B-26.3 RE-DEFER.
- **Related:** R20-AGDA-B-26.3 (closed by the same commit).

#### R20-AGDA-C-27.1. `sameLengthᵇ` hand-rolled [DROP — re-audited 2026-05-17, was DEFER]
- **File:** `src/Aletheia/Parser/Combinators.agda:161-186` (definition + 24-line DO-NOT-RE-RAISE block above it).
- **Finding (Cat 27):** Could be `length xs ≡ᵇ length ys` via stdlib `_≡ᵇ_`.
- **Why DROP:** The proposed swap is NOT a stdlib equivalence — stdlib has no list-length-equality primitive; `_≡ᵇ_` is on `ℕ`.  Routing through `length` changes the runtime profile from O(min(|xs|, |ys|)) parallel walk (short-circuits on first ctor mismatch) to O(|xs| + |ys|) two-pass walk with two intermediate ℕ values built in MAlonzo.  This is `manyHelper`'s per-iteration termination check on the `parseDBCText` runtime path (FFI-exposed via `client.parse_dbc_text`, already O(N²) per `feedback_parsedbc_quadratic_scaling.md`).  Empirical measurement 2026-05-17 on a 200-msg × 4-sig synthetic DBC (44 KB), 5 runs each, via `/tmp/sameLengthb_bench.py`: structural form 10.21s median (σ 0.11s); wrapper form 58.07s median (σ 0.31s) — **5.69× slowdown** for a one-line cosmetic change.  First-principles analysis predicted 2× from the parallel-walk vs two-pass difference; the additional ~2.85× factor is MAlonzo constructor-walk overhead on `length` (each call builds an intermediate ℕ Peano-via-Integer wrapper before the final `_≡ᵇ_` reduces it), confirmed by the fact that the `length`-route allocates whereas the structural recursor compiles to a tight GHC-inlined tail loop.  The 5 derived lemmas (`sameLengthᵇ-cons`, `-cons-cons`, `-lt`, `-len-≢`, `-app-nz` in `DBC/TextParser/Properties/*`) re-type-check unchanged under either definition (the wrapper is definitionally equivalent on list-constructor matches per the advisor's reduction trace; confirmed by a full `check-properties` pass under the wrapper at 12m31s), so the swap yields no proof-side simplification either.  In-source DO-NOT-RE-RAISE comment at `Combinators.agda:161-184` carries the same measurement + rationale.
- **Analytical history (audit-trail-is-the-point per this file's "How to Use" notes):** Filed 2026-05-15 as DEFER with rationale "cascade through ~30+ proof sites".  Re-audited 2026-05-17 (per `feedback_nofix_rationale_incomplete_axis.md` — NO-FIX re-audits ask "what's a different axis?"); the cascade count was overstated (actual: 5 derived lemmas + ~14 use sites in 6 files, all of which re-type-check unchanged on the wrapper).  Re-flipped to FIX, swap implemented + `check-properties` passed clean — confirming definitional equivalence.  Empirical measurement (advisor-prompted, per `feedback_runtime_fix_side_effect_audit.md`) then surfaced the 5.69× runtime cost on the `parseDBCText` path that neither the original DEFER rationale nor the FIX re-flip had analyzed.  Both prior analyses missed the right axis: the proposed swap is a DIFFERENT ALGORITHM, not a stdlib drop-in — the Cat 27 finding conflated "uses a stdlib function in its expansion" with "duplicates a stdlib function."  Final disposition: DROP, with the corrected rationale + measurement preserved in source and here.  Distillation: `feedback_stdlib_equivalence_vs_expansion.md` (new this round).
- **Revisit when:** Stdlib gains a `_≡ᵇ-len_` (or equivalent) list-length-equality primitive with O(min(N,M)) parallel-short-circuit semantics, OR a deeper refactor moves the DBC text parser off `manyHelper`'s per-iteration `sameLengthᵇ` check entirely.

#### R20-AGDA-B-26.1. Dec on parse-time validator [FP-VERIFIED]
- **File:** `src/Aletheia/DBC/Validator/Checks.agda:44,48`
- **Finding:** `_≟ₛ_` / `_≟_` Dec uses on parse-time validator paths.
- **Why FP:** Parse-time validator is a cold path (one-shot at DBC ingest, not per-frame); Cat 26 accepts `Dec` on cold paths.
- **Revisit when:** Validator promoted to a hot path (e.g. per-frame re-validation), OR a Dec-allocation audit surfaces a hot-path caller.

#### R20-AGDA-B-26.2. `lookupByKey` Dec [FP-VERIFIED]
- **File:** `src/Aletheia/Prelude.agda:80-86`
- **Finding:** `if ⌊ k ≟ₛ key ⌋ then …` strips Dec → Bool but the Dec witness is still allocated by `_≟ₛ_`.
- **Why FP:** Cold-path (no per-frame caller); in-source comment at `Prelude.agda:80` documents the "promote-to-hot-path" revisit signal explicitly.
- **Revisit when:** `lookupByKey` is adopted by a hot-path caller. The in-source comment is the trigger.

#### R20-AGDA-D-19.3 / R20-AGDA-D-GA20.1. `nothing≢just` local helper re-invents stdlib [FP-VERIFIED]
- **File:** `src/Aletheia/Protocol/Adequacy/StreamingWarm.agda:91-113` (helper + 13-line in-source DO-NOT-RE-RAISE block added 2026-05-17).
- **Finding:** 3-line local `nothing≢just () = ()` re-invents stdlib `Data.Maybe.Properties.just≢nothing` (modulo sym).
- **Why FP:** The 3-line local absurdity helper is shorter than `≢-sym just≢nothing` + the stdlib import + the sym-wrap; idiomatic per-module absurdity pattern. Stdlib symmetrisation adds an import for negative readability gain.
- **In-source DO-NOT-RE-RAISE block:** `StreamingWarm.agda` immediately above the helper (added 2026-05-17).  Documents the OPPOSITE direction of stdlib's `just≢nothing` (`just v ≡ nothing → ⊥`) and the call-site shape match with the `with`-discrimination at lines 213/215.
- **Revisit when:** A project-wide audit standardises on stdlib imports for absurdity helpers, OR stdlib gains a directly-signatured `nothing≢just`.

#### R20-GO-A-3.6. `StandardID`/`ExtendedID` `Value()` vs typedef accessor asymmetry [DROP]
- **File:** `go/aletheia/types.go:183-197` (`StandardID` definition + 14-line in-source DO-NOT-RE-RAISE block added 2026-05-17 immediately above it; covers `ExtendedID` by reference since the asymmetry is structural to both wrappers).
- **Finding:** Struct wrappers have `Value() uint32` methods; primitive typedefs (`BitPosition`, `BitLength`) use direct conversion (`uint16(bp)`, `uint8(bl)`).
- **Why DROP:** Asymmetry is structural (typedef vs struct), not naming. `Value()` exists on `StandardID`/`ExtendedID` because they wrap an unexported field (enforces `NewStandardID` validation; raw construction is unrepresentable); primitive-typedef conversion is idiomatic Go (cf. `time.Duration → int64`). Adding `Value()` to typedefs gains nothing; demoting wrappers to typedefs loses construction-validation safety.
- **In-source DO-NOT-RE-RAISE block:** `go/aletheia/types.go` immediately above `StandardID` (added 2026-05-17).
- **Revisit when:** Go conventions shift to require accessor parity across typedef-vs-struct, OR the wrappers are converted to typedefs (which would lose strong-typing properties).

#### R20-GO-A-3.7. `lockCh` vs `closeOnce` style split in Client [DROP]
- **File:** `go/aletheia/client.go:44-80` (Client struct definition + 16-line in-source DO-NOT-RE-RAISE block added 2026-05-17 immediately above it).
- **Finding:** Two sync primitives with different naming conventions on the same struct.
- **Why DROP:** Different sync mechanisms. `lockCh` is a 1-deep channel semaphore providing context-aware acquisition via `select { case ch <- struct{}{}: … case <-ctx.Done(): … }` (required by `docs/architecture/CANCELLATION.md` — `sync.Mutex.Lock` has no context-cancellable variant); `closeOnce` is `sync.Once` for one-shot close (idiomatic for double-close safety, clearer than a CAS on `closed`). Consolidating to either alone would lose a capability.
- **In-source DO-NOT-RE-RAISE block:** `go/aletheia/client.go` immediately above the `Client` struct (added 2026-05-17).
- **Revisit when:** Go stdlib gains a unified context-aware-mutex-with-idempotent-close primitive, OR a concurrency-model refactor consolidates the Client.

#### R20-GO-A-4.10. `limits.go` "Mirrored here verbatim" claim lacks CI parity check [DROP]
**✅ RESOLVED 2026-05-15** — flipped from DROP to implemented. `tools/check_limits_parity.py` (Python orchestrator per `feedback_python_over_bash.md`) parses `src/Aletheia/Limits.agda` for the `boundKindCode` mapping + `max-X = N` constants, parses `go/aletheia/limits.go` for `BoundKindX` / `MaxX` mirrors, and diffs both. Wired into `Shakefile.hs` as phony rule `check-limits-parity` AND into `tools/run_ci.py` as offline-enforcer step 12 so the canonical CI sweep runs it. Forward-revert verified: changing `MaxMessagesPerFile = 10000` to `9999` fires the gate; reverted, passes. Current run: 14 numeric constants and 7 BoundKind entries in parity. The original DROP rationale ("not Cat 1/4 hygiene") was correct — but the user's "no NO-FIX in a pre-user project" stance made the cost of building the gate (~250 LOC Python tool) cheaper than the cost of a future silent drift.

- **File:** `go/aletheia/limits.go:7`
- **Finding:** Comment claims values are mirrored from `Aletheia.Limits` but no CI gate enforces parity.
- **Why DROP (2026-05-12, since fixed):** A Shake gate that parses `Aletheia.Limits` and diffs each constant against the binding mirrors is a CI/tooling task, not Cat 1/4 hygiene. Same shape as the "Reproducible build verification" gate proposal in AGENTS.md.
- **Revisit when:** A tooling cluster is opened for CI-level cross-binding parity gates, OR the mirror drifts and silently triggers a real bug.

---

## R19 Phase 2 Carry-Overs (formalised 2026-05-17)

Phase 2 closed 19 of 19 clusters but two cluster-internal deferral lists (cluster 10 — 6 breaking changes; cluster 16 — 6 medium follow-ups) were tracked only in `memory/project_review_round19.md`.  Formalising them here ensures pre-merge audits surface them in the canonical durable index.

**Scope-deferral classification per advisor (2026-05-17):** these items are *planned future work*, not rejected NO-FIX choices.  They get DEFERRALS.md tracking AND a one-line `// R19P2-CL10-N` or `# R19P2-CL16-N` referent in `PARITY_PLAN.md` (Track item) BUT NOT in-source DO-NOT-RE-RAISE blocks (those are reserved for rejected choices per the pattern established by R20-AGDA-B-18.3 / R20-GO-A-3.6 / R20-GO-A-3.7).

### Cluster 10 — 6 breaking changes (cross-binding ergonomics)

#### R19P2-CL10-1. Go `Client.Close()` `io.Closer` parity [✅ RESOLVED]
- **File:** `go/aletheia/client.go:111`
- **Resolution:** `func (c *Client) Close() error` matches `io.Closer`; compile-time assertion `var _ io.Closer = (*Client)(nil)` at `client.go:17` enforces the contract.  Resolved in Phase 2 cluster 10 ship `0425550`.

#### R19P2-CL10-2. Go `BuildFrame`/`UpdateFrame` arg-order asymmetry [DEFER]
- **Files:** `go/aletheia/client.go:488` (`BuildFrame(ctx, id, signals, dlc)`) vs `go/aletheia/client.go:512` (`UpdateFrame(ctx, id, dlc, data, signals)`)
- **Finding:** `dlc` is positionally inconsistent; `signals` slot differs.
- **Why DEFER:** Stylistic cross-binding parity work; affects every call site in tests + binding-internal callers; needs paired cross-binding rename to Python's `build_frame(can_id=, dlc=, signals=)` / C++'s `build_frame(can_id, dlc, signals)` keyword-vs-positional shapes.  Project-wide migration scope per `feedback_no_backward_compat.md` is justifiable but not Phase 5.1-scope.
- **Revisit when:** A "Go API ergonomics cluster" is opened, OR a user reports the asymmetry causes confusion.

#### R19P2-CL10-3. `FormatDBC` return-type rework [DEFER]
- **Files:** `go/aletheia/dbc.go` `FormatDBC` / `FormatDBCText`; mirrored in Python `format_dbc`; C++ `format_dbc`
- **Finding:** Return-type rework (originally a String → structured-result migration) was deferred from cluster 10.
- **Why DEFER:** Structured-result wrapping changes the wire contract across all 3 bindings; benefits proper typing but unclear payoff vs migration cost.
- **Revisit when:** A consumer needs richer return metadata (e.g. structured rendering options) — at which point the migration becomes load-bearing.

#### R19P2-CL10-4. C++ `Rational` `struct` → `class` [DEFER]
- **File:** `cpp/include/aletheia/types.hpp:77`
- **Finding:** Currently `struct Rational { ... }` exposing public `num` / `den` fields; C++ idiom prefers `class` with private fields + accessors when validation invariant exists (cluster 12 added `den > 0` guard).
- **Why DEFER:** Cluster 12's `den > 0` `throw std::invalid_argument` runs at all callers via `Rational::make`, so the `struct` public-field exposure is already gated by the factory path; the cosmetic class promotion gains constructor-discipline but mass-migrates ~28 YAML/Excel/JSON callsites.  Holding pending a C++ ergonomics cluster.
- **Revisit when:** A C++ ergonomics cluster is opened, OR a callsite bypasses the factory and constructs a malformed `Rational` directly.

#### R19P2-CL10-5. C++ Check namespace-vs-static [DEFER]
- **File:** `cpp/include/aletheia/check.hpp:259` (`class Check` inside `namespace aletheia`)
- **Finding:** `class Check` with static-method factory pattern (e.g. `Check::Range(...)`) versus a `namespace aletheia::check` with free functions (`aletheia::check::range(...)`).
- **Why DEFER:** Namespace pattern is more idiomatic C++ for stateless factories; current `class Check` pattern came from a Python-mirror design ("Check.range(...)"). The migration touches every Check callsite in `cpp/tests/` and `cpp/examples/`.  Stylistic.
- **Revisit when:** A C++ idiom-conformance cluster is opened.

#### R19P2-CL10-6. Python `__init__` kwargs-only [DEFER]
- **Files:** `python/aletheia/dsl.py:106` (`Signal.__init__`); `:292` (`Property.__init__`); `:565` (`Predicate.__init__`)
- **Finding:** Public `__init__` methods allow positional args (`Signal("Speed")`); kwargs-only (`Signal(name="Speed")`) would prevent positional-confusion bugs as the API grows.
- **Why DEFER:** Migration breaks every doc-fence and test (`Signal("X")` → `Signal(name="X")`); cross-binding parity already strong-typed via Go/C++ struct construction.
- **Revisit when:** A signature gains an optional positional that could collide with the existing arg (e.g. `Signal(name: str, unit: str = "")` — `Signal("Speed", "km/h")` would silently mis-interpret).

### Cluster 16 — 6 medium follow-ups (Python boundary cleanup)

#### R19P2-CL16-1. `client/_types.py` split into `types.py` + `client/_internals.py` [DEFER]
- **File:** `python/aletheia/client/_types.py` (432 LOC, shrunk organically from earlier ~600 LOC)
- **Finding:** Single `_types.py` mixes public-ish types (e.g. exception hierarchy) with client-internal scaffolding.
- **Why DEFER:** Organic shrinkage during cluster 17 reduced urgency (was ~600 LOC pre-cluster-17, now 432).  Split would route public types via `aletheia.types` re-export which then needs `aletheia.AletheiaError` import-graph review (see CL16-2).
- **Revisit when:** `_types.py` re-grows past ~600 LOC, OR CL16-2 is taken on (it forces a co-decision on AletheiaError canonical path).

#### R19P2-CL16-2. `AletheiaError` duplicate import paths [DEFER]
- **Files:** Canonical at `python/aletheia/client/_types.py:18`; re-exported from `aletheia.AletheiaError` (`__init__.py:68,164`) AND `aletheia.client.AletheiaError` (`client/__init__.py:47,68`).
- **Finding:** Two public paths for the same class; documentation references `from aletheia import AletheiaError`.
- **Why DEFER:** Deprecating `aletheia.client.AletheiaError` is mechanically safe (re-export forwarder) but requires a deprecation warning + downstream user code review.  Project has no current external users so the warning-period is unnecessary, but the canonical-path decision is mostly cosmetic.
- **Revisit when:** First external user lands, OR a documentation sweep clarifies the canonical import paths.

#### R19P2-CL16-3. `is_str_dict` / `is_object_list` underscore-rename [DEFER]
- **Files:** `python/aletheia/_dbc_types.py:19` (`is_str_dict` public re-export); `python/aletheia/_loader_utils.py` (`is_object_list` definition)
- **Finding:** Internal TypeGuard helpers exposed publicly via no-underscore naming; project-internal usage only.
- **Why DEFER:** Mechanical rename + import-site update across ~10 call sites; gain is small (linter/dev-tooling clarity).
- **Revisit when:** First external user lands, OR a `python -m aletheia._loader_utils` discovery surfaces the helpers as confusing public API.

#### R19P2-CL16-4. `normalize_signal` → `_normalize_signal` [DEFER]
- **File:** `python/aletheia/client/_helpers.py:346` (`normalize_signal` public function)
- **Finding:** Internal DBC normaliser exposed publicly; only called by `_helpers.py` itself + tests.
- **Why DEFER:** Mechanical underscore-prefix + import update; same shape as CL16-3.
- **Revisit when:** Co-decided with CL16-3 (boundary-naming sweep).

#### R19P2-CL16-5. optional-extras upper-bound pins [✅ RESOLVED]
- **File:** `python/pyproject.toml`
- **Resolution:** `[project.optional-dependencies]` has explicit upper bounds with documented gate-mapping (`pylint<5` / `basedpyright<2` / `pytest<9` / `pytest-cov<7` / `pytest-markdown-docs<1`) inline as `dev = [...]`'s comment block.

#### R19P2-CL16-6. `client/_helpers.py` 732-LOC split [DEFER — REGRESSED]
- **File:** `python/aletheia/client/_helpers.py` (currently **798 LOC**, was 732 at finding time)
- **Finding:** Original 732-LOC overshoot of the ~700-line guideline; has since grown by 66 LOC.
- **Why DEFER:** Splitting requires identifying coherent sub-modules (currently: DBC normalisation + signal-value coercion + frame-builder helpers + presence-discriminator helpers).  Cluster 17 added cross-cutting helpers (e.g. `_normalize_signal_for_wire`), which increased rather than decreased the file's role count.
- **Revisit when:** `_helpers.py` exceeds 1000 LOC (pylint C0302 default threshold), OR a coherent sub-module emerges from another refactor.

---

## How to Use This File

- **Before a review round:** Check this list to avoid re-raising known deferrals without new justification.
- **When context changes:** If a deferred item's circumstances change (e.g., new MAlonzo compilation strategy, new downstream consumer that hits the weak invariant), move it out of this file and into the active review scope.
- **After a review round:** Add any new NO-FIX / DEFER / DROP items here with full details. **Do not delete resolved items** — annotate them in-place with `✅ RESOLVED <date>` + the resolving commit hash + a short note on whether the original disposition rationale held. The audit trail is the point.
- **Periodic NO-FIX audit:** In a pre-user project, every NO-FIX is suspect — the cost of fixing a phantom invariant before a real user is much lower than after. R6-B9.1 is the worked example. Re-audit periodically (suggested: every 3-5 review rounds) and flip dispositions that no longer survive scrutiny.
