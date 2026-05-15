# Deferred & NO-FIX Review Items

Items explicitly declined or deferred during AGENTS.md review rounds. Each entry records **what**, **where**, **why deferred**, and **what would change the decision**. Resolved items stay in this file with a `✅ RESOLVED` annotation rather than being deleted — NO-FIX in a pre-user project is worth periodic re-audit (worked example: R6-B9.1 was filed NO-FIX 2026-04-10 with a "non-trivial proof effort" rationale; R20 cluster W shipped an operational fix in `c40e3ba` after cluster S discovered the original stability claim was empirically false on raw `Until`/`Release`/`Atomic` shapes).

**Last updated:** 2026-05-15 (R20 closed — entries below; see `memory/project_review_round{11..20}.md` for per-round closure narratives; this revision adds Phase C1 (R6-B7.2 ✅), R20-GO-A-4.10 ✅, and pass-2 audit-trail closures for R5-A11 ✅ / R6-B9.1 ✅ / R6-P1.1 ✅ / R6-B7.3 🟢)

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
- **File:** `src/Aletheia/CAN/Signal.agda:22`
- **Finding:** `bitLength : ℕ` could be `ℕ⁺` to statically prevent zero-length signals.
- **Why NO-FIX:** Type-tightening that cascades through CAN/Signal, CAN/Encoding, CAN/Batch, DBC modules. The DBC validator catches `BitLengthZero` at validation time, and `physicalGate` rejects bitLength=0 for BE signals at parse time. LE bitLength=0 produces a degenerate but non-crashing extraction (0 bits = 0 value). Cost far exceeds benefit.
- **Related:** Round 6 B7.1 (same underlying issue, different angle).

#### R5-A11. `M.map` closure on eval hot path
**✅ RESOLVED in `bf238b3`** (round 11) — the cache-fallback path was rewritten during the round-11 batch sweep that introduced `cachedSignalValue` / `lookupCacheValue`. `getTruthValue` now uses Maybe's `<∣>` alternative (`Evaluation.agda:103-104`) and `evalValuePredicateTV` / `evalDeltaPredicateTV` consume the result via `case … of λ where` (line 108), eliminating the `M.map` closures originally at lines 84/98. Verified 2026-05-15 against current source.

- **File:** `src/Aletheia/LTL/SignalPredicate/Evaluation.agda:84,98`
- **Finding:** `M.map` (Data.Maybe.map) creates a closure on the cache-fallback path of `evalPredicateTV`.
- **Why NO-FIX (2026-04-10):** Low severity — only fires on cache hits (not the primary extraction path). The closure is short-lived. Replacing with a pattern match would be a micro-optimization with no proof impact and would need benchmarking to confirm any improvement.

#### R5-C2. Validation issue codes lack `validation_` prefix
- **File:** `src/Aletheia/Protocol/ResponseFormat.agda:127-142`
- **Finding:** Validation issue codes don't have a domain prefix like error codes do.
- **Why NO-FIX:** Validation codes live in `issues[].code` within `ValidationResponse`, already namespaced by response structure. Error codes need domain prefixes because they share a flat `code` field; validation codes don't. Adding `validation_` would touch 109 occurrences across 12 files for no disambiguation benefit.

---

### Round 6 (2026-04-10)

#### R6-B7.1. `bitLength` admits 0
- **File:** `src/Aletheia/CAN/Signal.agda:24`
- **Finding:** `bitLength : ℕ` allows 0, which is physically meaningless for a CAN signal.
- **Why NO-FIX:** `physicalGate` in `DBC/JSONParser.agda` rejects bitLength=0 for BE signals at parse time. `handleParseDBC` always runs `validateDBCFull` after parsing (line 124), and `checkBitLengthZero` rejects bitLength=0 for ALL byte orders. A DBC with bitLength=0 never enters `ReadyToStream`. Defense in depth at the parse layer would be nice but the validator already gates the data path.
- **Related:** Round 5 B1 (same underlying issue).

#### R6-B7.2. Metric `window`/`startTime` raw ℕ
**✅ RESOLVED 2026-05-15** — Phase C1 cascade lifted `MetricEventually` / `MetricAlways` / `MetricUntil` / `MetricRelease` from `ℕ → ℕ → LTL → LTL` to `Timestamp μs → ℕ → LTL → LTL` (window phantom-typed μs; `startTime` stays ℕ as a suc-encoded sentinel). Files touched: `LTL/Syntax.agda`, `LTL/Coalgebra.agda`, `LTL/Coalgebra/Properties.agda`, `LTL/Simplify.agda`, `LTL/JSON.agda` (parser wraps `mkTs`), `LTL/JSON/Format.agda` + `Properties.agda` (formatter unwraps `tsValue`; roundtrip preserved via Timestamp record η), `LTL/Semantics.agda`, `LTL/Semantics/MTL.agda`, `LTL/Adequacy.agda`, `LTL/Adequacy/Agreement.agda`, `LTL/SimplifySound/Decomposition.agda` (new `≡ᵇ⇒≡-ts` private helper), `Protocol/Adequacy/WarmCache.agda`, `Protocol/FrameProcessor/Properties/Bounded.agda`. Gates: `check-properties` 8m17s clean; `cabal run shake -- build` 2m00s clean; Agda invariants/erasure/fidelity/ffi-exports/bound-enforcement/runbook/changelog all clean; `pytest tests/` 854 passed; check-fidelity 17/17 (FFI smoke through bindings exercises the new constructor types). The R6-B7.2 NO-FIX rationale ("number of frames, not wall-clock") was wrong on the facts — the values ARE microsecond timestamps used in `metricElapsed s curr ≤ᵇ tsValue w` window-check arithmetic. Audit-trail preserved below for future review-round visibility.

- **File:** `src/Aletheia/LTL/Syntax.agda:45`
- **Finding:** `MetricEventually`, `MetricAlways`, etc. use raw `ℕ` for window size and start time instead of `Timestamp` or a refined type.
- **Why NO-FIX (2026-04-10, since invalidated):** Approved NO-FIX from round 5 (item A21). Refining these would cascade through all metric operator proofs in `Coalgebra.agda`, `Coalgebra/Properties.agda`, `Semantics/MTL.agda`, `Adequacy.agda`, and `Agreement.agda`. The ℕ values represent "number of frames" (window) and "frame count since start" (startTime), not wall-clock timestamps — they are dimensionally distinct from `Timestamp μs`.

#### R6-B7.3. `CachedSignal.lastObserved` unrefined ℕ
**🟢 HELD 2026-05-15** — re-audited during Phase C1's adjacent ℕ-→-Timestamp sweep. The in-source rationale block at `Cache.agda:31-36` ("Refactor to `Timestamp μs` only if Cache gains a public API") still holds: the cache is internal bookkeeping, the per-frame hot path benefits from the unwrap-avoidance, and no consumer passes a non-μs value. Hot-path concern reaffirmed by `feedback_hot_path_refactor_benchmark.md`. Disposition unchanged.

- **File:** `src/Aletheia/LTL/SignalPredicate/Cache.agda:31`
- **Finding:** `lastObserved : ℕ` is a timestamp but not typed as `Timestamp μs`.
- **Why NO-FIX (2026-04-10):** Approved NO-FIX from round 5 (item A23), documented during the Timestamp dimensional refinement (2026-04-08). `lastObserved` is internal bookkeeping — it is compared against frame timestamps but refining it would touch 9 files and reopen `Cache/Properties.agda` proofs for no new dimensional-analysis benefit. The comparison sites already use `timestampℕ` to unwrap `Timestamp μs` to ℕ.

#### R6-B7.4. `PropertyState.index` ℕ vs Fin
- **File:** `src/Aletheia/Protocol/StreamState/Types.agda:29`
- **Finding:** `PropertyState.index : ℕ` could be `Fin (length properties)` to prevent out-of-bounds.
- **Why NO-FIX:** Cold-path construction, but the index is read on the violation path in the stepping loop. `Fin → ℕ` conversion would be needed for JSON formatting (property index in violation responses). Cascade through 4+ files for marginal type safety gain. The index is always valid by construction (`initProperties` assigns sequential indices).

#### R6-B8.1. SimplifySound truth-table helpers repetitive (120+ lines)
- **File:** `src/Aletheia/LTL/SimplifySound.agda:340-458`
- **Finding:** Per-verdict helper functions for empty-trace And/Or cases are repetitive.
- **Why NO-FIX:** In-source design note A25 explains why extraction was rejected. The repetition is the price of three-valued Kleene correctness — each helper handles a specific `FinalVerdict` combination, and abstraction would require a higher-order combinator that Agda's termination checker cannot see through (the `with finalizeL a | finalizeL b` scrutinee abstraction limitation documented during Path G).

#### R6-B8.2. SoundOps `sound-and`/`sound-or` repetitive (380 lines each)
- **File:** `src/Aletheia/LTL/Adequacy/SoundOps.agda:92-444`
- **Finding:** `sound-and` and `sound-or` each have ~380 lines of similar structure.
- **Why NO-FIX:** In-source design note A24 explains why a generic `sound-binop` was rejected. The two functions differ in their Kleene truth-table entries, identity elements, and absorption rules. A generic version would need to be parameterized over 9 truth-table entries plus identity/absorption lemmas — the resulting type signature would be longer than the repeated code, and the proof would not be simpler.

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

#### R20-AGDA-B-26.3. `injectHelper` Dec on frame-build hot path [DEFER, RE-DEFER from R19-CARRY-1]
- **File:** `src/Aletheia/CAN/Encoding.agda:128`
- **Finding:** `Dec` dispatch on the per-frame inject path; MAlonzo allocates a Dec witness per call.
- **Why DEFER:** R19 cluster D + F's four-approach probe (direct rewrite / `mkBoundedBitVec` helper restructure / `@0`-with-Bool / `.()`-irrelevance) all hit the `with ... in eq` outer-abstraction barrier per `feedback_with_in_eq_outer_abstraction_barrier.md`. Standalone `@0`-erasure on `ℕToBitVec`'s bound slot shipped in R19 cluster D `471a9ce` (proof witness inside `_<?_`'s `yes`-constructor flows into the MAlonzo-erased slot); the `Dec` wrapper allocation remainder is blocked at the Agda elaboration layer.
- **In-source DEFER block:** `CAN/Encoding.agda:102-118` documents the rationale + cross-references the feedback memory.
- **Revisit when:** upstream Agda lands a fix for `with ... in eq` outer-abstraction, OR the `Dec` dispatch site is eliminated by a different refactor.

#### R20-AGDA-B-18.3. `injectHelper` `no _ = nothing` dead branch [DEFER]
- **File:** `src/Aletheia/CAN/Encoding.agda:130`
- **Finding:** `no` branch reachable post-R19 cluster D `@0`; provably dead under the bound-injection invariant.
- **Why DEFER:** Same `with ... in eq` outer-abstraction barrier as R20-AGDA-B-26.3 blocks branch elimination — promoting `injectHelper` to bypass `Dec` dispatch would close the dead branch but the four-approach probe established the elaboration barrier sits at Agda's `with`-abstraction mechanism, not the witness layer.
- **Related:** R20-AGDA-B-26.3 (same scope).

#### R20-AGDA-B-GA9.1. `injectHelper` canonical where-block on runtime path [DEFER]
- **File:** `src/Aletheia/CAN/Encoding.agda:122-151`
- **Finding:** Where-block hosts the `with` chain whose Dec dispatch + bounded-witness flow cannot be promoted to the `_<ᵇ_` Bool fast path.
- **Why DEFER:** Same scope as R20-AGDA-B-26.3 — the where-block hosts the barrier; closure waits on the same condition.
- **Related:** R20-AGDA-B-26.3.

#### R20-AGDA-C-27.1. `sameLengthᵇ` hand-rolled [DEFER]
- **File:** `src/Aletheia/Parser/Combinators.agda:165-169`
- **Finding:** Could be `length xs ≡ᵇ length ys` via stdlib `Data.Nat.Properties._≡ᵇ_`.
- **Why DEFER:** Structural lemmas downstream (`sameLengthᵇ-cons`, `sameLengthᵇ-app-nz`, `sameLengthᵇ-len-≢` in `DBC/TextParser/Properties/Preamble/Newline.agda` + `ManyRoundtrip.agda`) pattern-match on the definition's clause structure. Swapping to the stdlib form would cascade rewrites through ~30+ proof sites that currently rely on the named structural recursor. High cost, low value.
- **Revisit when:** A larger refactor of the Newline / ManyRoundtrip proof surface is on the agenda — the cascade cost is then amortized against a planned reach.

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
- **File:** `src/Aletheia/Protocol/StreamState/StreamingWarm.agda:91-99`
- **Finding:** 3-line local `nothing≢just () = ()` re-invents stdlib `Data.Maybe.Properties.just≢nothing` (modulo sym).
- **Why FP:** The 3-line local absurdity helper is shorter than `≢-sym just≢nothing` + the stdlib import + the sym-wrap; idiomatic per-module absurdity pattern. Stdlib symmetrisation adds an import for negative readability gain.
- **Revisit when:** A project-wide audit standardises on stdlib imports for absurdity helpers, OR stdlib gains a directly-signatured `nothing≢just`.

#### R20-GO-A-3.6. `StandardID`/`ExtendedID` `Value()` vs typedef accessor asymmetry [DROP]
- **File:** `go/aletheia/types.go:184, 200`
- **Finding:** Struct wrappers have `Value() uint32` methods; primitive typedefs (`BitPosition`, `BitLength`) use direct conversion (`uint16(bp)`, `uint8(bl)`).
- **Why DROP:** Asymmetry is structural (typedef vs struct), not naming. `Value()` exists on `StandardID`/`ExtendedID` because they wrap an unexported field; primitive-typedef conversion is idiomatic Go. Adding `Value()` to typedefs gains nothing.
- **Revisit when:** Go conventions shift to require accessor parity across typedef-vs-struct, OR the wrappers are converted to typedefs (which would lose strong-typing properties).

#### R20-GO-A-3.7. `lockCh` vs `closeOnce` style split in Client [DROP]
- **File:** `go/aletheia/client.go:47-63`
- **Finding:** Two sync primitives with different naming conventions on the same struct.
- **Why DROP:** Different sync mechanisms. `lockCh` is a 1-deep channel semaphore providing context-aware `TryLock` via `select { case ch <- struct{}{}: … case <-ctx.Done(): … }`; `closeOnce` is `sync.Once` for one-shot close. Consolidating either would lose a capability.
- **Revisit when:** Go stdlib gains a unified primitive covering both shapes, OR a concurrency-model refactor consolidates the Client.

#### R20-GO-A-4.10. `limits.go` "Mirrored here verbatim" claim lacks CI parity check [DROP]
**✅ RESOLVED 2026-05-15** — flipped from DROP to implemented. `tools/check_limits_parity.py` (Python orchestrator per `feedback_python_over_bash.md`) parses `src/Aletheia/Limits.agda` for the `boundKindCode` mapping + `max-X = N` constants, parses `go/aletheia/limits.go` for `BoundKindX` / `MaxX` mirrors, and diffs both. Wired into `Shakefile.hs` as phony rule `check-limits-parity` AND into `tools/run_ci.py` as offline-enforcer step 12 so the canonical CI sweep runs it. Forward-revert verified: changing `MaxMessagesPerFile = 10000` to `9999` fires the gate; reverted, passes. Current run: 14 numeric constants and 7 BoundKind entries in parity. The original DROP rationale ("not Cat 1/4 hygiene") was correct — but the user's "no NO-FIX in a pre-user project" stance made the cost of building the gate (~250 LOC Python tool) cheaper than the cost of a future silent drift.

- **File:** `go/aletheia/limits.go:7`
- **Finding:** Comment claims values are mirrored from `Aletheia.Limits` but no CI gate enforces parity.
- **Why DROP (2026-05-12, since fixed):** A Shake gate that parses `Aletheia.Limits` and diffs each constant against the binding mirrors is a CI/tooling task, not Cat 1/4 hygiene. Same shape as the "Reproducible build verification" gate proposal in AGENTS.md.
- **Revisit when:** A tooling cluster is opened for CI-level cross-binding parity gates, OR the mirror drifts and silently triggers a real bug.

---

## How to Use This File

- **Before a review round:** Check this list to avoid re-raising known deferrals without new justification.
- **When context changes:** If a deferred item's circumstances change (e.g., new MAlonzo compilation strategy, new downstream consumer that hits the weak invariant), move it out of this file and into the active review scope.
- **After a review round:** Add any new NO-FIX / DEFER / DROP items here with full details. **Do not delete resolved items** — annotate them in-place with `✅ RESOLVED <date>` + the resolving commit hash + a short note on whether the original disposition rationale held. The audit trail is the point.
- **Periodic NO-FIX audit:** In a pre-user project, every NO-FIX is suspect — the cost of fixing a phantom invariant before a real user is much lower than after. R6-B9.1 is the worked example. Re-audit periodically (suggested: every 3-5 review rounds) and flip dispositions that no longer survive scrutiny.
