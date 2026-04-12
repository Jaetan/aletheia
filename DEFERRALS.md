# Deferred & NO-FIX Review Items

Items explicitly declined or deferred during AGENTS.md review rounds. Each entry records **what**, **where**, **why deferred**, and **what would change the decision**. Resolved items are removed; see git history or `project_system_review_deferred.md` in memory for the full record.

**Last updated:** 2026-04-10 (after review round 6)

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
- **File:** `src/Aletheia/LTL/SignalPredicate/Evaluation.agda:84,98`
- **Finding:** `M.map` (Data.Maybe.map) creates a closure on the cache-fallback path of `evalPredicateTV`.
- **Why NO-FIX:** Low severity — only fires on cache hits (not the primary extraction path). The closure is short-lived. Replacing with a pattern match would be a micro-optimization with no proof impact and would need benchmarking to confirm any improvement.

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
- **File:** `src/Aletheia/LTL/Syntax.agda:45`
- **Finding:** `MetricEventually`, `MetricAlways`, etc. use raw `ℕ` for window size and start time instead of `Timestamp` or a refined type.
- **Why NO-FIX:** Approved NO-FIX from round 5 (item A21). Refining these would cascade through all metric operator proofs in `Coalgebra.agda`, `Coalgebra/Properties.agda`, `Semantics/MTL.agda`, `Adequacy.agda`, and `Agreement.agda`. The ℕ values represent "number of frames" (window) and "frame count since start" (startTime), not wall-clock timestamps — they are dimensionally distinct from `Timestamp μs`.

#### R6-B7.3. `CachedSignal.lastObserved` unrefined ℕ
- **File:** `src/Aletheia/LTL/SignalPredicate/Cache.agda:31`
- **Finding:** `lastObserved : ℕ` is a timestamp but not typed as `Timestamp μs`.
- **Why NO-FIX:** Approved NO-FIX from round 5 (item A23), documented during the Timestamp dimensional refinement (2026-04-08). `lastObserved` is internal bookkeeping — it is compared against frame timestamps but refining it would touch 9 files and reopen `Cache/Properties.agda` proofs for no new dimensional-analysis benefit. The comparison sites already use `timestampℕ` to unwrap `Timestamp μs` to ℕ.

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
- **File:** `src/Aletheia/Protocol/StreamState/Internals.agda:210`
- **Finding:** The Satisfied branch of `classifyStepResult` relies on an informal argument that a satisfied property stays satisfied.
- **Why NO-FIX:** Non-trivial proof effort. `runL-stepL-satisfied` in `Coalgebra/Properties.agda` already covers the safety property (a trace that evaluates to True stays True). The gap is about inner-process stepping behavior (that `stepL` on a `Done True` process stays `Done True`), not trace-level correctness. The claim is true by inspection of `stepL`'s `Done` clause but formalizing it would require threading process-level invariants through the stepping loop.

#### R6-P1.1. `_client.py` 1030 lines (marginal overshoot)
- **File:** `python/aletheia/client/_client.py`
- **Finding:** File is 1030 lines, exceeding the 1000-line guideline by 30 lines.
- **Why NO-FIX:** The file was already decomposed in prior rounds (cache logic, types, protocols all extracted). Further splitting would require passing 4+ fields through a new module boundary (FFI handle, caches, logger, state) for marginal line-count improvement. The 30-line overshoot is from the GD22.1 cross-binding parity fix (sorted iteration).

---

## How to Use This File

- **Before a review round:** Check this list to avoid re-raising known deferrals without new justification.
- **When context changes:** If a deferred item's circumstances change (e.g., new MAlonzo compilation strategy, new downstream consumer that hits the weak invariant), move it out of this file and into the active review scope.
- **After a review round:** Add any new NO-FIX items here with full details. Remove items that get resolved.
