-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Proof-facing internals for the streaming protocol.
--
-- Purpose: Helper functions that are implementation details of handleDataFrame
-- but need to be accessible for proofs in FrameProcessor/Properties.agda.
-- Not part of the public streaming API.
--
-- Exports: Formula indexing (collectAtomsAcc, indexHelper, lookupAtom),
--   shared per-frame extraction table (extractTable, cacheFromTable) and the
--   signal cache update (updateCacheFromFrame),
--   PredTable construction (mkPredTable spec, mkPredTableT runtime),
--   frame processing helpers (classifyStepResult, stepProperty, dispatchIterResult).
module Aletheia.Protocol.StreamState.Internals where
open import Aletheia.DBC.Identifier using (_≡csᵇ_)

open import Data.List using (List; []; _∷_; map; concatMap) renaming (_++_ to _++ₗ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; toℕ)
open import Data.Product using (_×_; _,_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Char using (Char)
open import Function using (case_of_)
open import Aletheia.DBC.Types using (DBC)
open import Aletheia.LTL.Syntax using (LTL; Atomic; Not; And; Or; Next; WNext; Always; Eventually; Until; Release; MetricEventually; MetricAlways; MetricUntil; MetricRelease)
open import Aletheia.LTL.SignalPredicate using (SignalPredicate; Unknown; SignalCache; updateCache; evalPredicateTV; evalPredicateTVT; extractTruthValue; signalOf; ExtractTable)
open import Aletheia.LTL.Incremental using (StepResult; Continue; Violated; Satisfied; Counterexample)
open import Aletheia.LTL.Coalgebra using (LTLProc; PredTable; stepL)
open import Aletheia.LTL.Simplify using (simplify)
open import Aletheia.Protocol.Message using (Response)
open import Aletheia.Protocol.StreamState.Types using (StreamState; Streaming; PropertyState; mkPropertyState)
open import Aletheia.Trace.CANTrace using (TimedFrame)
open import Aletheia.Trace.Time using (Timestamp; μs)
open import Aletheia.CAN.Frame using (CANFrame)
open import Aletheia.Protocol.Iteration using (StepOutcome; advance; halt; complete)
open import Aletheia.Protocol.Response as PR using (mkCounterexampleData)
open import Aletheia.Prelude using (listIndex)

-- ============================================================================
-- FORMULA INDEXING (LTL SignalPredicate → LTLProc + atom list)
-- ============================================================================

-- Collect all atomic predicates in left-to-right tree order (O(n) via accumulator).
-- Structurally polymorphic in the atom type: only LTL shape, no SignalPredicate
-- operations, are used. Specialized via `collectAtoms` below.
collectAtomsAcc : ∀ {α} → LTL α → List α → List α
collectAtomsAcc (Atomic a)                 acc = a ∷ acc
collectAtomsAcc (Not φ)                    acc = collectAtomsAcc φ acc
collectAtomsAcc (And φ ψ)                  acc = collectAtomsAcc φ (collectAtomsAcc ψ acc)
collectAtomsAcc (Or φ ψ)                   acc = collectAtomsAcc φ (collectAtomsAcc ψ acc)
collectAtomsAcc (Next φ)                   acc = collectAtomsAcc φ acc
collectAtomsAcc (WNext φ)                  acc = collectAtomsAcc φ acc
collectAtomsAcc (Always φ)                 acc = collectAtomsAcc φ acc
collectAtomsAcc (Eventually φ)             acc = collectAtomsAcc φ acc
collectAtomsAcc (Until φ ψ)                acc = collectAtomsAcc φ (collectAtomsAcc ψ acc)
collectAtomsAcc (Release φ ψ)              acc = collectAtomsAcc φ (collectAtomsAcc ψ acc)
collectAtomsAcc (MetricEventually _ _ φ)   acc = collectAtomsAcc φ acc
collectAtomsAcc (MetricAlways _ _ φ)       acc = collectAtomsAcc φ acc
collectAtomsAcc (MetricUntil _ _ φ ψ)      acc = collectAtomsAcc φ (collectAtomsAcc ψ acc)
collectAtomsAcc (MetricRelease _ _ φ ψ)    acc = collectAtomsAcc φ (collectAtomsAcc ψ acc)

-- The resulting list maps ℕ indices to predicates for PredTable construction.
collectAtoms : LTL SignalPredicate → List SignalPredicate
collectAtoms formula = collectAtomsAcc formula []

-- Replace each atom with its position index (counter-based, matches collectAtoms order)
indexHelper : LTL SignalPredicate → ℕ → LTL ℕ × ℕ
indexHelper (Atomic _) n            = (Atomic n , suc n)
indexHelper (Not φ) n               = let (φ' , n') = indexHelper φ n in (Not φ' , n')
indexHelper (And φ ψ) n             = let (φ' , n') = indexHelper φ n ; (ψ' , n'') = indexHelper ψ n' in (And φ' ψ' , n'')
indexHelper (Or φ ψ) n              = let (φ' , n') = indexHelper φ n ; (ψ' , n'') = indexHelper ψ n' in (Or φ' ψ' , n'')
indexHelper (Next φ) n              = let (φ' , n') = indexHelper φ n in (Next φ' , n')
indexHelper (WNext φ) n             = let (φ' , n') = indexHelper φ n in (WNext φ' , n')
indexHelper (Always φ) n            = let (φ' , n') = indexHelper φ n in (Always φ' , n')
indexHelper (Eventually φ) n        = let (φ' , n') = indexHelper φ n in (Eventually φ' , n')
indexHelper (Until φ ψ) n           = let (φ' , n') = indexHelper φ n ; (ψ' , n'') = indexHelper ψ n' in (Until φ' ψ' , n'')
indexHelper (Release φ ψ) n         = let (φ' , n') = indexHelper φ n ; (ψ' , n'') = indexHelper ψ n' in (Release φ' ψ' , n'')
indexHelper (MetricEventually w s φ) n    = let (φ' , n') = indexHelper φ n in (MetricEventually w s φ' , n')
indexHelper (MetricAlways w s φ) n        = let (φ' , n') = indexHelper φ n in (MetricAlways w s φ' , n')
indexHelper (MetricUntil w s φ ψ) n      = let (φ' , n') = indexHelper φ n ; (ψ' , n'') = indexHelper ψ n' in (MetricUntil w s φ' ψ' , n'')
indexHelper (MetricRelease w s φ ψ) n    = let (φ' , n') = indexHelper φ n ; (ψ' , n'') = indexHelper ψ n' in (MetricRelease w s φ' ψ' , n'')

indexFormula : LTL SignalPredicate → LTL ℕ
indexFormula φ = Data.Product.proj₁ (indexHelper φ 0)

-- Safe list indexing by ℕ (delegates to Prelude.listIndex with flipped args)
lookupAtom : List SignalPredicate → ℕ → Maybe SignalPredicate
lookupAtom xs n = listIndex n xs

-- Build PredTable from atom list + DBC + SignalCache.
-- The table maps predicate indices to evaluation functions.
--
-- The `nothing → Unknown` branch is dead code: all atom indices in a stepped
-- formula are in [0, length atoms) by construction. collectAtoms assigns
-- indices sequentially, indexFormula preserves them, and neither simplify
-- nor stepL introduces new Atom indices. Proven in
-- FrameProcessor/Properties.agda Property 27 (indexFormula-bound,
-- simplify-bound, stepL-bound, mkPredTable-bounded).
--
-- DEFERRED REFACTOR: One could replace the ℕ index
-- with `Fin (length atoms)` and make the nothing-branch structurally
-- impossible. This is a structural improvement, not a bug fix — Property 27
-- already closes the soundness gap propositionally — but it has a real
-- performance hazard on the hot path, so it is deliberately NOT done:
--
--   * MAlonzo compiles `Fin n` as a unary Peano chain:
--     `data T_Fin_10 = C_zero_12 | C_suc_16 T_Fin_10`. Every index value is
--     k heap-allocated constructor cells for `Fin k`; pattern matching costs
--     one heap dereference per step.
--   * The current ℕ index compiles via the BUILTIN pragma to Haskell
--     `Integer`, so `zero`/`suc` become `eqInt 0` / `subInt 1` — native ops
--     with no per-step allocation. `listIndex` (the engine of `lookupAtom`)
--     currently benefits from this.
--   * `mkPredTable` is called once per frame in the streaming loop, and its
--     returned closure is invoked by `stepL` for every Atomic cell reached
--     in the step. Any constant-factor slowdown to atom lookup lands
--     squarely on Stream LTL throughput.
--   * Same failure mode as the "Dec-vs-Bool" regression: replacing a
--     Bool-valued predicate with a Dec-valued one looks free at the type
--     level but allocates proof
--     terms per call and cost 30–65% throughput until reverted with an
--     equivalence-proven Bool fast path. Type-level strengthening in a
--     MAlonzo hot path warrants a benchmark before commit, not after.
--
-- Additional costs if this refactor is ever scheduled:
--   * Threading `length atoms` through `PredTable`, `stepL`, `runL`, `denot`
--     and all their callers (~8 files).
--   * The four-valued `agreement` theorem signature would have to change
--     shape to carry the bound.
--   * AletheiaFFI.hs would need re-verification of MAlonzo constructor
--     mangling.
--
-- Recommendation for future reviewers: leave this alone unless you have a
-- concrete reason beyond "the nothing branch is dead" (Property 27 already
-- says that). If you do pursue it, run
-- `benchmarks/run_all.sh --frames 10000 --runs 5 --bench throughput` across
-- all three benchmarks BEFORE committing, and be ready to fall back to a
-- Bool/ℕ fast path if Stream LTL regresses.
-- ====================================================================
-- STALE-CACHE SOUNDNESS
-- ====================================================================
--
-- The signal cache can become "stale": a signal observed N frames ago
-- may not appear in subsequent frames (different CAN ID). When
-- `evalPredicateTV` falls back to the cache via `getTruthValue`:
--
--   getTruthValue sigName dbc cache frame =
--     case extractTruthValue sigName dbc frame of
--       just v  → just v          -- prefer live extraction
--       nothing → map CachedSignal.value (lookupCache sigName cache)
--
-- the evaluation uses the most recent observed value. This is SOUND
-- by CAN bus semantics: signal values persist until the next message
-- carrying that signal. The cache stores the last definite observation,
-- so a stale cache entry is the correct last-known value.
--
-- Three cases:
--   1. Signal present in current frame → extracted directly, cache ignored.
--   2. Signal absent but in cache → cached value used; evalPredicateTV
--      returns a definite True/False (not Unknown). Sound because the
--      cached value IS the signal's current value under CAN persistence.
--   3. Signal never observed → cache miss; evalPredicateTV returns
--      Unknown. The coalgebra's stepL maps Unknown → Continue (formula
--      remains active), which is trivially sound: no definite verdict
--      is produced from missing data.
--
-- The formal proof chain for cases 1-2 is:
--   evalPredicate-cache-definite  (Evaluation/Properties.agda)
--     — cache hit ⇒ any predicate returns True or False
--   lookupAtom-warm               (Adequacy/WarmCache.agda)
--     — all atom indices have warm cache entries
--   warm-cache-table-definite     (Adequacy/WarmCache.agda)
--     — mkPredTable returns True/False when cache is warm
--   warm-cache-agreement          (Adequacy/WarmCache.agda)
--     — composes with adequacy for the main soundness theorem
--
-- The key invariant maintained by handleDataFrame in StreamState.agda is
-- the "evaluate then update" ordering:
--   stepProperty dbc table cache tf         — evaluates predicates with OLD cache
--   updatedCache = cacheFromTable ts table cache  — updates cache for NEXT frame
-- Both consume the same per-frame extraction `table`, but predicate evaluation
-- reads the OLD cache for the last-known-value fallback while the cache update
-- produces the cache for the NEXT frame.  This ensures that delta predicates
-- (ChangedBy, StableWithin) see the correct previous value (from the old cache)
-- and current value (from the table), without the cache update interfering with
-- the current frame's evaluation.
--
-- A formal proof of this ordering invariant is open: it
-- would require a foundational lemma `updateEntries-self-lookup :
-- lookupEntries name (updateEntries name val ts es) ≡ just (mkCachedSignal
-- val ts)` in `Cache/Properties.agda`, then show that for delta predicates
-- evaluate-before-update preserves distinct old/new values while
-- update-before-evaluate collapses them.
-- ====================================================================

mkPredTable : DBC → SignalCache → List SignalPredicate → PredTable
mkPredTable dbc cache atoms n frame =
  case lookupAtom atoms n of λ where
    nothing     → Unknown
    (just pred) → evalPredicateTV dbc cache pred (TimedFrame.frame frame)

-- Runtime PredTable driven by the shared per-frame extraction table.
-- Mirrors `mkPredTable` but reads each atom's signal value from `table`
-- (`evalPredicateTVT`) instead of re-extracting from `frame` — the streaming
-- step builds `table` once per accepted frame and shares it with the cache
-- update.  `dbc` and the per-index `frame` are unused (the extraction is
-- already in `table`); the signature keeps `mkPredTable`'s shape so the two
-- tables are pointwise comparable.  `mkPredTable` itself is retained as the
-- adequacy spec (Adequacy.WarmCache / streaming-adequacy reason about it).
mkPredTableT : ExtractTable → DBC → SignalCache → List SignalPredicate → PredTable
mkPredTableT table dbc cache atoms n frame =
  case lookupAtom atoms n of λ where
    nothing     → Unknown
    (just pred) → evalPredicateTVT table cache pred

-- ============================================================================
-- SIGNAL CACHE UPDATES
-- ============================================================================

-- ── Shared per-frame extraction table (bounded residency + extract-once) ─────
--
-- A cached signal value is only ever CONSULTED for a signal that some active
-- predicate's atom targets: `mkPredTableT`/`evalPredicateTVT` read the cache as
-- the last-known-value fallback for an atom's signal, and `collectUncachedWarnings`
-- looks up each atom's signal at EndStream — both key on `signalOf(atom)` over
-- the active `PropertyState.atoms`.  Every other signal a frame carries is
-- cached-but-never-read.
--
-- `readableSignals` derives the exact set of consultable signal names from the
-- active property atoms.  `extractTable` runs `extractTruthValue` once per
-- readable name and keeps the successes; the SAME table then warms the cache
-- (`cacheFromTable`) AND drives predicate evaluation (`mkPredTableT`).  This is
-- observationally identical to extracting per consumer: a name-keyed entry's
-- value is a pure function of the name (`extractTruthValue name dbc frame`), so
-- every consumer that consults a readable name reads the same value it would
-- have re-extracted, and the readable set never drifts narrower than the readers
-- because it is DERIVED from the atoms.  Soundness rests on `props` being
-- invariant over the cache's whole lifetime: the only transitions that change
-- the property set (`handleSetProperties`, DBC (re)load) reset the cache to
-- `emptyCache`, and `SetProperties` is rejected mid-stream — machine-checked by
-- `handleSetProperties-streaming-rejected` (`FrameProcessor.Properties.Handlers`),
-- which proves `handleSetProperties` on a `Streaming` state returns that state
-- verbatim with a `StreamActive` error.  So a signal that becomes readable later
-- is never read against a cache that predates it.

-- Bool membership of a signal name in the readable set (≡csᵇ fast path — never
-- `Dec`, which would allocate a proof term per signal per frame on the hot path).
-- Retained for the proof surface (`readableSignals` coverage / `AllReadable`);
-- the runtime table build no longer needs a membership test.
_∈ᵇ_ : List Char → List (List Char) → Bool
name ∈ᵇ []       = false
name ∈ᵇ (x ∷ xs) = if name ≡csᵇ x then true else name ∈ᵇ xs

-- The signal names any active predicate can read: the union over the active
-- properties of each atom's target signal.  Recomputed per frame from `props`
-- (carried by the `Streaming` constructor) so no `StreamState` field is added.
readableSignals : ∀ {n} → List (PropertyState n) → List (List Char)
readableSignals props = concatMap (λ p → map signalOf (PropertyState.atoms p)) props

-- Extract the readable-name list from the frame into a name-keyed table of
-- successes.  A name is kept iff `extractTruthValue name dbc frame ≡ just v`;
-- failures are dropped.  The list is `readableSignals props` (a plain
-- concatenation, so a signal read by several atoms appears — and is extracted —
-- once per occurrence, not deduplicated).  This is the single extraction pass
-- the streaming step shares between the cache update and predicate eval,
-- replacing the previous two independent passes.
extractTable : ∀ {n} → DBC → CANFrame n → List (List Char) → ExtractTable
extractTable dbc frame []             = []
extractTable dbc frame (name ∷ names) =
  case extractTruthValue name dbc frame of λ where
    nothing  → extractTable dbc frame names
    (just v) → (name , v) ∷ extractTable dbc frame names

-- Fold the extraction table into the cache (last-writer-wins per `updateCache`,
-- one shared timestamp).  Warms exactly the readable names the table recorded.
cacheFromTable : Timestamp μs → ExtractTable → SignalCache → SignalCache
cacheFromTable ts []               cache = cache
cacheFromTable ts ((name , v) ∷ rest) cache =
  cacheFromTable ts rest (updateCache name v ts cache)

-- Update cache with the readable signals extractable from a frame, via the
-- shared extraction table.  Takes the readable-name list as a parameter; the
-- body folds the table rather than re-extracting per signal, so the streaming
-- step passes the same table into predicate evaluation without a second
-- extraction pass.  The result is definitionally `cacheFromTable` of the
-- table, which the frame-processor proofs name directly.
updateCacheFromFrame : ∀ {n} → DBC → SignalCache → Timestamp μs → CANFrame n → List (List Char) → SignalCache
updateCacheFromFrame dbc cache ts frame readable =
  cacheFromTable ts (extractTable dbc frame readable) cache

-- ============================================================================
-- FRAME PROCESSING HELPERS
-- ============================================================================

-- Classify a single stepL result into a StepOutcome.  The third type
-- parameter `Fin n` is the completion payload: when a property becomes
-- Satisfied mid-stream it is dropped from the active set (per the
-- `complete` semantics), and the index flows out via `iterate`'s
-- completion-list so `dispatchIterResult` can emit a
-- `PropertyResult.Satisfaction` at the frame where the property
-- completed.  The index MUST flow out here: a completed property leaves the
-- active set, and EndStream's `finalizeL` walks only the survivors — so a
-- mid-stream Satisfaction not emitted here never reaches the wire at all.
classifyStepResult : ∀ {n} → StepResult LTLProc → PropertyState n
                   → StepOutcome (PropertyState n) (Fin n × Counterexample) (Fin n)
classifyStepResult (Continue _ newProc) prop =
  advance (mkPropertyState (PropertyState.index prop) (PropertyState.formula prop) (PropertyState.atoms prop) (simplify newProc))
classifyStepResult (Violated ce) prop = halt (PropertyState.index prop , ce)
-- Satisfied: property holds at this step.  The property is dropped from
-- the iteration list (`complete` outcome carrying its index) so its
-- proc is NOT re-evaluated on subsequent frames, AND the index flows
-- through `iterate`'s completion-list to `dispatchIterResult` for
-- mid-stream `PropertyResult.Satisfaction` emission.
--
-- Why drop instead of advance: re-evaluating a Satisfied proc on the
-- next frame is unsound for top-level `Until`, `Release`, `MetricUntil`,
-- `MetricRelease`, raw `Atomic`, or `And`/`Or`-of-atomic shapes.  Concrete
-- witness: `Until (Atomic 0) (Atomic 1)` with `table 1 y₁ = True` returns
-- `Satisfied` at y₁; with both atoms False at y₂ it returns `Violated`
-- (via `combineOr (Violated _) (Violated _) = Violated`).  Under a prior
-- `advance prop` design this would emit a false counterexample on y₂ for
-- a property already declared satisfied.  The `complete` outcome closes
-- the gap structurally — once a property is satisfied, no further frame
-- can flip the verdict because the proc is no longer in the active set.
--
-- Active-set monotonicity: `Aletheia.Protocol.Iteration.length-specResult-≤`
-- proves the post-iteration list is no longer than the input.  The
-- streaming runtime relies on this to argue that the active set shrinks
-- monotonically with `Satisfied` transitions; combined with `halt`
-- (Violated) terminating iteration, the active set never grows without
-- explicit user input (a fresh `SetProperties` reseeds it).
--
-- Shape characterizations in `Aletheia.LTL.Coalgebra.Properties` pin down
-- which user surfaces never trigger the drop:
--   * `stepL-always-never-satisfied`: `stepL (Always φ) y ≢ Satisfied`,
--     so `Always`-wrapped properties (the canonical CAN safety pattern)
--     never `complete` — they run for the entire stream.
--   * `stepL-eventually-never-violated`: `stepL (Eventually φ) y ≢
--     Violated ce`, so `Eventually`-wrapped properties (the canonical
--     liveness pattern) never `halt` — they `complete` cleanly on first
--     witness or stay `Continue` until EndStream.
classifyStepResult Satisfied prop = complete (PropertyState.index prop)

-- Step one property: build the runtime PredTable from the shared extraction
-- table, call stepL, classify result.  The `table` is built once per accepted
-- frame in `handleDataFrame` and shared across every property (and the cache
-- update), so no property re-extracts.
stepProperty : ∀ {n} → DBC → ExtractTable → SignalCache → TimedFrame → PropertyState n
             → StepOutcome (PropertyState n) (Fin n × Counterexample) (Fin n)
stepProperty dbc table cache tf prop =
  let ptable = mkPredTableT table dbc cache (PropertyState.atoms prop)
      result = stepL ptable (PropertyState.proc prop) tf
  in classifyStepResult result prop

-- Dispatch iteration result to StreamState × Response.  Iterator returns
-- `(survivors , Maybe halt , List Fin)`: completions carry property
-- indices so this dispatcher can emit one
-- `PropertyResult.Satisfaction` per completion in source-order,
-- co-emitted with any violation that halted the iteration on the same
-- frame.  `Fin n → ℕ` conversion via `toℕ` is at the wire boundary only;
-- the internal pipeline keeps `Fin n` throughout.
--
-- Wire shape: `Response.PropertyResponse` carries `List PropertyResult`.
-- Empty list is unreachable here — when there are no events on a frame
-- we emit `Response.Ack` instead (so single-event frames remain
-- single-element lists, never empty).
dispatchIterResult : ∀ {n} → DBC
                  → List (PropertyState n) × Maybe (Fin n × Counterexample) × List (Fin n)
                  → TimedFrame → SignalCache → StreamState × Response
dispatchIterResult {n} dbc (updatedProps , nothing , []) tf cache =
  (Streaming n dbc updatedProps (just tf) cache , Response.Ack)
dispatchIterResult {n} dbc (updatedProps , nothing , c ∷ cs) tf cache =
  let satisfactions = map (λ i → PR.PropertyResult.Satisfaction (toℕ i)) (c ∷ cs)
  in (Streaming n dbc updatedProps (just tf) cache , Response.PropertyResponse satisfactions)
dispatchIterResult {n} dbc (allProps , just (idx , ce) , completions) tf cache =
  let open Counterexample ce
      ceData = mkCounterexampleData (TimedFrame.timestamp violatingFrame) reason
      satisfactions = map (λ i → PR.PropertyResult.Satisfaction (toℕ i)) completions
      violation = PR.PropertyResult.Violation (toℕ idx) ceData
      -- Source-order: completions encountered BEFORE the halt come first;
      -- the violation closes the batch.
      results = satisfactions ++ₗ (violation ∷ [])
  in (Streaming n dbc allProps (just tf) cache , Response.PropertyResponse results)
