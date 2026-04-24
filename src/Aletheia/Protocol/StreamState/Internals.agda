{-# OPTIONS --safe --without-K #-}

-- Proof-facing internals for the streaming protocol.
--
-- Purpose: Helper functions that are implementation details of handleDataFrame
-- but need to be accessible for proofs in FrameProcessor/Properties.agda.
-- Not part of the public streaming API.
--
-- Exports: Formula indexing (collectAtomsAcc, indexHelper, lookupAtom),
--   signal cache updates (updateSignals, updateCacheFromFrame),
--   PredTable construction (mkPredTable),
--   frame processing helpers (classifyStepResult, stepProperty, dispatchIterResult).
module Aletheia.Protocol.StreamState.Internals where
open import Aletheia.DBC.Types using (signalNameStr)

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Function using (case_of_)
open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal)
open import Aletheia.LTL.Syntax using (LTL; Atomic; Not; And; Or; Next; WNext; Always; Eventually; Until; Release; MetricEventually; MetricAlways; MetricUntil; MetricRelease)
open import Aletheia.LTL.SignalPredicate using (SignalPredicate; TruthVal; True; False; Unknown; SignalCache; updateCache; evalPredicateTV; extractTruthValue)
open import Aletheia.LTL.Incremental using (StepResult; Continue; Violated; Satisfied; Counterexample)
open import Aletheia.LTL.Coalgebra using (LTLProc; PredTable; stepL)
open import Aletheia.LTL.Simplify using (simplify)
open import Aletheia.Protocol.Message using (Response)
open import Aletheia.Protocol.StreamState.Types using (StreamState; Streaming; PropertyState; mkPropertyState)
open import Aletheia.Trace.CANTrace using (TimedFrame)
open import Aletheia.CAN.Frame using (CANFrame)
open import Aletheia.CAN.DBCHelpers using (findMessageById)
open import Aletheia.Protocol.Iteration using (StepOutcome; advance; halt)
open import Aletheia.Protocol.Response as PR using (mkCounterexampleData; PropertyResult)
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
-- DEFERRED REFACTOR (system-review item 11.1): One could replace the ℕ index
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
--   * This is the same failure mode recorded in memory as the "Dec-vs-Bool"
--     regression (commit 5aa345e): replacing a Bool-valued predicate with a
--     Dec-valued one looked free at the type level but allocated proof
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
-- STALE-CACHE SOUNDNESS (finding A28)
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
--   stepProperty dbc cache tf       — evaluates predicates with OLD cache
--   updatedCache = updateCacheFromFrame ...  — updates cache for NEXT frame
-- This ensures that delta predicates (ChangedBy, StableWithin) see the
-- correct previous value (from cache) and current value (from frame),
-- without the cache update interfering with the current frame's evaluation.
--
-- A formal proof of this ordering invariant (R14 finding A9) would require
-- a foundational lemma `updateEntries-self-lookup : lookupEntries name
-- (updateEntries name val ts es) ≡ just (mkCachedSignal val ts)` in
-- Cache/Properties.agda, which does not exist yet.  The proof would then
-- show that for delta predicates, evaluate-before-update preserves distinct
-- old/new values while update-before-evaluate collapses them (2026-04-16).
-- ====================================================================

mkPredTable : DBC → SignalCache → List SignalPredicate → PredTable
mkPredTable dbc cache atoms n frame =
  case lookupAtom atoms n of λ where
    nothing     → Unknown
    (just pred) → evalPredicateTV dbc cache pred (TimedFrame.frame frame)

-- ============================================================================
-- SIGNAL CACHE UPDATES
-- ============================================================================

-- Update cache with all signals from a signal list.
updateSignals : ∀ {n} → DBC → CANFrame n → ℕ → List DBCSignal → SignalCache → SignalCache
updateSignals dbc frame ts [] c = c
updateSignals dbc frame ts (sig ∷ sigs) c =
  let sigName = signalNameStr sig
  in case extractTruthValue sigName dbc frame of λ where
    nothing  → updateSignals dbc frame ts sigs c
    (just v) → updateSignals dbc frame ts sigs (updateCache sigName v ts c)

-- Update cache with all signals extractable from a frame
updateCacheFromFrame : ∀ {n} → DBC → SignalCache → ℕ → CANFrame n → SignalCache
updateCacheFromFrame dbc cache ts frame =
  case findMessageById (CANFrame.id frame) dbc of λ where
    nothing    → cache
    (just msg) → updateSignals dbc frame ts (DBCMessage.signals msg) cache

-- ============================================================================
-- FRAME PROCESSING HELPERS
-- ============================================================================

-- Classify a single stepL result into a StepOutcome.
classifyStepResult : StepResult LTLProc → PropertyState → StepOutcome PropertyState (ℕ × Counterexample)
classifyStepResult (Continue _ newProc) prop =
  advance (mkPropertyState (PropertyState.index prop) (PropertyState.formula prop) (PropertyState.atoms prop) (simplify newProc))
classifyStepResult (Violated ce) prop = halt (PropertyState.index prop , ce)
-- Satisfied: property holds at this step. The property stays in the iteration
-- list and its proc continues being stepped on subsequent frames. This is
-- correct (re-evaluating a satisfied formula is harmless) but wasteful.
-- The LTL type lacks a Top constructor, so there's no trivially-true formula
-- to substitute that wouldn't risk false violations via stepL evaluation.
--
-- Stability argument: once stepL returns Satisfied for a formula, re-stepping
-- the same proc with any subsequent frame also returns Satisfied or Continue.
-- This follows from stepL's structural decomposition: Satisfied is a terminal
-- state for Always/Release (the only safety operators that yield Satisfied),
-- and combining Satisfied with any other StepResult via combineAnd/combineOr
-- preserves or downgrades — it cannot produce Violated. The runL-stepL-satisfied
-- lemma in Coalgebra/Properties.agda formalises the trace-level consequence.
classifyStepResult Satisfied prop = advance prop

-- Step one property: build PredTable, call stepL, classify result.
stepProperty : DBC → SignalCache → TimedFrame → PropertyState → StepOutcome PropertyState (ℕ × Counterexample)
stepProperty dbc cache tf prop =
  let table = mkPredTable dbc cache (PropertyState.atoms prop)
      result = stepL table (PropertyState.proc prop) tf
  in classifyStepResult result prop

-- Dispatch iteration result to StreamState × Response.
dispatchIterResult : DBC → List PropertyState × Maybe (ℕ × Counterexample) → TimedFrame → SignalCache → StreamState × Response
dispatchIterResult dbc (updatedProps , nothing) tf cache =
  (Streaming dbc updatedProps (just tf) cache , Response.Ack)
dispatchIterResult dbc (allProps , just (idx , ce)) tf cache =
  let open Counterexample ce
      ceData = mkCounterexampleData (TimedFrame.timestamp violatingFrame) reason
      violation = PR.PropertyResult.Violation idx ceData
  in (Streaming dbc allProps (just tf) cache , Response.PropertyResponse violation)
