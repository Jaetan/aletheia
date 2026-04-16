{-# OPTIONS --safe --without-K #-}

-- Defunctionalized LTL coalgebra with ℕ-indexed predicates.
--
-- Purpose: Define LTL semantics as "how it reacts to frames",
-- not "what it means". This is the defunctionalization trick that
-- avoids extended lambdas entirely!
--
-- Key insight: We don't define ⟦ φ ⟧ : Stream Frame → Set (semantic predicate).
-- Instead, we define stepL : PredTable → LTLProc → Frame → StepResult LTLProc
-- (operational reaction).
--
-- Design: LTLProc uses ℕ-indexed atomic predicates. A PredTable maps indices
-- to evaluation functions. This enables structural equality on formulas
-- (needed for simplification/dedup) while keeping evaluation parametric.
--
-- Two type universes:
--   Operational: LTL SignalPredicate (JSON, display, user-facing)
--   Proof:       LTLProc (ℕ-indexed, structural equality, stepL target)
-- Bridge: indexFormula (in Protocol.StreamState.Internals) converts the first to the second.

module Aletheia.LTL.Coalgebra where

open import Aletheia.Prelude
open import Aletheia.LTL.Syntax using (LTL; Atomic; Not; And; Or; Next; WNext; Always; Eventually; Until; Release; MetricEventually; MetricAlways; MetricUntil; MetricRelease)
open import Aletheia.LTL.Syntax using (decodeStart; mapLTL)
open import Aletheia.LTL.Incremental using
  ( StepResult; Continue; Violated; Satisfied
  ; Counterexample; mkCounterexample
  ; FinalVerdict; Holds; Fails; Unsure
  ; LTLReason
  ; AtomicFailed; NotStepSatisfied; MetricEventuallyExpired; MetricUntilExpired
  ; NotEosSatisfied; NextNoFrame; EventuallyUnsatisfied; UntilUnsatisfied
  ; MetricEventuallyUnsatisfied; MetricUntilUnsatisfied
  ; AtomicUnresolved
  )
open import Aletheia.LTL.SignalPredicate using (TruthVal; True; False; Unknown; Pending)
open import Aletheia.Trace.CANTrace using (TimedFrame; timestamp; timestampℕ)
open import Data.Nat using (_≤ᵇ_; _⊔_)

-- ============================================================================
-- PREDICATE TABLE
-- ============================================================================

-- Maps predicate indices to evaluation functions.
-- Rebuilt per-frame as a closure (O(1) construction, O(1) lookup).
PredTable : Set
PredTable = ℕ → TimedFrame → TruthVal

-- ============================================================================
-- LTLPROC: LTL with ℕ-indexed predicates (type alias)
-- ============================================================================

-- LTLProc is LTL with ℕ-indexed atomic predicates, enabling structural equality
-- needed for simplification and dedup. A PredTable maps indices to evaluation
-- functions at runtime.

LTLProc : Set
LTLProc = LTL ℕ

-- ============================================================================
-- DENOTATION: LTLProc → LTL (for proof interop with ⟦_⟧)
-- ============================================================================

-- Convert LTLProc to LTL formula for use with denotational semantics.
-- Uses mapLTL to convert ℕ indices to evaluation functions via PredTable.

denot : PredTable → LTLProc → LTL (TimedFrame → TruthVal)
denot table = mapLTL table

-- ============================================================================
-- INITIALIZATION: LTL ℕ → LTLProc (identity)
-- ============================================================================

-- Since LTLProc = LTL ℕ, initialization is the identity function.
-- Kept as a named definition for API compatibility.

initProc : LTL ℕ → LTLProc
initProc φ = φ

-- ============================================================================
-- COMBINE HELPERS: Standard Boolean algebra on StepResult
-- ============================================================================

-- combineAnd/combineOr implement Rosu-style composition on StepResult.
-- Standard Boolean algebra: resolved sides drop (True absorbed in And, False in Or).
-- These are used by And/Or in stepL and by temporal operator decomposition.
--
-- Remaining time: max of both sides (conservative).
-- Counterexample: first-wins (left operand priority).

combineAnd : StepResult LTLProc → StepResult LTLProc → StepResult LTLProc
-- Violated absorbs (short-circuit)
combineAnd (Violated ce) _ = Violated ce
combineAnd _ (Violated ce) = Violated ce
-- Satisfied drops (True is identity for ∧)
combineAnd Satisfied r = r
combineAnd l Satisfied = l
-- Both continue → And wrapper
combineAnd (Continue n₁ a) (Continue n₂ b) = Continue (n₁ ⊔ n₂) (And a b)

combineOr : StepResult LTLProc → StepResult LTLProc → StepResult LTLProc
-- Satisfied absorbs (short-circuit)
combineOr Satisfied _ = Satisfied
combineOr _ Satisfied = Satisfied
-- Violated drops (False is identity for ∨)
combineOr (Violated _) r = r
combineOr l (Violated _) = l
-- Both continue → Or wrapper
combineOr (Continue n₁ a) (Continue n₂ b) = Continue (n₁ ⊔ n₂) (Or a b)

-- ============================================================================
-- METRIC HELPER
-- ============================================================================

-- Elapsed microseconds since a metric operator's window opened.
-- Used by all four metric operators (Eventually/Always/Until/Release) below
-- and re-used by their proof obligations in `Coalgebra/Properties.agda`,
-- `Adequacy.agda`, and `Adequacy/Agreement.agda`. Defined as a top-level
-- function (not a `let`-binding inside `stepL`) so proofs can `with`-abstract
-- on the same syntactic form that `stepL` does.
metricElapsed : ℕ → TimedFrame → ℕ
metricElapsed startTime curr = timestampℕ curr ∸ decodeStart startTime (timestampℕ curr)

-- ============================================================================
-- DEFUNCTIONALIZED STEP SEMANTICS
-- ============================================================================

-- How LTL reacts to one frame.
-- Takes a PredTable for evaluating atomic predicates at ℕ indices.
-- No prev parameter — delta predicates use SignalCache externally.

stepL : PredTable → LTLProc → TimedFrame → StepResult LTLProc

-- Atomic: evaluate predicate via table lookup
stepL table (Atomic n) curr with table n curr
... | True    = Satisfied
... | False   = Violated (mkCounterexample curr AtomicFailed)
... | Unknown = Continue 0 (Atomic n)  -- Signal not yet observed
... | Pending = Continue 0 (Atomic n)  -- Not enough data yet (e.g., first delta observation)

-- Not: invert inner result
stepL table (Not φ) curr
  with stepL table φ curr
... | Continue _ φ' = Continue 0 (Not φ')
... | Violated _ = Satisfied  -- Inner violated means outer satisfied
... | Satisfied = Violated (mkCounterexample curr NotStepSatisfied)

-- And: standard Boolean (resolved sides drop via combineAnd)
stepL table (And φ ψ) curr = combineAnd (stepL table φ curr) (stepL table ψ curr)

-- Or: standard Boolean (resolved sides drop via combineOr)
stepL table (Or φ ψ) curr = combineOr (stepL table φ curr) (stepL table ψ curr)

-- Next: one-step skip (Rosu: prog(Xφ, e) = φ)
-- Skip current frame, inner formula evaluates on remaining trace
stepL table (Next φ) curr = Continue 0 φ

-- WNext: identical to Next mid-stream; differs only at finalization (Holds, not Fails)
stepL table (WNext φ) curr = Continue 0 φ

-- Always: Rosu prog(Gφ, e) = prog(φ,e) ∧ Gφ
stepL table (Always φ) curr = combineAnd (stepL table φ curr) (Continue 0 (Always φ))

-- Eventually: Rosu prog(Fφ, e) = prog(φ,e) ∨ Fφ
stepL table (Eventually φ) curr = combineOr (stepL table φ curr) (Continue 0 (Eventually φ))

-- Until: Rosu prog(φUψ, e) = prog(ψ,e) ∨ (prog(φ,e) ∧ φUψ)
stepL table (Until φ ψ) curr =
  combineOr (stepL table ψ curr) (combineAnd (stepL table φ curr) (Continue 0 (Until φ ψ)))

-- Release: Rosu prog(φRψ, e) = prog(ψ,e) ∧ (prog(φ,e) ∨ φRψ)
stepL table (Release φ ψ) curr =
  combineAnd (stepL table ψ curr) (combineOr (stepL table φ curr) (Continue 0 (Release φ ψ)))

-- All metric operators use `with` (not `if_then_else_`) so the boolean
-- reduces under proof with-abstraction (see SimplifySound / Adequacy proofs).
--
-- MetricEventually: Rosu prog(F[w]φ, e) = prog(φ,e) ∨ F[w]φ (within window)
-- Past window: always Violated (φ-satisfaction outside window doesn't count).
stepL table (MetricEventually windowMicros startTime φ) curr
  with metricElapsed startTime curr ≤ᵇ windowMicros
... | false = Violated (mkCounterexample curr MetricEventuallyExpired)
... | true  = combineOr (stepL table φ curr)
                (Continue (windowMicros ∸ metricElapsed startTime curr)
                          (MetricEventually windowMicros (suc (decodeStart startTime (timestampℕ curr))) φ))

-- MetricAlways: Rosu prog(G[w]φ, e) = prog(φ,e) ∧ G[w]φ (within window)
stepL table (MetricAlways windowMicros startTime φ) curr
  with metricElapsed startTime curr ≤ᵇ windowMicros
... | false = Satisfied  -- Window complete, always held
... | true  = combineAnd (stepL table φ curr)
                (Continue (windowMicros ∸ metricElapsed startTime curr)
                          (MetricAlways windowMicros (suc (decodeStart startTime (timestampℕ curr))) φ))

-- MetricUntil: Rosu prog(U[w](φ,ψ), e) = prog(ψ,e) ∨ (prog(φ,e) ∧ U[w](φ,ψ)) (within window)
-- Past window: always Violated (ψ not satisfied within window).
stepL table (MetricUntil windowMicros startTime φ ψ) curr
  with metricElapsed startTime curr ≤ᵇ windowMicros
... | false = Violated (mkCounterexample curr MetricUntilExpired)
... | true  = combineOr (stepL table ψ curr)
                (combineAnd (stepL table φ curr)
                  (Continue (windowMicros ∸ metricElapsed startTime curr)
                            (MetricUntil windowMicros (suc (decodeStart startTime (timestampℕ curr))) φ ψ)))

-- MetricRelease: Rosu prog(R[w](φ,ψ), e) = prog(ψ,e) ∧ (prog(φ,e) ∨ R[w](φ,ψ)) (within window)
stepL table (MetricRelease windowMicros startTime φ ψ) curr
  with metricElapsed startTime curr ≤ᵇ windowMicros
... | false = Satisfied  -- Window complete, ψ held throughout
... | true  = combineAnd (stepL table ψ curr)
                (combineOr (stepL table φ curr)
                  (Continue (windowMicros ∸ metricElapsed startTime curr)
                            (MetricRelease windowMicros (suc (decodeStart startTime (timestampℕ curr))) φ ψ)))

-- ============================================================================
-- END-OF-STREAM FINALIZATION
-- ============================================================================

-- Determine the final verdict for a formula that was still in Continue
-- state when the stream ended.
--
-- Key principle: LTLProc never stores terminal states (those are returned
-- as Violated/Satisfied directly). So finalizeL only handles active formulas.
-- Note: finalizeL does NOT need PredTable — it depends only on formula structure.

finalizeL : LTLProc → FinalVerdict

-- Atomic still active at end-of-stream → Unknown (Kleene three-valued).
-- Previously emitted Fails, which was denotationally sound via sound-m-unk
-- but user-surprising for properties like Always(p) where p's signal was
-- never observed. Unsure carries the same reason string but converts to
-- Unknown under verdictToSV, aligning with ⟦ Atomic p ⟧ [] = Unknown.
finalizeL (Atomic _) = Unsure AtomicUnresolved

-- Propositional: compose inner results via three-valued Kleene K3 logic.
-- Not: swap Holds↔Fails, Unsure is fixed point.
-- And: Fails (⊥) absorbs, Holds (⊤) is identity, Unsure propagates.
-- Or:  Holds (⊤) absorbs, Fails (⊥) is identity, Unsure propagates.
finalizeL (Not φ) with finalizeL φ
... | Holds    = Fails NotEosSatisfied
... | Fails _  = Holds
... | Unsure r = Unsure r

finalizeL (And φ ψ) with finalizeL φ
... | Fails r  = Fails r
... | Holds    with finalizeL ψ
...   | Fails r  = Fails r
...   | Holds    = Holds
...   | Unsure r = Unsure r
finalizeL (And φ ψ) | Unsure r with finalizeL ψ
...   | Fails r' = Fails r'
...   | Holds    = Unsure r
...   | Unsure _ = Unsure r

finalizeL (Or φ ψ) with finalizeL φ
... | Holds    = Holds
... | Fails _  with finalizeL ψ
...   | Holds    = Holds
...   | Fails r  = Fails r
...   | Unsure r = Unsure r
finalizeL (Or φ ψ) | Unsure r with finalizeL ψ
...   | Holds    = Holds
...   | Fails _  = Unsure r
...   | Unsure _ = Unsure r

-- Next: unresolved at end-of-stream → violated (next frame never arrived)
finalizeL (Next _) = Fails NextNoFrame

-- WNext: vacuously holds at end-of-stream (weak obligation — no successor required)
finalizeL (WNext _) = Holds

-- Always (SAFETY): vacuously true per standard LTLf
finalizeL (Always _) = Holds

-- Eventually (LIVENESS): still active → never satisfied
finalizeL (Eventually _) = Fails EventuallyUnsatisfied

-- Until (LIVENESS): ψ must eventually hold; still active → Fails
finalizeL (Until _ _) = Fails UntilUnsatisfied

-- Release (SAFETY): vacuously true per standard LTLf (dual of Until)
finalizeL (Release _ _) = Holds

-- MetricEventually: still active → never satisfied
finalizeL (MetricEventually _ _ _) = Fails MetricEventuallyUnsatisfied

-- MetricAlways (SAFETY): vacuously true per standard LTLf
finalizeL (MetricAlways _ _ _) = Holds

-- MetricUntil: still active → ψ never satisfied
finalizeL (MetricUntil _ _ _ _) = Fails MetricUntilUnsatisfied

-- MetricRelease (SAFETY): vacuously true per standard LTLf (dual of MetricUntil)
finalizeL (MetricRelease _ _ _ _) = Holds

-- Rosu simplification moved to LTL/Simplify.agda (separate concerns)
