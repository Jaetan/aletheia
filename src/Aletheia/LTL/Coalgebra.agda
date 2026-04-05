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
-- Bridge: indexFormula (in Protocol.StreamState) converts the first to the second.

module Aletheia.LTL.Coalgebra where

open import Aletheia.Prelude
open import Aletheia.LTL.Syntax using (LTL; Atomic; Not; And; Or; Next; Always; Eventually; Until; Release; MetricEventually; MetricAlways; MetricUntil; MetricRelease) public
open import Aletheia.LTL.Syntax using (decodeStart; mapLTL)
open import Aletheia.LTL.Incremental using (StepResult; Continue; Violated; Satisfied; Counterexample; mkCounterexample; FinalVerdict; Holds; Fails)
open import Aletheia.LTL.SignalPredicate using (TruthVal; True; False; Unknown; Pending)
open import Aletheia.Trace.CANTrace using (TimedFrame; timestamp)
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
-- DEFUNCTIONALIZED STEP SEMANTICS
-- ============================================================================

-- How LTL reacts to one frame.
-- Takes a PredTable for evaluating atomic predicates at ℕ indices.
-- No prev parameter — delta predicates use SignalCache externally.

stepL : PredTable → LTLProc → TimedFrame → StepResult LTLProc

-- Atomic: evaluate predicate via table lookup
stepL table (Atomic n) curr with table n curr
... | True    = Satisfied
... | False   = Violated (mkCounterexample curr "Atomic: predicate failed")
... | Unknown = Continue 0 (Atomic n)  -- Signal not yet observed
... | Pending = Continue 0 (Atomic n)  -- Not enough data yet (e.g., first delta observation)

-- Not: invert inner result
stepL table (Not φ) curr
  with stepL table φ curr
... | Continue _ φ' = Continue 0 (Not φ')
... | Violated _ = Satisfied  -- Inner violated means outer satisfied
... | Satisfied = Violated (mkCounterexample curr "Not: inner formula satisfied")

-- And: standard Boolean (resolved sides drop via combineAnd)
stepL table (And φ ψ) curr = combineAnd (stepL table φ curr) (stepL table ψ curr)

-- Or: standard Boolean (resolved sides drop via combineOr)
stepL table (Or φ ψ) curr = combineOr (stepL table φ curr) (stepL table ψ curr)

-- Next: one-step skip (Rosu: prog(Xφ, e) = φ)
-- Skip current frame, inner formula evaluates on remaining trace
stepL table (Next φ) curr = Continue 0 φ

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
  with (timestamp curr ∸ decodeStart startTime (timestamp curr)) ≤ᵇ windowMicros
... | false = Violated (mkCounterexample curr "MetricEventually: window expired")
... | true  = combineOr (stepL table φ curr)
                (Continue (windowMicros ∸ (timestamp curr ∸ decodeStart startTime (timestamp curr)))
                          (MetricEventually windowMicros (suc (decodeStart startTime (timestamp curr))) φ))

-- MetricAlways: Rosu prog(G[w]φ, e) = prog(φ,e) ∧ G[w]φ (within window)
stepL table (MetricAlways windowMicros startTime φ) curr
  with (timestamp curr ∸ decodeStart startTime (timestamp curr)) ≤ᵇ windowMicros
... | false = Satisfied  -- Window complete, always held
... | true  = combineAnd (stepL table φ curr)
                (Continue (windowMicros ∸ (timestamp curr ∸ decodeStart startTime (timestamp curr)))
                          (MetricAlways windowMicros (suc (decodeStart startTime (timestamp curr))) φ))

-- MetricUntil: Rosu prog(U[w](φ,ψ), e) = prog(ψ,e) ∨ (prog(φ,e) ∧ U[w](φ,ψ)) (within window)
-- Past window: always Violated (ψ not satisfied within window).
stepL table (MetricUntil windowMicros startTime φ ψ) curr
  with (timestamp curr ∸ decodeStart startTime (timestamp curr)) ≤ᵇ windowMicros
... | false = Violated (mkCounterexample curr "MetricUntil: window expired before ψ")
... | true  = combineOr (stepL table ψ curr)
                (combineAnd (stepL table φ curr)
                  (Continue (windowMicros ∸ (timestamp curr ∸ decodeStart startTime (timestamp curr)))
                            (MetricUntil windowMicros (suc (decodeStart startTime (timestamp curr))) φ ψ)))

-- MetricRelease: Rosu prog(R[w](φ,ψ), e) = prog(ψ,e) ∧ (prog(φ,e) ∨ R[w](φ,ψ)) (within window)
stepL table (MetricRelease windowMicros startTime φ ψ) curr
  with (timestamp curr ∸ decodeStart startTime (timestamp curr)) ≤ᵇ windowMicros
... | false = Satisfied  -- Window complete, ψ held throughout
... | true  = combineAnd (stepL table ψ curr)
                (combineOr (stepL table φ curr)
                  (Continue (windowMicros ∸ (timestamp curr ∸ decodeStart startTime (timestamp curr)))
                            (MetricRelease windowMicros (suc (decodeStart startTime (timestamp curr))) φ ψ)))

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

-- Atomic still active at end-of-stream → never resolved
finalizeL (Atomic _) = Fails "Atomic: predicate never resolved at end of stream"

-- Propositional: compose inner results
finalizeL (Not φ) with finalizeL φ
... | Holds   = Fails "Not: inner satisfied at end of stream"
... | Fails _ = Holds

finalizeL (And φ ψ) with finalizeL φ
... | Fails r = Fails r
... | Holds with finalizeL ψ
...   | Fails r = Fails r
...   | Holds   = Holds

finalizeL (Or φ ψ) with finalizeL φ
... | Holds = Holds
... | Fails _ with finalizeL ψ
...   | Holds   = Holds
...   | Fails r = Fails r

-- Next: unresolved at end-of-stream → violated (next frame never arrived)
finalizeL (Next _) = Fails "Next: no next frame available at end of stream"

-- Always (SAFETY): vacuously true per standard LTLf
finalizeL (Always _) = Holds

-- Eventually (LIVENESS): still active → never satisfied
finalizeL (Eventually _) = Fails "Eventually: never satisfied before end of stream"

-- Until (LIVENESS): ψ must eventually hold; still active → Fails
finalizeL (Until _ _) = Fails "Until: ψ never satisfied before end of stream"

-- Release (SAFETY): vacuously true per standard LTLf (dual of Until)
finalizeL (Release _ _) = Holds

-- MetricEventually: still active → never satisfied
finalizeL (MetricEventually _ _ _) = Fails "MetricEventually: never satisfied within window before end of stream"

-- MetricAlways (SAFETY): vacuously true per standard LTLf
finalizeL (MetricAlways _ _ _) = Holds

-- MetricUntil: still active → ψ never satisfied
finalizeL (MetricUntil _ _ _ _) = Fails "MetricUntil: ψ never satisfied within window before end of stream"

-- MetricRelease (SAFETY): vacuously true per standard LTLf (dual of MetricUntil)
finalizeL (MetricRelease _ _ _ _) = Holds

-- Rosu simplification moved to LTL/Simplify.agda (separate concerns)
