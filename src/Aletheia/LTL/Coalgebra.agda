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
open import Aletheia.LTL.Syntax using (LTL; Atomic; Not; And; Or; Next; Always; Eventually; Until; Release; MetricEventually; MetricAlways; MetricUntil; MetricRelease; decodeStart)
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
-- LTLPROC: Defunctionalized LTL process with ℕ-indexed predicates
-- ============================================================================

-- LTLProc is the LTL formula enriched with runtime state for operators that need it.
--
-- Design philosophy:
-- - Atomic predicates are ℕ indices into a PredTable (not functions)
-- - This enables structural equality, needed for simplification and dedup
-- - The formula tells us HOW to react to the next frame
-- - We pattern match on formula structure to define step behavior

data LTLProc : Set where
  -- Propositional operators
  Atomic : ℕ → LTLProc    -- Index into PredTable
  Not : LTLProc → LTLProc
  And : LTLProc → LTLProc → LTLProc
  Or : LTLProc → LTLProc → LTLProc

  -- Next: one-step skip (Rosu: prog(Xφ, e) = φ)
  Next : LTLProc → LTLProc

  -- Temporal operators
  Always : LTLProc → LTLProc
  Eventually : LTLProc → LTLProc
  Until : LTLProc → LTLProc → LTLProc
  Release : LTLProc → LTLProc → LTLProc  -- Dual of Until: ψ holds until φ releases it

  -- Bounded temporal operators (with time tracking)
  MetricEventuallyProc : ℕ → ℕ → LTLProc → LTLProc  -- windowMicros, startTime, inner
  MetricAlwaysProc : ℕ → ℕ → LTLProc → LTLProc      -- windowMicros, startTime, inner
  MetricUntilProc : ℕ → ℕ → LTLProc → LTLProc → LTLProc      -- windowMicros, startTime, φ, ψ
  MetricReleaseProc : ℕ → ℕ → LTLProc → LTLProc → LTLProc    -- windowMicros, startTime, φ, ψ

-- ============================================================================
-- DENOTATION: LTLProc → LTL (for proof interop with ⟦_⟧)
-- ============================================================================

-- Convert LTLProc to LTL formula for use with denotational semantics.
-- Uses PredTable to convert ℕ indices back to evaluation functions.
-- Next maps directly to Next (preserving temporal structure).

denot : PredTable → LTLProc → LTL (TimedFrame → TruthVal)
denot table (Atomic n) = Atomic (table n)
denot table (Not φ) = Not (denot table φ)
denot table (And φ ψ) = And (denot table φ) (denot table ψ)
denot table (Or φ ψ) = Or (denot table φ) (denot table ψ)
denot table (Next φ) = Next (denot table φ)
denot table (Always φ) = Always (denot table φ)
denot table (Eventually φ) = Eventually (denot table φ)
denot table (Until φ ψ) = Until (denot table φ) (denot table ψ)
denot table (Release φ ψ) = Release (denot table φ) (denot table ψ)
denot table (MetricEventuallyProc window start φ) = MetricEventually window start (denot table φ)
denot table (MetricAlwaysProc window start φ) = MetricAlways window start (denot table φ)
denot table (MetricUntilProc window start φ ψ) = MetricUntil window start (denot table φ) (denot table ψ)
denot table (MetricReleaseProc window start φ ψ) = MetricRelease window start (denot table φ) (denot table ψ)

-- ============================================================================
-- INITIALIZATION: LTL ℕ → initial LTLProc
-- ============================================================================

-- Convert an ℕ-indexed LTL formula to its initial LTLProc state.
-- Design choices:
--   - Bounded operators start with startTime=0
--   - Next starts in waiting mode

initProc : LTL ℕ → LTLProc
initProc (Atomic n)            = Atomic n
initProc (Not φ)               = Not (initProc φ)
initProc (And φ ψ)             = And (initProc φ) (initProc ψ)
initProc (Or φ ψ)              = Or (initProc φ) (initProc ψ)
initProc (Next φ)              = Next (initProc φ)
initProc (Always φ)            = Always (initProc φ)
initProc (Eventually φ)        = Eventually (initProc φ)
initProc (Until φ ψ)           = Until (initProc φ) (initProc ψ)
initProc (Release φ ψ)         = Release (initProc φ) (initProc ψ)
initProc (MetricEventually w s φ)    = MetricEventuallyProc w s (initProc φ)
initProc (MetricAlways w s φ)        = MetricAlwaysProc w s (initProc φ)
initProc (MetricUntil w s φ ψ)      = MetricUntilProc w s (initProc φ) (initProc ψ)
initProc (MetricRelease w s φ ψ)    = MetricReleaseProc w s (initProc φ) (initProc ψ)

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
stepL table (MetricEventuallyProc windowMicros startTime φ) curr
  with (timestamp curr ∸ decodeStart startTime (timestamp curr)) ≤ᵇ windowMicros
... | false = Violated (mkCounterexample curr "MetricEventually: window expired")
... | true  = combineOr (stepL table φ curr)
                (Continue (windowMicros ∸ (timestamp curr ∸ decodeStart startTime (timestamp curr)))
                          (MetricEventuallyProc windowMicros (suc (decodeStart startTime (timestamp curr))) φ))

-- MetricAlways: Rosu prog(G[w]φ, e) = prog(φ,e) ∧ G[w]φ (within window)
stepL table (MetricAlwaysProc windowMicros startTime φ) curr
  with (timestamp curr ∸ decodeStart startTime (timestamp curr)) ≤ᵇ windowMicros
... | false = Satisfied  -- Window complete, always held
... | true  = combineAnd (stepL table φ curr)
                (Continue (windowMicros ∸ (timestamp curr ∸ decodeStart startTime (timestamp curr)))
                          (MetricAlwaysProc windowMicros (suc (decodeStart startTime (timestamp curr))) φ))

-- MetricUntil: Rosu prog(U[w](φ,ψ), e) = prog(ψ,e) ∨ (prog(φ,e) ∧ U[w](φ,ψ)) (within window)
-- Past window: always Violated (ψ not satisfied within window).
stepL table (MetricUntilProc windowMicros startTime φ ψ) curr
  with (timestamp curr ∸ decodeStart startTime (timestamp curr)) ≤ᵇ windowMicros
... | false = Violated (mkCounterexample curr "MetricUntil: window expired before ψ")
... | true  = combineOr (stepL table ψ curr)
                (combineAnd (stepL table φ curr)
                  (Continue (windowMicros ∸ (timestamp curr ∸ decodeStart startTime (timestamp curr)))
                            (MetricUntilProc windowMicros (suc (decodeStart startTime (timestamp curr))) φ ψ)))

-- MetricRelease: Rosu prog(R[w](φ,ψ), e) = prog(ψ,e) ∧ (prog(φ,e) ∨ R[w](φ,ψ)) (within window)
stepL table (MetricReleaseProc windowMicros startTime φ ψ) curr
  with (timestamp curr ∸ decodeStart startTime (timestamp curr)) ≤ᵇ windowMicros
... | false = Satisfied  -- Window complete, ψ held throughout
... | true  = combineAnd (stepL table ψ curr)
                (combineOr (stepL table φ curr)
                  (Continue (windowMicros ∸ (timestamp curr ∸ decodeStart startTime (timestamp curr)))
                            (MetricReleaseProc windowMicros (suc (decodeStart startTime (timestamp curr))) φ ψ)))

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
finalizeL (MetricEventuallyProc _ _ _) = Fails "MetricEventually: never satisfied within window before end of stream"

-- MetricAlways (SAFETY): vacuously true per standard LTLf
finalizeL (MetricAlwaysProc _ _ _) = Holds

-- MetricUntil: still active → ψ never satisfied
finalizeL (MetricUntilProc _ _ _ _) = Fails "MetricUntil: ψ never satisfied within window before end of stream"

-- MetricRelease (SAFETY): vacuously true per standard LTLf (dual of MetricUntil)
finalizeL (MetricReleaseProc _ _ _ _) = Holds

-- Rosu simplification moved to LTL/Simplify.agda (separate concerns)
