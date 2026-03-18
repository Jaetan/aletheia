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

-- MetricEventually: Rosu prog(F[w]φ, e) = prog(φ,e) ∨ F[w]φ (within window)
-- Past window: always Violated (φ-satisfaction outside window doesn't count).
-- Uses `with` (not `if`) so the boolean reduces under proof with-abstraction.
stepL table (MetricEventuallyProc windowMicros startTime φ) curr
  with (timestamp curr ∸ decodeStart startTime (timestamp curr)) ≤ᵇ windowMicros
... | false = Violated (mkCounterexample curr "MetricEventually: window expired")
... | true  = combineOr (stepL table φ curr)
                (Continue (windowMicros ∸ (timestamp curr ∸ decodeStart startTime (timestamp curr)))
                          (MetricEventuallyProc windowMicros (suc (decodeStart startTime (timestamp curr))) φ))

-- MetricAlways: Rosu prog(G[w]φ, e) = prog(φ,e) ∧ G[w]φ (within window)
-- Uses `with` (not `if`) so the boolean reduces under proof with-abstraction.
stepL table (MetricAlwaysProc windowMicros startTime φ) curr
  with (timestamp curr ∸ decodeStart startTime (timestamp curr)) ≤ᵇ windowMicros
... | false = Satisfied  -- Window complete, always held
... | true  = combineAnd (stepL table φ curr)
                (Continue (windowMicros ∸ (timestamp curr ∸ decodeStart startTime (timestamp curr)))
                          (MetricAlwaysProc windowMicros (suc (decodeStart startTime (timestamp curr))) φ))

-- MetricUntil: Rosu prog(U[w](φ,ψ), e) = prog(ψ,e) ∨ (prog(φ,e) ∧ U[w](φ,ψ)) (within window)
-- Past window: always Violated (ψ not satisfied within window).
-- Uses `with` (not `if`) so the boolean reduces under proof with-abstraction.
stepL table (MetricUntilProc windowMicros startTime φ ψ) curr
  with (timestamp curr ∸ decodeStart startTime (timestamp curr)) ≤ᵇ windowMicros
... | false = Violated (mkCounterexample curr "MetricUntil: window expired before ψ")
... | true  = combineOr (stepL table ψ curr)
                (combineAnd (stepL table φ curr)
                  (Continue (windowMicros ∸ (timestamp curr ∸ decodeStart startTime (timestamp curr)))
                            (MetricUntilProc windowMicros (suc (decodeStart startTime (timestamp curr))) φ ψ)))

-- MetricRelease: Rosu prog(R[w](φ,ψ), e) = prog(ψ,e) ∧ (prog(φ,e) ∨ R[w](φ,ψ)) (within window)
-- Uses `with` (not `if`) so the boolean reduces under proof with-abstraction.
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

-- ============================================================================
-- ROSU SIMPLIFICATION
-- ============================================================================

-- Boolean structural equality on LTLProc.
-- Used by simplify to detect Rosu tree growth patterns.
_≡ᵇ-proc_ : LTLProc → LTLProc → Bool
Atomic n              ≡ᵇ-proc Atomic m              = n ≡ᵇ m
Not φ                 ≡ᵇ-proc Not ψ                 = φ ≡ᵇ-proc ψ
And φ₁ ψ₁             ≡ᵇ-proc And φ₂ ψ₂             = (φ₁ ≡ᵇ-proc φ₂) ∧ (ψ₁ ≡ᵇ-proc ψ₂)
Or φ₁ ψ₁              ≡ᵇ-proc Or φ₂ ψ₂              = (φ₁ ≡ᵇ-proc φ₂) ∧ (ψ₁ ≡ᵇ-proc ψ₂)
Next φ                ≡ᵇ-proc Next ψ                = φ ≡ᵇ-proc ψ
Always φ              ≡ᵇ-proc Always ψ              = φ ≡ᵇ-proc ψ
Eventually φ          ≡ᵇ-proc Eventually ψ          = φ ≡ᵇ-proc ψ
Until φ₁ ψ₁           ≡ᵇ-proc Until φ₂ ψ₂           = (φ₁ ≡ᵇ-proc φ₂) ∧ (ψ₁ ≡ᵇ-proc ψ₂)
Release φ₁ ψ₁         ≡ᵇ-proc Release φ₂ ψ₂         = (φ₁ ≡ᵇ-proc φ₂) ∧ (ψ₁ ≡ᵇ-proc ψ₂)
MetricEventuallyProc w₁ s₁ φ₁ ≡ᵇ-proc MetricEventuallyProc w₂ s₂ φ₂ =
  (w₁ ≡ᵇ w₂) ∧ (s₁ ≡ᵇ s₂) ∧ (φ₁ ≡ᵇ-proc φ₂)
MetricAlwaysProc w₁ s₁ φ₁ ≡ᵇ-proc MetricAlwaysProc w₂ s₂ φ₂ =
  (w₁ ≡ᵇ w₂) ∧ (s₁ ≡ᵇ s₂) ∧ (φ₁ ≡ᵇ-proc φ₂)
MetricUntilProc w₁ s₁ φ₁ ψ₁ ≡ᵇ-proc MetricUntilProc w₂ s₂ φ₂ ψ₂ =
  (w₁ ≡ᵇ w₂) ∧ (s₁ ≡ᵇ s₂) ∧ (φ₁ ≡ᵇ-proc φ₂) ∧ (ψ₁ ≡ᵇ-proc ψ₂)
MetricReleaseProc w₁ s₁ φ₁ ψ₁ ≡ᵇ-proc MetricReleaseProc w₂ s₂ φ₂ ψ₂ =
  (w₁ ≡ᵇ w₂) ∧ (s₁ ≡ᵇ s₂) ∧ (φ₁ ≡ᵇ-proc φ₂) ∧ (ψ₁ ≡ᵇ-proc ψ₂)
_ ≡ᵇ-proc _ = false

-- Rosu simplification: compact formula trees produced by combineAnd/combineOr.
--
-- Rosu's formula progression creates growing trees when subformulas return
-- Continue (Unknown/Pending signals). For example:
--   Always φ → combineAnd(Continue φ', Continue(Always φ)) → And φ' (Always φ)
-- After n frames with Unknown, the tree has n And nodes → O(n²) total work.
--
-- Two-phase approach:
--   Phase 1 (simplify): recurse into right subterms of And/Or to handle
--     nested patterns (e.g., Until/Release produce double nesting)
--   Phase 2 (absorb): apply Rosu absorption rules at the top level
--
-- Absorption rules (from Rosu's original paper, extended to all operators):
--   φ ∧ G(φ)     → G(φ)        φ ∨ F(φ)     → F(φ)
--   φ ∧ (φ U ψ)  → φ U ψ      ψ ∨ (φ U ψ)  → φ U ψ
--   ψ ∧ (φ R ψ)  → φ R ψ      φ ∨ (φ R ψ)  → φ R ψ
--   (and metric variants)
--
-- Semantically valid: e.g. ⟦ And φ (Always φ) ⟧ ≡ ⟦ Always φ ⟧ by idempotence of ∧TV.
-- Applied after stepL in the streaming pipeline (does not affect adequacy proof).

-- Phase 2: apply absorption rules (non-recursive)
absorb : LTLProc → LTLProc
-- And absorption: φ ∧ G(φ) → G(φ), φ ∧ (φ U ψ) → φ U ψ, ψ ∧ (φ R ψ) → φ R ψ
absorb (And φ (Always ψ)) with φ ≡ᵇ-proc ψ
... | true  = Always ψ
... | false = And φ (Always ψ)
absorb (And φ (Until ψ χ)) with φ ≡ᵇ-proc ψ
... | true  = Until ψ χ
... | false = And φ (Until ψ χ)
absorb (And ψ (Release φ χ)) with ψ ≡ᵇ-proc χ
... | true  = Release φ χ
... | false = And ψ (Release φ χ)
absorb (And φ (MetricAlwaysProc w s ψ)) with φ ≡ᵇ-proc ψ
... | true  = MetricAlwaysProc w s ψ
... | false = And φ (MetricAlwaysProc w s ψ)
absorb (And φ (MetricUntilProc w s ψ χ)) with φ ≡ᵇ-proc ψ
... | true  = MetricUntilProc w s ψ χ
... | false = And φ (MetricUntilProc w s ψ χ)
absorb (And ψ (MetricReleaseProc w s φ χ)) with ψ ≡ᵇ-proc χ
... | true  = MetricReleaseProc w s φ χ
... | false = And ψ (MetricReleaseProc w s φ χ)
-- Or absorption: φ ∨ F(φ) → F(φ), ψ ∨ (φ U ψ) → φ U ψ, φ ∨ (φ R ψ) → φ R ψ
absorb (Or φ (Eventually ψ)) with φ ≡ᵇ-proc ψ
... | true  = Eventually ψ
... | false = Or φ (Eventually ψ)
absorb (Or ψ (Until φ χ)) with ψ ≡ᵇ-proc χ
... | true  = Until φ χ
... | false = Or ψ (Until φ χ)
absorb (Or φ (Release ψ χ)) with φ ≡ᵇ-proc ψ
... | true  = Release ψ χ
... | false = Or φ (Release ψ χ)
absorb (Or φ (MetricEventuallyProc w s ψ)) with φ ≡ᵇ-proc ψ
... | true  = MetricEventuallyProc w s ψ
... | false = Or φ (MetricEventuallyProc w s ψ)
absorb (Or ψ (MetricUntilProc w s φ χ)) with ψ ≡ᵇ-proc χ
... | true  = MetricUntilProc w s φ χ
... | false = Or ψ (MetricUntilProc w s φ χ)
absorb (Or φ (MetricReleaseProc w s ψ χ)) with φ ≡ᵇ-proc ψ
... | true  = MetricReleaseProc w s ψ χ
... | false = Or φ (MetricReleaseProc w s ψ χ)
absorb x = x

-- Phase 1: recurse right to handle nested patterns, then absorb
simplify : LTLProc → LTLProc
simplify (And a b) = absorb (And a (simplify b))
simplify (Or a b)  = absorb (Or a (simplify b))
simplify x = x
