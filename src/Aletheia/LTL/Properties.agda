{-# OPTIONS --without-K --guardedness --sized-types #-}

-- Correctness properties for LTL evaluation (Phase 3 Goal #2).
--
-- Purpose: Prove LTL evaluator correctness for streaming protocol verification.
-- Properties: Coinductive equivalence between streaming stepEval and formal checkColist semantics.
-- Approach: Prove stepEval ≡ checkColist (streaming state machine matches infinite-trace LTL).
--
-- PROOF STRATEGY (Direct Coinductive Correctness):
--
-- Aletheia has TWO evaluation implementations:
--   1. stepEval (LTLEvalState → Frame → StepResult) - Streaming, O(1) memory, PRODUCTION
--   2. checkColist (Colist Frame → Delay Bool) - Coinductive, infinite streams, FORMAL SEMANTICS
--
-- This module proves: stepEval ≡ checkColist
--   - Defines foldStepEval: lifts stepEval to work on colists
--   - Proves equivalence: foldStepEval φ trace ≡ checkColist φ trace
--   - Uses coinductive reasoning, sized types, productivity checking
--
-- Why this approach?
--   - Production ONLY uses stepEval (streaming state machine)
--   - checkColist defines true LTL semantics (infinite traces)
--   - Avoids finite/streaming semantic mismatches
--   - Direct proof: show production implementation matches mathematical definition
--
-- Previous approach (DISCARDED):
--   - Proved checkIncremental (finite traces) was correct
--   - Attempted stepEval ≡ checkIncremental equivalence
--   - Blocked by semantic mismatch (Continue case on finite traces)
--   - checkIncremental never used in production → removed as dead code
--
-- See: /home/nicolas/.claude/plans/synthetic-honking-goblet.md for full rationale
--
-- Current status: Cleanup phase complete, ready for coinductive infrastructure
-- Next: Define foldStepEval, prove Atomic case, then propositional operators

module Aletheia.LTL.Properties where

-- Standard library imports
open import Size using (Size; ∞; Size<_)
open import Codata.Sized.Thunk using (Thunk; force)
open import Codata.Sized.Delay using (Delay; now; later)
open import Codata.Sized.Delay.Bisimilarity as DelayBisim using (_⊢_≈_; Bisim)
import Codata.Sized.Delay.Bisimilarity as DB
open import Codata.Sized.Colist as Colist using (Colist; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false; if_then_else_; not; _∧_; _∨_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; inspect; [_])

-- Aletheia imports
open import Aletheia.LTL.Syntax
open import Aletheia.LTL.Incremental
open import Aletheia.LTL.Coinductive as Coinductive using (checkColist)
open import Aletheia.Trace.Context using (TimedFrame)

-- ============================================================================
-- HELPER LEMMAS FOR TEMPORAL OPERATORS (Phase 4)
-- ============================================================================

-- These lemmas are essential for proving temporal operator equivalences.
-- They provide general bisimilarity congruence lemmas for Delay operations.

-- Helper: Map congruence for bisimilarity
-- If d₁ ≈ d₂, then mapping the same function preserves bisimilarity
-- NOTE: Commented out for now - will add if needed during temporal operator proofs
-- The issue is that Agda doesn't automatically reduce D.map applications in the
-- return type, causing unification issues. We may not need this lemma at all.
-- open import Codata.Sized.Delay as D using (map)
--
-- private
--   map-cong : ∀ {i A B} (f : A → B) {d₁ d₂ : Delay A ∞}
--     → i ⊢ d₁ ≈ d₂
--     → i ⊢ D.map f d₁ ≈ D.map f d₂
--   map-cong f (DB.now {x} refl) = DB.now refl
--   map-cong f (DB.later {xs} {ys} prf) =
--     DB.later λ where .force → map-cong f (prf .force)

-- Helper: If-then-else congruence for bisimilarity
-- Branch on boolean condition while preserving bisimilarity
private
  if-cong : ∀ {i} (b : Bool) {d₁ d₂ d₃ d₄ : Delay Bool ∞}
    → (b ≡ true → i ⊢ d₁ ≈ d₃)
    → (b ≡ false → i ⊢ d₂ ≈ d₄)
    → i ⊢ (if b then d₁ else d₂) ≈ (if b then d₃ else d₄)
  if-cong true  hyp-t hyp-f = hyp-t refl
  if-cong false hyp-t hyp-f = hyp-f refl

-- Helper: Later congruence for bisimilarity
-- This is actually just the later constructor of Bisim, included for clarity
-- If thunks are bisimilar when forced, then delaying them preserves bisimilarity
-- Note: We use DB.later directly in proofs, this is just documentation

-- ============================================================================
-- PHASE 2: COINDUCTIVE INFRASTRUCTURE
-- ============================================================================

-- Evaluator for atomic predicates in LTL (TimedFrame → Bool)
-- The predicate itself doesn't use previous frame, but stepEval's signature requires it
evalAtomicPred : Maybe TimedFrame → TimedFrame → (TimedFrame → Bool) → Bool
evalAtomicPred _ curr p = p curr

-- Top-level helper: threads state and previous frame through colist
-- Extracted from where-clause to make it visible in proofs
foldStepEval-go : ∀ {i : Size}
                → LTL (TimedFrame → Bool)     -- Original formula (for stepEval)
                → LTLEvalState                -- Current evaluation state
                → Maybe TimedFrame             -- Previous frame
                → TimedFrame                   -- Current frame
                → Colist TimedFrame i          -- Remaining frames
                → Delay Bool i

-- Process current frame with stepEval
foldStepEval-go φ st prev curr rest with stepEval φ evalAtomicPred st prev curr

-- Continue: process next frame (or finish if no more frames)
... | Continue st' with rest
...   | [] = now true  -- No more frames, default to true (finite prefix semantics)
...   | (next ∷ rest') = later λ where .force → foldStepEval-go φ st' (just curr) next (rest' .force)

-- Violated: property failed
foldStepEval-go φ st prev curr rest | Violated _ = now false

-- Satisfied: property succeeded
foldStepEval-go φ st prev curr rest | Satisfied = now true

-- Fold stepEval over a colist to get coinductive result
-- This bridges stepEval (frame-by-frame) and checkColist (whole colist)
foldStepEval : ∀ {i : Size}
             → LTL (TimedFrame → Bool)
             → Colist TimedFrame i
             → Delay Bool i

-- Empty trace: vacuously true
foldStepEval φ [] = now true

-- Non-empty trace: delegate to helper
foldStepEval φ (f ∷ rest) = later λ where .force → foldStepEval-go φ (initState φ) nothing f (rest .force)

-- ============================================================================
-- PHASE 3: ATOMIC CASE EQUIVALENCE
-- ============================================================================

-- Prove Atomic predicates are bisimilar between foldStepEval and checkColist
-- Uses weak bisimilarity (∞ ⊢_≈_) instead of propositional equality
-- This is the standard approach for coinductive proofs
-- Note: We specialize to size ∞ to match the bisimilarity relation

-- Helper lemma: stepEval for Atomic computes based on predicate value
-- The definition of stepEval for Atomic is: if eval then Satisfied else Violated
-- So we can directly compute what it returns based on p f
stepEval-atomic-computes : ∀ (p : TimedFrame → Bool) (f : TimedFrame)
  → stepEval (Atomic p) evalAtomicPred AtomicState nothing f
    ≡ (if p f then Satisfied else Violated (mkCounterexample f "atomic predicate failed"))
stepEval-atomic-computes p f with p f
... | true  = refl
... | false = refl

-- Helper: prove what foldStepEval-go computes for Atomic
-- Since foldStepEval-go is top-level, Agda can reduce it!
-- This is the key that makes the proof work
atomic-go-equiv : ∀ (p : TimedFrame → Bool) (f : TimedFrame) (rest : Colist TimedFrame ∞)
  → ∞ ⊢ foldStepEval-go (Atomic p) AtomicState nothing f rest ≈ now (p f)

-- Pattern match on p f to make both sides reduce
atomic-go-equiv p f rest with p f
... | true  = DB.now refl  -- When p f = true: foldStepEval-go reduces to 'now true', checkColist to 'now true'
... | false = DB.now refl  -- When p f = false: foldStepEval-go reduces to 'now false', checkColist to 'now false'

-- With foldStepEval-go extracted to top-level, Agda can now reduce it in proofs!
atomic-fold-equiv : ∀ (p : TimedFrame → Bool) (trace : Colist TimedFrame ∞)
  → ∞ ⊢ foldStepEval (Atomic p) trace ≈ checkColist (Atomic p) trace

-- Empty case: both return 'now true'
atomic-fold-equiv p [] = DB.now refl

-- Non-empty case: use copattern matching to handle the 'later' constructor
atomic-fold-equiv p (f ∷ rest) = DB.later λ where .force → atomic-go-equiv p f (rest .force)

-- ============================================================================
-- PHASE 4: PROPOSITIONAL OPERATORS
-- ============================================================================

-- Strategy: Use induction on formula structure + coinductive reasoning for delays
-- Key insight: Propositional operators in stepEval may return Continue,
-- requiring us to follow the state machine through multiple frames

-- Import Delay utilities for reasoning about coinductive results
open import Codata.Sized.Delay as Delay using (bind; map)
open import Data.Bool using (not; _∧_; _∨_)

-- Helper: prove what foldStepEval-go computes for Not (Atomic p)
-- The state machine for Not (Atomic p) is:
--   - If p f = true: Atomic returns Satisfied, Not returns Violated → foldStepEval-go returns now false
--   - If p f = false: Atomic returns Violated, Not returns Continue, then rest=[] → now true
not-atomic-go-equiv : ∀ (p : TimedFrame → Bool) (f : TimedFrame) (rest : Colist TimedFrame ∞)
  → ∞ ⊢ foldStepEval-go (Not (Atomic p)) (NotState AtomicState) nothing f rest ≈ now (not (p f))

-- Pattern match on p f to make both sides reduce
-- When p f = true: Atomic returns Satisfied, Not returns Violated, foldStepEval-go returns 'now false'
-- When p f = false: Atomic returns Violated, Not returns Satisfied, foldStepEval-go returns 'now true'
not-atomic-go-equiv p f rest with p f
... | true = DB.now refl  -- Both sides reduce to 'now false'
... | false = DB.now refl  -- Both sides reduce to 'now true'

-- Main theorem for Not (Atomic p)
not-atomic-fold-equiv : ∀ (p : TimedFrame → Bool) (trace : Colist TimedFrame ∞)
  → ∞ ⊢ foldStepEval (Not (Atomic p)) trace ≈ checkColist (Not (Atomic p)) trace

-- Empty case: both return 'now true'
not-atomic-fold-equiv p [] = DB.now refl

-- Non-empty case: use copattern matching to handle the 'later' constructor
not-atomic-fold-equiv p (f ∷ rest) = DB.later λ where .force → not-atomic-go-equiv p f (rest .force)

-- And: Both operands must hold
-- For And (Atomic p) (Atomic q), the result should be (p f ∧ q f)

and-atomic-go-equiv : ∀ (p q : TimedFrame → Bool) (f : TimedFrame) (rest : Colist TimedFrame ∞)
  → ∞ ⊢ foldStepEval-go (And (Atomic p) (Atomic q)) (AndState AtomicState AtomicState) nothing f rest
      ≈ now (p f ∧ q f)

-- Pattern match on p f and q f separately to enable reduction through stepEval-and-helper
and-atomic-go-equiv p q f rest with p f in eq-p | q f in eq-q
... | true  | true  = DB.now refl  -- Both satisfied: stepEval-and-helper → Satisfied → now true, RHS is now (true ∧ true) = now true
... | true  | false = DB.now refl  -- Right violated: stepEval-and-helper → Violated → now false, RHS is now (true ∧ false) = now false
... | false | true  = DB.now refl  -- Left violated: stepEval-and-helper → Violated → now false, RHS is now (false ∧ true) = now false
... | false | false = DB.now refl  -- Both violated: stepEval-and-helper → Violated → now false, RHS is now (false ∧ false) = now false

-- Main theorem for And (Atomic p) (Atomic q)
and-atomic-fold-equiv : ∀ (p q : TimedFrame → Bool) (trace : Colist TimedFrame ∞)
  → ∞ ⊢ foldStepEval (And (Atomic p) (Atomic q)) trace ≈ checkColist (And (Atomic p) (Atomic q)) trace

-- Empty case: both return 'now true'
and-atomic-fold-equiv p q [] = DB.now refl

-- Non-empty case: use copattern matching
and-atomic-fold-equiv p q (f ∷ rest) = DB.later λ where .force → and-atomic-go-equiv p q f (rest .force)

-- Or: Either operand must hold
-- For Or (Atomic p) (Atomic q), the result should be (p f ∨ q f)

or-atomic-go-equiv : ∀ (p q : TimedFrame → Bool) (f : TimedFrame) (rest : Colist TimedFrame ∞)
  → ∞ ⊢ foldStepEval-go (Or (Atomic p) (Atomic q)) (OrState AtomicState AtomicState) nothing f rest
      ≈ now (p f ∨ q f)

-- Pattern match on p f and q f directly to enable reduction through nested with-clauses
or-atomic-go-equiv p q f rest with p f in eq-p | q f in eq-q
... | true  | true  = DB.now refl  -- Left satisfied: Or returns Satisfied immediately, foldStepEval-go returns now true
... | true  | false = DB.now refl  -- Left satisfied: Or returns Satisfied immediately, foldStepEval-go returns now true
... | false | true  = DB.now refl  -- Left violated, right satisfied: Or returns Satisfied, foldStepEval-go returns now true
... | false | false = DB.now refl  -- Both violated: Or returns Violated, foldStepEval-go returns now false

-- Main theorem for Or (Atomic p) (Atomic q)
or-atomic-fold-equiv : ∀ (p q : TimedFrame → Bool) (trace : Colist TimedFrame ∞)
  → ∞ ⊢ foldStepEval (Or (Atomic p) (Atomic q)) trace ≈ checkColist (Or (Atomic p) (Atomic q)) trace

-- Empty case: both return 'now true'
or-atomic-fold-equiv p q [] = DB.now refl

-- Non-empty case: use copattern matching
or-atomic-fold-equiv p q (f ∷ rest) = DB.later λ where .force → or-atomic-go-equiv p q f (rest .force)

-- ============================================================================
-- PHASE 3.3: GENERAL COMPOSITIONAL PROOFS (IN PROGRESS)
-- ============================================================================

-- Goal: Prove equivalence for ALL LTL formulas using structural induction
-- Approach: Mutual recursion over formula structure
-- Status: Propositional operators only (temporal operators deferred to Phase 4)

-- Main theorem: prove foldStepEval ≈ checkColist for all formulas
-- Uses structural induction - each constructor delegates to helper lemmas
-- Atomic cases use proven lemmas from Phase 3.1-3.2
-- Temporal cases postulated (TODO Phase 4)

-- ============================================================================
-- AUXILIARY LEMMAS FOR TEMPORAL OPERATORS
-- ============================================================================

-- These lemmas help bridge the gap between incremental (state-based) and
-- coinductive (recursive) temporal operator semantics.

-- NOTE: The next-unwrap auxiliary lemma is no longer needed after fixing the Next operator bug.
-- The bug was that stepEval (Next φ) evaluated φ at the current frame instead of skipping it.
-- Now that Next correctly skips the first frame (using NextState → NextActive transition),
-- the proof should work directly without needing a complex state unwrapping lemma.
-- Keeping the commented-out old approach for reference:

{-
-- Auxiliary Lemma: NextState Unwrapping (OLD - before bug fix)
-- Shows that Next operator "passes through" to evaluate the inner formula on the tail.
next-unwrap : ∀ (φ : LTL (TimedFrame → Bool)) (f : TimedFrame) (next : TimedFrame) (rest : Thunk (Colist TimedFrame) ∞)
  → ∞ ⊢ foldStepEval-go (Next φ) (NextState (initState φ)) nothing f (next ∷ rest)
      ≈ foldStepEval φ (next ∷ rest)
next-unwrap φ f next rest = {!!}
-}

-- Postulates (TODO: Remove by implementing proofs)

-- Temporal operator proofs (postulated - to be proven in Phase 4)
-- NOTE: next-fold-equiv moved to mutual block (see Phase 4 section below)
postulate
  always-fold-equiv : ∀ (φ : LTL (TimedFrame → Bool)) (trace : Colist TimedFrame ∞)
    → ∞ ⊢ foldStepEval (Always φ) trace ≈ checkColist (Always φ) trace

  eventually-fold-equiv : ∀ (φ : LTL (TimedFrame → Bool)) (trace : Colist TimedFrame ∞)
    → ∞ ⊢ foldStepEval (Eventually φ) trace ≈ checkColist (Eventually φ) trace

  until-fold-equiv : ∀ (φ ψ : LTL (TimedFrame → Bool)) (trace : Colist TimedFrame ∞)
    → ∞ ⊢ foldStepEval (Until φ ψ) trace ≈ checkColist (Until φ ψ) trace

  eventually-within-fold-equiv : ∀ (n : ℕ) (φ : LTL (TimedFrame → Bool)) (trace : Colist TimedFrame ∞)
    → ∞ ⊢ foldStepEval (EventuallyWithin n φ) trace ≈ checkColist (EventuallyWithin n φ) trace

  always-within-fold-equiv : ∀ (n : ℕ) (φ : LTL (TimedFrame → Bool)) (trace : Colist TimedFrame ∞)
    → ∞ ⊢ foldStepEval (AlwaysWithin n φ) trace ≈ checkColist (AlwaysWithin n φ) trace

-- General propositional cases (postulated - TODO Phase 3.3)
postulate
  not-general-postulate : ∀ (φ : LTL (TimedFrame → Bool)) (trace : Colist TimedFrame ∞)
    → ∞ ⊢ foldStepEval (Not φ) trace ≈ checkColist (Not φ) trace

  and-general-postulate : ∀ (φ ψ : LTL (TimedFrame → Bool)) (trace : Colist TimedFrame ∞)
    → ∞ ⊢ foldStepEval (And φ ψ) trace ≈ checkColist (And φ ψ) trace

  or-general-postulate : ∀ (φ ψ : LTL (TimedFrame → Bool)) (trace : Colist TimedFrame ∞)
    → ∞ ⊢ foldStepEval (Or φ ψ) trace ≈ checkColist (Or φ ψ) trace

mutual
  -- Main equivalence theorem for all LTL formulas
  fold-equiv : ∀ (φ : LTL (TimedFrame → Bool)) (trace : Colist TimedFrame ∞)
    → ∞ ⊢ foldStepEval φ trace ≈ checkColist φ trace

  -- Base case: Atomic predicates (proven in Phase 3.1)
  fold-equiv (Atomic p) trace = atomic-fold-equiv p trace

  -- Propositional operators (use helper lemmas)
  fold-equiv (Not φ) trace = not-fold-equiv φ trace
  fold-equiv (And φ ψ) trace = and-fold-equiv φ ψ trace
  fold-equiv (Or φ ψ) trace = or-fold-equiv φ ψ trace

  -- Temporal operators (postulated - TODO Phase 4)
  fold-equiv (Next φ) trace = next-fold-equiv φ trace
  fold-equiv (Always φ) trace = always-fold-equiv φ trace
  fold-equiv (Eventually φ) trace = eventually-fold-equiv φ trace
  fold-equiv (Until φ ψ) trace = until-fold-equiv φ ψ trace
  fold-equiv (EventuallyWithin n φ) trace = eventually-within-fold-equiv n φ trace
  fold-equiv (AlwaysWithin n φ) trace = always-within-fold-equiv n φ trace

  -- General Not equivalence (for any φ, not just Atomic)
  -- NOTE: Full structural induction creates explosion of cases
  -- For now: prove key propositional cases, postulate rest
  not-fold-equiv : ∀ (φ : LTL (TimedFrame → Bool)) (trace : Colist TimedFrame ∞)
    → ∞ ⊢ foldStepEval (Not φ) trace ≈ checkColist (Not φ) trace
  not-fold-equiv (Atomic p) trace = not-atomic-fold-equiv p trace  -- Base case (proven)
  -- TODO Phase 3.3: Implement propositional compositions
  -- TODO Phase 4: Implement temporal compositions
  not-fold-equiv φ trace = not-general-postulate φ trace  -- Postulate for now

  -- General And equivalence (for any φ, ψ)
  -- NOTE: Full structural induction creates O(n²) cases
  -- For now: prove atomic base case, postulate rest
  and-fold-equiv : ∀ (φ ψ : LTL (TimedFrame → Bool)) (trace : Colist TimedFrame ∞)
    → ∞ ⊢ foldStepEval (And φ ψ) trace ≈ checkColist (And φ ψ) trace
  and-fold-equiv (Atomic p) (Atomic q) trace = and-atomic-fold-equiv p q trace  -- Base case (proven)
  -- TODO Phase 3.3: Implement propositional compositions
  -- TODO Phase 4: Implement temporal compositions
  and-fold-equiv φ ψ trace = and-general-postulate φ ψ trace  -- Postulate for now

  -- General Or equivalence (for any φ, ψ)
  -- NOTE: Full structural induction creates O(n²) cases
  -- For now: prove atomic base case, postulate rest
  or-fold-equiv : ∀ (φ ψ : LTL (TimedFrame → Bool)) (trace : Colist TimedFrame ∞)
    → ∞ ⊢ foldStepEval (Or φ ψ) trace ≈ checkColist (Or φ ψ) trace
  or-fold-equiv (Atomic p) (Atomic q) trace = or-atomic-fold-equiv p q trace  -- Base case (proven)
  -- TODO Phase 3.3: Implement propositional compositions
  -- TODO Phase 4: Implement temporal compositions
  or-fold-equiv φ ψ trace = or-general-postulate φ ψ trace  -- Postulate for now

  -- Next operator equivalence (Phase 4 - first temporal operator!)
  -- Next φ skips the first frame, then evaluates φ on the tail
  -- After bug fix: stepEval (Next φ) with NextState skips frame, transitions to NextActive
  next-fold-equiv : ∀ (φ : LTL (TimedFrame → Bool)) (trace : Colist TimedFrame ∞)
    → ∞ ⊢ foldStepEval (Next φ) trace ≈ checkColist (Next φ) trace
  next-fold-equiv φ [] = DB.now refl  -- Empty trace: both return 'now true'
  next-fold-equiv φ (f ∷ rest) = DB.later λ where .force → next-go-equiv-mut φ f (rest .force)
    where
      -- Helper: Prove foldStepEval-go (Next φ) (NextState st) behaves like coinductive Next
      -- Coinductive Next definition (from Coinductive.agda:131-133, inlined since go is private):
      --   go (Next ψ) frame [] = now (evalAtFrame frame ψ)
      --   go (Next ψ) frame (next ∷ rest') = later λ .force → go ψ next (rest' .force)
      --
      -- After the bug fix, incremental evaluation:
      --   stepEval (Next φ) (NextState st) = Continue (NextActive st)  (skips frame)
      --   stepEval (Next φ) (NextActive st) = [evaluates φ]  (on next frame)
      next-go-equiv-mut : ∀ (φ : LTL (TimedFrame → Bool)) (f : TimedFrame) (rest : Colist TimedFrame ∞)
        → ∞ ⊢ foldStepEval-go (Next φ) (NextState (initState φ)) nothing f rest
            ≈ checkColist φ rest  -- Note: φ, not Next φ! Coinductive Next skips to φ
      -- Empty rest: infinite extension
      -- LHS: foldStepEval-go (Next φ) (NextState (initState φ)) nothing f []
      --   with stepEval (Next φ) ... (NextState ...) nothing f  | Continue (NextActive (initState φ)) with []
      --   | [] = now true
      -- RHS: checkColist φ [] = now true
      -- Both sides: now true ≈ now true
      next-go-equiv-mut φ f [] = DB.now refl
      -- Non-empty rest: stepEval (Next φ) (NextState st) skips f, continues with NextActive
      -- LHS: foldStepEval-go (Next φ) (NextState (initState φ)) nothing f (next ∷ rest)
      --   = later λ .force → foldStepEval-go (Next φ) (NextActive (initState φ)) (just f) next (rest .force)
      -- RHS: checkColist φ (next ∷ rest)
      --   = later λ .force → [go φ next (rest .force)]
      -- Need auxiliary lemma: NextActive state evaluates φ correctly
      next-go-equiv-mut φ f (next ∷ rest) = {!!}  -- TODO: Prove NextActive unwrapping

-- ============================================================================
-- PHASE 4: TEMPORAL OPERATORS
-- ============================================================================

-- Strategy: Prove equivalence for each temporal operator using coinductive reasoning
-- Key technique: Use structural induction on formula φ + copattern matching for delays

-- Import coinductive checker for reference
open import Aletheia.LTL.Coinductive as Coinductive using ()

-- Helper: Prove equivalence for Next operator
-- Next φ means "φ holds at the next frame"
-- Coinductive: go (Next ψ) frame (next ∷ rest') = later (λ .force → go ψ next rest')
-- Incremental: stepEval (Next φ) wraps result in NextState

-- Key insight: Next φ on trace (f ∷ rest) evaluates φ on rest
-- The incremental version uses NextState to track "waiting for next frame"
-- The coinductive version pattern-matches on rest to skip the current frame

-- Observation: checkColist (Next φ) (f ∷ rest) ultimately evaluates φ on rest
--   - go (Next φ) f [] = now (evalAtFrame f φ)  [infinite extension]
--   - go (Next φ) f (next ∷ rest') = later (λ .force → go φ next rest')
--                                  ≈ checkColist φ (next ∷ rest')  [by definition]
-- So we need to show foldStepEval-go (Next φ) ... ≈ checkColist φ rest

-- Helper: Next operator skips current frame and evaluates φ on the rest
-- Pattern: Similar to atomic-go-equiv, but RHS is checkColist φ rest (not a simple value)
next-go-equiv : ∀ (φ : LTL (TimedFrame → Bool)) (f : TimedFrame) (rest : Colist TimedFrame ∞)
  → ∞ ⊢ foldStepEval-go (Next φ) (NextState (initState φ)) nothing f rest
      ≈ checkColist φ rest

-- Empty rest: Next with no next frame uses infinite extension semantics
-- Need to understand how stepEval (Next φ) behaves when rest is empty
next-go-equiv φ f [] = {!!}  -- TODO: Reduce both sides and show equality

-- Non-empty rest: This is the key case
-- LHS: foldStepEval-go (Next φ) (NextState (initState φ)) nothing f (next ∷ rest')
-- RHS: checkColist φ (next ∷ rest') = later (λ .force → go φ next (rest' .force))
-- Strategy: Use fold-equiv to relate to checkColist φ (next ∷ rest')
--
-- Key observation: We need to trace through what stepEval (Next φ) does:
-- stepEval (Next φ) eval (NextState st) prev curr
--   calls stepEval φ eval st prev curr
--   and wraps Continue results in NextState
--
-- We want to show this is bisimilar to foldStepEval φ (next ∷ rest')
-- Then use fold-equiv φ (next ∷ rest') to get bisimilarity with checkColist φ (next ∷ rest')
next-go-equiv φ f (next ∷ rest) =
  -- Use fold-equiv φ (next ∷ rest) which is available in the mutual recursion
  -- This gives us: foldStepEval φ (next ∷ rest) ≈ checkColist φ (next ∷ rest)
  -- And we need: foldStepEval-go (Next φ) (NextState (initState φ)) nothing f (next ∷ rest)
  --            ≈ checkColist φ (next ∷ rest)
  fold-equiv φ (next ∷ rest)

-- ============================================================================
-- PHASE 5: TEMPORAL OPERATORS (TODO - RESEARCH FIRST)
-- ============================================================================

-- ⚠️ PAUSE before implementation: Research coinductive LTL proofs
-- TODO: Always, Eventually, Until
-- TODO: EventuallyWithin, AlwaysWithin

-- ============================================================================
-- PHASE 6: GLOBAL EQUIVALENCE THEOREM (TODO)
-- ============================================================================

-- TODO: Main theorem combining all cases
-- postulate
--   stepEval-coinductive-equiv : ∀ {i : Size} (φ : LTL (TimedFrame → Bool)) (trace : Colist TimedFrame i)
--     → foldStepEval φ trace ≡ checkColist φ trace

-- ============================================================================
-- IMPLEMENTATION NOTES
-- ============================================================================

-- Phase 1 (COMPLETE): Cleanup
--   - Removed checkIncremental and all finite-trace proofs (~1100 lines)
--   - Removed extractResult, runStepEval, simpleEval helpers
--   - Updated module header to reflect coinductive strategy
--
-- Phase 2 (IN PROGRESS): Infrastructure
--   ✅ Resolved --safe vs sized-types (removed --safe, added --sized-types)
--   ✅ Imported coinductive infrastructure (Colist, Delay, Size)
--   ✅ Defined evalAtomicPred helper
--   ✅ Defined foldStepEval : LTL (TimedFrame → Bool) → Colist TimedFrame → Delay Bool
--   ⏸️ Type-checking in progress
--
-- Phase 3-4 (NEXT): Easy cases
--   - Atomic: Never returns Continue, simple proof
--   - Propositional: Not, And, Or using structural induction
--
-- Phase 5 (RESEARCH REQUIRED): Temporal operators
--   - Always: Productivity proof (infinite checking)
--   - Eventually: Termination/productivity
--   - Until: Complex state correspondence
--   - Requires: literature review, sized types expertise
--
-- Phase 6 (INTEGRATION): Global theorem
--   - Combine all operator proofs
--   - Pattern match on formula structure
