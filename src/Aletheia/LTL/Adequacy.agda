{-# OPTIONS --safe --without-K #-}

-- Adequacy of stepL (formula progression) w.r.t. denotational LTLf semantics.
--
-- Main theorem:
--   adequacy : ∀ table proc σ → Sound (runL table proc σ) (⟦ denot table proc ⟧ σ)
--
-- The coalgebra (stepL + finalizeL) never gives a wrong definite answer:
-- if runL says True, ⟦_⟧ says True; if runL says False, ⟦_⟧ says False.
-- When either side is uncertain (Unknown/Pending), any result is acceptable.
--
-- Proof architecture:
--   1. Sound compositionality (sound-and, sound-or, sound-not)
--   2. Operational decomposition (runL-*-decomp lemmas)
--   3. Soundness transport (subst-based, avoids with-auxiliaries)
--   4. Non-recursive metric helpers (fix termination checker)
--
-- All proofs hold for four-valued Kleene logic (True/False/Unknown/Pending).
-- Zero postulates, zero holes, all 13 LTL operators covered.
module Aletheia.LTL.Adequacy where

open import Aletheia.Prelude
open import Data.Nat using (_≤ᵇ_)
open import Relation.Binary.PropositionalEquality using (subst)

import Aletheia.LTL.Syntax as Syntax
open Syntax using (LTL; decodeStart)
open import Aletheia.LTL.SignalPredicate using (TruthVal; True; False; Unknown; Pending;
  notTV; _∧TV_; _∨TV_)
open import Aletheia.LTL.Coalgebra using (LTLProc; PredTable; stepL; finalizeL; denot;
  Atomic; Not; And; Or; Next; Always; Eventually; Until; Release;
  MetricEventuallyProc; MetricAlwaysProc; MetricUntilProc; MetricReleaseProc)
open import Aletheia.LTL.Incremental using (Continue; Violated; Satisfied;
  FinalVerdict; Holds; Fails)
open import Aletheia.LTL.Semantics using (⟦_⟧; met-ev-go; met-al-go; met-un-go; met-re-go)
open import Aletheia.Trace.CANTrace using (TimedFrame; timestamp)

-- ============================================================================
-- FINAL VERDICT → SIGNAL VALUE CONVERSION
-- ============================================================================

verdictToSV : FinalVerdict → TruthVal
verdictToSV Holds = True
verdictToSV (Fails _) = False

-- ============================================================================
-- COALGEBRA EXECUTION ON FULL TRACE
-- ============================================================================

-- Run the coalgebra on a full trace, producing a TruthVal.
-- Takes a PredTable for evaluating atomic predicates.
-- No prev parameter — delta predicates use SignalCache externally.
--
-- When stepL returns:
--   Satisfied       → True  (property definitely holds)
--   Violated _      → False (property definitely fails)
--   Continue _ proc' → recurse on remaining trace
--   (no Inconclusive — removed, Unknown/Pending signals produce Continue 0)

runL : PredTable → LTLProc → List TimedFrame → TruthVal
runL table proc [] = verdictToSV (finalizeL proc)
runL table proc (x ∷ rest) with stepL table proc x
... | Satisfied        = True
... | Violated _       = False
... | Continue _ proc' = runL table proc' rest

-- ============================================================================
-- MONITORING SOUNDNESS (Sound)
-- ============================================================================

-- Sound m d means "m is a sound monitoring result for denotation d."
--
-- Definite agreement:    Sound True True, Sound False False
-- Denotation uncertain:  Sound m Unknown, Sound m Pending  (any monitor result OK)
-- Monitor uncertain:     Sound Unknown d, Sound Pending d  (admits ignorance)
--
-- Key exclusions: NOT Sound True False, NOT Sound False True
-- (the monitor NEVER gives a wrong definite answer)

data Sound : TruthVal → TruthVal → Set where
  sound-tt    : Sound True True
  sound-ff    : Sound False False
  sound-unk   : ∀ {m} → Sound m Unknown
  sound-pen   : ∀ {m} → Sound m Pending
  sound-m-unk : ∀ {d} → Sound Unknown d
  sound-m-pen : ∀ {d} → Sound Pending d

-- ============================================================================
-- FOUR-VALUED IDENTITY LEMMAS
-- ============================================================================

-- Kleene logic identity/absorb laws. These are needed because Agda's
-- overlapping clause patterns for ∧TV/∨TV prevent automatic reduction
-- when one argument is abstract (e.g., True ∧TV y doesn't reduce since
-- clause 1 checks first-arg=False, blocking clause 2's match on y).

private
  -- Any a: a ∧TV False = False
  ∧TV-false-r : ∀ a → (a ∧TV False) ≡ False
  ∧TV-false-r True    = refl
  ∧TV-false-r False   = refl
  ∧TV-false-r Unknown = refl
  ∧TV-false-r Pending = refl

  -- Any a: a ∨TV True = True
  ∨TV-true-r : ∀ a → (a ∨TV True) ≡ True
  ∨TV-true-r True    = refl
  ∨TV-true-r False   = refl
  ∨TV-true-r Unknown = refl
  ∨TV-true-r Pending = refl

  ∨TV-false-r : ∀ a → (a ∨TV False) ≡ a
  ∨TV-false-r True    = refl
  ∨TV-false-r False   = refl
  ∨TV-false-r Unknown = refl
  ∨TV-false-r Pending = refl

  -- True ∧TV b = b (left identity)
  ∧TV-true-l : ∀ b → (True ∧TV b) ≡ b
  ∧TV-true-l True    = refl
  ∧TV-true-l False   = refl
  ∧TV-true-l Unknown = refl
  ∧TV-true-l Pending = refl

  -- Any a: a ∧TV True = a (right identity for ∧)
  ∧TV-true-r : ∀ a → (a ∧TV True) ≡ a
  ∧TV-true-r True    = refl
  ∧TV-true-r False   = refl
  ∧TV-true-r Unknown = refl
  ∧TV-true-r Pending = refl

  -- False ∨TV b = b (left identity for ∨)
  ∨TV-false-l : ∀ b → (False ∨TV b) ≡ b
  ∨TV-false-l True    = refl
  ∨TV-false-l False   = refl
  ∨TV-false-l Unknown = refl
  ∨TV-false-l Pending = refl

-- ============================================================================
-- SOUND COMPOSITIONALITY LEMMAS
-- ============================================================================

-- These let us compose Sound proofs through propositional connectives.

sound-not : ∀ {m d} → Sound m d → Sound (notTV m) (notTV d)
sound-not sound-tt    = sound-ff
sound-not sound-ff    = sound-tt
sound-not sound-unk   = sound-unk
sound-not sound-pen   = sound-pen
sound-not sound-m-unk = sound-m-unk
sound-not sound-m-pen = sound-m-pen

sound-and : ∀ {m₁ d₁ m₂ d₂} → Sound m₁ d₁ → Sound m₂ d₂ → Sound (m₁ ∧TV m₂) (d₁ ∧TV d₂)
sound-and sound-tt sound-tt = sound-tt
sound-and sound-tt sound-ff = sound-ff
sound-and sound-tt sound-unk = sound-unk
sound-and sound-tt sound-pen = sound-pen
sound-and sound-tt sound-m-unk = sound-m-unk
sound-and sound-tt sound-m-pen = sound-m-pen
sound-and sound-ff _ = sound-ff
sound-and sound-unk sound-tt = sound-unk
sound-and {m₁} sound-unk sound-ff rewrite ∧TV-false-r m₁ = sound-ff
sound-and sound-unk sound-unk = sound-unk
sound-and sound-unk sound-pen = sound-pen
sound-and {m₁} {_} {_} {d₂} sound-unk sound-m-unk = unk-and-unk m₁ d₂
  where
    unk-and-unk : ∀ a b → Sound (a ∧TV Unknown) (Unknown ∧TV b)
    unk-and-unk True    True    = sound-unk
    unk-and-unk True    False   = sound-m-unk
    unk-and-unk True    Unknown = sound-unk
    unk-and-unk True    Pending = sound-pen
    unk-and-unk False   True    = sound-unk
    unk-and-unk False   False   = sound-ff
    unk-and-unk False   Unknown = sound-unk
    unk-and-unk False   Pending = sound-pen
    unk-and-unk Unknown True    = sound-unk
    unk-and-unk Unknown False   = sound-m-unk
    unk-and-unk Unknown Unknown = sound-unk
    unk-and-unk Unknown Pending = sound-pen
    unk-and-unk Pending True    = sound-unk
    unk-and-unk Pending False   = sound-m-pen
    unk-and-unk Pending Unknown = sound-unk
    unk-and-unk Pending Pending = sound-pen
sound-and {m₁} {_} {_} {d₂} sound-unk sound-m-pen = unk-and-pen m₁ d₂
  where
    unk-and-pen : ∀ a b → Sound (a ∧TV Pending) (Unknown ∧TV b)
    unk-and-pen True    True    = sound-unk
    unk-and-pen True    False   = sound-m-pen
    unk-and-pen True    Unknown = sound-unk
    unk-and-pen True    Pending = sound-pen
    unk-and-pen False   True    = sound-unk
    unk-and-pen False   False   = sound-ff
    unk-and-pen False   Unknown = sound-unk
    unk-and-pen False   Pending = sound-pen
    unk-and-pen Unknown True    = sound-unk
    unk-and-pen Unknown False   = sound-m-pen
    unk-and-pen Unknown Unknown = sound-unk
    unk-and-pen Unknown Pending = sound-pen
    unk-and-pen Pending True    = sound-unk
    unk-and-pen Pending False   = sound-m-pen
    unk-and-pen Pending Unknown = sound-unk
    unk-and-pen Pending Pending = sound-pen
sound-and sound-pen sound-tt = sound-pen
sound-and {m₁} sound-pen sound-ff rewrite ∧TV-false-r m₁ = sound-ff
sound-and sound-pen sound-unk = sound-pen
sound-and sound-pen sound-pen = sound-pen
sound-and {m₁} {_} {_} {d₂} sound-pen sound-m-unk = pen-and-unk m₁ d₂
  where
    pen-and-unk : ∀ a b → Sound (a ∧TV Unknown) (Pending ∧TV b)
    pen-and-unk True    True    = sound-pen
    pen-and-unk True    False   = sound-m-unk
    pen-and-unk True    Unknown = sound-pen
    pen-and-unk True    Pending = sound-pen
    pen-and-unk False   True    = sound-pen
    pen-and-unk False   False   = sound-ff
    pen-and-unk False   Unknown = sound-pen
    pen-and-unk False   Pending = sound-pen
    pen-and-unk Unknown True    = sound-pen
    pen-and-unk Unknown False   = sound-m-unk
    pen-and-unk Unknown Unknown = sound-pen
    pen-and-unk Unknown Pending = sound-pen
    pen-and-unk Pending True    = sound-pen
    pen-and-unk Pending False   = sound-m-pen
    pen-and-unk Pending Unknown = sound-pen
    pen-and-unk Pending Pending = sound-pen
sound-and {m₁} {_} {_} {d₂} sound-pen sound-m-pen = pen-and-pen m₁ d₂
  where
    pen-and-pen : ∀ a b → Sound (a ∧TV Pending) (Pending ∧TV b)
    pen-and-pen True    True    = sound-pen
    pen-and-pen True    False   = sound-m-pen
    pen-and-pen True    Unknown = sound-pen
    pen-and-pen True    Pending = sound-pen
    pen-and-pen False   True    = sound-pen
    pen-and-pen False   False   = sound-ff
    pen-and-pen False   Unknown = sound-pen
    pen-and-pen False   Pending = sound-pen
    pen-and-pen Unknown True    = sound-pen
    pen-and-pen Unknown False   = sound-m-pen
    pen-and-pen Unknown Unknown = sound-pen
    pen-and-pen Unknown Pending = sound-pen
    pen-and-pen Pending True    = sound-pen
    pen-and-pen Pending False   = sound-m-pen
    pen-and-pen Pending Unknown = sound-pen
    pen-and-pen Pending Pending = sound-pen
sound-and sound-m-unk sound-tt = sound-m-unk
sound-and {_} {d₁} sound-m-unk sound-ff rewrite ∧TV-false-r d₁ = sound-ff
sound-and {_} {d₁} {m₂} {_} sound-m-unk sound-unk = munk-and-unk m₂ d₁
  where
    munk-and-unk : ∀ a b → Sound (Unknown ∧TV a) (b ∧TV Unknown)
    munk-and-unk True    True    = sound-unk
    munk-and-unk True    False   = sound-m-unk
    munk-and-unk True    Unknown = sound-unk
    munk-and-unk True    Pending = sound-pen
    munk-and-unk False   True    = sound-unk
    munk-and-unk False   False   = sound-ff
    munk-and-unk False   Unknown = sound-unk
    munk-and-unk False   Pending = sound-pen
    munk-and-unk Unknown True    = sound-unk
    munk-and-unk Unknown False   = sound-m-unk
    munk-and-unk Unknown Unknown = sound-unk
    munk-and-unk Unknown Pending = sound-pen
    munk-and-unk Pending True    = sound-unk
    munk-and-unk Pending False   = sound-m-pen
    munk-and-unk Pending Unknown = sound-unk
    munk-and-unk Pending Pending = sound-pen
sound-and {_} {d₁} {m₂} {_} sound-m-unk sound-pen = munk-and-pen m₂ d₁
  where
    munk-and-pen : ∀ a b → Sound (Unknown ∧TV a) (b ∧TV Pending)
    munk-and-pen True    True    = sound-pen
    munk-and-pen True    False   = sound-m-unk
    munk-and-pen True    Unknown = sound-pen
    munk-and-pen True    Pending = sound-pen
    munk-and-pen False   True    = sound-pen
    munk-and-pen False   False   = sound-ff
    munk-and-pen False   Unknown = sound-pen
    munk-and-pen False   Pending = sound-pen
    munk-and-pen Unknown True    = sound-pen
    munk-and-pen Unknown False   = sound-m-unk
    munk-and-pen Unknown Unknown = sound-pen
    munk-and-pen Unknown Pending = sound-pen
    munk-and-pen Pending True    = sound-pen
    munk-and-pen Pending False   = sound-m-pen
    munk-and-pen Pending Unknown = sound-pen
    munk-and-pen Pending Pending = sound-pen
sound-and sound-m-unk sound-m-unk = sound-m-unk
sound-and sound-m-unk sound-m-pen = sound-m-pen
sound-and sound-m-pen sound-tt = sound-m-pen
sound-and {_} {d₁} sound-m-pen sound-ff rewrite ∧TV-false-r d₁ = sound-ff
sound-and {_} {d₁} {m₂} {_} sound-m-pen sound-unk = mpen-and-unk m₂ d₁
  where
    mpen-and-unk : ∀ a b → Sound (Pending ∧TV a) (b ∧TV Unknown)
    mpen-and-unk True    True    = sound-unk
    mpen-and-unk True    False   = sound-m-pen
    mpen-and-unk True    Unknown = sound-unk
    mpen-and-unk True    Pending = sound-pen
    mpen-and-unk False   True    = sound-unk
    mpen-and-unk False   False   = sound-ff
    mpen-and-unk False   Unknown = sound-unk
    mpen-and-unk False   Pending = sound-pen
    mpen-and-unk Unknown True    = sound-unk
    mpen-and-unk Unknown False   = sound-m-pen
    mpen-and-unk Unknown Unknown = sound-unk
    mpen-and-unk Unknown Pending = sound-pen
    mpen-and-unk Pending True    = sound-unk
    mpen-and-unk Pending False   = sound-m-pen
    mpen-and-unk Pending Unknown = sound-unk
    mpen-and-unk Pending Pending = sound-pen
sound-and {_} {d₁} {m₂} {_} sound-m-pen sound-pen = mpen-and-pen m₂ d₁
  where
    mpen-and-pen : ∀ a b → Sound (Pending ∧TV a) (b ∧TV Pending)
    mpen-and-pen True    True    = sound-pen
    mpen-and-pen True    False   = sound-m-pen
    mpen-and-pen True    Unknown = sound-pen
    mpen-and-pen True    Pending = sound-pen
    mpen-and-pen False   True    = sound-pen
    mpen-and-pen False   False   = sound-ff
    mpen-and-pen False   Unknown = sound-pen
    mpen-and-pen False   Pending = sound-pen
    mpen-and-pen Unknown True    = sound-pen
    mpen-and-pen Unknown False   = sound-m-pen
    mpen-and-pen Unknown Unknown = sound-pen
    mpen-and-pen Unknown Pending = sound-pen
    mpen-and-pen Pending True    = sound-pen
    mpen-and-pen Pending False   = sound-m-pen
    mpen-and-pen Pending Unknown = sound-pen
    mpen-and-pen Pending Pending = sound-pen
sound-and sound-m-pen sound-m-unk = sound-m-pen
sound-and sound-m-pen sound-m-pen = sound-m-pen

sound-or : ∀ {m₁ d₁ m₂ d₂} → Sound m₁ d₁ → Sound m₂ d₂ → Sound (m₁ ∨TV m₂) (d₁ ∨TV d₂)
sound-or sound-tt _ = sound-tt
sound-or sound-ff sound-tt = sound-tt
sound-or sound-ff sound-ff = sound-ff
sound-or sound-ff sound-unk = sound-unk
sound-or sound-ff sound-pen = sound-pen
sound-or sound-ff sound-m-unk = sound-m-unk
sound-or sound-ff sound-m-pen = sound-m-pen
sound-or {m₁} sound-unk sound-tt rewrite ∨TV-true-r m₁ = sound-tt
sound-or sound-unk sound-ff = sound-unk
sound-or sound-unk sound-unk = sound-unk
sound-or sound-unk sound-pen = sound-pen
sound-or {m₁} {_} {_} {d₂} sound-unk sound-m-unk = unk-or-unk m₁ d₂
  where
    unk-or-unk : ∀ a b → Sound (a ∨TV Unknown) (Unknown ∨TV b)
    unk-or-unk True    True    = sound-tt
    unk-or-unk True    False   = sound-unk
    unk-or-unk True    Unknown = sound-unk
    unk-or-unk True    Pending = sound-pen
    unk-or-unk False   True    = sound-m-unk
    unk-or-unk False   False   = sound-unk
    unk-or-unk False   Unknown = sound-unk
    unk-or-unk False   Pending = sound-pen
    unk-or-unk Unknown True    = sound-m-unk
    unk-or-unk Unknown False   = sound-unk
    unk-or-unk Unknown Unknown = sound-unk
    unk-or-unk Unknown Pending = sound-pen
    unk-or-unk Pending True    = sound-m-pen
    unk-or-unk Pending False   = sound-unk
    unk-or-unk Pending Unknown = sound-unk
    unk-or-unk Pending Pending = sound-pen
sound-or {m₁} {_} {_} {d₂} sound-unk sound-m-pen = unk-or-pen m₁ d₂
  where
    unk-or-pen : ∀ a b → Sound (a ∨TV Pending) (Unknown ∨TV b)
    unk-or-pen True    True    = sound-tt
    unk-or-pen True    False   = sound-unk
    unk-or-pen True    Unknown = sound-unk
    unk-or-pen True    Pending = sound-pen
    unk-or-pen False   True    = sound-m-pen
    unk-or-pen False   False   = sound-unk
    unk-or-pen False   Unknown = sound-unk
    unk-or-pen False   Pending = sound-pen
    unk-or-pen Unknown True    = sound-m-pen
    unk-or-pen Unknown False   = sound-unk
    unk-or-pen Unknown Unknown = sound-unk
    unk-or-pen Unknown Pending = sound-pen
    unk-or-pen Pending True    = sound-m-pen
    unk-or-pen Pending False   = sound-unk
    unk-or-pen Pending Unknown = sound-unk
    unk-or-pen Pending Pending = sound-pen
sound-or {m₁} sound-pen sound-tt rewrite ∨TV-true-r m₁ = sound-tt
sound-or {m₁} sound-pen sound-ff rewrite ∨TV-false-r m₁ = sound-pen
sound-or sound-pen sound-unk = sound-pen
sound-or sound-pen sound-pen = sound-pen
sound-or {m₁} {_} {_} {d₂} sound-pen sound-m-unk = pen-or-unk m₁ d₂
  where
    pen-or-unk : ∀ a b → Sound (a ∨TV Unknown) (Pending ∨TV b)
    pen-or-unk True    True    = sound-tt
    pen-or-unk True    False   = sound-pen
    pen-or-unk True    Unknown = sound-pen
    pen-or-unk True    Pending = sound-pen
    pen-or-unk False   True    = sound-m-unk
    pen-or-unk False   False   = sound-pen
    pen-or-unk False   Unknown = sound-pen
    pen-or-unk False   Pending = sound-pen
    pen-or-unk Unknown True    = sound-m-unk
    pen-or-unk Unknown False   = sound-pen
    pen-or-unk Unknown Unknown = sound-pen
    pen-or-unk Unknown Pending = sound-pen
    pen-or-unk Pending True    = sound-m-pen
    pen-or-unk Pending False   = sound-pen
    pen-or-unk Pending Unknown = sound-pen
    pen-or-unk Pending Pending = sound-pen
sound-or {m₁} {_} {_} {d₂} sound-pen sound-m-pen = pen-or-pen m₁ d₂
  where
    pen-or-pen : ∀ a b → Sound (a ∨TV Pending) (Pending ∨TV b)
    pen-or-pen True    True    = sound-tt
    pen-or-pen True    False   = sound-pen
    pen-or-pen True    Unknown = sound-pen
    pen-or-pen True    Pending = sound-pen
    pen-or-pen False   True    = sound-m-pen
    pen-or-pen False   False   = sound-pen
    pen-or-pen False   Unknown = sound-pen
    pen-or-pen False   Pending = sound-pen
    pen-or-pen Unknown True    = sound-m-pen
    pen-or-pen Unknown False   = sound-pen
    pen-or-pen Unknown Unknown = sound-pen
    pen-or-pen Unknown Pending = sound-pen
    pen-or-pen Pending True    = sound-m-pen
    pen-or-pen Pending False   = sound-pen
    pen-or-pen Pending Unknown = sound-pen
    pen-or-pen Pending Pending = sound-pen
sound-or {_} {d₁} sound-m-unk sound-tt rewrite ∨TV-true-r d₁ = sound-tt
sound-or sound-m-unk sound-ff = sound-m-unk
sound-or {_} {d₁} {m₂} {_} sound-m-unk sound-unk = munk-or-unk m₂ d₁
  where
    munk-or-unk : ∀ a b → Sound (Unknown ∨TV a) (b ∨TV Unknown)
    munk-or-unk True    True    = sound-tt
    munk-or-unk True    False   = sound-unk
    munk-or-unk True    Unknown = sound-unk
    munk-or-unk True    Pending = sound-pen
    munk-or-unk False   True    = sound-m-unk
    munk-or-unk False   False   = sound-unk
    munk-or-unk False   Unknown = sound-unk
    munk-or-unk False   Pending = sound-pen
    munk-or-unk Unknown True    = sound-m-unk
    munk-or-unk Unknown False   = sound-unk
    munk-or-unk Unknown Unknown = sound-unk
    munk-or-unk Unknown Pending = sound-pen
    munk-or-unk Pending True    = sound-m-pen
    munk-or-unk Pending False   = sound-unk
    munk-or-unk Pending Unknown = sound-unk
    munk-or-unk Pending Pending = sound-pen
sound-or {_} {d₁} {m₂} {_} sound-m-unk sound-pen = munk-or-pen m₂ d₁
  where
    munk-or-pen : ∀ a b → Sound (Unknown ∨TV a) (b ∨TV Pending)
    munk-or-pen True    True    = sound-tt
    munk-or-pen True    False   = sound-pen
    munk-or-pen True    Unknown = sound-pen
    munk-or-pen True    Pending = sound-pen
    munk-or-pen False   True    = sound-m-unk
    munk-or-pen False   False   = sound-pen
    munk-or-pen False   Unknown = sound-pen
    munk-or-pen False   Pending = sound-pen
    munk-or-pen Unknown True    = sound-m-unk
    munk-or-pen Unknown False   = sound-pen
    munk-or-pen Unknown Unknown = sound-pen
    munk-or-pen Unknown Pending = sound-pen
    munk-or-pen Pending True    = sound-m-pen
    munk-or-pen Pending False   = sound-pen
    munk-or-pen Pending Unknown = sound-pen
    munk-or-pen Pending Pending = sound-pen
sound-or sound-m-unk sound-m-unk = sound-m-unk
sound-or sound-m-unk sound-m-pen = sound-m-pen
sound-or {_} {d₁} sound-m-pen sound-tt rewrite ∨TV-true-r d₁ = sound-tt
sound-or {_} {d₁} sound-m-pen sound-ff rewrite ∨TV-false-r d₁ = sound-m-pen
sound-or {_} {d₁} {m₂} {_} sound-m-pen sound-unk = mpen-or-unk m₂ d₁
  where
    mpen-or-unk : ∀ a b → Sound (Pending ∨TV a) (b ∨TV Unknown)
    mpen-or-unk True    True    = sound-tt
    mpen-or-unk True    False   = sound-unk
    mpen-or-unk True    Unknown = sound-unk
    mpen-or-unk True    Pending = sound-pen
    mpen-or-unk False   True    = sound-m-pen
    mpen-or-unk False   False   = sound-unk
    mpen-or-unk False   Unknown = sound-unk
    mpen-or-unk False   Pending = sound-pen
    mpen-or-unk Unknown True    = sound-m-pen
    mpen-or-unk Unknown False   = sound-unk
    mpen-or-unk Unknown Unknown = sound-unk
    mpen-or-unk Unknown Pending = sound-pen
    mpen-or-unk Pending True    = sound-m-pen
    mpen-or-unk Pending False   = sound-unk
    mpen-or-unk Pending Unknown = sound-unk
    mpen-or-unk Pending Pending = sound-pen
sound-or {_} {d₁} {m₂} {_} sound-m-pen sound-pen = mpen-or-pen m₂ d₁
  where
    mpen-or-pen : ∀ a b → Sound (Pending ∨TV a) (b ∨TV Pending)
    mpen-or-pen True    True    = sound-tt
    mpen-or-pen True    False   = sound-pen
    mpen-or-pen True    Unknown = sound-pen
    mpen-or-pen True    Pending = sound-pen
    mpen-or-pen False   True    = sound-m-pen
    mpen-or-pen False   False   = sound-pen
    mpen-or-pen False   Unknown = sound-pen
    mpen-or-pen False   Pending = sound-pen
    mpen-or-pen Unknown True    = sound-m-pen
    mpen-or-pen Unknown False   = sound-pen
    mpen-or-pen Unknown Unknown = sound-pen
    mpen-or-pen Unknown Pending = sound-pen
    mpen-or-pen Pending True    = sound-m-pen
    mpen-or-pen Pending False   = sound-pen
    mpen-or-pen Pending Unknown = sound-pen
    mpen-or-pen Pending Pending = sound-pen
sound-or sound-m-pen sound-m-unk = sound-m-pen
sound-or sound-m-pen sound-m-pen = sound-m-pen

-- Derived combinators: sound-or/sound-and with one absorbing argument.
-- These avoid stuck ∨TV/∧TV reductions (False ∨TV abstract, True ∧TV abstract)
-- by pattern matching on Sound constructors so both sides are concrete.
--
-- Why pattern matching (not subst): When the result of sound-or-false-l is passed
-- to sound-and or other combinators, the monitor component must be fully concrete.
-- subst leaves an abstract ∨TV/∧TV expression that blocks downstream unification.
-- Pattern matching computes the result directly — no stuck terms.

sound-or-false-l : ∀ {d₁ d₂ m₂} → Sound False d₁ → Sound m₂ d₂ → Sound m₂ (d₁ ∨TV d₂)
-- m₂ abstract: result independent of ∨TV computation
sound-or-false-l _         sound-m-unk = sound-m-unk
sound-or-false-l _         sound-m-pen = sound-m-pen
-- Both d₁ and d₂ concrete: ∨TV reduces, result mirrors output
sound-or-false-l sound-ff  sound-tt    = sound-tt
sound-or-false-l sound-ff  sound-ff    = sound-ff
sound-or-false-l sound-ff  sound-unk   = sound-unk
sound-or-false-l sound-ff  sound-pen   = sound-pen
sound-or-false-l sound-unk sound-tt    = sound-tt
sound-or-false-l sound-unk sound-ff    = sound-unk
sound-or-false-l sound-unk sound-unk   = sound-unk
sound-or-false-l sound-unk sound-pen   = sound-pen
sound-or-false-l sound-pen sound-tt    = sound-tt
sound-or-false-l sound-pen sound-ff    = sound-pen
sound-or-false-l sound-pen sound-unk   = sound-pen
sound-or-false-l sound-pen sound-pen   = sound-pen

sound-or-false-r : ∀ {d₁ d₂ m₁} → Sound m₁ d₁ → Sound False d₂ → Sound m₁ (d₁ ∨TV d₂)
sound-or-false-r sound-m-unk _         = sound-m-unk
sound-or-false-r sound-m-pen _         = sound-m-pen
sound-or-false-r sound-tt    _         = sound-tt
sound-or-false-r sound-ff  sound-ff    = sound-ff
sound-or-false-r sound-ff  sound-unk   = sound-unk
sound-or-false-r sound-ff  sound-pen   = sound-pen
sound-or-false-r sound-unk sound-ff    = sound-unk
sound-or-false-r sound-unk sound-unk   = sound-unk
sound-or-false-r sound-unk sound-pen   = sound-pen
sound-or-false-r sound-pen sound-ff    = sound-pen
sound-or-false-r sound-pen sound-unk   = sound-pen
sound-or-false-r sound-pen sound-pen   = sound-pen

sound-and-true-l : ∀ {d₁ d₂ m₂} → Sound True d₁ → Sound m₂ d₂ → Sound m₂ (d₁ ∧TV d₂)
sound-and-true-l _         sound-m-unk = sound-m-unk
sound-and-true-l _         sound-m-pen = sound-m-pen
sound-and-true-l sound-tt  sound-tt    = sound-tt
sound-and-true-l sound-tt  sound-ff    = sound-ff
sound-and-true-l sound-tt  sound-unk   = sound-unk
sound-and-true-l sound-tt  sound-pen   = sound-pen
sound-and-true-l sound-unk sound-tt    = sound-unk
sound-and-true-l sound-unk sound-ff    = sound-ff
sound-and-true-l sound-unk sound-unk   = sound-unk
sound-and-true-l sound-unk sound-pen   = sound-pen
sound-and-true-l sound-pen sound-tt    = sound-pen
sound-and-true-l sound-pen sound-ff    = sound-ff
sound-and-true-l sound-pen sound-unk   = sound-pen
sound-and-true-l sound-pen sound-pen   = sound-pen

sound-and-true-r : ∀ {d₁ d₂ m₁} → Sound m₁ d₁ → Sound True d₂ → Sound m₁ (d₁ ∧TV d₂)
sound-and-true-r sound-m-unk _         = sound-m-unk
sound-and-true-r sound-m-pen _         = sound-m-pen
sound-and-true-r sound-ff    _         = sound-ff
sound-and-true-r sound-tt  sound-tt    = sound-tt
sound-and-true-r sound-tt  sound-unk   = sound-unk
sound-and-true-r sound-tt  sound-pen   = sound-pen
sound-and-true-r sound-unk sound-tt    = sound-unk
sound-and-true-r sound-unk sound-unk   = sound-unk
sound-and-true-r sound-unk sound-pen   = sound-pen
sound-and-true-r sound-pen sound-tt    = sound-pen
sound-and-true-r sound-pen sound-unk   = sound-pen
sound-and-true-r sound-pen sound-pen   = sound-pen

-- ============================================================================
-- OPERATIONAL DECOMPOSITION LEMMAS
-- ============================================================================

-- runL distributes over And: the coalgebra run of And φ ψ equals
-- the ∧TV combination of the individual runs.
-- Proof: list induction on σ. Base case uses finalizeL decomposition.
-- Inductive case uses combineAnd decomposition + IH.

runL-and-decomp : ∀ (table : PredTable) (φ ψ : LTLProc) (σ : List TimedFrame)
  → runL table (And φ ψ) σ ≡ (runL table φ σ) ∧TV (runL table ψ σ)
runL-and-decomp table φ ψ [] with finalizeL φ
... | Fails _ = refl
... | Holds with finalizeL ψ
...   | Fails _ = refl
...   | Holds   = refl
runL-and-decomp table φ ψ (x ∷ σ) with stepL table φ x | stepL table ψ x
... | Violated _   | _             = refl
... | Satisfied    | Violated _    = refl
... | Continue _ a | Violated _    rewrite ∧TV-false-r (runL table a σ) = refl
... | Satisfied    | Satisfied     = refl
... | Satisfied    | Continue _ b  rewrite ∧TV-true-l (runL table b σ) = refl
... | Continue _ a | Satisfied     rewrite ∧TV-true-r (runL table a σ) = refl
... | Continue _ a | Continue _ b  = runL-and-decomp table a b σ

-- runL distributes over Not: coalgebra run of Not φ equals notTV of the inner run.
runL-not-decomp : ∀ (table : PredTable) (φ : LTLProc) (σ : List TimedFrame)
  → runL table (Not φ) σ ≡ notTV (runL table φ σ)
runL-not-decomp table φ [] with finalizeL φ
... | Holds   = refl
... | Fails _ = refl
runL-not-decomp table φ (x ∷ σ) with stepL table φ x
... | Satisfied    = refl
... | Violated _   = refl
... | Continue _ φ' = runL-not-decomp table φ' σ

-- runL distributes over Or: dual of runL-and-decomp.
runL-or-decomp : ∀ (table : PredTable) (φ ψ : LTLProc) (σ : List TimedFrame)
  → runL table (Or φ ψ) σ ≡ (runL table φ σ) ∨TV (runL table ψ σ)
runL-or-decomp table φ ψ [] with finalizeL φ
... | Holds = refl
... | Fails _ with finalizeL ψ
...   | Holds   = refl
...   | Fails _ = refl
runL-or-decomp table φ ψ (x ∷ σ) with stepL table φ x | stepL table ψ x
... | Satisfied    | _             = refl
... | Violated _   | Satisfied     = refl
... | Violated _   | Violated _    = refl
... | Violated _   | Continue _ b  rewrite ∨TV-false-l (runL table b σ) = refl
... | Continue _ a | Satisfied     rewrite ∨TV-true-r (runL table a σ) = refl
... | Continue _ a | Violated _    rewrite ∨TV-false-r (runL table a σ) = refl
... | Continue _ a | Continue _ b  = runL-or-decomp table a b σ

-- runL distributes over Always: coalgebra run decomposes like the denotational semantics.
-- Always φ steps as combineAnd (stepL φ) (Continue 0 (Always φ)), matching ⟦φ⟧∧TV⟦G φ⟧.
runL-always-decomp : ∀ (table : PredTable) (φ : LTLProc) (x : TimedFrame) (rest : List TimedFrame)
  → runL table (Always φ) (x ∷ rest) ≡ (runL table φ (x ∷ rest)) ∧TV (runL table (Always φ) rest)
runL-always-decomp table φ x rest with stepL table φ x
... | Satisfied     rewrite ∧TV-true-l (runL table (Always φ) rest) = refl
... | Violated _    = refl
... | Continue _ φ' = runL-and-decomp table φ' (Always φ) rest

-- runL distributes over Eventually: dual of Always decomposition.
-- Eventually φ steps as combineOr (stepL φ) (Continue 0 (Eventually φ)), matching ⟦φ⟧∨TV⟦F φ⟧.
runL-eventually-decomp : ∀ (table : PredTable) (φ : LTLProc) (x : TimedFrame) (rest : List TimedFrame)
  → runL table (Eventually φ) (x ∷ rest) ≡ (runL table φ (x ∷ rest)) ∨TV (runL table (Eventually φ) rest)
runL-eventually-decomp table φ x rest with stepL table φ x
... | Satisfied     = refl
... | Violated _    rewrite ∨TV-false-l (runL table (Eventually φ) rest) = refl
... | Continue _ φ' = runL-or-decomp table φ' (Eventually φ) rest

-- runL distributes over Until: φ U ψ ≡ ψ ∨ (φ ∧ X(φ U ψ)).
-- stepL(Until φ ψ) = combineOr (stepL ψ) (combineAnd (stepL φ) (Continue 0 (Until φ ψ)))
runL-until-decomp : ∀ (table : PredTable) (φ ψ : LTLProc) (x : TimedFrame) (rest : List TimedFrame)
  → runL table (Until φ ψ) (x ∷ rest)
    ≡ (runL table ψ (x ∷ rest)) ∨TV ((runL table φ (x ∷ rest)) ∧TV (runL table (Until φ ψ) rest))
runL-until-decomp table φ ψ x rest with stepL table ψ x | stepL table φ x
... | Satisfied     | _             = refl
... | Violated _    | Violated _    = refl
... | Violated _    | Satisfied
    rewrite ∧TV-true-l (runL table (Until φ ψ) rest)
          | ∨TV-false-l (runL table (Until φ ψ) rest) = refl
... | Violated _    | Continue _ φ'
    rewrite ∨TV-false-l ((runL table φ' rest) ∧TV (runL table (Until φ ψ) rest))
    = runL-and-decomp table φ' (Until φ ψ) rest
... | Continue _ ψ' | Violated _
    rewrite ∨TV-false-r (runL table ψ' rest) = refl
... | Continue _ ψ' | Satisfied
    rewrite ∧TV-true-l (runL table (Until φ ψ) rest)
    = runL-or-decomp table ψ' (Until φ ψ) rest
... | Continue _ ψ' | Continue _ φ'
    rewrite sym (runL-and-decomp table φ' (Until φ ψ) rest)
    = runL-or-decomp table ψ' (And φ' (Until φ ψ)) rest

-- runL distributes over Release: φ R ψ ≡ ψ ∧ (φ ∨ X(φ R ψ)).
-- stepL(Release φ ψ) = combineAnd (stepL ψ) (combineOr (stepL φ) (Continue 0 (Release φ ψ)))
runL-release-decomp : ∀ (table : PredTable) (φ ψ : LTLProc) (x : TimedFrame) (rest : List TimedFrame)
  → runL table (Release φ ψ) (x ∷ rest)
    ≡ (runL table ψ (x ∷ rest)) ∧TV ((runL table φ (x ∷ rest)) ∨TV (runL table (Release φ ψ) rest))
runL-release-decomp table φ ψ x rest with stepL table ψ x | stepL table φ x
... | Violated _    | _             = refl
... | Satisfied     | Satisfied     = refl
... | Satisfied     | Violated _
    rewrite ∨TV-false-l (runL table (Release φ ψ) rest)
          | ∧TV-true-l (runL table (Release φ ψ) rest) = refl
... | Satisfied     | Continue _ φ'
    rewrite ∧TV-true-l ((runL table φ' rest) ∨TV (runL table (Release φ ψ) rest))
    = runL-or-decomp table φ' (Release φ ψ) rest
... | Continue _ ψ' | Satisfied
    rewrite ∧TV-true-r (runL table ψ' rest) = refl
... | Continue _ ψ' | Violated _
    rewrite ∨TV-false-l (runL table (Release φ ψ) rest)
    = runL-and-decomp table ψ' (Release φ ψ) rest
... | Continue _ ψ' | Continue _ φ'
    rewrite sym (runL-or-decomp table φ' (Release φ ψ) rest)
    = runL-and-decomp table ψ' (Or φ' (Release φ ψ)) rest

-- ============================================================================
-- METRIC OPERATOR HELPERS
-- ============================================================================

-- Bridge between met-*-go helpers and ⟦ Metric* (suc start) ⟧.
-- The go helpers are top-level mutual functions in Semantics.agda.
-- Key property: met-ev-go w φ start σ ≡ ⟦ MetricEventually w (suc start) φ ⟧ σ
-- This is NOT definitional for abstract σ (both are stuck pattern matches),
-- but holds by case split on σ (both clauses are refl).

private
  met-ev-go-denot : ∀ (w : ℕ) (φ : LTL (TimedFrame → TruthVal)) (start : ℕ) (σ : List TimedFrame)
    → met-ev-go w φ start σ ≡ ⟦ Syntax.MetricEventually w (suc start) φ ⟧ σ
  met-ev-go-denot w φ start [] = refl
  met-ev-go-denot w φ start (_ ∷ _) = refl

  met-al-go-denot : ∀ (w : ℕ) (φ : LTL (TimedFrame → TruthVal)) (start : ℕ) (σ : List TimedFrame)
    → met-al-go w φ start σ ≡ ⟦ Syntax.MetricAlways w (suc start) φ ⟧ σ
  met-al-go-denot w φ start [] = refl
  met-al-go-denot w φ start (_ ∷ _) = refl

  met-un-go-denot : ∀ (w : ℕ) (φ ψ : LTL (TimedFrame → TruthVal)) (start : ℕ) (σ : List TimedFrame)
    → met-un-go w φ ψ start σ ≡ ⟦ Syntax.MetricUntil w (suc start) φ ψ ⟧ σ
  met-un-go-denot w φ ψ start [] = refl
  met-un-go-denot w φ ψ start (_ ∷ _) = refl

  met-re-go-denot : ∀ (w : ℕ) (φ ψ : LTL (TimedFrame → TruthVal)) (start : ℕ) (σ : List TimedFrame)
    → met-re-go w φ ψ start σ ≡ ⟦ Syntax.MetricRelease w (suc start) φ ψ ⟧ σ
  met-re-go-denot w φ ψ start [] = refl
  met-re-go-denot w φ ψ start (_ ∷ _) = refl

-- Generic monitor-side transport: rewrite the monitor argument of Sound
-- along an equality, without generating with-auxiliaries (unlike rewrite).
-- This is the single pattern that all operational transport lemmas use.

sound-transport-monitor : ∀ {m₁ m₂ d} → m₁ ≡ m₂ → Sound m₁ d → Sound m₂ d
sound-transport-monitor {d = d} eq = subst (λ m → Sound m d) eq

sound-transport-denot : ∀ {m d₁ d₂} → d₁ ≡ d₂ → Sound m d₁ → Sound m d₂
sound-transport-denot {m = m} eq = subst (Sound m) eq

-- Denotational transport: convert adequacy IH from ⟦ MetricOp (suc start) ⟧
-- to met-*-go. These avoid `rewrite met-*-go-denot` which generates
-- with-auxiliaries that hide recursive calls from the termination checker.

met-ev-go-sound : ∀ {m} w φ start rest →
  Sound m (⟦ Syntax.MetricEventually w (suc start) φ ⟧ rest) →
  Sound m (met-ev-go w φ start rest)
met-ev-go-sound w φ start rest =
  sound-transport-denot (sym (met-ev-go-denot w φ start rest))

met-al-go-sound : ∀ {m} w φ start rest →
  Sound m (⟦ Syntax.MetricAlways w (suc start) φ ⟧ rest) →
  Sound m (met-al-go w φ start rest)
met-al-go-sound w φ start rest =
  sound-transport-denot (sym (met-al-go-denot w φ start rest))

met-un-go-sound : ∀ {m} w φ ψ start rest →
  Sound m (⟦ Syntax.MetricUntil w (suc start) φ ψ ⟧ rest) →
  Sound m (met-un-go w φ ψ start rest)
met-un-go-sound w φ ψ start rest =
  sound-transport-denot (sym (met-un-go-denot w φ ψ start rest))

met-re-go-sound : ∀ {m} w φ ψ start rest →
  Sound m (⟦ Syntax.MetricRelease w (suc start) φ ψ ⟧ rest) →
  Sound m (met-re-go w φ ψ start rest)
met-re-go-sound w φ ψ start rest =
  sound-transport-denot (sym (met-re-go-denot w φ ψ start rest))

-- Monitor-side transport: convert between runL on composed formulas
-- and ∨TV/∧TV of decomposed runL results.

runL-or-sound : ∀ {d} (table : PredTable) (φ ψ : LTLProc) (σ : List TimedFrame)
  → Sound (runL table φ σ ∨TV runL table ψ σ) d
  → Sound (runL table (Or φ ψ) σ) d
runL-or-sound table φ ψ σ =
  sound-transport-monitor (sym (runL-or-decomp table φ ψ σ))

runL-and-sound : ∀ {d} (table : PredTable) (φ ψ : LTLProc) (σ : List TimedFrame)
  → Sound (runL table φ σ ∧TV runL table ψ σ) d
  → Sound (runL table (And φ ψ) σ) d
runL-and-sound table φ ψ σ =
  sound-transport-monitor (sym (runL-and-decomp table φ ψ σ))

-- ============================================================================
-- METRIC DECOMPOSITION LEMMAS
-- ============================================================================

-- Conditional decomposition: when inWindow ≡ true, the metric operators
-- decompose like their unbounded counterparts (Eventually/Always/Until/Release).
-- The false case is absurd (discharged via () on the equality proof).

-- MetricEventually: mirrors runL-eventually-decomp
runL-metric-eventually-decomp : ∀ (table : PredTable) (w s : ℕ) (φ : LTLProc) (x : TimedFrame) (rest : List TimedFrame)
  → ((timestamp x ∸ decodeStart s (timestamp x)) ≤ᵇ w) ≡ true
  → runL table (MetricEventuallyProc w s φ) (x ∷ rest)
    ≡ (runL table φ (x ∷ rest)) ∨TV (runL table (MetricEventuallyProc w (suc (decodeStart s (timestamp x))) φ) rest)
runL-metric-eventually-decomp table w s φ x rest eq
  with (timestamp x ∸ decodeStart s (timestamp x)) ≤ᵇ w
runL-metric-eventually-decomp table w s φ x rest () | false
runL-metric-eventually-decomp table w s φ x rest eq | true with stepL table φ x
... | Satisfied     = refl
... | Violated _    rewrite ∨TV-false-l (runL table (MetricEventuallyProc w (suc (decodeStart s (timestamp x))) φ) rest) = refl
... | Continue _ φ' = runL-or-decomp table φ' (MetricEventuallyProc w (suc (decodeStart s (timestamp x))) φ) rest

-- MetricAlways: mirrors runL-always-decomp
runL-metric-always-decomp : ∀ (table : PredTable) (w s : ℕ) (φ : LTLProc) (x : TimedFrame) (rest : List TimedFrame)
  → ((timestamp x ∸ decodeStart s (timestamp x)) ≤ᵇ w) ≡ true
  → runL table (MetricAlwaysProc w s φ) (x ∷ rest)
    ≡ (runL table φ (x ∷ rest)) ∧TV (runL table (MetricAlwaysProc w (suc (decodeStart s (timestamp x))) φ) rest)
runL-metric-always-decomp table w s φ x rest eq
  with (timestamp x ∸ decodeStart s (timestamp x)) ≤ᵇ w
runL-metric-always-decomp table w s φ x rest () | false
runL-metric-always-decomp table w s φ x rest eq | true with stepL table φ x
... | Satisfied     rewrite ∧TV-true-l (runL table (MetricAlwaysProc w (suc (decodeStart s (timestamp x))) φ) rest) = refl
... | Violated _    = refl
... | Continue _ φ' = runL-and-decomp table φ' (MetricAlwaysProc w (suc (decodeStart s (timestamp x))) φ) rest

-- MetricUntil: mirrors runL-until-decomp
runL-metric-until-decomp : ∀ (table : PredTable) (w s : ℕ) (φ ψ : LTLProc) (x : TimedFrame) (rest : List TimedFrame)
  → ((timestamp x ∸ decodeStart s (timestamp x)) ≤ᵇ w) ≡ true
  → runL table (MetricUntilProc w s φ ψ) (x ∷ rest)
    ≡ (runL table ψ (x ∷ rest)) ∨TV ((runL table φ (x ∷ rest)) ∧TV (runL table (MetricUntilProc w (suc (decodeStart s (timestamp x))) φ ψ) rest))
runL-metric-until-decomp table w s φ ψ x rest eq
  with (timestamp x ∸ decodeStart s (timestamp x)) ≤ᵇ w
runL-metric-until-decomp table w s φ ψ x rest () | false
runL-metric-until-decomp table w s φ ψ x rest eq | true with stepL table ψ x | stepL table φ x
... | Satisfied     | _             = refl
... | Violated _    | Violated _    = refl
... | Violated _    | Satisfied
    rewrite ∧TV-true-l (runL table (MetricUntilProc w (suc (decodeStart s (timestamp x))) φ ψ) rest)
          | ∨TV-false-l (runL table (MetricUntilProc w (suc (decodeStart s (timestamp x))) φ ψ) rest) = refl
... | Violated _    | Continue _ φ'
    rewrite ∨TV-false-l ((runL table φ' rest) ∧TV (runL table (MetricUntilProc w (suc (decodeStart s (timestamp x))) φ ψ) rest))
    = runL-and-decomp table φ' (MetricUntilProc w (suc (decodeStart s (timestamp x))) φ ψ) rest
... | Continue _ ψ' | Violated _
    rewrite ∨TV-false-r (runL table ψ' rest) = refl
... | Continue _ ψ' | Satisfied
    rewrite ∧TV-true-l (runL table (MetricUntilProc w (suc (decodeStart s (timestamp x))) φ ψ) rest)
    = runL-or-decomp table ψ' (MetricUntilProc w (suc (decodeStart s (timestamp x))) φ ψ) rest
... | Continue _ ψ' | Continue _ φ'
    rewrite sym (runL-and-decomp table φ' (MetricUntilProc w (suc (decodeStart s (timestamp x))) φ ψ) rest)
    = runL-or-decomp table ψ' (And φ' (MetricUntilProc w (suc (decodeStart s (timestamp x))) φ ψ)) rest

-- MetricRelease: mirrors runL-release-decomp
runL-metric-release-decomp : ∀ (table : PredTable) (w s : ℕ) (φ ψ : LTLProc) (x : TimedFrame) (rest : List TimedFrame)
  → ((timestamp x ∸ decodeStart s (timestamp x)) ≤ᵇ w) ≡ true
  → runL table (MetricReleaseProc w s φ ψ) (x ∷ rest)
    ≡ (runL table ψ (x ∷ rest)) ∧TV ((runL table φ (x ∷ rest)) ∨TV (runL table (MetricReleaseProc w (suc (decodeStart s (timestamp x))) φ ψ) rest))
runL-metric-release-decomp table w s φ ψ x rest eq
  with (timestamp x ∸ decodeStart s (timestamp x)) ≤ᵇ w
runL-metric-release-decomp table w s φ ψ x rest () | false
runL-metric-release-decomp table w s φ ψ x rest eq | true with stepL table ψ x | stepL table φ x
... | Violated _    | _             = refl
... | Satisfied     | Satisfied     = refl
... | Satisfied     | Violated _
    rewrite ∨TV-false-l (runL table (MetricReleaseProc w (suc (decodeStart s (timestamp x))) φ ψ) rest)
          | ∧TV-true-l (runL table (MetricReleaseProc w (suc (decodeStart s (timestamp x))) φ ψ) rest) = refl
... | Satisfied     | Continue _ φ'
    rewrite ∧TV-true-l ((runL table φ' rest) ∨TV (runL table (MetricReleaseProc w (suc (decodeStart s (timestamp x))) φ ψ) rest))
    = runL-or-decomp table φ' (MetricReleaseProc w (suc (decodeStart s (timestamp x))) φ ψ) rest
... | Continue _ ψ' | Satisfied
    rewrite ∧TV-true-r (runL table ψ' rest) = refl
... | Continue _ ψ' | Violated _
    rewrite ∨TV-false-l (runL table (MetricReleaseProc w (suc (decodeStart s (timestamp x))) φ ψ) rest)
    = runL-and-decomp table ψ' (MetricReleaseProc w (suc (decodeStart s (timestamp x))) φ ψ) rest
... | Continue _ ψ' | Continue _ φ'
    rewrite sym (runL-or-decomp table φ' (MetricReleaseProc w (suc (decodeStart s (timestamp x))) φ ψ) rest)
    = runL-and-decomp table ψ' (Or φ' (MetricReleaseProc w (suc (decodeStart s (timestamp x))) φ ψ)) rest

-- ============================================================================
-- METRIC ADEQUACY HELPERS (non-recursive)
-- ============================================================================

-- These helpers extract the boolean + stepL case analysis from adequacy,
-- so that adequacy itself has zero `with`s for metric operators.
-- The termination checker can then see the direct recursive calls.

-- MetricEventually: boolean guard + stepL case split. Non-recursive.
adequacy-met-ev : ∀ (table : PredTable) (w s : ℕ) (φ : LTLProc) (y : TimedFrame) (rest : List TimedFrame)
  → Sound (runL table φ (y ∷ rest)) (⟦ denot table φ ⟧ (y ∷ rest))
  → Sound (runL table (MetricEventuallyProc w (suc (decodeStart s (timestamp y))) φ) rest)
          (met-ev-go w (denot table φ) (decodeStart s (timestamp y)) rest)
  → Sound (runL table (MetricEventuallyProc w s φ) (y ∷ rest))
          (⟦ denot table (MetricEventuallyProc w s φ) ⟧ (y ∷ rest))
adequacy-met-ev table w s φ y rest ih-φ ih-MEP
  with (timestamp y ∸ decodeStart s (timestamp y)) ≤ᵇ w
... | false = sound-ff
... | true with stepL table φ y
...   | Satisfied   = sound-or ih-φ ih-MEP
...   | Violated _  = sound-or-false-l ih-φ ih-MEP
...   | Continue _ φ' = runL-or-sound table φ' (MetricEventuallyProc w (suc (decodeStart s (timestamp y))) φ) rest
                          (sound-or ih-φ ih-MEP)

-- MetricAlways: dual of MetricEventually (∧ instead of ∨, sound-tt on window expiry).
adequacy-met-al : ∀ (table : PredTable) (w s : ℕ) (φ : LTLProc) (y : TimedFrame) (rest : List TimedFrame)
  → Sound (runL table φ (y ∷ rest)) (⟦ denot table φ ⟧ (y ∷ rest))
  → Sound (runL table (MetricAlwaysProc w (suc (decodeStart s (timestamp y))) φ) rest)
          (met-al-go w (denot table φ) (decodeStart s (timestamp y)) rest)
  → Sound (runL table (MetricAlwaysProc w s φ) (y ∷ rest))
          (⟦ denot table (MetricAlwaysProc w s φ) ⟧ (y ∷ rest))
adequacy-met-al table w s φ y rest ih-φ ih-MAP
  with (timestamp y ∸ decodeStart s (timestamp y)) ≤ᵇ w
... | false = sound-tt
... | true with stepL table φ y
...   | Satisfied   = sound-and-true-l ih-φ ih-MAP
...   | Violated _  = sound-and ih-φ ih-MAP
...   | Continue _ φ' = runL-and-sound table φ' (MetricAlwaysProc w (suc (decodeStart s (timestamp y))) φ) rest
                          (sound-and ih-φ ih-MAP)

-- MetricUntil: simultaneous (stepL ψ × stepL φ) after boolean guard. Non-recursive.
adequacy-met-un : ∀ (table : PredTable) (w s : ℕ) (φ ψ : LTLProc) (y : TimedFrame) (rest : List TimedFrame)
  → Sound (runL table φ (y ∷ rest)) (⟦ denot table φ ⟧ (y ∷ rest))
  → Sound (runL table ψ (y ∷ rest)) (⟦ denot table ψ ⟧ (y ∷ rest))
  → Sound (runL table (MetricUntilProc w (suc (decodeStart s (timestamp y))) φ ψ) rest)
          (met-un-go w (denot table φ) (denot table ψ) (decodeStart s (timestamp y)) rest)
  → Sound (runL table (MetricUntilProc w s φ ψ) (y ∷ rest))
          (⟦ denot table (MetricUntilProc w s φ ψ) ⟧ (y ∷ rest))
adequacy-met-un table w s φ ψ y rest ih-φ ih-ψ ih-MUP
  with (timestamp y ∸ decodeStart s (timestamp y)) ≤ᵇ w
... | false = sound-ff
... | true with stepL table ψ y | stepL table φ y
...   | Satisfied     | _             = sound-or ih-ψ (sound-and ih-φ ih-MUP)
...   | Violated _    | Satisfied     = sound-or-false-l ih-ψ (sound-and-true-l ih-φ ih-MUP)
...   | Violated _    | Violated _    = sound-or ih-ψ (sound-and ih-φ ih-MUP)
...   | Violated _    | Continue _ φ' = sound-or-false-l ih-ψ
                                          (runL-and-sound table φ' (MetricUntilProc w (suc (decodeStart s (timestamp y))) φ ψ) rest
                                            (sound-and ih-φ ih-MUP))
...   | Continue _ ψ' | Satisfied     = runL-or-sound table ψ' (MetricUntilProc w (suc (decodeStart s (timestamp y))) φ ψ) rest
                                          (sound-or ih-ψ (sound-and-true-l ih-φ ih-MUP))
...   | Continue _ ψ' | Violated _    = sound-or-false-r ih-ψ (sound-and ih-φ ih-MUP)
...   | Continue _ ψ' | Continue _ φ' = runL-or-sound table ψ' (And φ' (MetricUntilProc w (suc (decodeStart s (timestamp y))) φ ψ)) rest
                                          (sound-or ih-ψ
                                            (runL-and-sound table φ' (MetricUntilProc w (suc (decodeStart s (timestamp y))) φ ψ) rest
                                              (sound-and ih-φ ih-MUP)))

-- MetricRelease: dual of MetricUntil (∧/∨ swapped). Non-recursive.
-- Decomposition: ψ ∧ (φ ∨ MRP). Simultaneous with on stepL ψ and stepL φ.
adequacy-met-re : ∀ (table : PredTable) (w s : ℕ) (φ ψ : LTLProc) (y : TimedFrame) (rest : List TimedFrame)
  → Sound (runL table φ (y ∷ rest)) (⟦ denot table φ ⟧ (y ∷ rest))
  → Sound (runL table ψ (y ∷ rest)) (⟦ denot table ψ ⟧ (y ∷ rest))
  → Sound (runL table (MetricReleaseProc w (suc (decodeStart s (timestamp y))) φ ψ) rest)
          (met-re-go w (denot table φ) (denot table ψ) (decodeStart s (timestamp y)) rest)
  → Sound (runL table (MetricReleaseProc w s φ ψ) (y ∷ rest))
          (⟦ denot table (MetricReleaseProc w s φ ψ) ⟧ (y ∷ rest))
adequacy-met-re table w s φ ψ y rest ih-φ ih-ψ ih-MRP
  with (timestamp y ∸ decodeStart s (timestamp y)) ≤ᵇ w
... | false = sound-tt
... | true with stepL table ψ y | stepL table φ y
...   | Violated _    | _             = sound-and ih-ψ (sound-or ih-φ ih-MRP)
...   | Satisfied     | Satisfied     = sound-and ih-ψ (sound-or ih-φ ih-MRP)
...   | Satisfied     | Violated _    = sound-and-true-l ih-ψ (sound-or-false-l ih-φ ih-MRP)
...   | Satisfied     | Continue _ φ' = sound-and-true-l ih-ψ
                                          (runL-or-sound table φ' (MetricReleaseProc w (suc (decodeStart s (timestamp y))) φ ψ) rest
                                            (sound-or ih-φ ih-MRP))
...   | Continue _ ψ' | Satisfied     = sound-and-true-r ih-ψ (sound-or ih-φ ih-MRP)
...   | Continue _ ψ' | Violated _    = runL-and-sound table ψ' (MetricReleaseProc w (suc (decodeStart s (timestamp y))) φ ψ) rest
                                          (sound-and ih-ψ (sound-or-false-l ih-φ ih-MRP))
...   | Continue _ ψ' | Continue _ φ' = runL-and-sound table ψ' (Or φ' (MetricReleaseProc w (suc (decodeStart s (timestamp y))) φ ψ)) rest
                                          (sound-and ih-ψ
                                            (runL-or-sound table φ' (MetricReleaseProc w (suc (decodeStart s (timestamp y))) φ ψ) rest
                                              (sound-or ih-φ ih-MRP)))

-- ============================================================================
-- ADEQUACY THEOREM
-- ============================================================================

-- The crown jewel: for any LTLProc and trace, the coalgebra execution (runL)
-- is sound with respect to the denotational semantics (⟦_⟧).
-- Structural induction on LTLProc (outer) + list induction on σ (inner).

adequacy : ∀ (table : PredTable) (proc : LTLProc) (σ : List TimedFrame)
  → Sound (runL table proc σ) (⟦ denot table proc ⟧ σ)

-- Atomic: empty trace
adequacy table (Atomic n) [] = sound-ff

-- Atomic: non-empty trace — case split on table n x
adequacy table (Atomic n) (x ∷ rest) with table n x
... | True    = sound-tt
... | False   = sound-ff
... | Unknown = sound-unk
... | Pending = sound-pen

-- And: decompose runL to ∧TV, then compose with sound-and + IH
adequacy table (And φ ψ) σ rewrite runL-and-decomp table φ ψ σ = sound-and (adequacy table φ σ) (adequacy table ψ σ)

-- Or: decompose runL to ∨TV, then compose with sound-or + IH
adequacy table (Or φ ψ) σ rewrite runL-or-decomp table φ ψ σ = sound-or (adequacy table φ σ) (adequacy table ψ σ)

-- Next: empty → sound-ff; non-empty → IH on tail
adequacy table (Next φ) [] = sound-ff
adequacy table (Next φ) (x ∷ rest) = adequacy table φ rest

-- Always: empty → sound-tt (vacuous); non-empty → decompose + sound-and + IH
-- Uses subst (not rewrite) to avoid with-generated auxiliary that confuses termination checker.
adequacy table (Always φ) [] = sound-tt
adequacy table (Always φ) (x ∷ rest) =
  subst (λ m → Sound m (⟦ denot table φ ⟧ (x ∷ rest) ∧TV ⟦ Syntax.Always (denot table φ) ⟧ rest))
        (sym (runL-always-decomp table φ x rest))
        (sound-and (adequacy table φ (x ∷ rest)) (adequacy table (Always φ) rest))

-- Eventually: empty → sound-ff; non-empty → decompose + sound-or + IH
adequacy table (Eventually φ) [] = sound-ff
adequacy table (Eventually φ) (x ∷ rest) =
  subst (λ m → Sound m (⟦ denot table φ ⟧ (x ∷ rest) ∨TV ⟦ Syntax.Eventually (denot table φ) ⟧ rest))
        (sym (runL-eventually-decomp table φ x rest))
        (sound-or (adequacy table φ (x ∷ rest)) (adequacy table (Eventually φ) rest))

-- Until: empty → sound-ff; non-empty → ψ ∨ (φ ∧ Until), subst on monitor
adequacy table (Until φ ψ) [] = sound-ff
adequacy table (Until φ ψ) (x ∷ rest) =
  subst (λ m → Sound m (⟦ denot table ψ ⟧ (x ∷ rest)
                          ∨TV (⟦ denot table φ ⟧ (x ∷ rest)
                               ∧TV ⟦ Syntax.Until (denot table φ) (denot table ψ) ⟧ rest)))
        (sym (runL-until-decomp table φ ψ x rest))
        (sound-or (adequacy table ψ (x ∷ rest))
                  (sound-and (adequacy table φ (x ∷ rest))
                             (adequacy table (Until φ ψ) rest)))

-- Release: empty → sound-tt; non-empty → ψ ∧ (φ ∨ Release), subst on monitor
adequacy table (Release φ ψ) [] = sound-tt
adequacy table (Release φ ψ) (x ∷ rest) =
  subst (λ m → Sound m (⟦ denot table ψ ⟧ (x ∷ rest)
                          ∧TV (⟦ denot table φ ⟧ (x ∷ rest)
                               ∨TV ⟦ Syntax.Release (denot table φ) (denot table ψ) ⟧ rest)))
        (sym (runL-release-decomp table φ ψ x rest))
        (sound-and (adequacy table ψ (x ∷ rest))
                   (sound-or (adequacy table φ (x ∷ rest))
                             (adequacy table (Release φ ψ) rest)))

-- MetricEventually: delegate to non-recursive helper (zero `with`s here)
adequacy table (MetricEventuallyProc w s φ) [] = sound-ff
adequacy table (MetricEventuallyProc w s φ) (y ∷ rest) =
  adequacy-met-ev table w s φ y rest
    (adequacy table φ (y ∷ rest))
    (met-ev-go-sound w (denot table φ) (decodeStart s (timestamp y)) rest
      (adequacy table (MetricEventuallyProc w (suc (decodeStart s (timestamp y))) φ) rest))

-- MetricAlways: delegate to non-recursive helper (zero `with`s here)
adequacy table (MetricAlwaysProc w s φ) [] = sound-tt
adequacy table (MetricAlwaysProc w s φ) (y ∷ rest) =
  adequacy-met-al table w s φ y rest
    (adequacy table φ (y ∷ rest))
    (met-al-go-sound w (denot table φ) (decodeStart s (timestamp y)) rest
      (adequacy table (MetricAlwaysProc w (suc (decodeStart s (timestamp y))) φ) rest))

-- MetricUntil: delegate to non-recursive helper (zero `with`s here)
adequacy table (MetricUntilProc w s φ ψ) [] = sound-ff
adequacy table (MetricUntilProc w s φ ψ) (y ∷ rest) =
  adequacy-met-un table w s φ ψ y rest
    (adequacy table φ (y ∷ rest))
    (adequacy table ψ (y ∷ rest))
    (met-un-go-sound w (denot table φ) (denot table ψ) (decodeStart s (timestamp y)) rest
      (adequacy table (MetricUntilProc w (suc (decodeStart s (timestamp y))) φ ψ) rest))

-- MetricRelease: delegate to non-recursive helper (zero `with`s here)
adequacy table (MetricReleaseProc w s φ ψ) [] = sound-tt
adequacy table (MetricReleaseProc w s φ ψ) (y ∷ rest) =
  adequacy-met-re table w s φ ψ y rest
    (adequacy table φ (y ∷ rest))
    (adequacy table ψ (y ∷ rest))
    (met-re-go-sound w (denot table φ) (denot table ψ) (decodeStart s (timestamp y)) rest
      (adequacy table (MetricReleaseProc w (suc (decodeStart s (timestamp y))) φ ψ) rest))

-- Not: decompose runL to notTV, then compose with sound-not + IH
adequacy table (Not φ) σ rewrite runL-not-decomp table φ σ = sound-not (adequacy table φ σ)
