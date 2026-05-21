{-# OPTIONS --safe --without-K #-}

-- Four-valued Kleene logic identity/absorb laws for TruthVal operators.
--
-- Purpose: Centralize ∧TV/∨TV algebraic identities used by Adequacy and SoundOps.
-- These are needed because Agda's overlapping clause patterns for ∧TV/∨TV
-- prevent automatic reduction when one argument is abstract.
--
-- Also includes: double-negation involutivity and de Morgan's laws,
-- used by Semantics.Duality to prove safety/liveness operator dualities.
module Aletheia.LTL.TruthVal.Properties where

open import Aletheia.LTL.SignalPredicate using (True; False; Unknown; Pending;
  notTV; _∧TV_; _∨TV_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong)

-- a ∧TV False ≡ False (right absorber for ∧)
∧TV-false-r : ∀ a → (a ∧TV False) ≡ False
∧TV-false-r True    = refl
∧TV-false-r False   = refl
∧TV-false-r Unknown = refl
∧TV-false-r Pending = refl

-- a ∨TV True ≡ True (right absorber for ∨)
∨TV-true-r : ∀ a → (a ∨TV True) ≡ True
∨TV-true-r True    = refl
∨TV-true-r False   = refl
∨TV-true-r Unknown = refl
∨TV-true-r Pending = refl

-- a ∨TV False ≡ a (right identity for ∨)
∨TV-false-r : ∀ a → (a ∨TV False) ≡ a
∨TV-false-r True    = refl
∨TV-false-r False   = refl
∨TV-false-r Unknown = refl
∨TV-false-r Pending = refl

-- True ∧TV b ≡ b (left identity for ∧)
∧TV-true-l : ∀ b → (True ∧TV b) ≡ b
∧TV-true-l True    = refl
∧TV-true-l False   = refl
∧TV-true-l Unknown = refl
∧TV-true-l Pending = refl

-- a ∧TV True ≡ a (right identity for ∧)
∧TV-true-r : ∀ a → (a ∧TV True) ≡ a
∧TV-true-r True    = refl
∧TV-true-r False   = refl
∧TV-true-r Unknown = refl
∧TV-true-r Pending = refl

-- False ∧TV b ≡ False (left absorber for ∧)
∧TV-false-l : ∀ b → (False ∧TV b) ≡ False
∧TV-false-l True    = refl
∧TV-false-l False   = refl
∧TV-false-l Unknown = refl
∧TV-false-l Pending = refl

-- False ∨TV b ≡ b (left identity for ∨)
∨TV-false-l : ∀ b → (False ∨TV b) ≡ b
∨TV-false-l True    = refl
∨TV-false-l False   = refl
∨TV-false-l Unknown = refl
∨TV-false-l Pending = refl

-- ============================================================================
-- DOUBLE NEGATION AND DE MORGAN'S LAWS
-- ============================================================================
-- Kleene logic preserves the classical structure: notTV is involutive on
-- all four values (True/False swap, Unknown/Pending fixed), and de Morgan
-- holds for both ∧TV and ∨TV. Used by Semantics.Duality.

-- Double negation: notTV is involutive.
notTV-involutive : ∀ x → notTV (notTV x) ≡ x
notTV-involutive True    = refl
notTV-involutive False   = refl
notTV-involutive Unknown = refl
notTV-involutive Pending = refl

-- De Morgan: notTV (a ∧TV b) ≡ notTV a ∨TV notTV b.
-- The False case collapses (clause 1 of ∧ matches with abstract b);
-- all other 3×4 = 12 cases need explicit b to fire ∧TV's later clauses.
deMorgan-∧ : ∀ a b → notTV (a ∧TV b) ≡ notTV a ∨TV notTV b
deMorgan-∧ False   b       = refl
deMorgan-∧ True    True    = refl
deMorgan-∧ True    False   = refl
deMorgan-∧ True    Unknown = refl
deMorgan-∧ True    Pending = refl
deMorgan-∧ Unknown True    = refl
deMorgan-∧ Unknown False   = refl
deMorgan-∧ Unknown Unknown = refl
deMorgan-∧ Unknown Pending = refl
deMorgan-∧ Pending True    = refl
deMorgan-∧ Pending False   = refl
deMorgan-∧ Pending Unknown = refl
deMorgan-∧ Pending Pending = refl

-- De Morgan: notTV (a ∨TV b) ≡ notTV a ∧TV notTV b. Dual of deMorgan-∧;
-- the True case collapses (clause 1 of ∨ matches with abstract b).
deMorgan-∨ : ∀ a b → notTV (a ∨TV b) ≡ notTV a ∧TV notTV b
deMorgan-∨ True    b       = refl
deMorgan-∨ False   True    = refl
deMorgan-∨ False   False   = refl
deMorgan-∨ False   Unknown = refl
deMorgan-∨ False   Pending = refl
deMorgan-∨ Unknown True    = refl
deMorgan-∨ Unknown False   = refl
deMorgan-∨ Unknown Unknown = refl
deMorgan-∨ Unknown Pending = refl
deMorgan-∨ Pending True    = refl
deMorgan-∨ Pending False   = refl
deMorgan-∨ Pending Unknown = refl
deMorgan-∨ Pending Pending = refl

-- a ∨TV b ≡ notTV (notTV a ∧TV notTV b). Used by SoundOps to derive sound-or
-- from sound-and via De Morgan, sidestepping a 6×6 truth-table enumeration.
-- Note: the dual ∧TV-via-De-Morgan would let sound-and be derived from sound-or
-- symmetrically, but Agda's termination checker rejects the resulting mutual
-- block (each call to sound-not preserves Sound-proof depth, so neither side
-- structurally decreases). One direction MUST be primitive; sound-and stays
-- primitive because its False-absorber short-circuit handles 6 of 36 outer
-- cases at the top.
∨TV-via-De-Morgan : ∀ a b → a ∨TV b ≡ notTV (notTV a ∧TV notTV b)
∨TV-via-De-Morgan a b = trans (sym (notTV-involutive (a ∨TV b)))
                              (cong notTV (deMorgan-∨ a b))
