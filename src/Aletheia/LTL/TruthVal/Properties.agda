{-# OPTIONS --safe --without-K #-}

-- Four-valued Kleene logic identity/absorb laws for TruthVal operators.
--
-- Purpose: Centralize ∧TV/∨TV algebraic identities used by Adequacy and SoundOps.
-- These are needed because Agda's overlapping clause patterns for ∧TV/∨TV
-- prevent automatic reduction when one argument is abstract.
module Aletheia.LTL.TruthVal.Properties where

open import Aletheia.LTL.SignalPredicate using (TruthVal; True; False; Unknown; Pending;
  _∧TV_; _∨TV_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

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

-- False ∨TV b ≡ b (left identity for ∨)
∨TV-false-l : ∀ b → (False ∨TV b) ≡ b
∨TV-false-l True    = refl
∨TV-false-l False   = refl
∨TV-false-l Unknown = refl
∨TV-false-l Pending = refl
