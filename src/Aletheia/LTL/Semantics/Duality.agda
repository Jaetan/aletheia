{-# OPTIONS --safe --without-K #-}

-- Safety/liveness operator dualities for the denotational LTLf semantics.
--
-- Closes Phase 5.1 LTLf liveness sub-item: textbook duality identities
-- between safety operators (Always, Release) and liveness operators
-- (Eventually, Until). All four hold pointwise on finite traces under
-- four-valued Kleene logic — the negation operator notTV is involutive
-- and de Morgan's laws hold for ∧TV/∨TV (proven in TruthVal.Properties),
-- so the classical structure carries through.
--
-- Theorems:
--   eventually-always-dual : ⟦ Eventually φ ⟧ σ ≡ notTV (⟦ Always (Not φ) ⟧ σ)
--   always-eventually-dual : ⟦ Always φ ⟧ σ     ≡ notTV (⟦ Eventually (Not φ) ⟧ σ)
--   until-release-dual     : ⟦ Until φ ψ ⟧ σ    ≡ notTV (⟦ Release (Not φ) (Not ψ) ⟧ σ)
--   release-until-dual     : ⟦ Release φ ψ ⟧ σ  ≡ notTV (⟦ Until (Not φ) (Not ψ) ⟧ σ)
--
-- Each pair (forward + converse) is symmetric: the converse falls out of
-- the forward direction by `notTV-involutive` on both `φ` and the formula.
module Aletheia.LTL.Semantics.Duality where

open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning

open import Aletheia.LTL.Syntax using (LTL; Not; Always; Eventually; Until; Release)
open import Aletheia.LTL.SignalPredicate using (TruthVal; notTV; _∧TV_; _∨TV_)
open import Aletheia.LTL.TruthVal.Properties using (notTV-involutive; deMorgan-∧; deMorgan-∨)
open import Aletheia.Trace.CANTrace using (TimedFrame)
open import Aletheia.LTL.Semantics using (⟦_⟧)

private
  variable
    φ ψ : LTL (TimedFrame → TruthVal)
    σ   : List TimedFrame

-- ============================================================================
-- EVENTUALLY ↔ ALWAYS DUALITY
-- ============================================================================

-- F φ ≡ ¬G(¬φ).
-- Base: ⟦Eventually φ⟧ [] = False, ⟦Always (Not φ)⟧ [] = True, notTV True = False.
-- Step: rewrite via IH then apply de Morgan + double-negation to push notTV
-- through the ∧TV from Always's body.
eventually-always-dual : ∀ φ σ → ⟦ Eventually φ ⟧ σ ≡ notTV (⟦ Always (Not φ) ⟧ σ)
eventually-always-dual φ [] = refl
eventually-always-dual φ (x ∷ rest) = begin
    ⟦ φ ⟧ (x ∷ rest) ∨TV ⟦ Eventually φ ⟧ rest
  ≡⟨ cong (⟦ φ ⟧ (x ∷ rest) ∨TV_) (eventually-always-dual φ rest) ⟩
    ⟦ φ ⟧ (x ∷ rest) ∨TV notTV (⟦ Always (Not φ) ⟧ rest)
  ≡⟨ cong (_∨TV notTV (⟦ Always (Not φ) ⟧ rest))
          (sym (notTV-involutive (⟦ φ ⟧ (x ∷ rest)))) ⟩
    notTV (notTV (⟦ φ ⟧ (x ∷ rest))) ∨TV notTV (⟦ Always (Not φ) ⟧ rest)
  ≡⟨ sym (deMorgan-∧ (notTV (⟦ φ ⟧ (x ∷ rest))) (⟦ Always (Not φ) ⟧ rest)) ⟩
    notTV (notTV (⟦ φ ⟧ (x ∷ rest)) ∧TV ⟦ Always (Not φ) ⟧ rest)
  ∎

-- G φ ≡ ¬F(¬φ). Converse direction; falls out of `eventually-always-dual`
-- by replacing φ with `Not φ` and applying `notTV-involutive`.
always-eventually-dual : ∀ φ σ → ⟦ Always φ ⟧ σ ≡ notTV (⟦ Eventually (Not φ) ⟧ σ)
always-eventually-dual φ [] = refl
always-eventually-dual φ (x ∷ rest) = begin
    ⟦ φ ⟧ (x ∷ rest) ∧TV ⟦ Always φ ⟧ rest
  ≡⟨ cong (⟦ φ ⟧ (x ∷ rest) ∧TV_) (always-eventually-dual φ rest) ⟩
    ⟦ φ ⟧ (x ∷ rest) ∧TV notTV (⟦ Eventually (Not φ) ⟧ rest)
  ≡⟨ cong (_∧TV notTV (⟦ Eventually (Not φ) ⟧ rest))
          (sym (notTV-involutive (⟦ φ ⟧ (x ∷ rest)))) ⟩
    notTV (notTV (⟦ φ ⟧ (x ∷ rest))) ∧TV notTV (⟦ Eventually (Not φ) ⟧ rest)
  ≡⟨ sym (deMorgan-∨ (notTV (⟦ φ ⟧ (x ∷ rest))) (⟦ Eventually (Not φ) ⟧ rest)) ⟩
    notTV (notTV (⟦ φ ⟧ (x ∷ rest)) ∨TV ⟦ Eventually (Not φ) ⟧ rest)
  ∎

-- ============================================================================
-- UNTIL ↔ RELEASE DUALITY
-- ============================================================================

-- φ U ψ ≡ ¬(¬φ R ¬ψ).
-- Base: ⟦Until φ ψ⟧ [] = False, ⟦Release (Not φ)(Not ψ)⟧ [] = True.
-- Step: push notTV through Release's outer ∧TV (de Morgan-∧), then
-- through the inner ∨TV (de Morgan-∨), eliminating the double negations
-- on ⟦φ⟧ and ⟦ψ⟧, and apply IH to the recursive Release tail.
until-release-dual : ∀ φ ψ σ →
  ⟦ Until φ ψ ⟧ σ ≡ notTV (⟦ Release (Not φ) (Not ψ) ⟧ σ)
until-release-dual φ ψ [] = refl
until-release-dual φ ψ (x ∷ rest) = begin
    ⟦ ψ ⟧ (x ∷ rest) ∨TV (⟦ φ ⟧ (x ∷ rest) ∧TV ⟦ Until φ ψ ⟧ rest)
  ≡⟨ cong (λ z → ⟦ ψ ⟧ (x ∷ rest) ∨TV (⟦ φ ⟧ (x ∷ rest) ∧TV z))
          (until-release-dual φ ψ rest) ⟩
    ⟦ ψ ⟧ (x ∷ rest) ∨TV (⟦ φ ⟧ (x ∷ rest) ∧TV notTV (⟦ Release (Not φ) (Not ψ) ⟧ rest))
  ≡⟨ cong (λ z → ⟦ ψ ⟧ (x ∷ rest) ∨TV (z ∧TV notTV (⟦ Release (Not φ) (Not ψ) ⟧ rest)))
          (sym (notTV-involutive (⟦ φ ⟧ (x ∷ rest)))) ⟩
    ⟦ ψ ⟧ (x ∷ rest) ∨TV (notTV (notTV (⟦ φ ⟧ (x ∷ rest))) ∧TV notTV (⟦ Release (Not φ) (Not ψ) ⟧ rest))
  ≡⟨ cong (⟦ ψ ⟧ (x ∷ rest) ∨TV_)
          (sym (deMorgan-∨ (notTV (⟦ φ ⟧ (x ∷ rest))) (⟦ Release (Not φ) (Not ψ) ⟧ rest))) ⟩
    ⟦ ψ ⟧ (x ∷ rest) ∨TV notTV (notTV (⟦ φ ⟧ (x ∷ rest)) ∨TV ⟦ Release (Not φ) (Not ψ) ⟧ rest)
  ≡⟨ cong (_∨TV notTV (notTV (⟦ φ ⟧ (x ∷ rest)) ∨TV ⟦ Release (Not φ) (Not ψ) ⟧ rest))
          (sym (notTV-involutive (⟦ ψ ⟧ (x ∷ rest)))) ⟩
    notTV (notTV (⟦ ψ ⟧ (x ∷ rest))) ∨TV notTV (notTV (⟦ φ ⟧ (x ∷ rest)) ∨TV ⟦ Release (Not φ) (Not ψ) ⟧ rest)
  ≡⟨ sym (deMorgan-∧ (notTV (⟦ ψ ⟧ (x ∷ rest)))
                     (notTV (⟦ φ ⟧ (x ∷ rest)) ∨TV ⟦ Release (Not φ) (Not ψ) ⟧ rest)) ⟩
    notTV (notTV (⟦ ψ ⟧ (x ∷ rest)) ∧TV (notTV (⟦ φ ⟧ (x ∷ rest)) ∨TV ⟦ Release (Not φ) (Not ψ) ⟧ rest))
  ∎

-- φ R ψ ≡ ¬(¬φ U ¬ψ). Converse direction.
release-until-dual : ∀ φ ψ σ →
  ⟦ Release φ ψ ⟧ σ ≡ notTV (⟦ Until (Not φ) (Not ψ) ⟧ σ)
release-until-dual φ ψ [] = refl
release-until-dual φ ψ (x ∷ rest) = begin
    ⟦ ψ ⟧ (x ∷ rest) ∧TV (⟦ φ ⟧ (x ∷ rest) ∨TV ⟦ Release φ ψ ⟧ rest)
  ≡⟨ cong (λ z → ⟦ ψ ⟧ (x ∷ rest) ∧TV (⟦ φ ⟧ (x ∷ rest) ∨TV z))
          (release-until-dual φ ψ rest) ⟩
    ⟦ ψ ⟧ (x ∷ rest) ∧TV (⟦ φ ⟧ (x ∷ rest) ∨TV notTV (⟦ Until (Not φ) (Not ψ) ⟧ rest))
  ≡⟨ cong (λ z → ⟦ ψ ⟧ (x ∷ rest) ∧TV (z ∨TV notTV (⟦ Until (Not φ) (Not ψ) ⟧ rest)))
          (sym (notTV-involutive (⟦ φ ⟧ (x ∷ rest)))) ⟩
    ⟦ ψ ⟧ (x ∷ rest) ∧TV (notTV (notTV (⟦ φ ⟧ (x ∷ rest))) ∨TV notTV (⟦ Until (Not φ) (Not ψ) ⟧ rest))
  ≡⟨ cong (⟦ ψ ⟧ (x ∷ rest) ∧TV_)
          (sym (deMorgan-∧ (notTV (⟦ φ ⟧ (x ∷ rest))) (⟦ Until (Not φ) (Not ψ) ⟧ rest))) ⟩
    ⟦ ψ ⟧ (x ∷ rest) ∧TV notTV (notTV (⟦ φ ⟧ (x ∷ rest)) ∧TV ⟦ Until (Not φ) (Not ψ) ⟧ rest)
  ≡⟨ cong (_∧TV notTV (notTV (⟦ φ ⟧ (x ∷ rest)) ∧TV ⟦ Until (Not φ) (Not ψ) ⟧ rest))
          (sym (notTV-involutive (⟦ ψ ⟧ (x ∷ rest)))) ⟩
    notTV (notTV (⟦ ψ ⟧ (x ∷ rest))) ∧TV notTV (notTV (⟦ φ ⟧ (x ∷ rest)) ∧TV ⟦ Until (Not φ) (Not ψ) ⟧ rest)
  ≡⟨ sym (deMorgan-∨ (notTV (⟦ ψ ⟧ (x ∷ rest)))
                     (notTV (⟦ φ ⟧ (x ∷ rest)) ∧TV ⟦ Until (Not φ) (Not ψ) ⟧ rest)) ⟩
    notTV (notTV (⟦ ψ ⟧ (x ∷ rest)) ∨TV (notTV (⟦ φ ⟧ (x ∷ rest)) ∧TV ⟦ Until (Not φ) (Not ψ) ⟧ rest))
  ∎
