{-# OPTIONS --safe --without-K #-}

-- Generic inversion lemmas for error-returning parser combinators.
--
-- Purpose: Decompose successful bind chains without case-splitting on
-- intermediate values. Used by SignalWF and MessageWF proofs.
module Aletheia.DBC.JSONParser.Inversion where

open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Aletheia.Prelude using (_>>=ₑ_)

-- Invert a successful bind: if (x >>=ₑ f) ≡ inj₂ b, then x ≡ inj₂ a and f a ≡ inj₂ b
>>=ₑ-invert : ∀ {A B : Set} {b : B} (x : String ⊎ A) (f : A → String ⊎ B)
  → (x >>=ₑ f) ≡ inj₂ b → Σ A (λ a → x ≡ inj₂ a × f a ≡ inj₂ b)
>>=ₑ-invert (inj₁ _) f ()
>>=ₑ-invert (inj₂ a) f eq = a , refl , eq
