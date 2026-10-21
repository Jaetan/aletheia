-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- What a parser's Boolean character tests say about the character.
--
-- A test built from `_≈ᵇ_`, `_<ᵇ_` and `any` decides on the character's
-- code, so a proof can recover the character, or its membership in the list
-- `any` searched, from the test's answer.
module Aletheia.Parser.Properties.Chars where

open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; T)
open import Data.Bool.ListAction using (any)
open import Data.Char using (Char; _≈ᵇ_)
open import Data.Char.Base using (toℕ)
open import Data.Char.Properties using (toℕ-injective)
open import Relation.Nullary.Negation using (contradiction)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat.Properties using (≡ᵇ⇒≡; ≡⇒≡ᵇ)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst)

T⇒≡ : ∀ {b} → T b → b ≡ true
T⇒≡ {true} _ = refl

∧-left : ∀ {a b} → (a ∧ b) ≡ true → a ≡ true
∧-left {true} _ = refl

∧-right : ∀ {a b} → (a ∧ b) ≡ true → b ≡ true
∧-right {true} e = e

not-true : ∀ {a} → not a ≡ true → a ≡ false
not-true {false} _ = refl

∨-cases : ∀ {a b} → (a ∨ b) ≡ true → a ≡ true ⊎ b ≡ true
∨-cases {true}  _ = inj₁ refl
∨-cases {false} e = inj₂ e

-- `_≈ᵇ_` decides equality.
≈ᵇ⇒≡ : ∀ {c d : Char} → (c ≈ᵇ d) ≡ true → c ≡ d
≈ᵇ⇒≡ {c} {d} eq = toℕ-injective c d (≡ᵇ⇒≡ (toℕ c) (toℕ d) (subst T (sym eq) tt))

≈ᵇ-refl : ∀ c → (c ≈ᵇ c) ≡ true
≈ᵇ-refl c = T⇒≡ (≡⇒≡ᵇ (toℕ c) (toℕ c) refl)

≈ᵇ-false : ∀ {c d : Char} → (c ≈ᵇ d) ≡ false → c ≢ d
≈ᵇ-false {c} eq refl = contradiction (trans (sym eq) (≈ᵇ-refl c)) (λ ())

-- A character `any (c ≈ᵇ_)` finds in a list is in it.
any-≈ᵇ : ∀ c ds → any (c ≈ᵇ_) ds ≡ true → c ∈ ds
any-≈ᵇ c (d ∷ ds) e with c ≈ᵇ d in e′
... | true  = here (≈ᵇ⇒≡ e′)
... | false = there (any-≈ᵇ c ds e)

∨-false : ∀ {a b} → (a ∨ b) ≡ false → a ≡ false × b ≡ false
∨-false {false} e = refl , e
