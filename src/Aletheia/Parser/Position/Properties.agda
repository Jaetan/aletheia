-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Advancing a position moves it strictly forward.
--
-- Positions are ordered lexicographically on (line, column), and advancing
-- over one character moves a position strictly forward (a newline to the
-- next line, any other character one column on), so advancing over a
-- non-empty character list never lands back where it started.  `many` relies
-- on this: an element parser that consumed input succeeded at a later
-- position, which `samePosᵇ` tells apart from the start.
module Aletheia.Parser.Position.Properties where

open import Aletheia.Parser.Position
  using (Position; mkPos; line; column; advancePosition; advancePositions; samePosᵇ)
open import Data.Bool using (true; false)
open import Data.Char using (Char; _≈ᵇ_)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (zero; suc; _<_; _≡ᵇ_)
open import Data.Nat.Properties using (<-trans; <-irrefl; n<1+n)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

-- The lexicographic order on positions.
data _<ₚ_ (p q : Position) : Set where
  line< : line p < line q → p <ₚ q
  col<  : line p ≡ line q → column p < column q → p <ₚ q

<ₚ-trans : ∀ {p q r} → p <ₚ q → q <ₚ r → p <ₚ r
<ₚ-trans         (line< a) (line< b)   = line< (<-trans a b)
<ₚ-trans {p}     (line< a) (col< e _)  = line< (subst (line p <_) e a)
<ₚ-trans {r = r} (col< e _) (line< b)  = line< (subst (_< line r) (sym e) b)
<ₚ-trans         (col< e a) (col< f b) = col< (trans e f) (<-trans a b)

-- One character moves a position strictly forward.
advance-< : ∀ (pos : Position) (c : Char) → pos <ₚ advancePosition pos c
advance-< pos c with c ≈ᵇ '\n'
... | true  = line< (n<1+n (line pos))
... | false = col< refl (n<1+n (column pos))

-- Advancing further keeps a position strictly after a given one.
advances-keep : ∀ {p} (q : Position) (cs : List Char) → p <ₚ q → p <ₚ advancePositions q cs
advances-keep q []       p<q = p<q
advances-keep q (c ∷ cs) p<q = advances-keep (advancePosition q c) cs (<ₚ-trans p<q (advance-< q c))

-- A non-empty character list moves a position strictly forward.
advances-< : ∀ (pos : Position) (c : Char) (cs : List Char) → pos <ₚ advancePositions pos (c ∷ cs)
advances-< pos c cs = advances-keep (advancePosition pos c) cs (advance-< pos c)

private
  ≡ᵇ-refl : ∀ n → (n ≡ᵇ n) ≡ true
  ≡ᵇ-refl zero    = refl
  ≡ᵇ-refl (suc n) = ≡ᵇ-refl n

  ≢⇒≡ᵇ-false : ∀ m n → m ≢ n → (m ≡ᵇ n) ≡ false
  ≢⇒≡ᵇ-false zero    zero    m≢n = ⊥-elim (m≢n refl)
  ≢⇒≡ᵇ-false zero    (suc n) _   = refl
  ≢⇒≡ᵇ-false (suc m) zero    _   = refl
  ≢⇒≡ᵇ-false (suc m) (suc n) m≢n = ≢⇒≡ᵇ-false m n (λ e → m≢n (cong suc e))

  <⇒≢ : ∀ {m n} → m < n → n ≢ m
  <⇒≢ m<n refl = <-irrefl refl m<n

-- A position is the same as itself.
samePosᵇ-refl : ∀ (p : Position) → samePosᵇ p p ≡ true
samePosᵇ-refl (mkPos l c) rewrite ≡ᵇ-refl l | ≡ᵇ-refl c = refl

-- A position strictly after another is not the same as it.
<ₚ⇒samePosᵇ-false : ∀ {p q} → p <ₚ q → samePosᵇ q p ≡ false
<ₚ⇒samePosᵇ-false {p} {q} (line< l<) rewrite ≢⇒≡ᵇ-false (line q) (line p) (<⇒≢ l<) = refl
<ₚ⇒samePosᵇ-false {p} {q} (col< e c<)
  rewrite sym e | ≡ᵇ-refl (line p) | ≢⇒≡ᵇ-false (column q) (column p) (<⇒≢ c<) = refl

-- Advancing over one character, or over a non-empty list, never stays put.
samePosᵇ-advance : ∀ (pos : Position) (c : Char) → samePosᵇ (advancePosition pos c) pos ≡ false
samePosᵇ-advance pos c = <ₚ⇒samePosᵇ-false (advance-< pos c)

samePosᵇ-advance2 : ∀ (pos : Position) (c d : Char)
  → samePosᵇ (advancePosition (advancePosition pos c) d) pos ≡ false
samePosᵇ-advance2 pos c d = <ₚ⇒samePosᵇ-false (<ₚ-trans (advance-< pos c) (advance-< (advancePosition pos c) d))

samePosᵇ-advances : ∀ (pos : Position) (cs : List Char) → 0 < length cs
  → samePosᵇ (advancePositions pos cs) pos ≡ false
samePosᵇ-advances pos (c ∷ cs) _ = <ₚ⇒samePosᵇ-false (advances-< pos c cs)
