-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 4a — char-class disjointness lemmas.
--
-- Layer 3 per-line-construct roundtrips take char-class-disjointness
-- facts as preconditions (`NodeNameStop`, `IdentNameStop`, etc.) rather
-- than discharging them in-place.  Those facts are universal (they
-- don't depend on the construct) and discharging them once at Layer 4
-- keeps Layer 3 proofs construct-local.
--
-- This module hosts the four facts the universal aggregator owes:
--
--   1. `isIdentStart→¬isHSpace`        — identifier-start char ⇒ not
--                                         horizontal whitespace.
--   2. `isIdentCont→¬isHSpace`         — identifier-cont char  ⇒ not
--                                         horizontal whitespace.
--   3. `isIdentCont→¬isNewlineStart`   — identifier-cont char  ⇒ not
--                                         newline starter.
--   4. `showInt-chars-head-non-hspace` — head of `showInt-chars z` is
--                                         non-hspace, for every ℤ.
--
-- Proof technique for the three identifier-class lemmas: case-split on
-- `c ≟ᶜ <reference>` for each reference char in the conclusion's `∨`
-- chain.  The `yes refl` branch unifies `c` with the reference, which
-- collapses `isIdentStart c` (or `isIdentCont c`) by closed-char
-- reduction of the underlying primitive (`isAlpha` / `isAlphaNum`)
-- plus `_≟ᶜ_`-on-closed-chars to `false`, contradicting the hypothesis
-- via `T false = ⊥`.  The `no _` branches collapse the conclusion's
-- `∨` to `false ∨ false = false`.
--
-- The fourth lemma, `showInt-chars-head-non-hspace`, dispatches on the
-- ℤ sign:
--   * `+ n`         — head is `digitChar d` for some `d < 10` via
--                     `showNat-chars-head`; close via the local
--                     `digitChar-not-isHSpace` 10-case + suc-chain.
--   * `-[1+ n ]`    — head is the closed char `'-'`; `λ ()` closes
--                     `¬ T (isHSpace '-')` directly.
module Aletheia.DBC.TextParser.Properties.CharClassDisjoint where

open import Data.Bool using (true; false; T)
open import Data.Char using (Char; _≈ᵇ_; toℕ) renaming (_≟_ to _≟ᶜ_)
open import Data.Char.Properties using (≈⇒≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Nat using (_≡ᵇ_)
open import Data.Nat.Properties using (≡ᵇ⇒≡)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; subst)
open import Relation.Nullary using (yes; no; ¬_)

open import Aletheia.DBC.Identifier using (isIdentStart; isIdentCont)
open import Aletheia.DBC.TextParser.Lexer using (isHSpace)
open import Aletheia.DBC.TextParser.Properties.Preamble.Newline
  using (isNewlineStart)
open import Aletheia.DBC.TextFormatter.Emitter
  using (showInt-chars; showNat-chars; digitChar)
open import Aletheia.DBC.TextParser.DecRatParse.Properties
  using (headOr; showNat-chars-head)
open import Aletheia.DBC.TextParser.Properties.Attributes.Assign.Common
  using (digitChar-not-isHSpace)

-- ============================================================================
-- IDENTIFIER-CLASS DISJOINTNESS WITH WS / NEWLINE
-- ============================================================================

-- `isIdentStart c = isAlpha c ∨ ⌊ c ≟ '_' ⌋`; `isHSpace c = ⌊ c ≟ ' ' ⌋
-- ∨ ⌊ c ≟ '\t' ⌋`.  In either yes-branch (`c ≡ ' '` or `c ≡ '\t'`), the
-- hypothesis `T (isIdentStart c)` reduces to `T false = ⊥` because both
-- `isAlpha ' '` / `isAlpha '\t'` reduce to `false` (closed primitive)
-- and `⌊ ' ' ≟ '_' ⌋` / `⌊ '\t' ≟ '_' ⌋` reduce to `false`.
isIdentStart→¬isHSpace : ∀ (c : Char) → T (isIdentStart c) → isHSpace c ≡ false
isIdentStart→¬isHSpace c h with c ≟ᶜ ' '
... | yes refl = ⊥-elim h
... | no _     with c ≟ᶜ '\t'
...   | yes refl = ⊥-elim h
...   | no _     = refl

-- `isIdentCont c = isAlphaNum c ∨ ⌊ c ≟ '_' ⌋`.  Same shape as above:
-- `isAlphaNum ' '` / `isAlphaNum '\t'` reduce to `false`.
isIdentCont→¬isHSpace : ∀ (c : Char) → T (isIdentCont c) → isHSpace c ≡ false
isIdentCont→¬isHSpace c h with c ≟ᶜ ' '
... | yes refl = ⊥-elim h
... | no _     with c ≟ᶜ '\t'
...   | yes refl = ⊥-elim h
...   | no _     = refl

-- `isNewlineStart c = (c ≈ᵇ '\n') ∨ (c ≈ᵇ '\r')`.  Unlike `isHSpace`
-- (which uses `⌊ _≟_ ⌋`), `isNewlineStart` uses `_≈ᵇ_` directly — so
-- splitting on `c ≟ᶜ '\n'` doesn't reduce the conclusion's `_≈ᵇ_`
-- terms.  We split on `c ≈ᵇ '\n' in eq1 / c ≈ᵇ '\r' in eq2`: in the
-- `false`/`false` branch the conclusion reduces directly; in either
-- `true` branch, `≈⇒≡` upgrades the boolean equality to propositional
-- equality, which lets the closed-char reduction collapse `isIdentCont`
-- to `false`, contradicting the hypothesis.
private
  isIdentCont-LF-absurd : ¬ T (isIdentCont '\n')
  isIdentCont-LF-absurd ()

  isIdentCont-CR-absurd : ¬ T (isIdentCont '\r')
  isIdentCont-CR-absurd ()

isIdentCont→¬isNewlineStart : ∀ (c : Char) → T (isIdentCont c) → isNewlineStart c ≡ false
isIdentCont→¬isNewlineStart c h with c ≈ᵇ '\n' in eq1 | c ≈ᵇ '\r' in eq2
... | false | false = refl
... | true  | _     = ⊥-elim (isIdentCont-LF-absurd (subst (T ∘ isIdentCont) c≡LF h))
  where
    -- `eq1 : (toℕ c ≡ᵇ toℕ '\n') ≡ true` ⟹ `T (toℕ c ≡ᵇ toℕ '\n')` via
    -- `subst T (sym eq1) tt` ⟹ `toℕ c ≡ toℕ '\n'` via `≡ᵇ⇒≡` ⟹ `c ≡ '\n'`
    -- via `≈⇒≡`.  Then `subst (T ∘ isIdentCont) c≡LF h` carries the
    -- hypothesis from `c` to `'\n'`, where `isIdentCont '\n'` reduces
    -- to `false` and the absurdity helper closes the goal.
    T-eq1 : T (toℕ c ≡ᵇ toℕ '\n')
    T-eq1 rewrite eq1 = tt
    c≡LF : c ≡ '\n'
    c≡LF = ≈⇒≡ (≡ᵇ⇒≡ (toℕ c) (toℕ '\n') T-eq1)
... | false | true  = ⊥-elim (isIdentCont-CR-absurd (subst (T ∘ isIdentCont) c≡CR h))
  where
    T-eq2 : T (toℕ c ≡ᵇ toℕ '\r')
    T-eq2 rewrite eq2 = tt
    c≡CR : c ≡ '\r'
    c≡CR = ≈⇒≡ (≡ᵇ⇒≡ (toℕ c) (toℕ '\r') T-eq2)

-- ============================================================================
-- DIGIT-CHAR / SHOWINT HEAD NON-HSPACE
-- ============================================================================

-- `showInt-chars z`'s head char is non-hspace.  Two-case dispatch on ℤ
-- sign: positive uses `showNat-chars-head` to expose the head as
-- `digitChar d`; negative emits `'-'` directly, closed reduction does
-- the rest.
--
-- The positive case stages two `with` rewrites: first to expose
-- `showNat-chars n ≡ digitChar d ∷ tail`, then to collapse
-- `isHSpace (digitChar d)` to `false`.  After both, the residual
-- hypothesis `T false` is absurd.
showInt-chars-head-non-hspace :
    ∀ (z : ℤ) → ¬ T (isHSpace (headOr (showInt-chars z) ' '))
showInt-chars-head-non-hspace -[1+ n ] = λ ()
showInt-chars-head-non-hspace (+ n) h = absurd
  where
    -- showNat-chars-head exposes the head as `digitChar d` for some `d`
    -- bounded by 10.  After the `refl` unification, `headOr (showNat-
    -- chars n) ' '` reduces to `digitChar d`; combining with
    -- `digitChar-not-isHSpace d` collapses `T (isHSpace (digitChar d))`
    -- to `T false = ⊥`.
    absurd : ⊥
    absurd with showNat-chars-head n
    ... | (d , tail , d<10 , eq)
      with showNat-chars n | eq
    ...   | _ | refl
        with isHSpace (digitChar d) | digitChar-not-isHSpace d
    ...     | _ | refl = h
