-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Phase 2 of the `parseDecRat` roundtrip proof — `many (satisfy P)`
-- prefix reader.  Carved out of the historical
-- `Aletheia.DBC.TextParser.DecRatParse.Properties` mega-module when it
-- was split into submodules.
--
-- Reusable for other primitives: any primitive whose parser is
-- `some (satisfy P)` or `many (satisfy P)` over a `List Char` suffix
-- that stops via `P c ≡ false` (or end-of-input) closes through this
-- layer.  For DecRat specifically: `parseNatural` (integer part,
-- `P = isDigit`) and `some digit` (fractional part, `P = isDigit`)
-- both land on `some-satisfy-prefix` below.
--
-- The workhorse lemma `manyHelper-satisfy-exhaust` is parameterised
-- over the predicate `P` and pattern-matches on the `manyHelper`
-- structure exposed publicly in `Aletheia.Parser.Combinators`
-- (unprivatised 2026-04-22 to enable this proof).
--
-- Phase organisation:
--   * 2.1: sameLengthᵇ cons (manyHelper termination-guard discharge).
--   * 2.2: SuffixStops P — characterises a stop boundary.
--   * 2.3: digitChar d is an ASCII digit (under d < 10).
--   * 2.4: All emitted characters are digits.
--   * 2.5: manyHelper-satisfy-exhaust — the workhorse lemma.
--   * 2.6: many-fuel specialisation.
--   * 2.7: some-satisfy-prefix — the reusable entry point.
--
-- Self-contained: no dependency on Phase 1 (it's lemmas about
-- `digitChar` reductions only; doesn't touch the `foldl`-side
-- roundtrip).  Both Phase 1 and Phase 2 are leaves under the
-- common stdlib + Combinators + Emitter import base.
module Aletheia.DBC.TextParser.DecRatParse.Properties.Phase2Many where

open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char)
open import Data.Char.Base using (isDigit)
open import Data.List using (List; []; _∷_; length) renaming (_++_ to _++ₗ_)
open import Data.List.Properties using () renaming (length-++ to length-++ₗ)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to All-++⁺)
open import Data.Maybe using (just)
open import Data.Product using (_,_; proj₂)
open import Data.Nat using (ℕ; zero; suc; _/_; _%_;
         _≤_; s≤s)
open import Data.Nat.Properties using (m≤m+n)
open import Data.Nat.DivMod using (m%n<n)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Aletheia.Parser.Combinators
  using (Position; mkResult;
         advancePosition; advancePositions;
         satisfy; some; manyHelper; sameLengthᵇ)
open import Aletheia.DBC.TextFormatter.Emitter
  using (digitChar; showNat-chars; showNat-chars-fuel; showℕ-padded-chars)

-- ----------------------------------------------------------------------------
-- Phase 2.1: sameLengthᵇ cons (manyHelper termination-guard discharge)
-- ----------------------------------------------------------------------------

-- `manyHelper` checks `sameLengthᵇ input (remaining result)` to
-- detect zero-progress parsers.  When `satisfy P` consumes a real
-- character, the post-result remaining is exactly one shorter than
-- the pre-input (i.e. `remaining ≡ tail input`), so the check must
-- discharge to `false`.
sameLengthᵇ-cons : ∀ {A : Set} (x : A) (l : List A) →
  sameLengthᵇ (x ∷ l) l ≡ false
sameLengthᵇ-cons _ []       = refl
sameLengthᵇ-cons _ (y ∷ ys) = sameLengthᵇ-cons y ys

-- ----------------------------------------------------------------------------
-- Phase 2.2: SuffixStops P — characterises a stop boundary
-- ----------------------------------------------------------------------------

-- `SuffixStops P suffix` — either the suffix is empty, or its first
-- character fails `P`.  In both cases `manyHelper (satisfy P)` on
-- `suffix` (with any fuel ≥ 0) returns the empty-result base.
data SuffixStops (P : Char → Bool) : List Char → Set where
  []-stop : SuffixStops P []
  ∷-stop  : ∀ {c cs} → P c ≡ false → SuffixStops P (c ∷ cs)

-- ----------------------------------------------------------------------------
-- Phase 2.3: digitChar d is an ASCII digit (under d < 10)
-- ----------------------------------------------------------------------------

-- Same pattern as `digitToNat-digitChar` / `charToDigit-digitChar`:
-- ten refl branches (primitive evaluation of `primIsDigit '0'..'9'`)
-- plus a suc-chain absurd on the catch-all (per
-- `feedback_literaltoobig_suc_chain.md`).
digitChar-isDigit : ∀ d → d Data.Nat.< 10 → isDigit (digitChar d) ≡ true
digitChar-isDigit 0 _ = refl
digitChar-isDigit 1 _ = refl
digitChar-isDigit 2 _ = refl
digitChar-isDigit 3 _ = refl
digitChar-isDigit 4 _ = refl
digitChar-isDigit 5 _ = refl
digitChar-isDigit 6 _ = refl
digitChar-isDigit 7 _ = refl
digitChar-isDigit 8 _ = refl
digitChar-isDigit 9 _ = refl
digitChar-isDigit (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _))))))))))
  (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ()))))))))))

-- ----------------------------------------------------------------------------
-- Phase 2.4: All emitted characters are digits
-- ----------------------------------------------------------------------------

-- Every character in `showNat-chars-fuel f n` passes `isDigit`
-- (independent of fuel — `f = 0` returns `[]` vacuously).  Mirrors
-- the `with n / 10` case-split in the emitter: both branches emit
-- `digitChar (n % 10)` at the low position, and the `suc m` branch
-- has an IH-covered prefix to its left.
All-isDigit-showNat-chars-fuel : ∀ f n →
  All (λ c → isDigit c ≡ true) (showNat-chars-fuel f n)
All-isDigit-showNat-chars-fuel zero     _ = []
All-isDigit-showNat-chars-fuel (suc f') n with n / 10
... | zero  = digitChar-isDigit (n % 10) (m%n<n n 10) ∷ []
... | suc m = All-++⁺ (All-isDigit-showNat-chars-fuel f' (suc m))
                      (digitChar-isDigit (n % 10) (m%n<n n 10) ∷ [])

-- Specialisation at the public `showNat-chars n = showNat-chars-fuel
-- (suc n) n` entry point.
All-isDigit-showNat-chars : ∀ n →
  All (λ c → isDigit c ≡ true) (showNat-chars n)
All-isDigit-showNat-chars n = All-isDigit-showNat-chars-fuel (suc n) n

-- Every character in `showℕ-padded-chars w n` passes `isDigit`.
-- Structural recursion on `w`; no precondition on `n` needed — the
-- digit property is orthogonal to the width-bounded roundtrip.
All-isDigit-showℕ-padded-chars : ∀ w n →
  All (λ c → isDigit c ≡ true) (showℕ-padded-chars w n)
All-isDigit-showℕ-padded-chars zero    _ = []
All-isDigit-showℕ-padded-chars (suc w) n =
  All-++⁺ (All-isDigit-showℕ-padded-chars w (n / 10))
          (digitChar-isDigit (n % 10) (m%n<n n 10) ∷ [])

-- ----------------------------------------------------------------------------
-- Phase 2.5: manyHelper-satisfy-exhaust — the workhorse lemma
-- ----------------------------------------------------------------------------

-- Given enough fuel, `manyHelper (satisfy P)` on `xs ++ suffix` with
-- every `xs` character `P`-true and `suffix` at a stop boundary
-- returns `xs` and leaves `suffix` unconsumed (with a correctly
-- advanced position).
--
-- Six coverage cases after splitting on fuel / `xs` / `suffix`:
--   * fuel = 0, xs = [], suffix = []:             manyHelper short-
--     circuits on fuel before inspecting the parser; reduces to
--     `just (mkResult [] pos [])` directly.
--   * fuel = 0, xs = [], suffix = c ∷ cs:         same short-circuit.
--   * fuel = 0, xs = x ∷ xs':                     absurd via
--                                                  `suc _ ≤ 0`.
--   * fuel = suc n', xs = [], suffix = []:        satisfy fails on
--     empty input; manyHelper falls through the `nothing` branch.
--   * fuel = suc n', xs = [], suffix = c ∷ cs:    `rewrite h` (the
--     `P c ≡ false` component of `∷-stop`) makes satisfy return
--     `nothing`; manyHelper's `nothing` branch.
--   * fuel = suc n', xs = x ∷ xs':                inductive step.
--     Rewrites (1) `px : P x ≡ true` (satisfy returns `just`) and
--     (2) `sameLengthᵇ-cons` (zero-progress guard → `false`); then a
--     simultaneous `with` on the recursive manyHelper call and the IH
--     — the IH is outcome-level (`proj₂`), so it cannot fire as a
--     rewrite on the pair-typed scrutinee; abstracting the pair and
--     matching the IH's `refl` forces the outcome component, and the
--     stuck watermark (`proj₁`) is discarded definitionally.
manyHelper-satisfy-exhaust : (P : Char → Bool) (pos : Position)
  → (xs suffix : List Char)
  → All (λ c → P c ≡ true) xs
  → SuffixStops P suffix
  → (n : ℕ) → length xs ≤ n
  → proj₂ (manyHelper (satisfy P) pos (xs ++ₗ suffix) n)
    ≡ just (mkResult xs (advancePositions pos xs) suffix)
manyHelper-satisfy-exhaust P pos []        []       _          _          zero     _            = refl
manyHelper-satisfy-exhaust P pos []        (c ∷ cs) _          _          zero     _            = refl
manyHelper-satisfy-exhaust P pos (x ∷ xs') _        _          _          zero     ()
manyHelper-satisfy-exhaust P pos []        []       _          _          (suc n') _            = refl
manyHelper-satisfy-exhaust P pos []        (c ∷ cs) _          (∷-stop h) (suc n') _
  rewrite h = refl
manyHelper-satisfy-exhaust P pos (x ∷ xs') suffix   (px ∷ pxs) ss         (suc n') (s≤s len≤)
  rewrite px
        | sameLengthᵇ-cons x (xs' ++ₗ suffix)
  with manyHelper (satisfy P) (advancePosition pos x) (xs' ++ₗ suffix) n'
     | manyHelper-satisfy-exhaust P (advancePosition pos x) xs' suffix pxs ss n' len≤
... | w' , just restResult | refl = refl

-- ----------------------------------------------------------------------------
-- Phase 2.6: many-fuel specialisation
-- ----------------------------------------------------------------------------

-- `many p pos input = manyHelper p pos input (length input)`.  For
-- `input = xs ++ suffix`, the fuel is `length (xs ++ suffix)`, which
-- is `≥ length xs` via `length-++ₗ` + `m≤m+n`.  This wrapper
-- specialises the exhaustion lemma to exactly the shape that
-- `some-satisfy-prefix` needs.
manyHelper-satisfy-exhaust-many : (P : Char → Bool) (pos : Position)
  → (xs suffix : List Char)
  → All (λ c → P c ≡ true) xs
  → SuffixStops P suffix
  → proj₂ (manyHelper (satisfy P) pos (xs ++ₗ suffix) (length (xs ++ₗ suffix)))
    ≡ just (mkResult xs (advancePositions pos xs) suffix)
manyHelper-satisfy-exhaust-many P pos xs suffix pxs ss =
  manyHelper-satisfy-exhaust P pos xs suffix pxs ss
    (length (xs ++ₗ suffix)) len-xs≤len-xs++suffix
  where
    len-xs≤len-xs++suffix : length xs ≤ length (xs ++ₗ suffix)
    len-xs≤len-xs++suffix
      rewrite length-++ₗ xs {suffix}
      = m≤m+n (length xs) (length suffix)

-- ----------------------------------------------------------------------------
-- Phase 2.7: some-satisfy-prefix — the reusable entry point
-- ----------------------------------------------------------------------------

-- `some p = p ∷ many p` (in list form).  Applied to `(x ∷ xs') ++
-- suffix` with head `P`-true, tail `P`-true, and `suffix` at a stop
-- boundary, `some (satisfy P)` returns the whole prefix.  `rewrite px`
-- resolves the leading `satisfy` call inside `<$>`/`<*>`; then the
-- simultaneous `with` on the recursive `many` call + the outcome-level
-- exhaustion lemma resolves the tail, letting the remaining `<$>`
-- reduce to the final `mkResult` (same idiom as the inductive step of
-- `manyHelper-satisfy-exhaust` above).
--
-- Shared by `parseNatural-showNat-chars` (integer part) and the
-- fractional `some digit` call in `parseDecRat` — both use `P =
-- isDigit`.
some-satisfy-prefix : (P : Char → Bool) (pos : Position)
  → (x : Char) (xs' suffix : List Char)
  → P x ≡ true
  → All (λ c → P c ≡ true) xs'
  → SuffixStops P suffix
  → proj₂ (some (satisfy P) pos ((x ∷ xs') ++ₗ suffix))
    ≡ just (mkResult (x ∷ xs') (advancePositions pos (x ∷ xs')) suffix)
some-satisfy-prefix P pos x xs' suffix px pxs ss
  rewrite px
  with manyHelper (satisfy P) (advancePosition pos x) (xs' ++ₗ suffix) (length (xs' ++ₗ suffix))
     | manyHelper-satisfy-exhaust-many P (advancePosition pos x) xs' suffix pxs ss
... | w' , just restResult | refl = refl
