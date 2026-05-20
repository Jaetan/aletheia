{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 3 3d.5.d 3c-A — `Format.AttrDef` head-non-hspace helpers.
--
-- Extracted from `Format/AttrDef.agda` (R22 continuation of R21
-- AGDA-D-15.1) to bring the parent module under the 800-LOC trigger.
-- These helpers bridge from emit-shape to `SuffixStops isHSpace …` /
-- `SuffixStops isDigit …` preconditions required by the EMITS-OK
-- BUILDERS section in AttrDef.agda; for closed prefixes the head is a
-- literal letter, but the data-dependent leaves
-- (`showNat-chars` / `showInt-chars` / `showDecRat-dec-chars` /
-- `quoteStringLit-chars`) need per-shape arguments that this module
-- packages.
--
-- Dependency direction is one-way `HeadHelpers → {Lexer, Emitter,
-- DecRatParse.Properties}`; AttrDef.agda imports back from this
-- module.  No cycle.
module Aletheia.DBC.TextParser.Format.AttrDef.HeadHelpers where

open import Data.Bool using (false)
open import Data.Char using (Char)
open import Data.Char.Base using (isDigit)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (List; _∷_) renaming (_++_ to _++ₗ_)
open import Data.List.Properties using () renaming (++-assoc to ++ₗ-assoc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; subst)

open import Aletheia.DBC.DecRat using (DecRat; mkDecRat)
open import Aletheia.DBC.TextParser.Lexer using (isHSpace)
open import Aletheia.DBC.TextFormatter.Emitter
  using (digitChar; showInt-chars; showNat-chars; showDecRat-dec-chars;
         quoteStringLit-chars)
open import Aletheia.DBC.TextParser.DecRatParse.Properties
  using (SuffixStops; ∷-stop; headOr;
         showNat-chars-head;
         showDecRat-chars-head-dash; showDecRat-chars-head-digit)

-- 10 digit chars are non-hspace.  `digitChar d` for any closed `d` is
-- in {'0' … '9'}; closed-char `≈ᵇ` comparison reduces to `false` for
-- both space (' ') and tab ('\t').
digit-not-isHSpace : ∀ d → isHSpace (digitChar d) ≡ false
digit-not-isHSpace 0 = refl
digit-not-isHSpace 1 = refl
digit-not-isHSpace 2 = refl
digit-not-isHSpace 3 = refl
digit-not-isHSpace 4 = refl
digit-not-isHSpace 5 = refl
digit-not-isHSpace 6 = refl
digit-not-isHSpace 7 = refl
digit-not-isHSpace 8 = refl
digit-not-isHSpace 9 = refl
digit-not-isHSpace
  (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _)))))))))) = refl

-- Head of `(showNat-chars n ++ inner-rest) ++ outer-suffix` is non-hspace.
-- Mirrors `Format/Comments.agda`'s `showNat-chars-head-non-hspace`.
showNat-chars-head-stop : ∀ (n : ℕ) (rest : List Char)
  → SuffixStops isHSpace (showNat-chars n ++ₗ rest)
showNat-chars-head-stop n rest with showNat-chars-head n
... | d , tail , _ , eq =
      subst (λ xs → SuffixStops isHSpace (xs ++ₗ rest))
            (sym eq)
            (∷-stop (digit-not-isHSpace d))

-- Head of `(showInt-chars z ++ inner-rest) ++ outer-suffix` is non-hspace.
-- Three-case dispatch: `(+ zero)` / `(+ suc n)` / `-[1+ _ ]` (the
-- `-` head is non-hspace by `refl`).
showInt-chars-head-stop : ∀ (z : ℤ) (rest : List Char)
  → SuffixStops isHSpace (showInt-chars z ++ₗ rest)
showInt-chars-head-stop (+ n) rest = showNat-chars-head-stop n rest
showInt-chars-head-stop (-[1+ _ ]) _ = ∷-stop refl

-- Head of `(showDecRat-dec-chars d ++ inner-rest) ++ outer-suffix` is
-- non-hspace.  Three-case dispatch on the DecRat numerator's sign.
showDecRat-chars-head-stop : ∀ (d : DecRat) (rest : List Char)
  → SuffixStops isHSpace (showDecRat-dec-chars d ++ₗ rest)
showDecRat-chars-head-stop (mkDecRat (+ zero) a b cx) rest
  with showDecRat-chars-head-digit zero a b cx
... | k , tail , _ , eq =
      subst (λ xs → SuffixStops isHSpace (xs ++ₗ rest))
            (sym eq)
            (∷-stop (digit-not-isHSpace k))
showDecRat-chars-head-stop (mkDecRat (+ suc n) a b cx) rest
  with showDecRat-chars-head-digit (suc n) a b cx
... | k , tail , _ , eq =
      subst (λ xs → SuffixStops isHSpace (xs ++ₗ rest))
            (sym eq)
            (∷-stop (digit-not-isHSpace k))
showDecRat-chars-head-stop (mkDecRat (-[1+ n ]) a b cx) rest
  with showDecRat-chars-head-dash n a b cx
... | tail , eq =
      subst (λ xs → SuffixStops isHSpace (xs ++ₗ rest))
            (sym eq)
            (∷-stop refl)

-- Head of `(quoteStringLit-chars cs ++ inner-rest) ++ outer-suffix` is
-- `'"'` (non-hspace).  `quoteStringLit-chars` always starts with `'"'`
-- by definitional reduction.
quoted-head-stop : ∀ (cs rest : List Char)
  → SuffixStops isHSpace (quoteStringLit-chars cs ++ₗ rest)
quoted-head-stop _ _ = ∷-stop refl

-- `'.' ≢ headOr (' ' ∷ rest) '_'` discharges by `λ ()` — `headOr`
-- returns the first elem when non-empty, so `headOr (' ' ∷ rest) _ = ' '`
-- and `'.' ≡ ' '` is absurd.
not-dot-after-space : ∀ (rest : List Char)
  → '.' ≢ headOr (' ' ∷ rest) '_'
not-dot-after-space _ = λ ()

-- ++ₗ-assoc bridge: convert a right-associated `xs ++ (as ++ bs)`
-- SuffixStops witness to the left-associated `(xs ++ as) ++ bs`
-- shape required by EmitsOK reductions of `withWS (pair intDecRat
-- (withWS intDecRat))` etc.  `withWS f`'s emit is `' ' ∷ emit f a`,
-- and `pair g h`'s emit is `emit g a ++ emit h b`, so the suffix at
-- the leading-ws slot is `(emit g a ++ emit h b) ++ outer-suffix` —
-- left-associated.  Our `showXxx-chars-head-stop` helpers produce a
-- right-associated witness; this bridges them.
assoc-bridgeᴴ : ∀ (xs as bs : List Char)
  → SuffixStops isHSpace (xs ++ₗ (as ++ₗ bs))
  → SuffixStops isHSpace ((xs ++ₗ as) ++ₗ bs)
assoc-bridgeᴴ xs as bs ss =
  subst (SuffixStops isHSpace) (sym (++ₗ-assoc xs as bs)) ss

assoc-bridgeᴰ : ∀ (xs as bs : List Char)
  → SuffixStops isDigit (xs ++ₗ (as ++ₗ bs))
  → SuffixStops isDigit ((xs ++ₗ as) ++ₗ bs)
assoc-bridgeᴰ xs as bs ss =
  subst (SuffixStops isDigit) (sym (++ₗ-assoc xs as bs)) ss
