-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- The one way a number literal becomes a value, shared by the DBC text
-- grammar and the kernel's JSON grammar.
--
-- A literal is read as its integer digits, its fraction digits and a
-- decimal exponent.  The core strips the leading and trailing zeros of
-- the significand and folds what is left only when the result can fit:
-- a literal whose value, once those zeros are stripped, has `digitCutoff`
-- or more digits before the decimal point, `placeCutoff` or more after
-- it, or `digitCutoff` or more significant digits, is *held* instead, as
-- a value with one component exactly 2^64, without its digits ever being
-- folded into a number.  The bound checks that
-- follow every parse (`max-rational-component-magnitude`) refuse a held
-- value the way they refuse any value past the bound, so the cost of
-- reading a literal is linear in its length whatever it holds, and no
-- literal that fits the bound is ever held.
--
-- `Aletheia.DBC.DecRat.Literal.Properties` proves both directions: a held
-- literal's exact value has a component of at least 2^64, and a literal
-- that is not held reads to exactly the value the digit fold gives.
module Aletheia.DBC.DecRat.Literal where

open import Data.Bool using (Bool; true; false; if_then_else_; _∨_)
open import Data.Char using (Char; toℕ)
open import Data.List using (List; []; _∷_; _++_; foldl; length; reverse)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_; _≤ᵇ_; _<ᵇ_; _≡ᵇ_)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Product using (_×_; _,_; proj₁)

open import Aletheia.DBC.DecRat using (DecRat; canonicalizeDecRat)
open import Aletheia.DBC.TextFormatter.Emitter using (showNat-chars)

-- ============================================================================
-- DIGITS
-- ============================================================================

-- The value of a digit character, and 0 for any other character.  Every
-- digit run a parser hands over was read through a digit predicate, so
-- the second arm is never taken at run time; it makes the value of every
-- character below 10, which the proofs rest on.
digitValue : Char → ℕ
digitValue c = let v = toℕ c ∸ 48 in if v <ᵇ 10 then v else 0

-- Left-to-right digit fold: `"042"` reads as 42.
foldDigits : List Char → ℕ
foldDigits = foldl (λ acc c → acc * 10 + digitValue c) 0

isZeroDigit : Char → Bool
isZeroDigit c = digitValue c ≡ᵇ 0

-- The run with its leading zero-valued characters removed.
dropZeros : List Char → List Char
dropZeros []       = []
dropZeros (c ∷ cs) = if isZeroDigit c then dropZeros cs else c ∷ cs

-- The significand of a run with no leading zeros: the run with its
-- trailing zeros removed, and the number removed.  Defined by cases on
-- the run, so `significand cs` below stays one term in a proof until the
-- stripped run is known.
significandFrom : List Char → List Char × ℕ
significandFrom []               = [] , 0
significandFrom leading@(_ ∷ _)  =
  let trailing = dropZeros (reverse leading)
  in reverse trailing , length leading ∸ length trailing

-- The significand of a digit run: the run with its leading and trailing
-- zeros removed, and the number of trailing zeros removed.  An all-zero
-- run gives the empty significand.
significand : List Char → List Char × ℕ
significand cs = significandFrom (dropZeros cs)

-- ============================================================================
-- THE CUTOFF
-- ============================================================================

-- A significand of this many digits, or more, is at least 10^64, past
-- every component bound.
digitCutoff : ℕ
digitCutoff = 65

-- A denominator of this many decimal places, or more, is at least 2^64
-- or 5^64 after reduction, since a significand ends in a nonzero digit.
placeCutoff : ℕ
placeCutoff = 64

-- The component a held literal carries: 2^64, one past the largest
-- `observed` a refusal reports.
heldMagnitude : ℕ
heldMagnitude = 18446744073709551616

-- A held value whose numerator crossed: 2^64 / 1.
heldNumerator : ℕ × ℕ × ℕ
heldNumerator = heldMagnitude , 0 , 0

-- A held value whose denominator crossed: 1 / 2^64, already canonical.
heldDenominator : ℕ × ℕ × ℕ
heldDenominator = 1 , placeCutoff , 0

-- ============================================================================
-- THE CORE
-- ============================================================================

-- The unsigned raw value of a literal from its significand, as a
-- numerator and the exponents of 2 and 5 of its denominator before
-- canonicalisation: `places` is the number of fraction digits plus the
-- magnitude of a negative exponent, `power` a positive exponent, and the
-- literal denotes `digits * 10^power / 10^places`.
--
-- With `s` significant digits and `t` trailing zeros stripped: when the
-- places are covered (`places ≤ power + t`) the value is an integer of
-- `s + e` digits, `e = power + t ∸ places`, held at `digitCutoff`;
-- otherwise it has `d = places ∸ (power + t)` decimal places and is held
-- at `placeCutoff` places or `digitCutoff` digits.  Zero is never held.
rawFromSignificand : List Char × ℕ → ℕ → ℕ → ℕ × ℕ × ℕ
rawFromSignificand ([] , _) _ _ = 0 , 0 , 0
rawFromSignificand (sig , t) places power =
  if places ≤ᵇ power + t
    then (let e = power + t ∸ places
          in if digitCutoff ≤ᵇ length sig + e
               then heldNumerator
               else foldDigits sig * 10 ^ e , 0 , 0)
    else (let d = places ∸ (power + t)
          in if (placeCutoff ≤ᵇ d) ∨ (digitCutoff ≤ᵇ length sig)
               then heldDenominator
               else foldDigits sig , d , d)

-- The unsigned raw value of a digit run: the integer digits followed by
-- the fraction digits.
rawLiteral : List Char → ℕ → ℕ → ℕ × ℕ × ℕ
rawLiteral digits = rawFromSignificand (significand digits)

-- A natural-number literal: its digits, or 2^64 when there are at least
-- `digitCutoff` significant ones.
natLiteral : List Char → ℕ
natLiteral digits = proj₁ (rawLiteral digits 0 0)

-- The sign applied to a magnitude; `-0` is `+0`.
applySign : Maybe Char → ℕ → ℤ
applySign nothing  n       = + n
applySign (just _) zero    = + 0
applySign (just _) (suc n) = -[1+ n ]

-- The places and the power a decimal exponent contributes.
exponentPlaces : ℤ → ℕ
exponentPlaces (+ _)     = 0
exponentPlaces -[1+ n ]  = suc n

exponentPower : ℤ → ℕ
exponentPower (+ n)     = n
exponentPower -[1+ _ ]  = 0

-- The canonical `DecRat` of a sign and a raw value.
signedDecRat : Maybe Char → ℕ × ℕ × ℕ → DecRat
signedDecRat neg (n , a , b) = canonicalizeDecRat (applySign neg n) a b

-- A decimal literal: an optional sign, integer digits, fraction digits
-- and a decimal exponent, read to its canonical `DecRat`.
decimalLiteral : Maybe Char → List Char → List Char → ℤ → DecRat
decimalLiteral neg int frac x =
  signedDecRat neg
    (rawLiteral (int ++ frac) (length frac + exponentPlaces x) (exponentPower x))

-- The held value a parser returns for a literal whose exponent alone
-- carries it past the bound, before the exponent's digits are folded:
-- the numerator side for a positive exponent, the denominator side for
-- a negative one.
heldLiteral : Maybe Char → Bool → DecRat
heldLiteral neg negativeExponent =
  signedDecRat neg (if negativeExponent then heldDenominator else heldNumerator)

-- ============================================================================
-- THE EXPONENT
-- ============================================================================

-- A decimal exponent written with a sign and digits, as the JSON grammar
-- has it.  `'-'` negates; any other sign, or none, is positive.
signedExponent : Maybe Char → ℕ → ℤ
signedExponent (just '-') n = applySign (just '-') n
signedExponent _          n = + n

-- Whether an exponent's digits alone carry a nonzero literal past the
-- bound: an exponent with more significant digits than the number
-- `places + t + digitCutoff` has is at least that number's successor
-- power of ten, so the literal is held whichever way the exponent points.
-- Decided by comparing digit counts, before the exponent is folded.
exponentHolds : ℕ → ℕ → List Char → Bool
exponentHolds places t expDigits =
  length (showNat-chars (places + t + digitCutoff)) <ᵇ length (dropZeros expDigits)

-- A literal in scientific notation: an optional sign, integer digits,
-- fraction digits, and the exponent's sign and digits.  Zero is zero
-- whatever its exponent; a nonzero literal whose exponent is too long to
-- matter is held; every other exponent is folded and read exactly.
scientificLiteral : Maybe Char → List Char → List Char → Maybe Char → List Char → DecRat
scientificLiteral neg int frac expSign expDigits with significand (int ++ frac)
... | [] , _ = signedDecRat neg (0 , 0 , 0)
... | _  , t =
  if exponentHolds (length frac) t expDigits
    then heldLiteral neg (isMinus expSign)
    else decimalLiteral neg int frac (signedExponent expSign (foldDigits expDigits))
  where
    isMinus : Maybe Char → Bool
    isMinus (just '-') = true
    isMinus _          = false
