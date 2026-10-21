-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- The JSON formatter.
--
-- Each value is written in front of the text that follows it, so a reply is
-- built in one pass and `fromList` turns it into a string once.  A string
-- or key is escaped: the quotation mark, the reverse solidus, and every
-- character below U+0020 (`\b \f \n \r \t`, the others `\u00XX`).  An
-- integer is written as its decimal digits, a rational with a denominator
-- above 1 as the object `{"numerator": n, "denominator": d}`.
module Aletheia.Protocol.JSON.Format where

open import Data.String using (String; toList; fromList)
open import Data.List using (List; []; _∷_)
open import Data.Char using (Char; _≈ᵇ_)
open import Data.Char.Base using (toℕ; fromℕ)
open import Data.Bool using (true; false; _∨_; if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _<ᵇ_; _/_; _%_; s≤s; z≤n)
open import Data.Nat.DivMod using (m/n<m)
open import Data.Nat.Induction using (<-wellFounded-fast)
open import Induction.WellFounded using (Acc; acc)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Rational using (ℚ; mkℚ)
open import Data.Product using (_×_; _,_)
open import Aletheia.DBC.TextFormatter.Emitter using (digitChar)
open import Aletheia.Protocol.JSON.Types using (JSON; JNull; JBool; JNumber; JString; JArray; JObject)

-- `n`, below 16, as a lowercase hex digit.
hexDigitChar : ℕ → Char
hexDigitChar n = if n <ᵇ 10 then fromℕ (48 + n) else fromℕ (87 + n)

-- The escape of the character numbered `n`, below 32, after its `\`.
controlEscape : ℕ → List Char → List Char
controlEscape 8  rest = 'b' ∷ rest
controlEscape 9  rest = 't' ∷ rest
controlEscape 10 rest = 'n' ∷ rest
controlEscape 12 rest = 'f' ∷ rest
controlEscape 13 rest = 'r' ∷ rest
controlEscape n  rest = 'u' ∷ '0' ∷ '0' ∷ hexDigitChar (n / 16) ∷ hexDigitChar (n % 16) ∷ rest

escapeChar : Char → List Char → List Char
escapeChar c rest =
  if toℕ c <ᵇ 32 then '\\' ∷ controlEscape (toℕ c) rest
  else if (c ≈ᵇ '"') ∨ (c ≈ᵇ '\\') then '\\' ∷ c ∷ rest
  else c ∷ rest

escapeOnto : List Char → List Char → List Char
escapeOnto []       rest = rest
escapeOnto (c ∷ cs) rest = escapeChar c (escapeOnto cs rest)

-- A quoted string.
showsString : List Char → List Char → List Char
showsString cs rest = '"' ∷ escapeOnto cs ('"' ∷ rest)

-- The decimal digits of `n` in front of `rest`, most significant first, by
-- well-founded recursion on `n`.  Zero writes nothing, so the first digit
-- written is never `0`.
digitsOnto : (n : ℕ) → Acc _<_ n → List Char → List Char
digitsOnto zero      _         rest = rest
digitsOnto n@(suc _) (acc rec) rest =
  digitsOnto (n / 10) (rec (m/n<m n 10 (s≤s (s≤s z≤n)))) (digitChar (n % 10) ∷ rest)

showsℕ : ℕ → List Char → List Char
showsℕ zero      rest = '0' ∷ rest
showsℕ n@(suc _) rest = digitsOnto n (<-wellFounded-fast n) rest

showsℤ : ℤ → List Char → List Char
showsℤ (+ n)    rest = showsℕ n rest
showsℤ -[1+ n ] rest = '-' ∷ showsℕ (suc n) rest

showsRational : ℚ → List Char → List Char
showsRational (mkℚ num zero      _) rest = showsℤ num rest
showsRational (mkℚ num (suc d-1) _) rest =
  '{' ∷ showsString (toList "numerator") (':' ∷ ' ' ∷ showsℤ num
    (',' ∷ ' ' ∷ showsString (toList "denominator") (':' ∷ ' ' ∷ showsℕ (suc (suc d-1)) ('}' ∷ rest))))

mutual
  showsJSON : JSON → List Char → List Char
  showsJSON JNull         rest = 'n' ∷ 'u' ∷ 'l' ∷ 'l' ∷ rest
  showsJSON (JBool true)  rest = 't' ∷ 'r' ∷ 'u' ∷ 'e' ∷ rest
  showsJSON (JBool false) rest = 'f' ∷ 'a' ∷ 'l' ∷ 's' ∷ 'e' ∷ rest
  showsJSON (JNumber r)   rest = showsRational r rest
  showsJSON (JString cs)  rest = showsString cs rest
  showsJSON (JArray [])                rest = '[' ∷ ']' ∷ rest
  showsJSON (JArray (x ∷ xs))          rest = '[' ∷ showsJSON x (showsElements xs (']' ∷ rest))
  showsJSON (JObject [])               rest = '{' ∷ '}' ∷ rest
  showsJSON (JObject ((k , v) ∷ fs))   rest = '{' ∷ showsField k v (showsFields fs ('}' ∷ rest))

  -- Each element after the first, after a comma and a space.
  showsElements : List JSON → List Char → List Char
  showsElements []       rest = rest
  showsElements (x ∷ xs) rest = ',' ∷ ' ' ∷ showsJSON x (showsElements xs rest)

  showsFields : List (String × JSON) → List Char → List Char
  showsFields []             rest = rest
  showsFields ((k , v) ∷ fs) rest = ',' ∷ ' ' ∷ showsField k v (showsFields fs rest)

  showsField : String → JSON → List Char → List Char
  showsField k v rest = showsString (toList k) (':' ∷ ' ' ∷ showsJSON v rest)

formatJSONChars : JSON → List Char
formatJSONChars j = showsJSON j []

formatJSON : JSON → String
formatJSON j = fromList (formatJSONChars j)
