-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- JSON formatter (structurally recursive on JSON).
--
-- Purpose: Serialize JSON values to strings.
-- Strings are escaped (", \, \n, \r, \t) to be inverse to JSON.Parse, which
-- has handled escapes from the start.  The escape pass lets
-- DBCTextResponse carry literal quotes and newlines round-trip through
-- the JSON envelope.
module Aletheia.Protocol.JSON.Format where

open import Data.String using (String; fromList) renaming (_++_ to _++ₛ_)
open import Data.List using (List; []; _∷_; length; intersperse) renaming (_++_ to _++ₗ_)
open import Data.Char using (Char)
open import Data.Bool using (true; false)
open import Data.Nat using (zero; suc; _<_; z<s; s<s)
open import Data.Nat.Induction using (<-wellFounded-fast)
open import Data.Nat.Properties using (m<n⇒m<1+n)
open import Induction.WellFounded using (Acc; acc)
open import Data.Integer using ()
open import Data.Rational as Rat using (ℚ)
open import Data.Rational.Unnormalised as ℚᵘ using ()
open import Data.Product using (_×_; _,_)
open import Data.Integer.Show using () renaming (show to showℤ)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Aletheia.Protocol.JSON.Types using (JSON; JNull; JBool; JNumber; JString; JArray; JObject)

-- Format a rational: integers as decimal notation, non-integers as object
formatRational : ℚ → String
formatRational r with Rat.toℚᵘ r
... | ℚᵘ.mkℚᵘ num zero =
      -- Denominator is 1, format as integer
      showℤ num
... | ℚᵘ.mkℚᵘ num (suc denom-1) =
      -- Denominator > 1, format as object for exact representation
      "{\"numerator\": " ++ₛ showℤ num ++ₛ
      ", \"denominator\": " ++ₛ showℕ (suc (suc denom-1)) ++ₛ "}"

private
  escapeChar : Char → List Char
  escapeChar c with c
  ... | '"'   = '\\' ∷ '"' ∷ []
  ... | '\\'  = '\\' ∷ '\\' ∷ []
  ... | '\n'  = '\\' ∷ 'n' ∷ []
  ... | '\r'  = '\\' ∷ 'r' ∷ []
  ... | '\t'  = '\\' ∷ 't' ∷ []
  ... | other = other ∷ []

  -- `cs` escaped, in front of `rest`.
  escapeOnto : List Char → List Char → List Char
  escapeOnto []       rest = rest
  escapeOnto (c ∷ cs) rest = escapeChar c ++ₗ escapeOnto cs rest

-- The elements of an array are rendered one by one and then joined
-- neighbour to neighbour, which halves their number: every round copies the
-- text once, so n elements cost a number of copies logarithmic in n, where
-- appending them one by one would copy everything after an element once per
-- element.  The rounds end because each shortens the list, the same
-- well-founded recursion as stdlib's merge sort.  Within one value the few
-- pieces are appended directly, which is cheapest for the small responses a
-- stream answers each frame with.
private
  pairUp : List String → List String
  pairUp (a ∷ b ∷ rest) = (a ++ₛ b) ∷ pairUp rest
  pairUp xs             = xs

  pairUp-shorter : ∀ a b rest → length (pairUp (a ∷ b ∷ rest)) < length (a ∷ b ∷ rest)
  pairUp-shorter _ _ []           = s<s z<s
  pairUp-shorter _ _ (_ ∷ [])     = s<s (s<s z<s)
  pairUp-shorter _ _ (c ∷ d ∷ cs) = s<s (m<n⇒m<1+n (pairUp-shorter c d cs))

  joinAll : (xs : List String) → Acc _<_ (length xs) → String
  joinAll []                _         = ""
  joinAll (x ∷ [])          _         = x
  joinAll xs@(a ∷ b ∷ rest) (acc rec) = joinAll (pairUp xs) (rec (pairUp-shorter a b rest))

  -- Rendered elements, separated by commas.
  joinSeparated : List String → String
  joinSeparated xs = joinAll (intersperse ", " xs) (<-wellFounded-fast _)

mutual
  formatJSON : JSON → String
  formatJSON JNull         = "null"
  formatJSON (JBool true)  = "true"
  formatJSON (JBool false) = "false"
  formatJSON (JNumber n)   = formatRational n
  formatJSON (JString cs)  = fromList ('"' ∷ escapeOnto cs ('"' ∷ []))
  formatJSON (JArray xs)   = "[" ++ₛ joinSeparated (renderElements xs) ++ₛ "]"
  formatJSON (JObject fs)  = "{" ++ₛ renderFields fs ++ₛ "}"

  renderElements : List JSON → List String
  renderElements []       = []
  renderElements (x ∷ xs) = formatJSON x ∷ renderElements xs

  -- An object's fields are the few its kind declares, so they are appended
  -- one by one; a collection the data sizes is an array.
  renderFields : List (String × JSON) → String
  renderFields []                          = ""
  renderFields ((key , val) ∷ [])          = renderField key val
  renderFields ((key , val) ∷ rest@(_ ∷ _)) = renderField key val ++ₛ ", " ++ₛ renderFields rest

  renderField : String → JSON → String
  renderField key val = "\"" ++ₛ key ++ₛ "\": " ++ₛ formatJSON val
