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

open import Data.String using (String; fromList; toList) renaming (_++_ to _++ₛ_)
open import Data.List using (List; []; _∷_) renaming (_++_ to _++ₗ_)
open import Data.Char using (Char)
open import Data.Bool using (true; false)
open import Data.Nat using (zero; suc)
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

-- Each value is written in front of the characters that follow it, so every
-- character of the response is produced once and rendering costs time linear
-- in the response's length; the `String` is built once, from the finished
-- list.  Appending `String`s copies both operands, so a response assembled by
-- appending its elements one by one would cost time quadratic in their count.
mutual
  renderJSON : JSON → List Char → List Char
  renderJSON JNull              rest = 'n' ∷ 'u' ∷ 'l' ∷ 'l' ∷ rest
  renderJSON (JBool true)       rest = 't' ∷ 'r' ∷ 'u' ∷ 'e' ∷ rest
  renderJSON (JBool false)      rest = 'f' ∷ 'a' ∷ 'l' ∷ 's' ∷ 'e' ∷ rest
  renderJSON (JNumber n)        rest = toList (formatRational n) ++ₗ rest
  renderJSON (JString cs)       rest = '"' ∷ escapeOnto cs ('"' ∷ rest)
  renderJSON (JArray [])        rest = '[' ∷ ']' ∷ rest
  renderJSON (JArray (x ∷ xs))  rest = '[' ∷ renderJSON x (renderElements xs (']' ∷ rest))
  renderJSON (JObject [])       rest = '{' ∷ '}' ∷ rest
  renderJSON (JObject (f ∷ fs)) rest = '{' ∷ renderField f (renderFields fs ('}' ∷ rest))

  -- The elements after the first, each after its separator.
  renderElements : List JSON → List Char → List Char
  renderElements []       rest = rest
  renderElements (x ∷ xs) rest = ',' ∷ ' ' ∷ renderJSON x (renderElements xs rest)

  renderField : String × JSON → List Char → List Char
  renderField (key , val) rest = '"' ∷ toList key ++ₗ '"' ∷ ':' ∷ ' ' ∷ renderJSON val rest

  -- The fields after the first, each after its separator.
  renderFields : List (String × JSON) → List Char → List Char
  renderFields []       rest = rest
  renderFields (f ∷ fs) rest = ',' ∷ ' ' ∷ renderField f (renderFields fs rest)

formatJSON : JSON → String
formatJSON j = fromList (renderJSON j [])
