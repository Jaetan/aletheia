{-# OPTIONS --safe --without-K #-}

-- JSON formatter (structurally recursive on JSON).
--
-- Purpose: Serialize JSON values to strings.
-- Strings are escaped (", \, \n, \r, \t) to be inverse to JSON.Parse, which
-- has handled escapes from the start.  Track E.10 added the escape pass so
-- DBCTextResponse can carry literal quotes and newlines round-trip through
-- the JSON envelope.
module Aletheia.Protocol.JSON.Format where

open import Data.String using (String; fromList) renaming (_++_ to _++ₛ_)
open import Data.List using (List; []; _∷_; concatMap)
open import Data.Char using (Char)
open import Data.Bool using (true; false)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Integer using (ℤ)
open import Data.Rational as Rat using (ℚ)
open import Data.Rational.Unnormalised as ℚᵘ using (ℚᵘ; mkℚᵘ)
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

  escapeString : List Char → List Char
  escapeString = concatMap escapeChar

formatJSON : JSON → String
formatJSON JNull = "null"
formatJSON (JBool true) = "true"
formatJSON (JBool false) = "false"
formatJSON (JNumber n) = formatRational n
formatJSON (JString cs) = "\"" ++ₛ fromList (escapeString cs) ++ₛ "\""
formatJSON (JArray xs) = "[" ++ₛ formatJSONList xs ++ₛ"]"
  where
    formatJSONList : List JSON → String
    formatJSONList [] = ""
    formatJSONList (x ∷ []) = formatJSON x
    formatJSONList (x ∷ xs) = formatJSON x ++ₛ ", " ++ₛ formatJSONList xs
formatJSON (JObject fields) = "{" ++ₛ formatFields fields ++ₛ"}"
  where
    formatField : String × JSON → String
    formatField (key , val) = "\"" ++ₛ key ++ₛ"\": " ++ₛ formatJSON val

    formatFields : List (String × JSON) → String
    formatFields [] = ""
    formatFields (f ∷ []) = formatField f
    formatFields (f ∷ fs) = formatField f ++ₛ ", " ++ₛ formatFields fs
