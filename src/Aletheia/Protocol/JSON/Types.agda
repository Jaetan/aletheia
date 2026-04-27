{-# OPTIONS --safe --without-K #-}

-- JSON data type definition.
--
-- Purpose: Core JSON value representation used throughout the protocol layer.
-- Numbers use rationals (ℚ) for exact decimal representation.
--
-- Phase B.3.d 3d.4 + JSON-mirror (2026-04-27): `JString : List Char → JSON`
-- (was `String → JSON`). Aligns the JSON internal string representation
-- with the JSON tokenizer's working representation (which already builds
-- chars in `Parse.agda:parseStringChar`) and with Identifier's post-3d.4
-- `name : List Char`. Identifier-typed JSON fields then roundtrip
-- axiom-free; the wire-level UTF-8 representation is unchanged because
-- `JString` always serialises as `fromList chars` for output. Object keys
-- stay `String` (used as map indices, not roundtripped through wire chars).
module Aletheia.Protocol.JSON.Types where

open import Data.Char using (Char)
open import Data.String using (String; toList; fromList)
open import Data.List using (List)
open import Data.Bool using (Bool)
open import Data.Rational using (ℚ)
open import Data.Product using (_×_)
open import Function using (_∘_)

-- JSON value representation
-- Numbers are represented as rationals (ℚ) to support decimal values
data JSON : Set where
  JNull   : JSON
  JBool   : Bool → JSON
  JNumber : ℚ → JSON
  JString : List Char → JSON
  JArray  : List JSON → JSON
  JObject : List (String × JSON) → JSON

-- Convenience: build a JString from a String literal.  Used at sites where
-- a static String (e.g. JSON kind discriminator like `"node"`, `"network"`)
-- is the natural source.  Definitionally equals `JString (toList s)`.
JStringS : String → JSON
JStringS = JString ∘ toList
