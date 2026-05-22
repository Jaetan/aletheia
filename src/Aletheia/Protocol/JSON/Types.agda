{-# OPTIONS --safe --without-K #-}

-- JSON data type definition.
--
-- Purpose: Core JSON value representation used throughout the protocol layer.
-- Numbers use rationals (ℚ) for exact decimal representation.
--
-- Track B.3.d 3d.4 + JSON-mirror (2026-04-27): `JString : List Char → JSON`
-- (was `String → JSON`). Aligns the JSON internal string representation
-- with the JSON tokenizer's working representation (which already builds
-- chars in `Parse.agda:parseStringChar`) and with Identifier's post-3d.4
-- `name : List Char`. Identifier-typed JSON fields then roundtrip
-- axiom-free; the wire-level UTF-8 representation is unchanged because
-- `JString` always serialises as `fromList chars` for output. Object keys
-- stay `String` (used as map indices, not roundtripped through wire chars).
module Aletheia.Protocol.JSON.Types where

open import Data.Char using (Char)
open import Data.String using (String; toList)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool)
open import Data.Nat using (ℕ; suc; _⊔_)
open import Data.Rational using (ℚ)
open import Data.Product using (_×_; proj₂)
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

-- R19 cluster 8 phase e.2 (companion to e.1 / e.2 pattern): structural
-- nesting depth of a JSON value.  Mirrors nlohmann/json's
-- `parse_event_t::object_start` / `array_start` callback semantics —
-- primitives are depth 0, each Array/Object nesting level increments by 1.
-- Used at the parseJSON surface for a post-parse depth check that mirrors
-- e.1's Identifier length bound and e.2's atom-count bound.  Direct
-- measurement, NOT fuel — the bound `max-nesting-depth` is the
-- canonical adversarial-input limit (`Aletheia.Limits`, 64).
mutual
  jsonDepth : JSON → ℕ
  jsonDepth JNull             = 0
  jsonDepth (JBool _)         = 0
  jsonDepth (JNumber _)       = 0
  jsonDepth (JString _)       = 0
  jsonDepth (JArray xs)       = suc (listDepth xs)
  jsonDepth (JObject fields)  = suc (fieldsDepth fields)

  -- Maximum depth across a list of JSON values (children of an Array).
  listDepth : List JSON → ℕ
  listDepth []       = 0
  listDepth (x ∷ xs) = jsonDepth x ⊔ listDepth xs

  -- Maximum depth across an Object's field values; keys carry no nesting.
  fieldsDepth : List (String × JSON) → ℕ
  fieldsDepth []           = 0
  fieldsDepth (kv ∷ rest)  = jsonDepth (proj₂ kv) ⊔ fieldsDepth rest
