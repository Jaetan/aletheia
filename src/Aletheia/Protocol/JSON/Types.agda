-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- JSON data type definition.
--
-- Purpose: Core JSON value representation used throughout the protocol layer.
-- Numbers use rationals (ℚ) for exact decimal representation.
--
-- `JString` carries `List Char` (not `String`). This aligns the JSON
-- internal string representation with the JSON tokenizer's working
-- representation (which already builds chars in `Parse.agda:parseStringChar`)
-- and with Identifier's `name : List Char`. Identifier-typed JSON fields
-- then roundtrip axiom-free; the wire-level UTF-8 representation is
-- unchanged because `JString` always serialises as `fromList chars` for
-- output. Object keys stay `String` (used as map indices, not roundtripped
-- through wire chars).
module Aletheia.Protocol.JSON.Types where

open import Data.Char using (Char)
open import Data.String using (String; toList)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool)
open import Data.Unit using (⊤)
open import Data.Integer using (∣_∣)
-- `_⊔′_`, NOT `_⊔_`: stdlib's `_⊔_` is defined by structural recursion on the
-- unary view, so MAlonzo compiles it to decrement-and-recurse — cost linear in
-- the VALUE of its arguments, not their bit width, and not tail recursive.  On
-- a rational component that is fatal: a submitted factor of `<17 digits>/10^17`
-- makes the measurement below allocate until the host dies (the JSON-bound
-- check would itself be unbounded in the magnitude it exists to bound).
-- `_⊔′_` is stdlib's primitive-comparison max (constant time); `⊔≡⊔′` in
-- Data.Nat.Properties converts between them should a proof ever need the
-- recursive form.  Both measurements here feed Bool bound checks only, so
-- neither has a proof obligation to preserve.
open import Data.Nat using (ℕ; suc; _⊔′_; _≤_)
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

-- Structural nesting depth of a JSON value.  Mirrors nlohmann/json's
-- `parse_event_t::object_start` / `array_start` callback semantics —
-- primitives are depth 0, each Array/Object nesting level increments by 1.
-- Used at the parseJSON surface for a post-parse depth check alongside
-- the Identifier length bound and the atom-count bound.  Direct
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
  listDepth (x ∷ xs) = jsonDepth x ⊔′ listDepth xs

  -- Maximum depth across an Object's field values; keys carry no nesting.
  fieldsDepth : List (String × JSON) → ℕ
  fieldsDepth []           = 0
  fieldsDepth (kv ∷ rest)  = jsonDepth (proj₂ kv) ⊔′ fieldsDepth rest

-- Largest rational-component magnitude of any number in a JSON value:
-- the maximum over all `JNumber q` of `∣ numerator q ∣ ⊔′ denominator q`
-- (the parsed, reduced components — reduction only shrinks magnitudes,
-- so a bounded submitted literal stays bounded).  Companion to
-- `jsonDepth`: direct measurement of the parsed tree, consumed by the
-- post-parse `max-rational-component-magnitude` bound (the Int64 wire
-- range) at the `processJSONLine` surface.  Primitives without numeric
-- content and empty containers contribute 0.
mutual
  jsonMaxComponent : JSON → ℕ
  jsonMaxComponent JNull            = 0
  jsonMaxComponent (JBool _)        = 0
  jsonMaxComponent (JNumber q)      = ∣ ℚ.numerator q ∣ ⊔′ suc (ℚ.denominator-1 q)
  jsonMaxComponent (JString _)      = 0
  jsonMaxComponent (JArray xs)      = listMaxComponent xs
  jsonMaxComponent (JObject fields) = fieldsMaxComponent fields

  -- Maximum component magnitude across an Array's elements.
  listMaxComponent : List JSON → ℕ
  listMaxComponent []       = 0
  listMaxComponent (x ∷ xs) = jsonMaxComponent x ⊔′ listMaxComponent xs

  -- Maximum component magnitude across an Object's field values; keys
  -- carry no numeric content.
  fieldsMaxComponent : List (String × JSON) → ℕ
  fieldsMaxComponent []          = 0
  fieldsMaxComponent (kv ∷ rest) = jsonMaxComponent (proj₂ kv) ⊔′ fieldsMaxComponent rest

-- Every number in a JSON value satisfies a claim on rationals; a `Set`,
-- never computed at run time, stated per number so a proof can follow the
-- tree.
mutual
  NumbersSatisfy : (ℚ → Set) → JSON → Set
  NumbersSatisfy _ JNull            = ⊤
  NumbersSatisfy _ (JBool _)        = ⊤
  NumbersSatisfy P (JNumber q)      = P q
  NumbersSatisfy _ (JString _)      = ⊤
  NumbersSatisfy P (JArray xs)      = ListNumbersSatisfy P xs
  NumbersSatisfy P (JObject fields) = FieldsNumbersSatisfy P fields

  -- Every element of an Array.
  ListNumbersSatisfy : (ℚ → Set) → List JSON → Set
  ListNumbersSatisfy _ []       = ⊤
  ListNumbersSatisfy P (x ∷ xs) = NumbersSatisfy P x × ListNumbersSatisfy P xs

  -- Every field value of an Object; keys carry no numeric content.
  FieldsNumbersSatisfy : (ℚ → Set) → List (String × JSON) → Set
  FieldsNumbersSatisfy _ []          = ⊤
  FieldsNumbersSatisfy P (kv ∷ rest) = NumbersSatisfy P (proj₂ kv) × FieldsNumbersSatisfy P rest

-- Both reduced components of a rational within a bound: the magnitude of its
-- numerator and its denominator, the claim `jsonMaxComponent` measures.
ComponentsWithin : ℕ → ℚ → Set
ComponentsWithin bound q = ∣ ℚ.numerator q ∣ ≤ bound × suc (ℚ.denominator-1 q) ≤ bound

-- Every number in a JSON value has both components within the bound.
NumbersWithin : ℕ → JSON → Set
NumbersWithin bound = NumbersSatisfy (ComponentsWithin bound)

ListNumbersWithin : ℕ → List JSON → Set
ListNumbersWithin bound = ListNumbersSatisfy (ComponentsWithin bound)

FieldsNumbersWithin : ℕ → List (String × JSON) → Set
FieldsNumbersWithin bound = FieldsNumbersSatisfy (ComponentsWithin bound)
