{-# OPTIONS --safe --without-K #-}

-- Correctness properties for JSON parser and formatter (Phase 3).
--
-- Purpose: Prove soundness of JSON parsing/formatting for Aletheia's protocol schemas.
-- Properties: Parser determinism, structural preservation, schema soundness (DBC, line protocol).
-- Approach: Congruence lemmas, structural induction, no character/integer decomposition.
module Aletheia.Protocol.JSON.Properties where

open import Aletheia.Protocol.JSON
open import Aletheia.Parser.Combinators
open import Aletheia.Parser.Properties
open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char)
open import Data.String using (String; _≟_) renaming (_++_ to _++ₛ_)
open import Data.List using (List; []; _∷_; map; length) renaming (_++_ to _++ₗ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Rational using (ℚ; _/_)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst; trans; _≢_)
open import Relation.Nullary using (Dec; yes; no)
open import Function using (_∘_)

-- ============================================================================
-- PROTOCOL VALUE DEFINITION
-- ============================================================================

-- Define protocol-relevant JSON values (those used in Aletheia's protocol)
mutual
  data IsProtocolValue : JSON → Set where
    proto-null   : IsProtocolValue JNull
    proto-bool   : ∀ b → IsProtocolValue (JBool b)
    -- Protocol uses integer rationals (denominator = 1)
    proto-int-pos : ∀ n → IsProtocolValue (JNumber ((+ n) / 1))
    proto-int-neg : ∀ n → IsProtocolValue (JNumber (-[1+ n ] / 1))
    -- Protocol treats strings as opaque (no escape sequences, no character-level reasoning)
    proto-string  : ∀ s → IsProtocolValue (JString s)
    proto-array   : ∀ {xs} → AllProtocolValues xs → IsProtocolValue (JArray xs)
    proto-object  : ∀ {fields} → AllProtocolFields fields → IsProtocolValue (JObject fields)

  -- All elements in a list are protocol values
  data AllProtocolValues : List JSON → Set where
    all-nil  : AllProtocolValues []
    all-cons : ∀ {x xs} → IsProtocolValue x → AllProtocolValues xs → AllProtocolValues (x ∷ xs)

  -- All fields in an object have protocol values
  data AllProtocolFields : List (String × JSON) → Set where
    fields-nil  : AllProtocolFields []
    fields-cons : ∀ {k v fields} → IsProtocolValue v → AllProtocolFields fields
                → AllProtocolFields ((k , v) ∷ fields)

-- ============================================================================
-- CONGRUENCE LEMMAS (Equality-Preserving Properties)
-- ============================================================================

-- Base cases for empty structures (non-trivial, keep these)
formatJSON-empty-array : formatJSON (JArray []) ≡ "[]"
formatJSON-empty-array = refl

formatJSON-empty-object : formatJSON (JObject []) ≡ "{}"
formatJSON-empty-object = refl

-- Note: Trivial congruence lemmas removed - use stdlib cong when needed.
-- Parser determinism proven in Parser.Properties (parseJSON-deterministic).

-- ============================================================================
-- STRUCTURAL PROPERTIES (for schema proofs)
-- ============================================================================

-- Array length (needed for validation)
array-length-empty : length ([] {A = JSON}) ≡ 0
array-length-empty = refl

-- Object field lookup properties (needed for schema parsing proofs)
open import Aletheia.Prelude using (lookupByKey)
open import Data.Empty using (⊥-elim; ⊥)

lookupByKey-empty : ∀ {A : Set} (key : String)
  → lookupByKey {A} key [] ≡ nothing
lookupByKey-empty key = refl

-- Note: These proofs require reasoning about if_then_else with decidable equality
-- When key ≟ key returns yes, ⌊ yes _ ⌋ = true, so if evaluates to then-branch
lookupByKey-here : ∀ {A : Set} (key : String) (v : A) (rest : List (String × A))
  → lookupByKey key ((key , v) ∷ rest) ≡ just v
lookupByKey-here {A} key v rest with key ≟ key
lookupByKey-here {A} key v rest | yes eq = refl
lookupByKey-here {A} key v rest | no k≢k = ⊥-elim (k≢k refl)

lookupByKey-there : ∀ {A : Set} (key key' : String) (v : A) (rest : List (String × A))
  → key ≢ key'
  → lookupByKey key ((key' , v) ∷ rest) ≡ lookupByKey key rest
lookupByKey-there {A} key key' v rest key≢key' with key' ≟ key
lookupByKey-there {A} key key' v rest key≢key' | yes key'≡key = ⊥-elim (key≢key' (sym key'≡key))
lookupByKey-there {A} key key' v rest key≢key' | no _ = refl

-- ============================================================================
-- SCHEMA-SPECIFIC PROPERTIES
-- ============================================================================

-- Use inspect idiom to capture equality in with-abstractions
open Relation.Binary.PropositionalEquality using (inspect; [_])

-- DBC File Structure
-- Proves that DBC files have expected structure (object with version and messages)
data DBCFileStructure : JSON → Set where
  dbc-structure : ∀ (obj : List (String × JSON)) (version : String) (messages : List JSON) →
    lookupByKey "version" obj ≡ just (JString version) →
    lookupByKey "messages" obj ≡ just (JArray messages) →
    DBCFileStructure (JObject obj)

-- Soundness: parseDBC only succeeds on well-formed DBC JSON objects
open import Aletheia.DBC.JSONParser using (parseDBC)
open import Aletheia.DBC.Types using (DBC)

parseDBC-sound : ∀ (input : JSON) (result : DBC)
  → parseDBC input ≡ just result
  → ∃[ obj ] ∃[ version ] ∃[ messages ]
      (input ≡ JObject obj
       × lookupByKey "version" obj ≡ just (JString version)
       × lookupByKey "messages" obj ≡ just (JArray messages))
parseDBC-sound (JObject obj) result eq with lookupByKey "version" obj | inspect (lookupByKey "version") obj
parseDBC-sound (JObject obj) result eq | just (JString version) | [ eqVer ]
  with lookupByKey "messages" obj | inspect (lookupByKey "messages") obj
parseDBC-sound (JObject obj) result eq | just (JString version) | [ eqVer ]
  | just (JArray messages) | [ eqMsgs ] = obj , version , messages , refl , eqVer , eqMsgs
parseDBC-sound (JObject obj) result () | just (JString version) | [ eqVer ] | just (JBool _) | _
parseDBC-sound (JObject obj) result () | just (JString version) | [ eqVer ] | just (JNumber _) | _
parseDBC-sound (JObject obj) result () | just (JString version) | [ eqVer ] | just (JString _) | _
parseDBC-sound (JObject obj) result () | just (JString version) | [ eqVer ] | just (JObject _) | _
parseDBC-sound (JObject obj) result () | just (JString version) | [ eqVer ] | just JNull | _
parseDBC-sound (JObject obj) result () | just (JString version) | [ eqVer ] | nothing | _
parseDBC-sound (JObject obj) result () | just (JBool _) | _  -- version not a string
parseDBC-sound (JObject obj) result () | just (JNumber _) | _
parseDBC-sound (JObject obj) result () | just (JArray _) | _
parseDBC-sound (JObject obj) result () | just (JObject _) | _
parseDBC-sound (JObject obj) result () | just JNull | _
parseDBC-sound (JObject obj) result () | nothing | _  -- no version field
parseDBC-sound JNull result ()
parseDBC-sound (JBool _) result ()
parseDBC-sound (JNumber _) result ()
parseDBC-sound (JString _) result ()
parseDBC-sound (JArray _) result ()

-- Line Protocol Structure
-- Proves that line protocol messages are JSON objects with a "type" string field
data LineProtocolStructure : JSON → Set where
  line-structure : ∀ (obj : List (String × JSON)) (msgType : String) →
    lookupByKey "type" obj ≡ just (JString msgType) →
    LineProtocolStructure (JObject obj)

-- Soundness: parseRequest only succeeds on well-formed line protocol messages
open import Aletheia.Protocol.Routing using (parseRequest)
open import Aletheia.Data.Message using (Request)

parseRequest-sound : ∀ (input : JSON) (result : Request)
  → parseRequest input ≡ just result
  → ∃[ obj ] ∃[ msgType ] (input ≡ JObject obj × lookupByKey "type" obj ≡ just (JString msgType))
parseRequest-sound (JObject obj) result eq with lookupByKey "type" obj | inspect (lookupByKey "type") obj
parseRequest-sound (JObject obj) result eq | just (JString msgType) | [ eq' ] = obj , msgType , refl , eq'
-- All other cases: lookupString returns nothing → parseRequest returns nothing → absurd
parseRequest-sound (JObject obj) result () | just (JBool _) | _  -- getString (JBool _) = nothing
parseRequest-sound (JObject obj) result () | just (JNumber _) | _  -- getString (JNumber _) = nothing
parseRequest-sound (JObject obj) result () | just (JArray _) | _  -- getString (JArray _) = nothing
parseRequest-sound (JObject obj) result () | just (JObject _) | _  -- getString (JObject _) = nothing
parseRequest-sound (JObject obj) result () | just JNull | _  -- getString JNull = nothing
parseRequest-sound (JObject obj) result () | nothing | _  -- lookupString nothing → parseRequest nothing
parseRequest-sound JNull result ()
parseRequest-sound (JBool _) result ()
parseRequest-sound (JNumber _) result ()
parseRequest-sound (JString _) result ()
parseRequest-sound (JArray _) result ()

-- ============================================================================
-- PROVEN PROPERTIES
-- ============================================================================
--
-- PARSER CORRECTNESS:
--   - parseJSON-deterministic: Parser produces unique results for same input
--   - parseRequest-sound: Line protocol parser accepts only well-formed objects
--   - parseDBC-sound: DBC parser accepts only well-formed objects
--
-- STRUCTURAL HELPERS:
--   - lookupByKey-{empty,here,there}: Object field lookup properties
--   - array-length-empty: Empty array has length 0
--   - formatJSON-empty-{array,object}: Base cases for empty structures
--
-- All proofs use structural induction and congruence. No postulates.
-- Character/integer decomposition kept at I/O boundaries only.
-- ============================================================================

-- All JSON parsers are deterministic (follows from parser combinators)
parseJSON-deterministic : ∀ (pos : Position) (input : List Char) (r₁ r₂ : ParseResult JSON)
                        → parseJSON pos input ≡ just r₁
                        → parseJSON pos input ≡ just r₂
                        → r₁ ≡ r₂
parseJSON-deterministic = parser-deterministic parseJSON
