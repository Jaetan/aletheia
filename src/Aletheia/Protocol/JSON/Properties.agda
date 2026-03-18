{-# OPTIONS --safe --without-K #-}

-- Correctness properties for JSON parser and formatter (Phase 3).
--
-- Purpose: Prove soundness of JSON parsing/formatting for Aletheia's protocol schemas.
-- Properties: Parser determinism, structural preservation, schema soundness (DBC, line protocol).
-- Approach: Congruence lemmas, structural induction, no character/integer decomposition.
module Aletheia.Protocol.JSON.Properties where

open import Aletheia.Protocol.JSON using (JSON; JNull; JBool; JNumber; JString; JArray; JObject; formatJSON; parseJSON; lookupString; lookupRational; lookupObject)
open import Aletheia.Parser.Combinators using (Parser; ParseResult; Position)
open import Aletheia.Parser.Properties using (parser-deterministic)
open import Data.Bool using (true)
open import Data.Char using (Char)
open import Data.String using (String; _≟_)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Rational using (ℚ)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; _≢_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

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
open import Data.Empty using (⊥-elim)

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

-- ============================================================================
-- INSPECT IDIOM FOR WITH-ABSTRACTION PROOFS
-- ============================================================================
--
-- The inspect idiom solves a critical problem in Agda proofs:
--
-- Problem: In with-abstractions, we lose track of which expression produced
--          which result. For example:
--
--   proof x with someFunction x
--   ... | result = ?
--
--   We know someFunction returned 'result', but we can't reference
--   the equality (someFunction x ≡ result) in the proof term.
--
-- Solution: The inspect idiom captures this equality:
--
--   proof x with someFunction x | inspect someFunction x
--   ... | result | [ eq ] = ...
--
--   Now 'eq' has type: someFunction x ≡ result
--
-- Usage in this module:
--   parseDBC-sound and parseRequest-sound use inspect to capture
--   lookupByKey equalities for the soundness proof witness.
--
-- This is the most advanced proof technique in the Aletheia codebase.
-- ============================================================================

open Relation.Binary.PropositionalEquality using (inspect; [_])

-- DBC File Structure
-- Proves that DBC files have expected structure (object with version and messages)
data DBCFileStructure : JSON → Set where
  dbc-structure : ∀ (obj : List (String × JSON)) (version : String) (messages : List JSON) →
    lookupByKey "version" obj ≡ just (JString version) →
    lookupByKey "messages" obj ≡ just (JArray messages) →
    DBCFileStructure (JObject obj)

-- Soundness: parseDBCWithErrors only succeeds on well-formed DBC JSON objects
open import Aletheia.DBC.JSONParser using (parseDBCWithErrors)
open import Aletheia.DBC.Types using (DBC)
open import Data.Sum using (_⊎_; inj₁; inj₂)

parseDBC-sound : ∀ (input : JSON) (result : DBC)
  → parseDBCWithErrors input ≡ inj₂ result
  → ∃[ obj ] ∃[ version ] ∃[ messages ]
      (input ≡ JObject obj
       × lookupByKey "version" obj ≡ just (JString version)
       × lookupByKey "messages" obj ≡ just (JArray messages))
parseDBC-sound (JObject obj) result eq with lookupByKey "version" obj | inspect (lookupByKey "version") obj
parseDBC-sound (JObject obj) result eq | just (JString version) | [ eqVer ]
  with lookupByKey "messages" obj | inspect (lookupByKey "messages") obj
parseDBC-sound (JObject obj) result eq | just (JString version) | [ eqVer ]
  | just (JArray messages) | [ eqMsgs ] = obj , version , messages , refl , eqVer , eqMsgs
-- Absurdity cases: messages field has wrong type (6 cases)
-- All are impossible because parser rejects non-array "messages" fields
parseDBC-sound (JObject obj) result () | just (JString version) | [ eqVer ] | just (JBool _) | _
parseDBC-sound (JObject obj) result () | just (JString version) | [ eqVer ] | just (JNumber _) | _
parseDBC-sound (JObject obj) result () | just (JString version) | [ eqVer ] | just (JString _) | _
parseDBC-sound (JObject obj) result () | just (JString version) | [ eqVer ] | just (JObject _) | _
parseDBC-sound (JObject obj) result () | just (JString version) | [ eqVer ] | just JNull | _
parseDBC-sound (JObject obj) result () | just (JString version) | [ eqVer ] | nothing | _
-- Absurdity cases: version field has wrong type (6 cases)
-- All are impossible because parser rejects non-string "version" fields
parseDBC-sound (JObject obj) result () | just (JBool _) | _  -- version not a string
parseDBC-sound (JObject obj) result () | just (JNumber _) | _
parseDBC-sound (JObject obj) result () | just (JArray _) | _
parseDBC-sound (JObject obj) result () | just (JObject _) | _
parseDBC-sound (JObject obj) result () | just JNull | _
parseDBC-sound (JObject obj) result () | nothing | _  -- no version field
-- Absurdity cases: input is not an object (5 cases)
-- parseDBCWithErrors requires JObject input; all other JSON types rejected at entry
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
-- Absurdity cases: type field has wrong type (6 cases)
-- All are impossible because lookupString rejects non-string values
parseRequest-sound (JObject obj) result () | just (JBool _) | _  -- getString (JBool _) = nothing
parseRequest-sound (JObject obj) result () | just (JNumber _) | _  -- getString (JNumber _) = nothing
parseRequest-sound (JObject obj) result () | just (JArray _) | _  -- getString (JArray _) = nothing
parseRequest-sound (JObject obj) result () | just (JObject _) | _  -- getString (JObject _) = nothing
parseRequest-sound (JObject obj) result () | just JNull | _  -- getString JNull = nothing
parseRequest-sound (JObject obj) result () | nothing | _  -- lookupString nothing → parseRequest nothing
-- Absurdity cases: input is not an object (5 cases)
-- parseRequest requires JObject input; all other JSON types rejected at entry
parseRequest-sound JNull result ()
parseRequest-sound (JBool _) result ()
parseRequest-sound (JNumber _) result ()
parseRequest-sound (JString _) result ()
parseRequest-sound (JArray _) result ()

-- ============================================================================
-- TYPED LOOKUP LEMMAS (for roundtrip proofs)
-- ============================================================================

-- String decidable equality is reflexive (needed for dispatchOperator if-then-else)
≟-refl : (s : String) → (⌊ s ≟ s ⌋) ≡ true
≟-refl s with s ≟ s
... | yes _ = refl
... | no s≢s = ⊥-elim (s≢s refl)

-- Typed lookup at head position: lookupString
lookupString-here : (k : String) (s : String) (rest : List (String × JSON))
  → lookupString k ((k , JString s) ∷ rest) ≡ just s
lookupString-here k s rest
  with lookupByKey k ((k , JString s) ∷ rest) | lookupByKey-here k (JString s) rest
... | .(just (JString s)) | refl = refl

-- Typed lookup at head position: lookupRational
lookupRational-here : (k : String) (r : ℚ) (rest : List (String × JSON))
  → lookupRational k ((k , JNumber r) ∷ rest) ≡ just r
lookupRational-here k r rest
  with lookupByKey k ((k , JNumber r) ∷ rest) | lookupByKey-here k (JNumber r) rest
... | .(just (JNumber r)) | refl = refl

-- Typed lookup at head position: lookupObject
lookupObject-here : (k : String) (fs : List (String × JSON)) (rest : List (String × JSON))
  → lookupObject k ((k , JObject fs) ∷ rest) ≡ just fs
lookupObject-here k fs rest
  with lookupByKey k ((k , JObject fs) ∷ rest) | lookupByKey-here k (JObject fs) rest
... | .(just (JObject fs)) | refl = refl

-- All JSON parsers are deterministic (follows from parser combinators)
parseJSON-deterministic : ∀ (pos : Position) (input : List Char) (r₁ r₂ : ParseResult JSON)
                        → parseJSON pos input ≡ just r₁
                        → parseJSON pos input ≡ just r₂
                        → r₁ ≡ r₂
parseJSON-deterministic = parser-deterministic parseJSON
