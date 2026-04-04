{-# OPTIONS --safe --without-K #-}

-- Correctness properties for response formatting.
--
-- Purpose: Prove each Response constructor maps to the expected JSON structure.
-- These are definitional equalities (refl) — the proof IS the code.
-- If someone accidentally swaps two pattern-match cases, the refl fails.
--
-- Risk mitigated: Ack formatted as Violation or vice versa would cause
-- language bindings to misinterpret the result.
module Aletheia.Protocol.ResponseFormat.Properties where

open import Data.String using (String)
open import Data.List using (List; []; _∷_; map)
open import Data.Rational using (ℚ)
open import Data.Vec using (Vec)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Aletheia.Protocol.JSON using (JSON; JObject; JArray; JString; JNumber; JBool; ℕtoℚ)
open import Aletheia.Protocol.Message using (Response; Success; Error; ByteArray;
  ExtractionResultsResponse; PropertyResponse; Ack; Complete; ValidationResponse; DBCResponse)
open import Aletheia.Protocol.Response using (PropertyResult; CounterexampleData)
open import Aletheia.Protocol.ResponseFormat using (formatResponse; formatPropertyResult; bytesToJSON)
open import Aletheia.CAN.Frame using (Byte)
open import Aletheia.DBC.Types using (ValidationIssue)

-- ============================================================================
-- RESPONSE CONSTRUCTOR CORRECTNESS
-- ============================================================================

-- Each proof establishes the exact JSON output for a Response constructor.

formatResponse-ack : formatResponse Ack
  ≡ JObject (("status" , JString "ack") ∷ [])
formatResponse-ack = refl

formatResponse-success : ∀ msg → formatResponse (Success msg)
  ≡ JObject (("status" , JString "success") ∷ ("message" , JString msg) ∷ [])
formatResponse-success _ = refl

formatResponse-error : ∀ reason → formatResponse (Error reason)
  ≡ JObject (("status" , JString "error") ∷ ("message" , JString reason) ∷ [])
formatResponse-error _ = refl

formatResponse-bytearray : ∀ {n} (bytes : Vec Byte n) → formatResponse (ByteArray bytes)
  ≡ JObject (("status" , JString "success") ∷ ("data" , bytesToJSON bytes) ∷ [])
formatResponse-bytearray _ = refl

formatResponse-dbc : ∀ j → formatResponse (DBCResponse j)
  ≡ JObject (("status" , JString "success") ∷ ("dbc" , j) ∷ [])
formatResponse-dbc _ = refl

-- ============================================================================
-- PROPERTY RESULT CORRECTNESS
-- ============================================================================

formatPropertyResult-violation : ∀ idx ce → formatPropertyResult (PropertyResult.Violation idx ce)
  ≡ JObject (
      ("type" , JString "property") ∷
      ("status" , JString "fails") ∷
      ("property_index" , JNumber (ℕtoℚ idx)) ∷
      ("timestamp" , JNumber (ℕtoℚ (CounterexampleData.timestamp ce))) ∷
      ("reason" , JString (CounterexampleData.reason ce)) ∷
      [])
formatPropertyResult-violation _ _ = refl

formatPropertyResult-satisfaction : ∀ idx → formatPropertyResult (PropertyResult.Satisfaction idx)
  ≡ JObject (
      ("type" , JString "property") ∷
      ("status" , JString "holds") ∷
      ("property_index" , JNumber (ℕtoℚ idx)) ∷
      [])
formatPropertyResult-satisfaction _ = refl

formatPropertyResult-complete : formatPropertyResult PropertyResult.StreamComplete
  ≡ JObject (
      ("type" , JString "complete") ∷
      ("status" , JString "stream_ended") ∷
      [])
formatPropertyResult-complete = refl

-- ============================================================================
-- FORMAT-RESPONSE INJECTIVITY (Ack uniqueness)
-- ============================================================================

-- Ack is the only Response constructor mapping to the Ack JSON.
-- Each non-Ack case produces a JObject with ≥ 2 fields, while Ack has exactly 1.
-- Agda refutes the equality by list-length mismatch (x ∷ y ∷ ... ≢ z ∷ []).
-- This is the key lemma enabling end-to-end Ack soundness at the JSON level:
-- if the formatted response equals the Ack JSON, the response IS Ack.
formatResponse-ack-unique : ∀ r → formatResponse r ≡ formatResponse Ack → r ≡ Ack
formatResponse-ack-unique (Success _) ()
formatResponse-ack-unique (Error _) ()
formatResponse-ack-unique (ByteArray _) ()
formatResponse-ack-unique (ExtractionResultsResponse _ _ _) ()
formatResponse-ack-unique (PropertyResponse (PropertyResult.Violation _ _)) ()
formatResponse-ack-unique (PropertyResponse (PropertyResult.Satisfaction _)) ()
formatResponse-ack-unique (PropertyResponse PropertyResult.StreamComplete) ()
formatResponse-ack-unique Ack _ = refl
formatResponse-ack-unique (Complete _) ()
formatResponse-ack-unique (DBCResponse _) ()
formatResponse-ack-unique (ValidationResponse _) ()
