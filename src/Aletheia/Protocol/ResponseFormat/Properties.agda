-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Correctness properties for response formatting.
--
-- Purpose: Prove format-response injectivity (Ack uniqueness).
-- Risk mitigated: Ack formatted as Violation or vice versa would cause
-- language bindings to misinterpret the result.
module Aletheia.Protocol.ResponseFormat.Properties where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Aletheia.Protocol.Message using (Success; Error;
  ExtractionResultsResponse; PropertyResponse; Ack; Complete; ValidationResponse; DBCResponse;
  ParsedDBCResponse; DBCTextResponse)
open import Aletheia.Protocol.Response using ()
open import Aletheia.Protocol.ResponseFormat using (formatResponse)

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
formatResponse-ack-unique (ExtractionResultsResponse _ _ _) ()
-- PropertyResponse carries `List PropertyResult`.
-- The wire emit is `{"type": "property_batch", "results": [...]}` —
-- always a 2-field JObject regardless of list length, so the inhabitant
-- can never collapse to Ack's 1-field shape.  The single `_` covers the
-- empty / singleton / batch cases uniformly.
formatResponse-ack-unique (PropertyResponse _) ()
formatResponse-ack-unique Ack _ = refl
formatResponse-ack-unique (Complete _ _) ()
formatResponse-ack-unique (DBCResponse _) ()
formatResponse-ack-unique (ValidationResponse _) ()
formatResponse-ack-unique (ParsedDBCResponse _ _) ()
formatResponse-ack-unique (DBCTextResponse _) ()
