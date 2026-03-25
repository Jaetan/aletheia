{-# OPTIONS --safe --without-K #-}

-- Correctness properties for the DBC JSON parser.
--
-- Purpose: Prove parse-wellformed (if parsing succeeds, result is well-formed)
-- and the weak inverse corollary (parse ∘ format ∘ parse = parse).
-- Properties:
--   parse-wellformed   : parseDBCWithErrors j ≡ inj₂ d → WellFormedDBC d
--   parse-format-parse : (deferred) requires proving PhysicallyValid for parsed signals
-- Role: Completes the weak inverse pair together with Formatter.Properties.
module Aletheia.DBC.JSONParser.Properties where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Aletheia.Protocol.JSON using (JSON; JNull; JBool; JNumber; JString; JArray; JObject;
  lookupString; lookupArray)
open import Aletheia.DBC.Types using (DBC)
open import Aletheia.DBC.JSONParser using (parseDBCWithErrors; parseMessageList)
open import Aletheia.DBC.Formatter using (formatDBC)
open import Aletheia.DBC.Formatter.Properties using (WellFormedDBC; WellFormedDBCRT;
  format-parse-roundtrip)
open import Aletheia.DBC.JSONParser.MessageWF using (parseMessageList-wf)

-- ============================================================================
-- PARSE WELL-FORMEDNESS
-- ============================================================================

-- If parsing succeeds, the result is well-formed.
-- Strategy: case-split on JSON (only JObject succeeds), then invert the
-- 3-step bind chain (version, messages, construction).
parse-wellformed : ∀ j d
  → parseDBCWithErrors j ≡ inj₂ d → WellFormedDBC d
parse-wellformed (JObject obj) d eq
  with lookupString "version" obj | eq
... | nothing | ()
... | just version | eq₁
  with lookupArray "messages" obj | eq₁
...   | nothing | ()
...   | just msgsJSON | eq₂
    with parseMessageList msgsJSON 0 in msgs-eq | eq₂
...     | inj₁ _ | ()
...     | inj₂ msgs | refl =
          record { messages-wf = parseMessageList-wf msgsJSON 0 msgs msgs-eq }
parse-wellformed JNull d ()
parse-wellformed (JBool _) d ()
parse-wellformed (JNumber _) d ()
parse-wellformed (JString _) d ()
parse-wellformed (JArray _) d ()

-- ============================================================================
-- WEAK INVERSE: parse ∘ format ∘ parse = parse
-- ============================================================================

-- NOTE: The parse-format-parse corollary (if parsing succeeds, formatting and
-- re-parsing recovers the original) is currently deferred. It requires proving
-- that parsed signals satisfy PhysicallyValid (1 ≤ bitLength, signal fits in
-- frame, Motorola MSB constraint). The parser does not enforce these invariants
-- (e.g., bitLength=0 parses successfully), so this theorem cannot hold in full
-- generality without strengthening the parser or adding preconditions.
--
-- The core format-parse-roundtrip (in Formatter.Properties) IS fully proven
-- under WellFormedDBCRT, which includes the PhysicallyValid constraints.
