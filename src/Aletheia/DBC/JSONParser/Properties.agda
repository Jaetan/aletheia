{-# OPTIONS --safe --without-K #-}

-- Correctness properties for the DBC JSON parser.
--
-- Purpose: Prove parse-wellformed (if parsing succeeds, result is full-WF)
-- and the unconditional weak inverse (parse ∘ format ∘ parse = parse).
-- Properties:
--   parse-wellformed   : parseDBCWithErrors j ≡ inj₂ d → WellFormedDBCRT d
--   parse-format-parse : parseDBCWithErrors j ≡ inj₂ d
--                      → parseDBCWithErrors (formatDBC d) ≡ parseDBCWithErrors j
-- Role: Completes the weak inverse pair together with Formatter.Properties.
-- The parser-strengthening gap that previously gated the unconditional version
-- (system review §12.1) was closed by adding `physicalGate` to parseSignalFields
-- so the parser refuses signals violating the BigEndian PhysicallyValid bounds.
module Aletheia.DBC.JSONParser.Properties where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Aletheia.JSON using (JSON; JNull; JBool; JNumber; JString; JArray; JObject;
  lookupChars; lookupArray)
open import Aletheia.DBC.Types using (DBC)
open import Aletheia.DBC.JSONParser using (parseDBCWithErrors; parseMessageList;
  parseOptionalArray; parseSignalGroupList; parseEnvironmentVarList; parseValueTableList;
  parseNodeList; parseCommentList; parseAttributeList; parseRawValueDescList)
open import Aletheia.DBC.Formatter using (formatDBC)
open import Aletheia.DBC.Formatter.Properties using (WellFormedDBC; WellFormedDBCRT;
  format-parse-roundtrip)
open import Aletheia.DBC.JSONParser.MessageWF using (parseMessageList-pv)

-- ============================================================================
-- PARSE WELL-FORMEDNESS
-- ============================================================================

-- If parsing succeeds, the result is fully well-formed (WellFormedDBCRT).
-- This is the strengthened version: it carries `PhysicallyValid` for every
-- signal because parseSignalFields' physicalGate refuses BigEndian signals
-- that don't satisfy the three bounds (1 ≤ bitLength, fits-in-frame, msb-ge-len).
-- Strategy: case-split on JSON (only JObject succeeds), then invert the
-- 6-step bind chain (version, messages, groups, envvars, vtables, construction).
parse-wellformed : ∀ j d
  → parseDBCWithErrors j ≡ inj₂ d → WellFormedDBCRT d
parse-wellformed (JObject obj) d eq
  with lookupChars "version" obj | eq
... | nothing | ()
... | just version | eq₁
  with lookupArray "messages" obj | eq₁
...   | nothing | ()
...   | just msgsJSON | eq₂
    with parseMessageList msgsJSON 0 in msgs-eq | eq₂
...     | inj₁ _ | ()
...     | inj₂ msgs | eq₃
      with parseOptionalArray parseSignalGroupList (lookupArray "signalGroups" obj) | eq₃
...       | inj₁ _ | ()
...       | inj₂ groups | eq₄
        with parseOptionalArray parseEnvironmentVarList (lookupArray "environmentVars" obj) | eq₄
...         | inj₁ _ | ()
...         | inj₂ envvars | eq₅
          with parseOptionalArray parseValueTableList (lookupArray "valueTables" obj) | eq₅
...           | inj₁ _ | ()
...           | inj₂ vtables | eq₆
            with parseOptionalArray parseNodeList (lookupArray "nodes" obj) | eq₆
...             | inj₁ _ | ()
...             | inj₂ nodes | eq₇
              with parseOptionalArray parseCommentList (lookupArray "comments" obj) | eq₇
...               | inj₁ _ | ()
...               | inj₂ comments | eq₈
                with parseOptionalArray parseAttributeList (lookupArray "attributes" obj) | eq₈
...                 | inj₁ _ | ()
...                 | inj₂ attributes | eq₉
                  with parseOptionalArray parseRawValueDescList
                                          (lookupArray "unresolvedValueDescs" obj) | eq₉
...                   | inj₁ _ | ()
...                   | inj₂ _ | refl =
                        record { messages-wf = parseMessageList-pv msgsJSON 0 msgs msgs-eq }
parse-wellformed JNull d ()
parse-wellformed (JBool _) d ()
parse-wellformed (JNumber _) d ()
parse-wellformed (JString _) d ()
parse-wellformed (JArray _) d ()

-- ============================================================================
-- WEAK INVERSE: parse ∘ format ∘ parse = parse
-- ============================================================================

-- Now unconditional: the parser produces WellFormedDBCRT directly (via
-- physicalGate in parseSignalFields), so the format-parse-roundtrip applies
-- without a caller-supplied PhysicallyValid witness. This closes deferred
-- system review item §12.1.
parse-format-parse : ∀ j d
  → parseDBCWithErrors j ≡ inj₂ d
  → parseDBCWithErrors (formatDBC d) ≡ parseDBCWithErrors j
parse-format-parse j d eq =
  trans (format-parse-roundtrip d (parse-wellformed j d eq)) (sym eq)

-- The core format-parse-roundtrip (in Formatter.Properties) IS fully proven
-- under WellFormedDBCRT, which includes the PhysicallyValid constraints.
-- Other corollaries proven there:
--   format-parse-format         : formatDBC is a fixed point of the round trip
--   formatDBC-injective         : formatter does not lose information from WF DBCs
--   parseDBC-complete-on-format : parser succeeds on every formatDBC image
