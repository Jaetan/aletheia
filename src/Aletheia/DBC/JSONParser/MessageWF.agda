{-# OPTIONS --safe --without-K #-}

-- Message-level well-formedness proofs for the DBC JSON parser.
--
-- Purpose: Prove that if parseMessage/parseMessageList succeeds, the result
-- satisfies WellFormedMessage (dlc ≤ 8, WellFormedCANId, all signals WF).
-- Key insight: The parser enforces bounds via _%_ and _<ᵇ_/_≤ᵇ_ guards.
-- Role: Used by Properties for the top-level parse-wellformed theorem.
module Aletheia.DBC.JSONParser.MessageWF where

open import Data.Nat using (ℕ; _+_; _<_; _≤_; s≤s)
open import Data.Nat.DivMod using (m%n<n)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.String using (String)
open import Data.Product using (_×_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Aletheia.Protocol.JSON using (JSON; JNull; JBool; JNumber; JString; JArray; JObject;
  lookupString; lookupBool; lookupNat; lookupArray)
open import Aletheia.CAN.Frame using (CANId; Standard; Extended)
open import Aletheia.DBC.Types using (DBCMessage)
open import Aletheia.DBC.JSONParser using (parseCANId; parseMessageId; parseMessageBody;
  parseMessageFields; parseMessage; parseMessageList; parseSignalList)
open import Aletheia.DBC.Formatter.WellFormed using (WellFormedSignal; WellFormedCANId;
  WellFormedMessage; wf-standard; wf-extended)
open import Aletheia.DBC.JSONParser.SignalWF using (parseSignalList-wf)
open import Aletheia.Prelude using (standard-can-id-max; extended-can-id-max)

-- ============================================================================
-- HELPERS
-- ============================================================================

private
  -- m < suc n implies m ≤ n (destructor of s≤s)
  <suc⇒≤ : ∀ {m n} → m < (ℕ.suc n) → m ≤ n
  <suc⇒≤ (s≤s p) = p

-- ============================================================================
-- CAN ID WELL-FORMEDNESS
-- ============================================================================

-- If parseCANId succeeds, the result is well-formed.
-- Strategy: with on lookupBool "extended", then with on rawId <ᵇ max.
-- In each success case, the ID uses _%_ modulo and m%n<n provides the bound.
parseCANId-wf : ∀ ctx rawId obj canId
  → parseCANId ctx rawId obj ≡ inj₂ canId → WellFormedCANId canId
parseCANId-wf ctx rawId obj canId eq
  with lookupBool "extended" obj
... | just true
  with Data.Nat._<ᵇ_ rawId extended-can-id-max | eq
...   | true  | refl = wf-extended (m%n<n rawId extended-can-id-max)
...   | false | ()
-- Note: just false / nothing cases are identical but can't be merged with _
-- because Agda needs the concrete constructor to reduce parseCANId.
parseCANId-wf ctx rawId obj canId eq
  | just false
  with Data.Nat._<ᵇ_ rawId standard-can-id-max | eq
...   | true  | refl = wf-standard (m%n<n rawId standard-can-id-max)
...   | false | ()
parseCANId-wf ctx rawId obj canId eq
  | nothing
  with Data.Nat._<ᵇ_ rawId standard-can-id-max | eq
...   | true  | refl = wf-standard (m%n<n rawId standard-can-id-max)
...   | false | ()

-- ============================================================================
-- MESSAGE ID WELL-FORMEDNESS
-- ============================================================================

-- If parseMessageId succeeds, the result is well-formed.
parseMessageId-wf : ∀ ctx obj canId
  → parseMessageId ctx obj ≡ inj₂ canId → WellFormedCANId canId
parseMessageId-wf ctx obj canId eq
  with lookupNat "id" obj | eq
... | nothing | ()
... | just rawId | eq' = parseCANId-wf ctx rawId obj canId eq'

-- ============================================================================
-- MESSAGE BODY WELL-FORMEDNESS
-- ============================================================================

-- If parseMessageBody succeeds with a well-formed CAN ID, the result is well-formed.
parseMessageBody-wf : ∀ ctx name canId obj msg
  → WellFormedCANId canId
  → parseMessageBody ctx name canId obj ≡ inj₂ msg
  → WellFormedMessage msg
parseMessageBody-wf ctx name canId obj msg id-wf eq
  with lookupNat "dlc" obj | eq
... | nothing | ()
... | just rawDlc | eq₁
  with lookupString "sender" obj | eq₁
...   | nothing | ()
...   | just sender | eq₂
    with lookupArray "signals" obj | eq₂
...     | nothing | ()
...     | just signalsJSON | eq₃
      with parseSignalList ctx signalsJSON 0 in sig-eq | eq₃
...       | inj₁ _ | ()
...       | inj₂ signals | eq₄
        with Data.Nat._≤ᵇ_ rawDlc 8 | eq₄
...         | true  | refl = record
              { dlc-bound  = <suc⇒≤ (m%n<n rawDlc 9)
              ; id-wf      = id-wf
              ; signals-wf = parseSignalList-wf ctx signalsJSON 0 signals sig-eq
              }
...         | false | ()

-- ============================================================================
-- MESSAGE FIELDS WELL-FORMEDNESS
-- ============================================================================

-- If parseMessageFields succeeds, the result is well-formed.
-- Intermediate lemma: composes parseMessageId-wf and parseMessageBody-wf.
parseMessageFields-wf : ∀ ctx name obj msg
  → parseMessageFields ctx name obj ≡ inj₂ msg → WellFormedMessage msg
parseMessageFields-wf ctx name obj msg eq
  with parseMessageId ctx obj in id-eq | eq
... | inj₁ _ | ()
... | inj₂ canId | eq' =
    parseMessageBody-wf ctx name canId obj msg
      (parseMessageId-wf ctx obj canId id-eq) eq'

-- ============================================================================
-- MESSAGE WELL-FORMEDNESS
-- ============================================================================

-- If parseMessage succeeds, the result is well-formed.
parseMessage-wf : ∀ obj msg
  → parseMessage obj ≡ inj₂ msg → WellFormedMessage msg
parseMessage-wf obj msg eq
  with lookupString "name" obj | eq
... | nothing | ()
... | just name | eq' = parseMessageFields-wf _ name obj msg eq'

-- ============================================================================
-- MESSAGE LIST WELL-FORMEDNESS
-- ============================================================================

-- If parseMessageList succeeds, all messages are well-formed.
parseMessageList-wf : ∀ jsons idx msgs
  → parseMessageList jsons idx ≡ inj₂ msgs → All WellFormedMessage msgs
parseMessageList-wf [] idx .[] refl = []
parseMessageList-wf (JObject msgObj ∷ rest) idx msgs eq
  with parseMessage msgObj in msg-eq | eq
... | inj₁ _ | ()
... | inj₂ msg | eq₁
  with parseMessageList rest (idx + 1) in rest-eq | eq₁
...   | inj₁ _ | ()
...   | inj₂ msgs' | refl = parseMessage-wf msgObj msg msg-eq ∷
                              parseMessageList-wf rest (idx + 1) msgs' rest-eq
parseMessageList-wf (JNull     ∷ _) idx msgs ()
parseMessageList-wf (JBool _   ∷ _) idx msgs ()
parseMessageList-wf (JNumber _ ∷ _) idx msgs ()
parseMessageList-wf (JString _ ∷ _) idx msgs ()
parseMessageList-wf (JArray _  ∷ _) idx msgs ()
