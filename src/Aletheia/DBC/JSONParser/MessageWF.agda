{-# OPTIONS --safe --without-K #-}

-- Message-level well-formedness proofs for the DBC JSON parser.
--
-- Purpose: Prove that if parseMessage/parseMessageList succeeds, the result
-- satisfies WellFormedMessage (dlc ≤ 64, all signals WF).
-- Key insight: The parser enforces bounds via _<ᵇ_/_≤ᵇ_ guards.
-- CAN ID bounds are now intrinsic in the CANId type (T (n <ᵇ max)).
-- Role: Used by Properties for the top-level parse-wellformed theorem.
module Aletheia.DBC.JSONParser.MessageWF where

open import Data.Nat using (ℕ; _+_; _<_; _≤_; s≤s; _≤ᵇ_)
open import Data.Nat.DivMod using (m%n<n)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.String using (String)
open import Data.Product using (_×_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false; T)
open import Data.Unit using (tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Data.Nat.Properties using (≤ᵇ⇒≤)

open import Aletheia.Protocol.JSON using (JSON; JNull; JBool; JNumber; JString; JArray; JObject;
  lookupString; lookupNat; lookupArray)
open import Aletheia.CAN.Frame using (CANId)
open import Aletheia.DBC.Types using (DBCMessage)
open import Aletheia.DBC.JSONParser using (parseMessageId; parseMessageBody;
  parseMessageFields; parseMessage; parseMessageList; parseSignalList)
open import Aletheia.DBC.Formatter.WellFormed using (WellFormedSignal;
  WellFormedMessage)
open import Aletheia.DBC.JSONParser.SignalWF using (parseSignalList-wf)

-- ============================================================================
-- HELPERS
-- ============================================================================

private
  -- m < suc n implies m ≤ n (destructor of s≤s)
  <suc⇒≤ : ∀ {m n} → m < (ℕ.suc n) → m ≤ n
  <suc⇒≤ (s≤s p) = p

-- ============================================================================
-- MESSAGE BODY WELL-FORMEDNESS
-- ============================================================================

-- If parseMessageBody succeeds, the result is well-formed.
-- CAN ID bounds are intrinsic in the CANId type, so no id-wf parameter needed.
parseMessageBody-wf : ∀ ctx name canId obj msg
  → parseMessageBody ctx name canId obj ≡ inj₂ msg
  → WellFormedMessage msg
parseMessageBody-wf ctx name canId obj msg eq
  with lookupNat "dlc" obj | eq
... | nothing | ()
... | just rawDlc | eq₁
  with lookupString "sender" obj | eq₁
...   | nothing | ()
...   | just sender | eq₂
    with lookupArray "signals" obj | eq₂
...     | nothing | ()
...     | just signalsJSON | eq₃
      with parseSignalList rawDlc ctx signalsJSON 0 in sig-eq | eq₃
...       | inj₁ _ | ()
...       | inj₂ signals | eq₄
        with rawDlc ≤ᵇ 64 in leq-eq | eq₄
...         | true  | refl = record
              { dlc-bound  = <suc⇒≤ (m%n<n rawDlc 65)
              ; signals-wf = parseSignalList-wf rawDlc ctx signalsJSON 0 signals
                               (≤ᵇ⇒≤ rawDlc 64 (subst T (sym leq-eq) tt)) sig-eq
              }
...         | false | ()

-- ============================================================================
-- MESSAGE FIELDS WELL-FORMEDNESS
-- ============================================================================

-- If parseMessageFields succeeds, the result is well-formed.
-- Intermediate lemma: composes parseMessageId and parseMessageBody-wf.
parseMessageFields-wf : ∀ ctx name obj msg
  → parseMessageFields ctx name obj ≡ inj₂ msg → WellFormedMessage msg
parseMessageFields-wf ctx name obj msg eq
  with parseMessageId ctx obj in id-eq | eq
... | inj₁ _ | ()
... | inj₂ canId | eq' =
    parseMessageBody-wf ctx name canId obj msg eq'

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
