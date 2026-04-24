{-# OPTIONS --safe --without-K #-}

-- Message-level well-formedness proofs for the DBC JSON parser.
--
-- Purpose: Prove that if parseMessage/parseMessageList succeeds, the result
-- satisfies WellFormedMessage (dlc ≤ 64, all signals WF).
-- Key insight: The parser enforces bounds via bytesToValidDLC (validated DLC).
-- CAN ID bounds are now intrinsic in the CANId type (T (n <ᵇ max)).
-- Role: Used by Properties for the top-level parse-wellformed theorem.
module Aletheia.DBC.JSONParser.MessageWF where

open import Data.Nat using (ℕ; suc; z≤n; _+_; _<_; _≤_; _≡ᵇ_)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.String using (String)
open import Data.Product using (_×_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false; T)
open import Data.Unit using (tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Data.Nat.Properties using (≡ᵇ⇒≡; m≤m+n; ≤-refl)

open import Aletheia.JSON using (JSON; JNull; JBool; JNumber; JString; JArray; JObject;
  lookupString; lookupNat; lookupArray)
open import Aletheia.CAN.Frame using (CANId)
open import Aletheia.CAN.DLC using (DLC; mkDLC; bytesToValidDLC; dlcBytes)
open import Aletheia.CAN.DLC.Properties using (bvd-bytes)
open import Aletheia.DBC.Types using (DBCMessage)
open import Aletheia.DBC.JSONParser using (parseMessageId; parseMessageBody;
  parseMessageFields; parseMessage; parseMessageList; parseSignalList;
  parseOptionalArray; parseStringList; validateIdent; validateIdentList)
open import Aletheia.DBC.Formatter.WellFormed using (WellFormedSignal;
  WellFormedMessage; WellFormedMessageRT; PhysicallyValid)
open import Aletheia.DBC.JSONParser.SignalWF using (parseSignalList-wf; parseSignalList-pv)

-- ============================================================================
-- HELPERS
-- ============================================================================

private
  -- Convert ≡ᵇ-true to ≤ 64 bound: if m ≡ᵇ k = true then m ≤ 64 (given k ≤ 64)
  ≡ᵇ-true→≤64 : ∀ m k → (m ≡ᵇ k) ≡ true → k ≤ 64 → m ≤ 64
  ≡ᵇ-true→≤64 m k eq bound = subst (_≤ 64) (sym (≡ᵇ⇒≡ m k (subst T (sym eq) tt))) bound

  -- dlcBytes of any DLC value is ≤ 64.
  -- Mirrors dlcToBytes-bounded from DLC/Properties.agda but operates on the
  -- DLC newtype (whose @0 erased bound cannot be extracted to delegate).
  -- Exhaustive match on the 16 valid DLC codes; ≥16 is absurd by erased bound.
  dlcBytes-bounded : ∀ (d : DLC) → dlcBytes d ≤ 64
  dlcBytes-bounded (mkDLC 0  _) = z≤n
  dlcBytes-bounded (mkDLC 1  _) = m≤m+n 1 63
  dlcBytes-bounded (mkDLC 2  _) = m≤m+n 2 62
  dlcBytes-bounded (mkDLC 3  _) = m≤m+n 3 61
  dlcBytes-bounded (mkDLC 4  _) = m≤m+n 4 60
  dlcBytes-bounded (mkDLC 5  _) = m≤m+n 5 59
  dlcBytes-bounded (mkDLC 6  _) = m≤m+n 6 58
  dlcBytes-bounded (mkDLC 7  _) = m≤m+n 7 57
  dlcBytes-bounded (mkDLC 8  _) = m≤m+n 8 56
  dlcBytes-bounded (mkDLC 9  _) = m≤m+n 12 52
  dlcBytes-bounded (mkDLC 10 _) = m≤m+n 16 48
  dlcBytes-bounded (mkDLC 11 _) = m≤m+n 20 44
  dlcBytes-bounded (mkDLC 12 _) = m≤m+n 24 40
  dlcBytes-bounded (mkDLC 13 _) = m≤m+n 32 32
  dlcBytes-bounded (mkDLC 14 _) = m≤m+n 48 16
  dlcBytes-bounded (mkDLC 15 _) = ≤-refl
  dlcBytes-bounded (mkDLC (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _)))))))))))))))) ())

  -- When bytesToValidDLC succeeds, the raw byte count ≤ 64.
  -- Literals 0–16 cover bytesToValidDLC's literal patterns.
  -- The catch-all (n ≥ 17, via suc^17) mirrors bytesToValidDLC's if/≡ᵇ chain:
  -- n ≡ᵇ 20, 24, 32, 48, 64 give valid results; all-false gives nothing (absurd).
  bvd-raw-bound : ∀ n d → bytesToValidDLC n ≡ just d → n ≤ 64
  bvd-raw-bound 0  _ refl = z≤n
  bvd-raw-bound 1  _ refl = m≤m+n 1 63
  bvd-raw-bound 2  _ refl = m≤m+n 2 62
  bvd-raw-bound 3  _ refl = m≤m+n 3 61
  bvd-raw-bound 4  _ refl = m≤m+n 4 60
  bvd-raw-bound 5  _ refl = m≤m+n 5 59
  bvd-raw-bound 6  _ refl = m≤m+n 6 58
  bvd-raw-bound 7  _ refl = m≤m+n 7 57
  bvd-raw-bound 8  _ refl = m≤m+n 8 56
  bvd-raw-bound 9  _ ()
  bvd-raw-bound 10 _ ()
  bvd-raw-bound 11 _ ()
  bvd-raw-bound 12 _ refl = m≤m+n 12 52
  bvd-raw-bound 13 _ ()
  bvd-raw-bound 14 _ ()
  bvd-raw-bound 15 _ ()
  bvd-raw-bound 16 _ refl = m≤m+n 16 48
  -- Catch-all: bytesToValidDLC falls to its if/≡ᵇ chain for n ≥ 17.
  -- with n ≡ᵇ k mirrors each branch; ≡ᵇ-true→≤64 converts success to n ≤ 64.
  bvd-raw-bound n@(suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _))))))))))))))))) d eq
    with n ≡ᵇ 20 in eq₂₀ | eq
  ... | true  | refl = ≡ᵇ-true→≤64 n 20 eq₂₀ (m≤m+n 20 44)
  ... | false | eq₁ with n ≡ᵇ 24 in eq₂₄ | eq₁
  ...   | true  | refl = ≡ᵇ-true→≤64 n 24 eq₂₄ (m≤m+n 24 40)
  ...   | false | eq₂ with n ≡ᵇ 32 in eq₃₂ | eq₂
  ...     | true  | refl = ≡ᵇ-true→≤64 n 32 eq₃₂ (m≤m+n 32 32)
  ...     | false | eq₃ with n ≡ᵇ 48 in eq₄₈ | eq₃
  ...       | true  | refl = ≡ᵇ-true→≤64 n 48 eq₄₈ (m≤m+n 48 16)
  ...       | false | eq₄ with n ≡ᵇ 64 in eq₆₄ | eq₄
  ...         | true  | refl = ≡ᵇ-true→≤64 n 64 eq₆₄ ≤-refl
  ...         | false | ()

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
  with bytesToValidDLC rawDlc in bvd-eq | eq₁
...   | nothing | ()
...   | just dlc | eq₂
    with lookupString "sender" obj | eq₂
...     | nothing | ()
...     | just sender | eq₃
      with parseOptionalArray parseStringList (lookupArray "senders" obj) | eq₃
...       | inj₁ _ | ()
...       | inj₂ senders | eq₃'
        with lookupArray "signals" obj | eq₃'
...         | nothing | ()
...         | just signalsJSON | eq₄
          with parseSignalList rawDlc ctx signalsJSON 0 in sig-eq | eq₄
...           | inj₁ _ | ()
...           | inj₂ signals | eq₅
            with validateIdent name | eq₅
...           | inj₁ _ | ()
...           | inj₂ nameId | eq₆
              with validateIdent sender | eq₆
...             | inj₁ _ | ()
...             | inj₂ senderId | eq₇
                with validateIdentList senders | eq₇
...               | inj₁ _ | ()
...               | inj₂ senderIds | refl = record
                    { dlc-bound  = dlcBytes-bounded dlc
                    ; signals-wf = parseSignalList-wf rawDlc ctx signalsJSON 0 signals
                                     (bvd-raw-bound rawDlc dlc bvd-eq) sig-eq
                    }

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
-- MESSAGE LIST: SHARED LIFT COMBINATOR
-- ============================================================================

-- Lift a per-element proof over parseMessageList's traversal.
private
  parseMessageList-lift : ∀ {P : DBCMessage → Set}
    → (∀ obj msg → parseMessage obj ≡ inj₂ msg → P msg)
    → ∀ jsons idx msgs
    → parseMessageList jsons idx ≡ inj₂ msgs → All P msgs
  parseMessageList-lift _ [] idx .[] refl = []
  parseMessageList-lift f (JObject msgObj ∷ rest) idx msgs eq
    with parseMessage msgObj in msg-eq | eq
  ... | inj₁ _ | ()
  ... | inj₂ msg | eq₁
    with parseMessageList rest (idx + 1) in rest-eq | eq₁
  ...   | inj₁ _ | ()
  ...   | inj₂ msgs' | refl = f msgObj msg msg-eq ∷
                                parseMessageList-lift f rest (idx + 1) msgs' rest-eq
  parseMessageList-lift _ (JNull     ∷ _) idx msgs ()
  parseMessageList-lift _ (JBool _   ∷ _) idx msgs ()
  parseMessageList-lift _ (JNumber _ ∷ _) idx msgs ()
  parseMessageList-lift _ (JString _ ∷ _) idx msgs ()
  parseMessageList-lift _ (JArray _  ∷ _) idx msgs ()

-- ============================================================================
-- MESSAGE LIST WELL-FORMEDNESS
-- ============================================================================

-- If parseMessageList succeeds, all messages are well-formed.
parseMessageList-wf : ∀ jsons idx msgs
  → parseMessageList jsons idx ≡ inj₂ msgs → All WellFormedMessage msgs
parseMessageList-wf = parseMessageList-lift parseMessage-wf

-- ============================================================================
-- MESSAGE PHYSICAL VALIDITY
-- ============================================================================
--
-- Mirrors the wf chain above but extracts `All (PhysicallyValid …)` from
-- successful parses. parseMessageList-pv assembles `WellFormedMessageRT` by
-- calling BOTH parseMessage-wf and parseMessage-pv at each step.

parseMessageBody-pv : ∀ ctx name canId obj msg
  → parseMessageBody ctx name canId obj ≡ inj₂ msg
  → All (PhysicallyValid (dlcBytes (DBCMessage.dlc msg))) (DBCMessage.signals msg)
parseMessageBody-pv ctx name canId obj msg eq
  with lookupNat "dlc" obj | eq
... | nothing | ()
... | just rawDlc | eq₁
  with bytesToValidDLC rawDlc in bvd-eq | eq₁
...   | nothing | ()
...   | just dlc | eq₂
    with lookupString "sender" obj | eq₂
...     | nothing | ()
...     | just sender | eq₃
      with parseOptionalArray parseStringList (lookupArray "senders" obj) | eq₃
...       | inj₁ _ | ()
...       | inj₂ senders | eq₃'
        with lookupArray "signals" obj | eq₃'
...         | nothing | ()
...         | just signalsJSON | eq₄
          with parseSignalList rawDlc ctx signalsJSON 0 in sig-eq | eq₄
...           | inj₁ _ | ()
...           | inj₂ signals | eq₅
            with validateIdent name | eq₅
...           | inj₁ _ | ()
...           | inj₂ nameId | eq₆
              with validateIdent sender | eq₆
...             | inj₁ _ | ()
...             | inj₂ senderId | eq₇
                with validateIdentList senders | eq₇
...               | inj₁ _ | ()
...               | inj₂ senderIds | refl =
                    -- parseSignalList-pv returns `All (PhysicallyValid rawDlc) signals`
                    -- but the message has `dlc = dlc` so the goal is
                    -- `All (PhysicallyValid (dlcBytes dlc)) signals`. bvd-bytes
                    -- bridges via dlcBytes dlc ≡ rawDlc.
                    subst (λ n → All (PhysicallyValid n) signals)
                          (sym (bvd-bytes rawDlc dlc bvd-eq))
                          (parseSignalList-pv rawDlc ctx signalsJSON 0 signals
                            (bvd-raw-bound rawDlc dlc bvd-eq) sig-eq)

parseMessageFields-pv : ∀ ctx name obj msg
  → parseMessageFields ctx name obj ≡ inj₂ msg
  → All (PhysicallyValid (dlcBytes (DBCMessage.dlc msg))) (DBCMessage.signals msg)
parseMessageFields-pv ctx name obj msg eq
  with parseMessageId ctx obj in id-eq | eq
... | inj₁ _ | ()
... | inj₂ canId | eq' =
    parseMessageBody-pv ctx name canId obj msg eq'

parseMessage-pv : ∀ obj msg
  → parseMessage obj ≡ inj₂ msg
  → All (PhysicallyValid (dlcBytes (DBCMessage.dlc msg))) (DBCMessage.signals msg)
parseMessage-pv obj msg eq
  with lookupString "name" obj | eq
... | nothing | ()
... | just name | eq' = parseMessageFields-pv _ name obj msg eq'

-- Combines parseMessage-wf and parseMessage-pv to produce WellFormedMessageRT
-- for every message in the list.
parseMessageList-pv : ∀ jsons idx msgs
  → parseMessageList jsons idx ≡ inj₂ msgs → All WellFormedMessageRT msgs
parseMessageList-pv = parseMessageList-lift
  (λ obj msg eq → record
    { msg-wf     = parseMessage-wf obj msg eq
    ; signals-pv = parseMessage-pv obj msg eq
    })
