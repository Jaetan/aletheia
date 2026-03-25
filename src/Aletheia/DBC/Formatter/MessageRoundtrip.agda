{-# OPTIONS --safe --without-K #-}

-- Message-level roundtrip proofs for the DBC formatter.
--
-- Strategy: Standard and Extended cases are in separate modules to keep
-- normalization bounded. This module composes them and exports the
-- top-level message-roundtrip and message-list-roundtrip theorems.
module Aletheia.DBC.Formatter.MessageRoundtrip where

open import Data.Nat using (ℕ; _≤_; _+_)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Sum using (_⊎_; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Aletheia.DBC.Types using (DBCMessage; DBCSignal)
open import Aletheia.DBC.Formatter using (formatDBCMessage)
open import Aletheia.DBC.JSONParser using (parseMessage; parseMessageList)
open import Aletheia.CAN.Frame using (CANId; Standard; Extended)
open import Aletheia.DBC.Formatter.WellFormed using (WellFormedSignal; WellFormedCANId;
  WellFormedMessage; WellFormedMessageRT; PhysicallyValid; wf-standard; wf-extended)
open import Aletheia.DBC.Formatter.MessageRoundtrip.Base using (mkMessage; messageFields)
open import Aletheia.DBC.Formatter.MessageRoundtrip.Standard using (message-roundtrip-std)
open import Aletheia.DBC.Formatter.MessageRoundtrip.Extended using (message-roundtrip-ext)

private
  message-roundtrip-go : ∀ canId n dlc sender signals
    → WellFormedCANId canId → dlc ≤ 64
    → All WellFormedSignal signals → All (PhysicallyValid dlc) signals
    → parseMessage (messageFields (mkMessage canId n dlc sender signals))
      ≡ inj₂ (mkMessage canId n dlc sender signals)
  message-roundtrip-go (Standard rawId) n dlc sender signals (wf-standard id-bound) dlc-bound sigs-wf sigs-pv =
    message-roundtrip-std rawId n dlc sender signals id-bound dlc-bound sigs-wf sigs-pv
  message-roundtrip-go (Extended rawId) n dlc sender signals (wf-extended id-bound) dlc-bound sigs-wf sigs-pv =
    message-roundtrip-ext rawId n dlc sender signals id-bound dlc-bound sigs-wf sigs-pv

message-roundtrip : ∀ msg → WellFormedMessageRT msg
  → parseMessage (messageFields msg) ≡ inj₂ msg
message-roundtrip msg wfrt = message-roundtrip-go
  (DBCMessage.id msg) (DBCMessage.name msg) (DBCMessage.dlc msg)
  (DBCMessage.sender msg) (DBCMessage.signals msg)
  (WellFormedMessage.id-wf (WellFormedMessageRT.msg-wf wfrt))
  (WellFormedMessage.dlc-bound (WellFormedMessageRT.msg-wf wfrt))
  (WellFormedMessage.signals-wf (WellFormedMessageRT.msg-wf wfrt))
  (WellFormedMessageRT.signals-pv wfrt)

message-list-roundtrip : ∀ msgs idx → All WellFormedMessageRT msgs
  → parseMessageList (map formatDBCMessage msgs) idx ≡ inj₂ msgs
message-list-roundtrip [] idx [] = refl
message-list-roundtrip (msg ∷ msgs) idx (wfrt ∷ wfrts)
  rewrite message-roundtrip msg wfrt
        | message-list-roundtrip msgs (idx + 1) wfrts
  = refl
