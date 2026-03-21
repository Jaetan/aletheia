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
  WellFormedMessage; wf-standard; wf-extended)
open import Aletheia.DBC.Formatter.MessageRoundtrip.Shared using (mkMessage; messageFields)
open import Aletheia.DBC.Formatter.MessageRoundtrip.Standard using (message-roundtrip-std)
open import Aletheia.DBC.Formatter.MessageRoundtrip.Extended using (message-roundtrip-ext)

private
  message-roundtrip-go : ∀ canId n dlc sender signals
    → WellFormedCANId canId → dlc ≤ 8 → All WellFormedSignal signals
    → parseMessage (messageFields (mkMessage canId n dlc sender signals))
      ≡ inj₂ (mkMessage canId n dlc sender signals)
  message-roundtrip-go (Standard rawId) n dlc sender signals (wf-standard id-bound) dlc-bound sigs-wf =
    message-roundtrip-std rawId n dlc sender signals id-bound dlc-bound sigs-wf
  message-roundtrip-go (Extended rawId) n dlc sender signals (wf-extended id-bound) dlc-bound sigs-wf =
    message-roundtrip-ext rawId n dlc sender signals id-bound dlc-bound sigs-wf

message-roundtrip : ∀ msg → WellFormedMessage msg
  → parseMessage (messageFields msg) ≡ inj₂ msg
message-roundtrip msg wf = message-roundtrip-go
  (DBCMessage.id msg) (DBCMessage.name msg) (DBCMessage.dlc msg)
  (DBCMessage.sender msg) (DBCMessage.signals msg)
  (WellFormedMessage.id-wf wf) (WellFormedMessage.dlc-bound wf) (WellFormedMessage.signals-wf wf)

message-list-roundtrip : ∀ msgs idx → All WellFormedMessage msgs
  → parseMessageList (map formatDBCMessage msgs) idx ≡ inj₂ msgs
message-list-roundtrip [] idx [] = refl
message-list-roundtrip (msg ∷ msgs) idx (wf ∷ wfs)
  rewrite message-roundtrip msg wf
        | message-list-roundtrip msgs (idx + 1) wfs
  = refl
