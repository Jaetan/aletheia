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

open import Data.Bool using (T)
open import Aletheia.DBC.Types using (DBCMessage; DBCSignal)
open import Aletheia.CAN.DLC using (DLC; dlcBytes)
open import Aletheia.DBC.Formatter using (formatDBCMessage)
open import Aletheia.DBC.JSONParser using (parseMessage; parseMessageList)
open import Aletheia.CAN.Frame using (CANId; Standard; Extended)
open import Aletheia.Prelude using (standard-can-id-max; extended-can-id-max)
open import Aletheia.DBC.Formatter.WellFormed using (WellFormedSignal;
  WellFormedMessage; WellFormedMessageRT; PhysicallyValid)
open import Aletheia.DBC.Formatter.MessageRoundtrip.Base using (mkMessage; messageFields)
open import Aletheia.DBC.Formatter.MessageRoundtrip.Standard using (message-roundtrip-std)
open import Aletheia.DBC.Formatter.MessageRoundtrip.Extended using (message-roundtrip-ext)

private
  message-roundtrip-go : ∀ canId n (dlc : DLC) sender signals
    → dlcBytes dlc ≤ 64
    → All WellFormedSignal signals → All (PhysicallyValid (dlcBytes dlc)) signals
    → parseMessage (messageFields (mkMessage canId n dlc sender signals))
      ≡ inj₂ (mkMessage canId n dlc sender signals)
  message-roundtrip-go (Standard rawId pf) n dlc sender signals dlc-bound sigs-wf sigs-pv =
    message-roundtrip-std rawId pf n dlc sender signals dlc-bound sigs-wf sigs-pv
  message-roundtrip-go (Extended rawId pf) n dlc sender signals dlc-bound sigs-wf sigs-pv =
    message-roundtrip-ext rawId pf n dlc sender signals dlc-bound sigs-wf sigs-pv

message-roundtrip : ∀ msg → WellFormedMessageRT msg
  → parseMessage (messageFields msg) ≡ inj₂ msg
message-roundtrip msg wfrt = message-roundtrip-go
  (DBCMessage.id msg) (DBCMessage.name msg) (DBCMessage.dlc msg)
  (DBCMessage.sender msg) (DBCMessage.signals msg)
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
