{-# OPTIONS --safe --without-K #-}

-- Standard CAN ID message roundtrip proofs.
-- Split from MessageRoundtrip to keep normalization bounded.
module Aletheia.DBC.Formatter.MessageRoundtrip.Standard where

open import Data.Bool using (T)
open import Data.Nat using (ℕ; suc; _<_; _≤_; _<ᵇ_; s≤s)
open import Data.List using (List)
open import Data.List.Relation.Unary.All using (All)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

open import Aletheia.DBC.Types using (DBCMessage; DBCSignal)
open import Aletheia.CAN.DLC using (DLC; dlcBytes)
open import Aletheia.CAN.DLC.Properties using (bytesToValidDLC-roundtrip)
open import Aletheia.DBC.JSONParser using (parseMessage;
  parseMessageId; parseMessageBody; parseCANId)
open import Aletheia.CAN.Frame using (CANId; Standard)
open import Aletheia.CAN.Constants using (standard-can-id-max)
open import Aletheia.Prelude using (ifᵀ-witness)
open import Aletheia.DBC.Formatter.WellFormed using (WellFormedSignal; PhysicallyValid;
  getNat-ℕtoJSON)
open import Aletheia.DBC.Formatter.SignalRoundtrip using (signal-list-roundtrip)
open import Aletheia.DBC.Formatter.MessageRoundtrip.Base

private
  -- Stage 1: parseCANId roundtrip (Standard)
  canId-std : ∀ rawId (pf : T (rawId <ᵇ standard-can-id-max)) n (dlc : DLC) sender signals
    → parseCANId (ctx n) rawId (messageFields (mkMessage (Standard rawId pf) n dlc sender signals))
      ≡ inj₂ (Standard rawId pf)
  canId-std rawId pf n dlc sender signals = ifᵀ-witness _ _ pf

  msgId-std : ∀ rawId (pf : T (rawId <ᵇ standard-can-id-max)) n (dlc : DLC) sender signals
    → parseMessageId (ctx n) (messageFields (mkMessage (Standard rawId pf) n dlc sender signals))
      ≡ inj₂ (Standard rawId pf)
  msgId-std rawId pf n dlc sender signals
    rewrite getNat-ℕtoJSON rawId
    = canId-std rawId pf n dlc sender signals

  -- Stage 2: parseMessageBody roundtrip (Standard)
  msgBody-std : ∀ rawId (pf : T (rawId <ᵇ standard-can-id-max)) n (dlc : DLC) sender signals
    → dlcBytes dlc ≤ 64
    → All WellFormedSignal signals → All (PhysicallyValid (dlcBytes dlc)) signals
    → parseMessageBody (ctx n) n (Standard rawId pf) (messageFields (mkMessage (Standard rawId pf) n dlc sender signals))
      ≡ inj₂ (mkMessage (Standard rawId pf) n dlc sender signals)
  msgBody-std rawId pf n dlc sender signals dlc-bound sigs-wf sigs-pv
    rewrite getNat-ℕtoJSON (dlcBytes dlc)
          | bytesToValidDLC-roundtrip dlc
          | signal-list-roundtrip (dlcBytes dlc) (ctx n) signals 0 sigs-wf dlc-bound sigs-pv
    = refl

-- Composed Standard message roundtrip
message-roundtrip-std : ∀ rawId (pf : T (rawId <ᵇ standard-can-id-max)) n (dlc : DLC) sender signals
  → dlcBytes dlc ≤ 64
  → All WellFormedSignal signals → All (PhysicallyValid (dlcBytes dlc)) signals
  → parseMessage (messageFields (mkMessage (Standard rawId pf) n dlc sender signals))
    ≡ inj₂ (mkMessage (Standard rawId pf) n dlc sender signals)
message-roundtrip-std rawId pf n dlc sender signals dlc-bound sigs-wf sigs-pv =
  trans (>>=ₑ-congʳ _ (msgId-std rawId pf n dlc sender signals))
        (msgBody-std rawId pf n dlc sender signals dlc-bound sigs-wf sigs-pv)
