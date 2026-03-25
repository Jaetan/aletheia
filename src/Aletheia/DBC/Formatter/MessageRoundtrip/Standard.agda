{-# OPTIONS --safe --without-K #-}

-- Standard CAN ID message roundtrip proofs.
-- Split from MessageRoundtrip to keep normalization bounded.
module Aletheia.DBC.Formatter.MessageRoundtrip.Standard where

open import Data.Nat using (ℕ; suc; _<_; _≤_; s≤s)
open import Data.Nat.DivMod using (m<n⇒m%n≡m)
open import Data.List using (List)
open import Data.List.Relation.Unary.All using (All)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

open import Aletheia.DBC.Types using (DBCMessage; DBCSignal)
open import Aletheia.DBC.JSONParser using (parseMessage;
  parseMessageId; parseMessageBody; parseCANId)
open import Aletheia.CAN.Frame using (CANId; Standard)
open import Aletheia.Prelude using (standard-can-id-max)
open import Aletheia.DBC.Formatter.WellFormed using (WellFormedSignal; PhysicallyValid;
  getNat-ℕtoJSON; <→<ᵇ-true; ≤→≤ᵇ-true)
open import Aletheia.DBC.Formatter.SignalRoundtrip using (signal-list-roundtrip)
open import Aletheia.DBC.Formatter.MessageRoundtrip.Base

private
  -- Stage 1: parseMessageId roundtrip (Standard)
  canId-std : ∀ rawId n dlc sender signals → rawId < standard-can-id-max
    → parseCANId (ctx n) rawId (messageFields (mkMessage (Standard rawId) n dlc sender signals))
      ≡ inj₂ (Standard rawId)
  canId-std rawId n dlc sender signals lt
    rewrite <→<ᵇ-true lt | m<n⇒m%n≡m lt = refl

  msgId-std : ∀ rawId n dlc sender signals → rawId < standard-can-id-max
    → parseMessageId (ctx n) (messageFields (mkMessage (Standard rawId) n dlc sender signals))
      ≡ inj₂ (Standard rawId)
  msgId-std rawId n dlc sender signals id-bound
    rewrite getNat-ℕtoJSON rawId
    = canId-std rawId n dlc sender signals id-bound

  -- Stage 2: parseMessageBody roundtrip (Standard)
  msgBody-std : ∀ rawId n dlc sender signals → dlc ≤ 64
    → All WellFormedSignal signals → All (PhysicallyValid dlc) signals
    → parseMessageBody (ctx n) n (Standard rawId) (messageFields (mkMessage (Standard rawId) n dlc sender signals))
      ≡ inj₂ (mkMessage (Standard rawId) n dlc sender signals)
  msgBody-std rawId n dlc sender signals dlc-bound sigs-wf sigs-pv
    rewrite getNat-ℕtoJSON dlc
          | signal-list-roundtrip dlc (ctx n) signals 0 sigs-wf dlc-bound sigs-pv
          | ≤→≤ᵇ-true dlc-bound
          | m<n⇒m%n≡m (s≤s dlc-bound)
    = refl

-- Composed Standard message roundtrip
message-roundtrip-std : ∀ rawId n dlc sender signals
  → rawId < standard-can-id-max → dlc ≤ 64
  → All WellFormedSignal signals → All (PhysicallyValid dlc) signals
  → parseMessage (messageFields (mkMessage (Standard rawId) n dlc sender signals))
    ≡ inj₂ (mkMessage (Standard rawId) n dlc sender signals)
message-roundtrip-std rawId n dlc sender signals id-bound dlc-bound sigs-wf sigs-pv =
  trans (>>=ₑ-congʳ _ (msgId-std rawId n dlc sender signals id-bound))
        (msgBody-std rawId n dlc sender signals dlc-bound sigs-wf sigs-pv)
