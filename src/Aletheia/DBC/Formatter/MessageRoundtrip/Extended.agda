{-# OPTIONS --safe --without-K #-}

-- Extended CAN ID message roundtrip proofs.
-- Split from MessageRoundtrip to keep normalization bounded.
module Aletheia.DBC.Formatter.MessageRoundtrip.Extended where

open import Data.Bool using (T)
open import Data.Nat using (ℕ; suc; _<_; _≤_; _<ᵇ_; s≤s)
open import Data.Nat.DivMod using (m<n⇒m%n≡m)
open import Data.List using (List)
open import Data.List.Relation.Unary.All using (All)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

open import Aletheia.DBC.Types using (DBCMessage; DBCSignal)
open import Aletheia.DBC.JSONParser using (parseMessage;
  parseMessageId; parseMessageBody; parseCANId)
open import Aletheia.CAN.Frame using (CANId; Extended)
open import Aletheia.Prelude using (extended-can-id-max; ifᵀ-witness)
open import Aletheia.DBC.Formatter.WellFormed using (WellFormedSignal; PhysicallyValid;
  getNat-ℕtoJSON; ≤→≤ᵇ-true)
open import Aletheia.DBC.Formatter.SignalRoundtrip using (signal-list-roundtrip)
open import Aletheia.DBC.Formatter.MessageRoundtrip.Base

private
  -- Stage 1: parseCANId roundtrip (Extended)
  -- After parseCANId reduces through lookupBool "extended" → just true,
  -- the goal is ifᵀ (rawId <ᵇ max) then (λ q → inj₂ (Extended rawId q)) else err ≡ inj₂ (Extended rawId pf).
  -- ifᵀ-witness closes this without with-abstraction (which would fail due to Extended's rigid type).
  canId-ext : ∀ rawId (pf : T (rawId <ᵇ extended-can-id-max)) n dlc sender signals
    → parseCANId (ctx n) rawId (messageFields (mkMessage (Extended rawId pf) n dlc sender signals))
      ≡ inj₂ (Extended rawId pf)
  canId-ext rawId pf n dlc sender signals = ifᵀ-witness _ _ pf

  msgId-ext : ∀ rawId (pf : T (rawId <ᵇ extended-can-id-max)) n dlc sender signals
    → parseMessageId (ctx n) (messageFields (mkMessage (Extended rawId pf) n dlc sender signals))
      ≡ inj₂ (Extended rawId pf)
  msgId-ext rawId pf n dlc sender signals
    rewrite getNat-ℕtoJSON rawId
    = canId-ext rawId pf n dlc sender signals

  -- Stage 2: parseMessageBody roundtrip (Extended)
  msgBody-ext : ∀ rawId (pf : T (rawId <ᵇ extended-can-id-max)) n dlc sender signals → dlc ≤ 64
    → All WellFormedSignal signals → All (PhysicallyValid dlc) signals
    → parseMessageBody (ctx n) n (Extended rawId pf) (messageFields (mkMessage (Extended rawId pf) n dlc sender signals))
      ≡ inj₂ (mkMessage (Extended rawId pf) n dlc sender signals)
  msgBody-ext rawId pf n dlc sender signals dlc-bound sigs-wf sigs-pv
    rewrite getNat-ℕtoJSON dlc
          | signal-list-roundtrip dlc (ctx n) signals 0 sigs-wf dlc-bound sigs-pv
          | ≤→≤ᵇ-true dlc-bound
          | m<n⇒m%n≡m (s≤s dlc-bound)
    = refl

-- Composed Extended message roundtrip
message-roundtrip-ext : ∀ rawId (pf : T (rawId <ᵇ extended-can-id-max)) n dlc sender signals
  → dlc ≤ 64
  → All WellFormedSignal signals → All (PhysicallyValid dlc) signals
  → parseMessage (messageFields (mkMessage (Extended rawId pf) n dlc sender signals))
    ≡ inj₂ (mkMessage (Extended rawId pf) n dlc sender signals)
message-roundtrip-ext rawId pf n dlc sender signals dlc-bound sigs-wf sigs-pv =
  trans (>>=ₑ-congʳ _ (msgId-ext rawId pf n dlc sender signals))
        (msgBody-ext rawId pf n dlc sender signals dlc-bound sigs-wf sigs-pv)
