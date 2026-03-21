{-# OPTIONS --safe --without-K #-}

-- Extended CAN ID message roundtrip proofs.
-- Split from MessageRoundtrip to keep normalization bounded.
-- Uses cong instead of chained rewrite to avoid with-auxiliary duplication.
module Aletheia.DBC.Formatter.MessageRoundtrip.Extended where

open import Data.Nat using (ℕ; suc; _<_; _≤_; s≤s)
open import Data.Nat.DivMod using (m<n⇒m%n≡m)
open import Data.List using (List)
open import Data.List.Relation.Unary.All using (All)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

open import Aletheia.DBC.Types using (DBCMessage; DBCSignal)
open import Aletheia.DBC.JSONParser using (parseMessage;
  parseMessageId; parseMessageBody; parseCANId)
open import Aletheia.CAN.Frame using (CANId; Extended)
open import Aletheia.Prelude using (extended-can-id-max)
open import Aletheia.DBC.Formatter.WellFormed using (WellFormedSignal;
  getNat-ℕtoJSON; <→<ᵇ-true; ≤→≤ᵇ-true)
open import Aletheia.DBC.Formatter.SignalRoundtrip using (signal-list-roundtrip)
open import Aletheia.DBC.Formatter.MessageRoundtrip.Shared

private
  -- Stage 1: parseMessageId roundtrip (Extended)
  -- Uses 1 rewrite + cong to avoid with-auxiliary duplication on large goal
  canId-ext : ∀ rawId n dlc sender signals → rawId < extended-can-id-max
    → parseCANId (ctx n) rawId (messageFields (mkMessage (Extended rawId) n dlc sender signals))
      ≡ inj₂ (Extended rawId)
  canId-ext rawId n dlc sender signals lt
    rewrite <→<ᵇ-true lt = cong (λ x → inj₂ (Extended x)) (m<n⇒m%n≡m lt)

  msgId-ext : ∀ rawId n dlc sender signals → rawId < extended-can-id-max
    → parseMessageId (ctx n) (messageFields (mkMessage (Extended rawId) n dlc sender signals))
      ≡ inj₂ (Extended rawId)
  msgId-ext rawId n dlc sender signals id-bound
    rewrite getNat-ℕtoJSON rawId
    = canId-ext rawId n dlc sender signals id-bound

  -- Stage 2: parseMessageBody roundtrip (Extended)
  -- Uses 3 rewrites + cong to stay within memory bounds
  msgBody-ext : ∀ rawId n dlc sender signals → dlc ≤ 8 → All WellFormedSignal signals
    → parseMessageBody (ctx n) n (Extended rawId) (messageFields (mkMessage (Extended rawId) n dlc sender signals))
      ≡ inj₂ (mkMessage (Extended rawId) n dlc sender signals)
  msgBody-ext rawId n dlc sender signals dlc-bound sigs-wf
    rewrite getNat-ℕtoJSON dlc
          | signal-list-roundtrip (ctx n) signals 0 sigs-wf
          | ≤→≤ᵇ-true dlc-bound
    = cong (λ x → inj₂ (record
        { id = Extended rawId ; name = n ; dlc = x
        ; sender = sender ; signals = signals }))
        (m<n⇒m%n≡m (s≤s dlc-bound))

-- Composed Extended message roundtrip
message-roundtrip-ext : ∀ rawId n dlc sender signals
  → rawId < extended-can-id-max → dlc ≤ 8 → All WellFormedSignal signals
  → parseMessage (messageFields (mkMessage (Extended rawId) n dlc sender signals))
    ≡ inj₂ (mkMessage (Extended rawId) n dlc sender signals)
message-roundtrip-ext rawId n dlc sender signals id-bound dlc-bound sigs-wf =
  trans (>>=ₑ-congʳ _ (msgId-ext rawId n dlc sender signals id-bound))
        (msgBody-ext rawId n dlc sender signals dlc-bound sigs-wf)
