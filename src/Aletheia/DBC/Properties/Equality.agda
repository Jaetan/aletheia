{-# OPTIONS --safe --without-K #-}

-- Decidable equality for DBC types.
--
-- Purpose: Provide decidable equality instances for SignalPresence,
--   SignalDef, and DBCSignal, used by membership checks and pair validity.
module Aletheia.DBC.Properties.Equality where

open import Aletheia.DBC.Types using (DBCSignal; SignalPresence; Always; When)
open import Aletheia.DBC.Identifier using (Identifier; _≟ᴵ_)
open import Aletheia.DBC.CanonicalReceivers using (_≟ᶜʳ_)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.CAN.Endianness using (_≟-ByteOrder_)
open import Data.List using (List)
open import Data.List.NonEmpty using (List⁺) renaming (_∷_ to _∷⁺_)
open import Data.List.Properties using (≡-dec)
open import Data.Nat using (ℕ)
open import Data.Nat.Properties using (_≟_)
open import Aletheia.DBC.DecRat using (_≟ᵈ_)
open import Data.Bool.Properties using () renaming (_≟_ to _≟ᵇ_)
open import Data.Char using (Char) renaming (_≟_ to _≟ᶜ_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (Dec; yes; no)

-- Decidable equality for List⁺ ℕ
private
  _≟-List⁺ℕ_ : (vs₁ vs₂ : List⁺ ℕ) → Dec (vs₁ ≡ vs₂)
  (h₁ ∷⁺ t₁) ≟-List⁺ℕ (h₂ ∷⁺ t₂) with h₁ ≟ h₂ | ≡-dec _≟_ t₁ t₂
  ... | yes refl | yes refl = yes refl
  ... | no  h≢   | _        = no (λ { refl → h≢ refl })
  ... | _        | no  t≢   = no (λ { refl → t≢ refl })

-- Decidable equality for SignalPresence
_≟-SignalPresence_ : (p₁ p₂ : SignalPresence) → Dec (p₁ ≡ p₂)
Always       ≟-SignalPresence Always       = yes refl
Always       ≟-SignalPresence When _ _     = no (λ ())
When _ _     ≟-SignalPresence Always       = no (λ ())
When m₁ vs₁ ≟-SignalPresence When m₂ vs₂ with m₁ ≟ᴵ m₂ | vs₁ ≟-List⁺ℕ vs₂
... | yes refl | yes refl = yes refl
... | no  m≢   | _        = no (λ { refl → m≢ refl })
... | _        | no  vs≢  = no (λ { refl → vs≢ refl })

-- Decidable equality for SignalDef (7 fields)
_≟-SignalDef_ : (s₁ s₂ : SignalDef) → Dec (s₁ ≡ s₂)
s₁ ≟-SignalDef s₂
  with SignalDef.startBit s₁ ≟ SignalDef.startBit s₂
... | no ¬p = no (λ eq → ¬p (cong SignalDef.startBit eq))
... | yes refl
  with SignalDef.bitLength s₁ ≟ SignalDef.bitLength s₂
... | no ¬p = no (λ eq → ¬p (cong SignalDef.bitLength eq))
... | yes refl
  with SignalDef.isSigned s₁ ≟ᵇ SignalDef.isSigned s₂
... | no ¬p = no (λ eq → ¬p (cong SignalDef.isSigned eq))
... | yes refl
  with SignalDef.factor s₁ ≟ᵈ SignalDef.factor s₂
... | no ¬p = no (λ eq → ¬p (cong SignalDef.factor eq))
... | yes refl
  with SignalDef.offset s₁ ≟ᵈ SignalDef.offset s₂
... | no ¬p = no (λ eq → ¬p (cong SignalDef.offset eq))
... | yes refl
  with SignalDef.minimum s₁ ≟ᵈ SignalDef.minimum s₂
... | no ¬p = no (λ eq → ¬p (cong SignalDef.minimum eq))
... | yes refl
  with SignalDef.maximum s₁ ≟ᵈ SignalDef.maximum s₂
... | no ¬p = no (λ eq → ¬p (cong SignalDef.maximum eq))
... | yes refl = yes refl

-- Decidable equality for one (value, description) pair from `valueDescriptions`.
private
  _≟-vd_ : (e₁ e₂ : ℕ × List Char) → Dec (e₁ ≡ e₂)
  (n₁ , cs₁) ≟-vd (n₂ , cs₂) with n₁ ≟ n₂ | ≡-dec _≟ᶜ_ cs₁ cs₂
  ... | yes refl | yes refl = yes refl
  ... | no n≢   | _        = no (λ { refl → n≢ refl })
  ... | _        | no cs≢  = no (λ { refl → cs≢ refl })

-- Decidable equality for DBCSignal (7 fields, post-E.1)
_≟-DBCSignal_ : (s₁ s₂ : DBCSignal) → Dec (s₁ ≡ s₂)
s₁ ≟-DBCSignal s₂
  with DBCSignal.name s₁ ≟ᴵ DBCSignal.name s₂
... | no ¬p = no (λ eq → ¬p (cong DBCSignal.name eq))
... | yes refl
  with DBCSignal.signalDef s₁ ≟-SignalDef DBCSignal.signalDef s₂
... | no ¬p = no (λ eq → ¬p (cong DBCSignal.signalDef eq))
... | yes refl
  with DBCSignal.byteOrder s₁ ≟-ByteOrder DBCSignal.byteOrder s₂
... | no ¬p = no (λ eq → ¬p (cong DBCSignal.byteOrder eq))
... | yes refl
  with ≡-dec _≟ᶜ_ (DBCSignal.unit s₁) (DBCSignal.unit s₂)
... | no ¬p = no (λ eq → ¬p (cong DBCSignal.unit eq))
... | yes refl
  with DBCSignal.presence s₁ ≟-SignalPresence DBCSignal.presence s₂
... | no ¬p = no (λ eq → ¬p (cong DBCSignal.presence eq))
... | yes refl
  with DBCSignal.receivers s₁ ≟ᶜʳ DBCSignal.receivers s₂
... | no ¬p = no (λ eq → ¬p (cong DBCSignal.receivers eq))
... | yes refl
  with ≡-dec _≟-vd_ (DBCSignal.valueDescriptions s₁)
                    (DBCSignal.valueDescriptions s₂)
... | no ¬p = no (λ eq → ¬p (cong DBCSignal.valueDescriptions eq))
... | yes refl = yes refl
