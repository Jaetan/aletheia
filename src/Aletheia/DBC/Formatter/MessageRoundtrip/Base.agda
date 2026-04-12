{-# OPTIONS --safe --without-K #-}

-- Base helpers for message roundtrip proofs.
-- Defines mkMessage, messageFields, ctx, and >>=ₑ-congʳ once.
-- All exports are used by Standard.agda and Extended.agda.
module Aletheia.DBC.Formatter.MessageRoundtrip.Base where

open import Data.Nat using (ℕ)
open import Data.List using (List; _∷_; map; []) renaming (_++_ to _++ₗ_)
open import Data.String using (String) renaming (_++_ to _++ₛ_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Aletheia.DBC.Types using (DBCMessage; DBCSignal)
open import Aletheia.CAN.DLC using (DLC; dlcBytes)
open import Aletheia.DBC.Formatter using (ℕtoJSON; formatCANId; formatDBCSignal)
open import Aletheia.CAN.Frame using (CANId)
open import Aletheia.JSON using (JSON; JString; JNumber; JArray)
open import Aletheia.Prelude using (_>>=ₑ_)

mkMessage : CANId → String → DLC → String → List DBCSignal → DBCMessage
mkMessage i n d s sigs = record
  { id = i ; name = n ; dlc = d ; sender = s ; signals = sigs }

messageFields : DBCMessage → List (String × JSON)
messageFields msg =
  formatCANId (DBCMessage.id msg) ++ₗ
  ("name"    , JString (DBCMessage.name msg)) ∷
  ("dlc"     , ℕtoJSON (dlcBytes (DBCMessage.dlc msg))) ∷
  ("sender"  , JString (DBCMessage.sender msg)) ∷
  ("signals" , JArray (map (formatDBCSignal (dlcBytes (DBCMessage.dlc msg))) (DBCMessage.signals msg))) ∷
  []

ctx : String → String
ctx n = "message '" ++ₛ n ++ₛ "'"

>>=ₑ-congʳ : ∀ {E A B : Set} {x : E ⊎ A} {a : A} (f : A → E ⊎ B)
  → x ≡ inj₂ a → (x >>=ₑ f) ≡ f a
>>=ₑ-congʳ f refl = refl
