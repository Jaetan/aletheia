{-# OPTIONS --safe --without-K #-}

-- Base helpers for message roundtrip proofs.
-- Defines mkMessage, messageFields, ctx, and >>=ₑ-congʳ once.
-- All exports are used by Standard.agda and Extended.agda.
module Aletheia.DBC.Formatter.MessageRoundtrip.Base where
open import Aletheia.DBC.Identifier using (Identifier)

open import Data.Char using (Char)
open import Data.Nat using (ℕ)
open import Data.List using (List; _∷_; map; []) renaming (_++_ to _++ₗ_)
open import Data.String using (String; fromList) renaming (_++_ to _++ₛ_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Aletheia.DBC.Types using (DBCMessage; DBCSignal)
open import Aletheia.CAN.DLC using (DLC; dlcBytes)
open import Aletheia.DBC.Formatter using (ℕtoJSON; identJSON; formatCANId; formatDBCSignal)
open import Aletheia.CAN.Frame using (CANId)
open import Aletheia.JSON using (JSON; JString; JNumber; JArray)
open import Aletheia.Prelude using (_>>=ₑ_)

mkMessage : CANId → Identifier → DLC → Identifier → List Identifier → List DBCSignal → DBCMessage
mkMessage i n d s ss sigs = record
  { id = i ; name = n ; dlc = d ; sender = s ; senders = ss ; signals = sigs }

messageFields : DBCMessage → List (String × JSON)
messageFields msg =
  formatCANId (DBCMessage.id msg) ++ₗ
  ("name"    , identJSON (DBCMessage.name msg)) ∷
  ("dlc"     , ℕtoJSON (dlcBytes (DBCMessage.dlc msg))) ∷
  ("sender"  , identJSON (DBCMessage.sender msg)) ∷
  ("senders" , JArray (map identJSON (DBCMessage.senders msg))) ∷
  ("signals" , JArray (map (formatDBCSignal (dlcBytes (DBCMessage.dlc msg))) (DBCMessage.signals msg))) ∷
  []

-- Diagnostic context string built from a message-name char list.  Mirrors the
-- shape used by `parseMessage`'s `let context = "message '" ++ fromList name
-- ++ "'"`; the `fromList` here is a one-shot diagnostic call (not roundtripped).
ctx : List Char → String
ctx n = "message '" ++ₛ fromList n ++ₛ "'"

>>=ₑ-congʳ : ∀ {E A B : Set} {x : E ⊎ A} {a : A} (f : A → E ⊎ B)
  → x ≡ inj₂ a → (x >>=ₑ f) ≡ f a
>>=ₑ-congʳ f refl = refl
