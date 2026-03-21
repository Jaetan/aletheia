{-# OPTIONS --safe --without-K #-}

-- Well-formedness predicates and bridge lemmas for DBC formatter proofs.
--
-- Purpose: Define what it means for a DBC to be "well-formed" (field values
-- within bounds so parse ∘ format = id), plus reusable bridge lemmas.
-- Role: Foundation layer for SignalRoundtrip and MessageRoundtrip proofs.
module Aletheia.DBC.Formatter.WellFormed where

open import Data.Nat using (ℕ; suc; _<_; _≤_; s≤s; _<ᵇ_; _≤ᵇ_)
open import Data.Nat.Properties using (≤⇒≤ᵇ)
open import Data.List using (List)
open import Data.List.Relation.Unary.All using (All)
open import Data.Bool using (Bool; true; T)
open import Data.Maybe using (just)
open import Data.Sum using (_⊎_; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal)
open import Aletheia.DBC.Formatter using (ℕtoJSON; formatByteOrder)
open import Aletheia.DBC.JSONParser using (parseByteOrder)
open import Aletheia.CAN.Frame using (CANId; Standard; Extended)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.CAN.Endianness using (ByteOrder; LittleEndian; BigEndian)
open import Aletheia.Protocol.JSON using (getNat)
open import Aletheia.Protocol.JSON.Properties using (getNat-ℕtoℚ)
open import Aletheia.Prelude using (standard-can-id-max; extended-can-id-max)

-- ============================================================================
-- WELL-FORMEDNESS PREDICATES
-- ============================================================================

record WellFormedSignalDef (sd : SignalDef) : Set where
  field
    startBit-bound  : SignalDef.startBit sd < 64
    bitLength-bound : SignalDef.bitLength sd < 65

record WellFormedSignal (s : DBCSignal) : Set where
  field
    def-wf : WellFormedSignalDef (DBCSignal.signalDef s)

data WellFormedCANId : CANId → Set where
  wf-standard : ∀ {n} → n < standard-can-id-max → WellFormedCANId (Standard n)
  wf-extended : ∀ {n} → n < extended-can-id-max → WellFormedCANId (Extended n)

record WellFormedMessage (m : DBCMessage) : Set where
  field
    dlc-bound  : DBCMessage.dlc m ≤ 8
    id-wf      : WellFormedCANId (DBCMessage.id m)
    signals-wf : All WellFormedSignal (DBCMessage.signals m)

record WellFormedDBC (d : DBC) : Set where
  field
    messages-wf : All WellFormedMessage (DBC.messages d)

-- ============================================================================
-- BRIDGE LEMMAS
-- ============================================================================

-- ℕtoJSON n = JNumber (ℕtoℚ n), so getNat-ℕtoℚ applies directly.
getNat-ℕtoJSON : ∀ n → getNat (ℕtoJSON n) ≡ just n
getNat-ℕtoJSON = getNat-ℕtoℚ

-- Byte order roundtrip: parse ∘ format = id
byteOrder-roundtrip : ∀ bo → parseByteOrder (formatByteOrder bo) ≡ inj₂ bo
byteOrder-roundtrip LittleEndian = refl
byteOrder-roundtrip BigEndian = refl

-- Boolean bridge helpers
T→true : ∀ {b : Bool} → T b → b ≡ true
T→true {true} _ = refl

<→<ᵇ-true : ∀ {m n} → m < n → (m <ᵇ n) ≡ true
<→<ᵇ-true p = T→true (≤⇒≤ᵇ p)

≤→≤ᵇ-true : ∀ {m n} → m ≤ n → (m ≤ᵇ n) ≡ true
≤→≤ᵇ-true p = T→true (≤⇒≤ᵇ p)
