{-# OPTIONS --safe --without-K #-}

-- Well-formedness predicates and bridge lemmas for DBC formatter proofs.
--
-- Purpose: Define what it means for a DBC to be "well-formed" (field values
-- within bounds so parse ∘ format = id), plus reusable bridge lemmas.
-- Role: Foundation layer for SignalRoundtrip and MessageRoundtrip proofs.
module Aletheia.DBC.Formatter.WellFormed where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _<_; _≤_; z≤n; s≤s; _<ᵇ_; _≤ᵇ_; _/_; _%_)
open import Data.Nat.DivMod using (m%n<n; m<n⇒m%n≡m)
open import Data.Nat.Properties using (≤⇒≤ᵇ; ≤-trans; <-≤-trans; ≤-<-trans; *-monoˡ-≤; m∸n≤m; +-comm)
open import Data.List using (List; [])
open import Data.List.Relation.Unary.All using (All)
open import Data.Bool using (Bool; true; T)
open import Data.Maybe using (just)
open import Data.Sum using (_⊎_; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)

open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal; SignalGroup; EnvironmentVar; ValueTable)
open import Aletheia.DBC.Formatter using (ℕtoJSON; formatByteOrder)
open import Aletheia.DBC.JSONParser using (parseByteOrder)
open import Aletheia.CAN.Frame using (CANId; Standard; Extended)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.CAN.Endianness using (ByteOrder; LittleEndian; BigEndian; unconvertStartBit)
open import Aletheia.CAN.Endianness.Properties using (physicalBitPos-BE-bounded-any)
open import Aletheia.Protocol.JSON using (getNat)
open import Aletheia.Protocol.JSON.Properties using (getNat-ℕtoℚ)
open import Aletheia.Prelude using (standard-can-id-max; extended-can-id-max; max-physical-bits; 8≤max-physical-bits)

-- ============================================================================
-- WELL-FORMEDNESS PREDICATES
-- ============================================================================

record WellFormedSignalDef (sd : SignalDef) : Set where
  field
    startBit-bound  : SignalDef.startBit sd < max-physical-bits
    bitLength-bound : SignalDef.bitLength sd < suc max-physical-bits

record WellFormedSignal (s : DBCSignal) : Set where
  field
    def-wf : WellFormedSignalDef (DBCSignal.signalDef s)

data WellFormedCANId : CANId → Set where
  wf-standard : ∀ {n} → n < standard-can-id-max → WellFormedCANId (Standard n)
  wf-extended : ∀ {n} → n < extended-can-id-max → WellFormedCANId (Extended n)

record WellFormedMessage (m : DBCMessage) : Set where
  field
    dlc-bound  : DBCMessage.dlc m ≤ 64
    id-wf      : WellFormedCANId (DBCMessage.id m)
    signals-wf : All WellFormedSignal (DBCMessage.signals m)

-- Additional constraints on a signal within a frame, needed for the BigEndian
-- unconvert→convert roundtrip. Always satisfied by physically valid CAN signals.
-- LE signals don't need these — the roundtrip closes from WellFormedSignalDef alone.
record PhysicallyValid (frameBytes : ℕ) (s : DBCSignal) : Set where
  field
    len-pos       : 1 ≤ SignalDef.bitLength (DBCSignal.signalDef s)
    fits-in-frame : SignalDef.startBit (DBCSignal.signalDef s) +
                    SignalDef.bitLength (DBCSignal.signalDef s) ∸ 1 < frameBytes * 8
    msb-ge-len    : SignalDef.bitLength (DBCSignal.signalDef s) ∸ 1 ≤
                    SignalDef.startBit (DBCSignal.signalDef s)

-- Full well-formedness for message roundtrip: WellFormedMessage plus
-- PhysicallyValid for each signal (needed for BigEndian startBit roundtrip).
record WellFormedMessageRT (m : DBCMessage) : Set where
  field
    msg-wf     : WellFormedMessage m
    signals-pv : All (PhysicallyValid (DBCMessage.dlc m)) (DBCMessage.signals m)

record WellFormedDBC (d : DBC) : Set where
  field
    messages-wf : All WellFormedMessage (DBC.messages d)

-- Full well-formedness for DBC roundtrip: WellFormedMessage plus
-- PhysicallyValid for each signal in each message.
-- Metadata fields (signal groups, environment vars, value tables) must be empty
-- because the JSON parser does not yet round-trip them — it always produces [].
record WellFormedDBCRT (d : DBC) : Set where
  field
    messages-wf   : All WellFormedMessageRT (DBC.messages d)
    groups-empty  : DBC.signalGroups d ≡ []
    envvars-empty : DBC.environmentVars d ≡ []
    vtables-empty : DBC.valueTables d ≡ []

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

-- ============================================================================
-- UNCONVERT STARTBIT BOUNDS
-- ============================================================================

-- unconvertStartBit n _ s l < max-physical-bits when n ≤ 64.
-- LE case: unconvertStartBit _ LE s _ = s, and s < max-physical-bits from WellFormedSignalDef.
-- BE case (suc n): physicalBitPos (suc n) BE x < (suc n)*8 ≤ 64*8 = max-physical-bits.
-- BE case (zero): physicalBitPos 0 BE x = (0∸(x/8))*8 + x%8 = x%8 < 8 ≤ max-physical-bits.
unconvertSB-bound : ∀ n s l → n ≤ 64 → s < max-physical-bits
  → unconvertStartBit n LittleEndian s l < max-physical-bits
unconvertSB-bound _ s _ _ s<mpb = s<mpb

private
  0∸x≡0 : ∀ m → 0 ∸ m ≡ 0
  0∸x≡0 zero    = refl
  0∸x≡0 (suc _) = refl

unconvertSB-bound-BE-zero : ∀ s l → unconvertStartBit 0 BigEndian s l < max-physical-bits
unconvertSB-bound-BE-zero s l = bound
  where
    x = s + l ∸ 1
    eq : unconvertStartBit 0 BigEndian s l ≡ x % 8
    eq = cong (λ v → v * 8 + x % 8) (0∸x≡0 (x / 8))
    bound : unconvertStartBit 0 BigEndian s l < max-physical-bits
    bound = subst (_< max-physical-bits) (sym eq) (<-≤-trans (m%n<n x 8) 8≤max-physical-bits)

unconvertSB-bound-BE : ∀ n s l → n ≤ 64
  → unconvertStartBit n BigEndian s l < max-physical-bits
unconvertSB-bound-BE zero s l _ = unconvertSB-bound-BE-zero s l
unconvertSB-bound-BE (suc n') s l n≤64 =
  <-≤-trans (physicalBitPos-BE-bounded-any (suc n') (s + l ∸ 1) (s≤s z≤n))
            (*-monoˡ-≤ 8 n≤64)
