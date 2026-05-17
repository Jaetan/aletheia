{-# OPTIONS --safe --without-K #-}

-- Well-formedness predicates and bridge lemmas for DBC formatter proofs.
--
-- Purpose: Define what it means for a DBC to be "well-formed" (field values
-- within bounds so parse ∘ format = id), plus reusable bridge lemmas.
-- Role: Foundation layer for SignalRoundtrip and MessageRoundtrip proofs.
module Aletheia.DBC.Formatter.WellFormed where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _<_; _≤_; z≤n; s≤s; _<ᵇ_; _≤ᵇ_; _/_; _%_)
open import Data.Nat.DivMod using (m%n<n; m<n⇒m%n≡m)
open import Data.Nat.Divisibility using (1∣_; _∣?_)
open import Data.Nat.Properties using (≤-trans; <-≤-trans; ≤-<-trans; *-monoˡ-≤; m∸n≤m; +-comm)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (List; [])
open import Data.List.Relation.Unary.All using (All)
open import Data.Bool using (Bool; true; T)
open import Data.Empty as Empty using (⊥-elim)
open import Data.Maybe using (just)
open import Data.Sum using (_⊎_; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)

open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal)
open import Aletheia.CAN.DLC using (dlcBytes)
open import Aletheia.DBC.Formatter using (ℕtoJSON; ℤtoJSON; formatByteOrder)
open import Aletheia.DBC.JSONParser using (parseByteOrder)
open import Aletheia.CAN.Frame using (CANId)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.CAN.Endianness using (ByteOrder; LittleEndian; BigEndian; unconvertStartBit)
open import Aletheia.CAN.Endianness.Properties using (physicalBitPos-BE-bounded-any)
open import Aletheia.JSON using (getNat; getInt)
open import Aletheia.JSON.Properties using (getNat-ℕtoℚ)
open import Aletheia.CAN.Constants using (max-physical-bits; 8≤max-physical-bits)


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

record WellFormedMessage (m : DBCMessage) : Set where
  field
    dlc-bound  : dlcBytes (DBCMessage.dlc m) ≤ 64
    signals-wf : All WellFormedSignal (DBCMessage.signals m)

-- Additional constraints on a signal within a frame, needed for the BigEndian
-- unconvert→convert roundtrip AND for parse-time bit-length-positivity
-- (R5-B1 / R6-B7.1 closure, 2026-05-15: LE bl=0 now rejected at the JSON
-- parse boundary, completing BE-LE parity).
--
-- BE signals carry three constraints:
--   • len-pos       — bitLength ≥ 1 (signals must occupy at least one bit).
--   • fits-in-frame — startBit + bitLength − 1 < frameBytes * 8.
--   • msb-ge-len    — bitLength − 1 ≤ startBit (the BE LSB is below the MSB).
--
-- LE signals carry the len-pos constraint only.  `msb-ge-len` and
-- `fits-in-frame` would reject most real LE signals (a typical 8-bit LE
-- signal at startBit 0 has `msb = 7 > 0 = startBit`); the unconvert→convert
-- roundtrip is the identity for LE so neither is needed.
data PhysicallyValid (frameBytes : ℕ) (s : DBCSignal) : Set where
  -- LE signals: still require bitLength ≥ 1 (parse-time gate matches BE).
  pv-LE : DBCSignal.byteOrder s ≡ LittleEndian
        → 1 ≤ SignalDef.bitLength (DBCSignal.signalDef s)
        → PhysicallyValid frameBytes s
  -- BE signals: three constraints needed for unconvert→convert roundtrip.
  pv-BE : DBCSignal.byteOrder s ≡ BigEndian
        → 1 ≤ SignalDef.bitLength (DBCSignal.signalDef s)
        → SignalDef.startBit (DBCSignal.signalDef s) +
          SignalDef.bitLength (DBCSignal.signalDef s) ∸ 1 < frameBytes * 8
        → SignalDef.bitLength (DBCSignal.signalDef s) ∸ 1 ≤
          SignalDef.startBit (DBCSignal.signalDef s)
        → PhysicallyValid frameBytes s

-- Full well-formedness for message roundtrip: WellFormedMessage plus
-- PhysicallyValid for each signal (needed for BigEndian startBit roundtrip).
record WellFormedMessageRT (m : DBCMessage) : Set where
  field
    msg-wf     : WellFormedMessage m
    signals-pv : All (PhysicallyValid (dlcBytes (DBCMessage.dlc m))) (DBCMessage.signals m)

-- JSON-roundtrip well-formedness predicate.  Counterpart on the text
-- side is `Aletheia.DBC.TextParser.WellFormed.WellFormedTextDBCAgg` (8
-- fields).  The asymmetry is by design, not under-specification: JSON
-- emission preserves every metadata array unconditionally — signal
-- groups, env vars, value tables, nodes, comments, attributes,
-- unresolved value descs all round-trip without additional preconditions
-- because their field types either parse unconditionally (rationals,
-- naturals, identifier-validated strings) or carry their constraint at
-- the type level.  Text emission is materially lossier (Vector__XXX
-- placeholders, dropped `BO_TX_BU_`, multi-value mux selectors,
-- unresolved VAL_ entries) and the text-side aggregator predicate
-- carries a per-section field for each lossy region.  Reviewers comparing
-- the two records: the difference reflects the wire-format gap, not a
-- missing constraint here.  See `TextParser.WellFormed`'s header for
-- the full contract.
--
-- AGDA-D-11.2 (R18 cluster 14): the absence of `unresolved-empty`,
-- `msg-ids-unique`, attribute-WF, and SG-WF on this record is the
-- correct shape for JSON roundtrip; the FormatDBCText FFI handler's
-- mixed-discharge for `WellFormedTextDBCAgg` is tracked separately
-- as AGDA-D-19.6.
record WellFormedDBC (d : DBC) : Set where
  field
    messages-wf : All WellFormedMessage (DBC.messages d)

-- Full well-formedness for DBC roundtrip: WellFormedMessage plus
-- PhysicallyValid for each signal in each message.
-- Metadata fields (signal groups, environment vars, value tables) round-trip
-- without additional constraints — all field types are strings, rationals, or
-- bounded naturals that parse/format cleanly.
record WellFormedDBCRT (d : DBC) : Set where
  field
    messages-wf : All WellFormedMessageRT (DBC.messages d)

-- ============================================================================
-- BRIDGE LEMMAS
-- ============================================================================

-- ℕtoJSON n = JNumber (ℕtoℚ n), so getNat-ℕtoℚ applies directly.
getNat-ℕtoJSON : ∀ n → getNat (ℕtoJSON n) ≡ just n
getNat-ℕtoJSON = getNat-ℕtoℚ

-- ℤtoJSON z = JNumber (fromℤ z), where fromℤ puts z in the numerator and 0
-- in denominator-1 (so toℚᵘ (fromℤ z) = mkℚᵘ z 0). `getInt` then runs its
-- internal `with (suc 0) ∣? ∣ z ∣` check, which always succeeds (1 divides
-- everything). The outer `with 1 ∣? ∣ z ∣` shares Agda's abstraction with
-- `getInt`'s inner `with`, so `refl` closes each `yes`-branch and `1∣_`
-- refutes each `no`-branch. Case-split on z reveals `∣ z ∣` concretely:
-- `∣ + n ∣ = n` and `∣ -[1+ n ] ∣ = suc n`.
getInt-ℤtoJSON : ∀ z → getInt (ℤtoJSON z) ≡ just z
getInt-ℤtoJSON (+ n) with 1 ∣? n
... | yes _    = refl
... | no ¬1∣n  = ⊥-elim (¬1∣n (1∣ n))
getInt-ℤtoJSON -[1+ n ] with 1 ∣? suc n
... | yes _    = refl
... | no ¬1∣sn = ⊥-elim (¬1∣sn (1∣ suc n))

-- Byte order roundtrip: parse ∘ format = id
byteOrder-roundtrip : ∀ bo → parseByteOrder (formatByteOrder bo) ≡ inj₂ bo
byteOrder-roundtrip LittleEndian = refl
byteOrder-roundtrip BigEndian = refl

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
