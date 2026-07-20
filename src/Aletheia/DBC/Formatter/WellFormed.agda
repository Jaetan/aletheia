-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Well-formedness predicates and bridge lemmas for DBC formatter proofs.
--
-- Purpose: Define what it means for a DBC to be "well-formed" (field values
-- within bounds so parse ∘ format = id), plus reusable bridge lemmas.
-- Role: Foundation layer for SignalRoundtrip and MessageRoundtrip proofs.
module Aletheia.DBC.Formatter.WellFormed where

open import Data.Nat using (ℕ; suc; _+_; _*_; _<_; _≤_)
open import Data.Nat.Divisibility using (1∣_; _∣?_)
open import Data.Integer using (+_; -[1+_])
open import Data.List.Relation.Unary.All using (All)
open import Data.Empty as Empty using (⊥-elim)
open import Data.Maybe using (just)
open import Data.Sum using (inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal)
open import Aletheia.CAN.DLC using (dlcBytes)
open import Aletheia.DBC.Formatter using (ℕtoJSON; ℤtoJSON; formatByteOrder)
open import Aletheia.DBC.JSONParser using (parseByteOrder)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.CAN.Endianness using (LittleEndian; BigEndian)
open import Aletheia.JSON using (getNat; getInt)
open import Aletheia.JSON.Properties using (getNat-ℕtoℚ)
open import Aletheia.CAN.Constants using (max-physical-bits)


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

-- Frame-capacity constraints on a signal's INTERNAL (post-conversion)
-- geometry — exactly what the entry gates (`JSONParser.physicalGate`,
-- `TextParser.Topology.SignalLine.buildSignal`) establish, and what the
-- emit→re-parse roundtrips consume.
--
-- LE signals carry the three linear-form conditions the gate checks
-- directly (internal geometry = raw geometry for LE):
--   • len-pos     — bitLength ≥ 1 (signals must occupy at least one bit).
--   • sb-in-frame — startBit < frameBytes * 8.
--   • bl-in-frame — bitLength ≤ frameBytes * 8.
--
-- BE signals carry len-pos plus the fits conjunct
--   • fits-in-frame — startBit + bitLength ≤ frameBytes * 8
-- (the `Validity.BitsInFrame` form, decided by the shared
-- `SignalGeometry.signalFitsFrame?`).  The raw-side gate conditions
-- (MSB in frame + no-wrap) imply it via `convertStartBit-BE-fits`, and it
-- alone drives the unconvert→convert roundtrip
-- (`unconvertStartBit-roundtrip`) — the internal start/length bounds
-- follow from it, so BE needs no separate linear conjuncts.  The former
-- MSB-layout conjunct (`bitLength − 1 ≤ startBit`, post-conversion) is
-- gone: it was never consumed by the roundtrip and falsely excluded
-- textbook Motorola layouts whose internal run starts near bit 0.
data PhysicallyValid (frameBytes : ℕ) (s : DBCSignal) : Set where
  pv-LE : DBCSignal.byteOrder s ≡ LittleEndian
        → 1 ≤ SignalDef.bitLength (DBCSignal.signalDef s)
        → SignalDef.startBit (DBCSignal.signalDef s) < frameBytes * 8
        → SignalDef.bitLength (DBCSignal.signalDef s) ≤ frameBytes * 8
        → PhysicallyValid frameBytes s
  pv-BE : DBCSignal.byteOrder s ≡ BigEndian
        → 1 ≤ SignalDef.bitLength (DBCSignal.signalDef s)
        → SignalDef.startBit (DBCSignal.signalDef s) +
          SignalDef.bitLength (DBCSignal.signalDef s) ≤ frameBytes * 8
        → PhysicallyValid frameBytes s

-- Full well-formedness for message roundtrip: WellFormedMessage plus
-- PhysicallyValid for each signal (needed for BigEndian startBit roundtrip).
record WellFormedMessageRT (m : DBCMessage) : Set where
  field
    msg-wf     : WellFormedMessage m
    signals-pv : All (PhysicallyValid (dlcBytes (DBCMessage.dlc m))) (DBCMessage.signals m)

-- JSON-roundtrip well-formedness predicate.  Counterpart on the text
-- side is `Aletheia.DBC.TextParser.WellFormed.WellFormedTextDBCAgg` (9
-- fields).  The asymmetry is by design, not under-specification: JSON
-- emission preserves every metadata array unconditionally — signal
-- groups, env vars, value tables, nodes, comments, attributes,
-- unresolved value descs all round-trip without additional preconditions
-- because their field types either parse unconditionally (rationals,
-- naturals, identifier-validated strings) or carry their constraint at
-- the type level.  Text emission is materially lossier (Vector__XXX
-- placeholders, dropped `BO_TX_BU_`, multi-value mux selectors,
-- unresolved VAL_ entries) and the text-side aggregator predicate
-- carries a per-section field for each lossy region.  The two records
-- differ in shape: that difference reflects the wire-format gap, not a
-- missing constraint here.  See `TextParser.WellFormed`'s header for
-- the full contract.
--
-- The absence of `unresolved-empty`,
-- `msg-ids-unique`, attribute-WF, and SG-WF on this record is the
-- correct shape for JSON roundtrip; the FormatDBCText FFI handler's
-- mixed-discharge for `WellFormedTextDBCAgg` is handled separately.
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

