-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Gate⇒checker deadness (and liveness) for the geometry checker arms.
--
-- DEADNESS, machine-checked: any signal accepted by either entry route's
-- geometry gate — `parseSignalFields` on the JSON wire, `buildSignal` on
-- the text route — satisfies `PhysicallyValid`, and a `PhysicallyValid`
-- signal draws NO issue from any geometry checker arm
-- (`checkSignalBounds`'s two capacity arms and `pvGo`'s
-- length-positivity / fits arms, WellFormedCheck.agda).  The arms and the
-- gates consume the same shared deciders (`DBC.Decidable.SignalGeometry`),
-- so this is a theorem about one condition set, not an observation about
-- two encodings that happen to agree.  The arms stay in the checker as
-- defense-in-depth for kernel-internally constructed DBC values; on every
-- public parse route they are PROVEN unreachable — out-of-capacity
-- geometry is refused with a typed parse error before a DBC value exists.
--
-- LIVENESS, machine-checked: the arms are not vacuous — concrete
-- violating signal values (constructible only by bypassing the gates)
-- make each checker family emit.  A checker that could never fail would
-- be a bug, not a defense.
module Aletheia.DBC.Properties.GeometryGateDeadness where

open import Data.Bool using (false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Data.Sum using (inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Aletheia.CAN.Endianness using (ByteOrder; LittleEndian; BigEndian)
open import Aletheia.CAN.Endianness.Properties using (convertStartBit-BE-fits)
open import Aletheia.DBC.Identifier using (Identifier; mkIdent)
open import Aletheia.DBC.CanonicalReceivers using (mkCanonicalFromList)
open import Aletheia.DBC.DecRat using (0ᵈ; 1ᵈ)
open import Aletheia.DBC.Types using (DBCSignal; Always)
open import Aletheia.JSON using (JSON)
open import Aletheia.DBC.Decidable.SignalGeometry using (geometryRefusal)
open import Aletheia.DBC.Decidable.SignalGeometry.Properties using
  (geometryRefusal-inv-LE; geometryRefusal-inv-BE)
open import Aletheia.DBC.Formatter.WellFormed using (PhysicallyValid; pv-LE; pv-BE)
open import Aletheia.DBC.JSONParser using (parseSignalFields)
open import Aletheia.DBC.JSONParser.SignalWF using (parseSignalFields-pv)
open import Aletheia.DBC.TextParser.Topology.Foundations using (RawSignal)
open import Aletheia.DBC.TextParser.Topology using (buildSignal; resolvePresence)
open import Aletheia.DBC.TextParser.WellFormedCheck using
  (checkSignalBounds; pvIssues)
open import Aletheia.DBC.TextParser.Properties.WellFormedCheck.Sound.Signal using
  (signalBounds-complete; pvGo-complete)

-- ============================================================================
-- TEXT-ROUTE GATE INVERSION: buildSignal acceptance ⇒ PhysicallyValid
-- ============================================================================

-- Mirrors `parseSignalFields-pv` (JSONParser/SignalWF.agda) on the text
-- route: a signal `buildSignal` accepted passed the shared gate, whose
-- inversion supplies the PhysicallyValid conjuncts.
buildSignal-pv : ∀ (fb : ℕ) (m : Maybe Identifier) (raw : RawSignal) (sig : DBCSignal)
  → buildSignal fb m raw ≡ just (inj₂ sig)
  → PhysicallyValid fb sig
buildSignal-pv fb m raw sig eq
  with resolvePresence m (RawSignal.muxMarker raw) | eq
... | nothing | ()
... | just presence | eq₁ with RawSignal.byteOrder raw | eq₁
buildSignal-pv fb m raw sig eq | just presence | eq₁ | LittleEndian | eq₂
  with geometryRefusal fb LittleEndian (RawSignal.startBit raw) (RawSignal.bitLength raw)
       in g-eq | eq₂
... | just _  | ()
... | nothing | refl =
      let (lp , sbF , blF) =
            geometryRefusal-inv-LE fb (RawSignal.startBit raw) (RawSignal.bitLength raw) g-eq
      in pv-LE refl lp sbF blF
buildSignal-pv fb m raw sig eq | just presence | eq₁ | BigEndian | eq₂
  with geometryRefusal fb BigEndian (RawSignal.startBit raw) (RawSignal.bitLength raw)
       in g-eq | eq₂
... | just _  | ()
... | nothing | refl =
      let (lp , sbF , blF , nw) =
            geometryRefusal-inv-BE fb (RawSignal.startBit raw) (RawSignal.bitLength raw) g-eq
      in pv-BE refl lp
           (convertStartBit-BE-fits fb (RawSignal.startBit raw) (RawSignal.bitLength raw)
             lp sbF nw)

-- ============================================================================
-- DEADNESS — PhysicallyValid empties every geometry checker arm
-- ============================================================================

bounds-dead : ∀ (fb : ℕ) (s : DBCSignal)
  → PhysicallyValid fb s → checkSignalBounds fb s ≡ []
bounds-dead = signalBounds-complete

pv-dead : ∀ (fb : ℕ) (s : DBCSignal)
  → PhysicallyValid fb s → pvIssues fb s ≡ []
pv-dead fb s pv = pvGo-complete fb _ s pv

-- JSON route composition: gate acceptance at parse time empties the arms.
parseSignalFields-geometry-dead :
  ∀ (fb : ℕ) (ctx : String) (name : List _) (obj : List (String × JSON)) (sig : DBCSignal)
  → fb ≤ 64
  → parseSignalFields fb ctx name obj ≡ inj₂ sig
  → (checkSignalBounds fb sig ≡ []) × (pvIssues fb sig ≡ [])
parseSignalFields-geometry-dead fb ctx name obj sig fb≤64 eq =
  bounds-dead fb sig pv , pv-dead fb sig pv
  where pv = parseSignalFields-pv fb ctx name obj sig fb≤64 eq

-- Text route composition: buildSignal acceptance empties the arms.
buildSignal-geometry-dead :
  ∀ (fb : ℕ) (m : Maybe Identifier) (raw : RawSignal) (sig : DBCSignal)
  → buildSignal fb m raw ≡ just (inj₂ sig)
  → (checkSignalBounds fb sig ≡ []) × (pvIssues fb sig ≡ [])
buildSignal-geometry-dead fb m raw sig eq =
  bounds-dead fb sig pv , pv-dead fb sig pv
  where pv = buildSignal-pv fb m raw sig eq

-- ============================================================================
-- LIVENESS — the arms can fire (on gate-bypassing constructions)
-- ============================================================================

private
  liveIdent : Identifier
  liveIdent = mkIdent ('S' ∷ []) tt

  -- Zero-length signal whose start bit also lies outside a classic
  -- 8-byte frame: both checker families emit on it.
  liveBad : DBCSignal
  liveBad = record
    { name      = liveIdent
    ; signalDef = record
        { startBit = 64 ; bitLength = 0 ; isSigned = false
        ; factor = 1ᵈ ; offset = 0ᵈ ; minimum = 0ᵈ ; maximum = 0ᵈ }
    ; byteOrder = LittleEndian
    ; unit      = []
    ; presence  = Always
    ; receivers = mkCanonicalFromList []
    ; valueDescriptions = []
    }

bounds-live : checkSignalBounds 8 liveBad ≢ []
bounds-live ()

pv-live : pvIssues 8 liveBad ≢ []
pv-live ()
