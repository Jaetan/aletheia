-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Signal-level roundtrip proofs for the DBC formatter.
--
-- Purpose: Prove parseSignal frameBytes (signalFields frameBytes sig) ≡ inj₂ sig
-- for well-formed signals.
-- Role: Middle layer — used by MessageRoundtrip for the signal-list component.
--
-- Design: signalFields mirrors formatDBCSignal (including unconvertStartBit for
-- Motorola/BigEndian signals). The roundtrip proof handles:
-- - LE: unconvert/convert are both identity; PhysicallyValid's capacity
--   conjuncts discharge the entry gate directly.
-- - BE: the emitted (raw) start bit satisfies the gate's conditions via the
--   frame-capacity bridges (unconvertSB-BE-inFrame / fits⇒bl≤cap /
--   unconvertSB-BE-noWrap, all derived from the fits conjunct), then
--   unconvertStartBit-roundtrip recovers the internal start bit.
module Aletheia.DBC.Formatter.SignalRoundtrip where
open import Aletheia.DBC.Identifier using (Identifier)
open import Aletheia.DBC.CanonicalReceivers using (CanonicalReceivers; mkCanonicalFromList-list)

open import Data.Char using (Char)
open import Data.Nat using (ℕ; _+_; _*_; _<_; _≤_)
open import Data.List using (List; []; _∷_; map)
open import Data.List.NonEmpty as List⁺ using ()
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.String using (String)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Aletheia.DBC.Types using (DBCSignal; SignalPresence; Always; When)
open import Aletheia.DBC.Formatter using (ℕtoJSON; identJSON; formatDBCSignal; formatByteOrder; formatPresence; formatValueEntry)
open import Aletheia.DBC.JSONParser using (parseSignal; parseSignalList; parseNatList)
open import Aletheia.DBC.Formatter.MetadataRoundtrip using (parseCharsList-roundtrip; validateIdent-roundtrip; validateIdentList-roundtrip; map-∘-identifier; valueEntry-list-roundtrip)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.DBC.DecRat using (toℚ)
open import Aletheia.DBC.DecRat.RationalRoundtrip using (fromℚ?-after-toℚ)
open import Aletheia.CAN.Endianness using (ByteOrder; LittleEndian; BigEndian; unconvertStartBit)
open import Aletheia.CAN.Endianness.Properties using
  (unconvertStartBit-roundtrip; fits⇒∸<; fits⇒1≤n; fits⇒bl≤cap;
   unconvertSB-BE-inFrame; unconvertSB-BE-noWrap)
open import Aletheia.DBC.Decidable.SignalGeometry.Properties using
  (geometryRefusal-accept-LE; geometryRefusal-accept-BE)
open import Aletheia.JSON using (JSON; JString; JNumber; JBool; JArray)
open import Aletheia.DBC.Formatter.WellFormed using (WellFormedSignal;
  PhysicallyValid; pv-LE; pv-BE; getNat-ℕtoJSON; byteOrder-roundtrip)

-- ============================================================================
-- SIGNAL ROUNDTRIP
-- ============================================================================

private
  mkSignal : Identifier → SignalDef → ByteOrder → List Char → SignalPresence → CanonicalReceivers
           → List (ℕ × List Char) → DBCSignal
  mkSignal n sd bo u p rs vds = record
    { name = n ; signalDef = sd ; byteOrder = bo ; unit = u ; presence = p ; receivers = rs
    ; valueDescriptions = vds }

  -- Mirrors the body of formatDBCSignal (without JObject wrapper).
  -- parseSignalList pattern-matches on JObject, so proofs work on the
  -- unwrapped field list.
  signalFields : ℕ → DBCSignal → List (String × JSON)
  signalFields frameBytes sig =
    let def = DBCSignal.signalDef sig
        bo  = DBCSignal.byteOrder sig
        sb  = unconvertStartBit frameBytes bo (SignalDef.startBit def) (SignalDef.bitLength def)
    in ("name"      , identJSON (DBCSignal.name sig)) ∷
       ("startBit"  , ℕtoJSON sb) ∷
       ("length"    , ℕtoJSON (SignalDef.bitLength def)) ∷
       ("byteOrder" , JString (formatByteOrder (DBCSignal.byteOrder sig))) ∷
       ("signed"    , JBool (SignalDef.isSigned def)) ∷
       ("factor"    , JNumber (toℚ (SignalDef.factor def))) ∷
       ("offset"    , JNumber (toℚ (SignalDef.offset def))) ∷
       ("minimum"   , JNumber (toℚ (SignalDef.minimum def))) ∷
       ("maximum"   , JNumber (toℚ (SignalDef.maximum def))) ∷
       ("unit"      , JString (DBCSignal.unit sig)) ∷
       ("receivers" , JArray (map identJSON (CanonicalReceivers.list (DBCSignal.receivers sig)))) ∷
       ("valueDescriptions" , JArray (map formatValueEntry (DBCSignal.valueDescriptions sig))) ∷
       formatPresence (DBCSignal.presence sig)

  -- parseNatList roundtrips through map ℕtoJSON
  parseNatList-roundtrip : ∀ ns → parseNatList (map ℕtoJSON ns) ≡ inj₂ ns
  parseNatList-roundtrip [] = refl
  parseNatList-roundtrip (n ∷ ns)
    rewrite getNat-ℕtoJSON n | parseNatList-roundtrip ns = refl

  -- LE roundtrip: unconvertStartBit _ LE s _ = s, convertStartBit _ LE s _ = s;
  -- PhysicallyValid's three LE conjuncts discharge the entry gate.
  signal-roundtrip-LE : ∀ frameBytes ctx n sd u p rs vds
    → 1 ≤ SignalDef.bitLength sd
    → SignalDef.startBit sd < frameBytes * 8
    → SignalDef.bitLength sd ≤ frameBytes * 8
    → parseSignal frameBytes ctx (signalFields frameBytes (mkSignal n sd LittleEndian u p rs vds))
      ≡ inj₂ (mkSignal n sd LittleEndian u p rs vds)
  signal-roundtrip-LE frameBytes ctx n sd u Always rs vds len-pos sbF blF
    rewrite getNat-ℕtoJSON (SignalDef.startBit sd)
          | getNat-ℕtoJSON (SignalDef.bitLength sd)
          | byteOrder-roundtrip LittleEndian
          | map-∘-identifier JString (CanonicalReceivers.list rs)
          | parseCharsList-roundtrip (map Identifier.name (CanonicalReceivers.list rs))
          | fromℚ?-after-toℚ (SignalDef.factor sd)
          | fromℚ?-after-toℚ (SignalDef.offset sd)
          | fromℚ?-after-toℚ (SignalDef.minimum sd)
          | fromℚ?-after-toℚ (SignalDef.maximum sd)
          | valueEntry-list-roundtrip vds
          | validateIdent-roundtrip n
          | validateIdentList-roundtrip (CanonicalReceivers.list rs)
          | mkCanonicalFromList-list rs
          | geometryRefusal-accept-LE frameBytes (SignalDef.startBit sd)
              (SignalDef.bitLength sd) len-pos sbF blF
    = refl
  signal-roundtrip-LE frameBytes ctx n sd u (When mux (v List⁺.∷ vs)) rs vds len-pos sbF blF
    rewrite getNat-ℕtoJSON (SignalDef.startBit sd)
          | getNat-ℕtoJSON (SignalDef.bitLength sd)
          | byteOrder-roundtrip LittleEndian
          | map-∘-identifier JString (CanonicalReceivers.list rs)
          | parseCharsList-roundtrip (map Identifier.name (CanonicalReceivers.list rs))
          | fromℚ?-after-toℚ (SignalDef.factor sd)
          | fromℚ?-after-toℚ (SignalDef.offset sd)
          | fromℚ?-after-toℚ (SignalDef.minimum sd)
          | fromℚ?-after-toℚ (SignalDef.maximum sd)
          | getNat-ℕtoJSON v
          | parseNatList-roundtrip vs
          | valueEntry-list-roundtrip vds
          | validateIdent-roundtrip n
          | validateIdent-roundtrip mux
          | validateIdentList-roundtrip (CanonicalReceivers.list rs)
          | mkCanonicalFromList-list rs
          | geometryRefusal-accept-LE frameBytes (SignalDef.startBit sd)
              (SignalDef.bitLength sd) len-pos sbF blF
    = refl

  -- BE roundtrip: the emitted raw start bit passes the gate via the
  -- frame-capacity bridges (all derived from len-pos + fits), then
  -- unconvertStartBit-roundtrip recovers the internal start bit.
  signal-roundtrip-BE : ∀ frameBytes ctx n sd u p rs vds
    → 1 ≤ SignalDef.bitLength sd
    → SignalDef.startBit sd + SignalDef.bitLength sd ≤ frameBytes * 8
    → parseSignal frameBytes ctx (signalFields frameBytes (mkSignal n sd BigEndian u p rs vds))
      ≡ inj₂ (mkSignal n sd BigEndian u p rs vds)
  signal-roundtrip-BE frameBytes ctx n sd u Always rs vds len-pos fits
    rewrite getNat-ℕtoJSON (unconvertStartBit frameBytes BigEndian (SignalDef.startBit sd) (SignalDef.bitLength sd))
          | getNat-ℕtoJSON (SignalDef.bitLength sd)
          | byteOrder-roundtrip BigEndian
          | map-∘-identifier JString (CanonicalReceivers.list rs)
          | parseCharsList-roundtrip (map Identifier.name (CanonicalReceivers.list rs))
          | fromℚ?-after-toℚ (SignalDef.factor sd)
          | fromℚ?-after-toℚ (SignalDef.offset sd)
          | fromℚ?-after-toℚ (SignalDef.minimum sd)
          | fromℚ?-after-toℚ (SignalDef.maximum sd)
          | valueEntry-list-roundtrip vds
          | validateIdent-roundtrip n
          | validateIdentList-roundtrip (CanonicalReceivers.list rs)
          | mkCanonicalFromList-list rs
          | geometryRefusal-accept-BE frameBytes
              (unconvertStartBit frameBytes BigEndian (SignalDef.startBit sd) (SignalDef.bitLength sd))
              (SignalDef.bitLength sd)
              len-pos
              (unconvertSB-BE-inFrame frameBytes (SignalDef.startBit sd) (SignalDef.bitLength sd)
                (fits⇒1≤n frameBytes (SignalDef.startBit sd) (SignalDef.bitLength sd) len-pos fits))
              (fits⇒bl≤cap frameBytes (SignalDef.startBit sd) (SignalDef.bitLength sd) fits)
              (unconvertSB-BE-noWrap frameBytes (SignalDef.startBit sd) (SignalDef.bitLength sd) len-pos fits)
          | unconvertStartBit-roundtrip frameBytes (SignalDef.startBit sd) (SignalDef.bitLength sd)
              len-pos (fits⇒∸< frameBytes (SignalDef.startBit sd) (SignalDef.bitLength sd) len-pos fits)
    = refl
  signal-roundtrip-BE frameBytes ctx n sd u (When mux (v List⁺.∷ vs)) rs vds len-pos fits
    rewrite getNat-ℕtoJSON (unconvertStartBit frameBytes BigEndian (SignalDef.startBit sd) (SignalDef.bitLength sd))
          | getNat-ℕtoJSON (SignalDef.bitLength sd)
          | byteOrder-roundtrip BigEndian
          | map-∘-identifier JString (CanonicalReceivers.list rs)
          | parseCharsList-roundtrip (map Identifier.name (CanonicalReceivers.list rs))
          | fromℚ?-after-toℚ (SignalDef.factor sd)
          | fromℚ?-after-toℚ (SignalDef.offset sd)
          | fromℚ?-after-toℚ (SignalDef.minimum sd)
          | fromℚ?-after-toℚ (SignalDef.maximum sd)
          | getNat-ℕtoJSON v
          | parseNatList-roundtrip vs
          | valueEntry-list-roundtrip vds
          | validateIdent-roundtrip n
          | validateIdent-roundtrip mux
          | validateIdentList-roundtrip (CanonicalReceivers.list rs)
          | mkCanonicalFromList-list rs
          | geometryRefusal-accept-BE frameBytes
              (unconvertStartBit frameBytes BigEndian (SignalDef.startBit sd) (SignalDef.bitLength sd))
              (SignalDef.bitLength sd)
              len-pos
              (unconvertSB-BE-inFrame frameBytes (SignalDef.startBit sd) (SignalDef.bitLength sd)
                (fits⇒1≤n frameBytes (SignalDef.startBit sd) (SignalDef.bitLength sd) len-pos fits))
              (fits⇒bl≤cap frameBytes (SignalDef.startBit sd) (SignalDef.bitLength sd) fits)
              (unconvertSB-BE-noWrap frameBytes (SignalDef.startBit sd) (SignalDef.bitLength sd) len-pos fits)
          | unconvertStartBit-roundtrip frameBytes (SignalDef.startBit sd) (SignalDef.bitLength sd)
              len-pos (fits⇒∸< frameBytes (SignalDef.startBit sd) (SignalDef.bitLength sd) len-pos fits)
    = refl

  signal-roundtrip-go : ∀ frameBytes ctx n sd bo u p rs vds
    → PhysicallyValid frameBytes (mkSignal n sd bo u p rs vds)
    → parseSignal frameBytes ctx (signalFields frameBytes (mkSignal n sd bo u p rs vds))
      ≡ inj₂ (mkSignal n sd bo u p rs vds)
  signal-roundtrip-go frameBytes ctx n sd LittleEndian u p rs vds (pv-LE _ lp sbF blF) =
    signal-roundtrip-LE frameBytes ctx n sd u p rs vds lp sbF blF
  signal-roundtrip-go frameBytes ctx n sd LittleEndian u p rs vds (pv-BE () _ _)
  signal-roundtrip-go frameBytes ctx n sd BigEndian u p rs vds (pv-BE _ lp fits) =
    signal-roundtrip-BE frameBytes ctx n sd u p rs vds lp fits
  signal-roundtrip-go frameBytes ctx n sd BigEndian u p rs vds (pv-LE () _ _ _)

-- The WellFormedSignal and frameBytes ≤ 64 arguments are retained for the
-- established call shape (MessageRoundtrip supplies them); the proof itself
-- runs entirely on the PhysicallyValid capacity conjuncts.
signal-roundtrip : ∀ frameBytes ctx sig
  → WellFormedSignal sig → frameBytes ≤ 64
  → PhysicallyValid frameBytes sig
  → parseSignal frameBytes ctx (signalFields frameBytes sig) ≡ inj₂ sig
signal-roundtrip frameBytes ctx sig _ _ pv = signal-roundtrip-go frameBytes ctx
  (DBCSignal.name sig) (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig)
  (DBCSignal.unit sig) (DBCSignal.presence sig) (DBCSignal.receivers sig)
  (DBCSignal.valueDescriptions sig)
  pv

-- ============================================================================
-- SIGNAL LIST ROUNDTRIP
-- ============================================================================

signal-list-roundtrip : ∀ frameBytes ctx sigs idx
  → All WellFormedSignal sigs → frameBytes ≤ 64
  → All (PhysicallyValid frameBytes) sigs
  → parseSignalList frameBytes ctx (map (formatDBCSignal frameBytes) sigs) idx ≡ inj₂ sigs
signal-list-roundtrip frameBytes ctx [] idx [] _ [] = refl
signal-list-roundtrip frameBytes ctx (sig ∷ sigs) idx (wf ∷ wfs) fb≤64 (pv ∷ pvs)
  rewrite signal-roundtrip frameBytes ctx sig wf fb≤64 pv
        | signal-list-roundtrip frameBytes ctx sigs (idx + 1) wfs fb≤64 pvs
  = refl
