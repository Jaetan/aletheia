{-# OPTIONS --safe --without-K #-}

-- Signal-level roundtrip proofs for the DBC formatter.
--
-- Purpose: Prove parseSignal frameBytes (signalFields frameBytes sig) ≡ inj₂ sig
-- for well-formed signals.
-- Role: Middle layer — used by MessageRoundtrip for the signal-list component.
--
-- Design: signalFields mirrors formatDBCSignal (including unconvertStartBit for
-- Motorola/BigEndian signals). The roundtrip proof handles:
-- - LE: unconvert/convert are both identity, so startBit % 512 roundtrips via WF bounds.
-- - BE: unconvertStartBit output < 512 (via unconvertSB-bound-BE when frameBytes ≤ 64),
--   then unconvertStartBit-roundtrip closes the proof (requires physical signal
--   constraints: 1 ≤ bitLength, startBit + bitLength ∸ 1 < frameBytes * 8,
--   bitLength ∸ 1 ≤ startBit).
module Aletheia.DBC.Formatter.SignalRoundtrip where

open import Data.Nat using (ℕ; _+_; _∸_; _*_; _<_; _≤_)
open import Data.Nat.DivMod using (m<n⇒m%n≡m)
open import Data.List using (List; []; _∷_; map)
open import Data.List.NonEmpty as List⁺ using (List⁺)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.String using (String)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

open import Aletheia.DBC.Types using (DBCSignal; SignalPresence; Always; When)
open import Aletheia.DBC.Formatter using (ℕtoJSON; formatDBCSignal; formatByteOrder; formatPresence)
open import Aletheia.DBC.JSONParser using (parseSignal; parseSignalList; parseNatList)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.CAN.Endianness using (ByteOrder; LittleEndian; BigEndian; unconvertStartBit)
open import Aletheia.CAN.Endianness.Properties using (unconvertStartBit-roundtrip)
open import Aletheia.JSON using (JSON; JObject; JString; JNumber; JBool; JArray)
open import Aletheia.DBC.Formatter.WellFormed using (WellFormedSignalDef; WellFormedSignal;
  PhysicallyValid; pv-LE; pv-BE; getNat-ℕtoJSON; byteOrder-roundtrip; unconvertSB-bound-BE)
open import Aletheia.Prelude using (T→true)
open import Data.Nat.Properties using (≤⇒≤ᵇ)

-- ============================================================================
-- SIGNAL ROUNDTRIP
-- ============================================================================

private
  mkSignal : String → SignalDef → ByteOrder → String → SignalPresence → DBCSignal
  mkSignal n sd bo u p = record
    { name = n ; signalDef = sd ; byteOrder = bo ; unit = u ; presence = p }

  -- Mirrors the body of formatDBCSignal (without JObject wrapper).
  -- parseSignalList pattern-matches on JObject, so proofs work on the
  -- unwrapped field list.
  signalFields : ℕ → DBCSignal → List (String × JSON)
  signalFields frameBytes sig =
    let def = DBCSignal.signalDef sig
        bo  = DBCSignal.byteOrder sig
        sb  = unconvertStartBit frameBytes bo (SignalDef.startBit def) (SignalDef.bitLength def)
    in ("name"      , JString (DBCSignal.name sig)) ∷
       ("startBit"  , ℕtoJSON sb) ∷
       ("length"    , ℕtoJSON (SignalDef.bitLength def)) ∷
       ("byteOrder" , JString (formatByteOrder (DBCSignal.byteOrder sig))) ∷
       ("signed"    , JBool (SignalDef.isSigned def)) ∷
       ("factor"    , JNumber (SignalDef.factor def)) ∷
       ("offset"    , JNumber (SignalDef.offset def)) ∷
       ("minimum"   , JNumber (SignalDef.minimum def)) ∷
       ("maximum"   , JNumber (SignalDef.maximum def)) ∷
       ("unit"      , JString (DBCSignal.unit sig)) ∷
       formatPresence (DBCSignal.presence sig)

  -- parseNatList roundtrips through map ℕtoJSON
  parseNatList-roundtrip : ∀ ns → parseNatList (map ℕtoJSON ns) ≡ inj₂ ns
  parseNatList-roundtrip [] = refl
  parseNatList-roundtrip (n ∷ ns)
    rewrite getNat-ℕtoJSON n | parseNatList-roundtrip ns = refl

  -- LE roundtrip: unconvertStartBit _ LE s _ = s, convertStartBit _ LE s _ = s,
  -- so the startBit roundtrips through % 512 using WF bounds.
  signal-roundtrip-LE : ∀ frameBytes ctx n sd u p → WellFormedSignalDef sd
    → parseSignal frameBytes ctx (signalFields frameBytes (mkSignal n sd LittleEndian u p))
      ≡ inj₂ (mkSignal n sd LittleEndian u p)
  signal-roundtrip-LE frameBytes ctx n sd u Always dwf
    rewrite getNat-ℕtoJSON (SignalDef.startBit sd)
          | getNat-ℕtoJSON (SignalDef.bitLength sd)
          | byteOrder-roundtrip LittleEndian
          | m<n⇒m%n≡m (WellFormedSignalDef.startBit-bound dwf)
          | m<n⇒m%n≡m (WellFormedSignalDef.bitLength-bound dwf)
    = refl
  signal-roundtrip-LE frameBytes ctx n sd u (When mux vs) dwf
    rewrite getNat-ℕtoJSON (SignalDef.startBit sd)
          | getNat-ℕtoJSON (SignalDef.bitLength sd)
          | byteOrder-roundtrip LittleEndian
          | parseNatList-roundtrip (List⁺.toList vs)
          | m<n⇒m%n≡m (WellFormedSignalDef.startBit-bound dwf)
          | m<n⇒m%n≡m (WellFormedSignalDef.bitLength-bound dwf)
    = refl

  -- BE roundtrip: uses unconvertSB-bound-BE for % 512 identity,
  -- unconvertStartBit-roundtrip for convert∘unconvert = id.
  signal-roundtrip-BE : ∀ frameBytes ctx n sd u p
    → WellFormedSignalDef sd → frameBytes ≤ 64
    → 1 ≤ SignalDef.bitLength sd
    → SignalDef.startBit sd + SignalDef.bitLength sd ∸ 1 < frameBytes * 8
    → SignalDef.bitLength sd ∸ 1 ≤ SignalDef.startBit sd
    → parseSignal frameBytes ctx (signalFields frameBytes (mkSignal n sd BigEndian u p))
      ≡ inj₂ (mkSignal n sd BigEndian u p)
  signal-roundtrip-BE frameBytes ctx n sd u Always dwf fb≤64 len-pos fits msb-ge
    rewrite getNat-ℕtoJSON (unconvertStartBit frameBytes BigEndian (SignalDef.startBit sd) (SignalDef.bitLength sd))
          | getNat-ℕtoJSON (SignalDef.bitLength sd)
          | byteOrder-roundtrip BigEndian
          | m<n⇒m%n≡m (unconvertSB-bound-BE frameBytes (SignalDef.startBit sd) (SignalDef.bitLength sd) fb≤64)
          | m<n⇒m%n≡m (WellFormedSignalDef.bitLength-bound dwf)
          | unconvertStartBit-roundtrip frameBytes (SignalDef.startBit sd) (SignalDef.bitLength sd) len-pos fits msb-ge
          | T→true (≤⇒≤ᵇ len-pos)    -- enables physicalGate's `1 ≤ᵇ bl` branch
          | T→true (≤⇒≤ᵇ fits)      -- enables physicalGate's `csb + bl ∸ 1 <ᵇ fb*8` branch
          | T→true (≤⇒≤ᵇ msb-ge)    -- enables physicalGate's `bl ∸ 1 ≤ᵇ csb` branch
    = refl
  signal-roundtrip-BE frameBytes ctx n sd u (When mux vs) dwf fb≤64 len-pos fits msb-ge
    rewrite getNat-ℕtoJSON (unconvertStartBit frameBytes BigEndian (SignalDef.startBit sd) (SignalDef.bitLength sd))
          | getNat-ℕtoJSON (SignalDef.bitLength sd)
          | byteOrder-roundtrip BigEndian
          | parseNatList-roundtrip (List⁺.toList vs)
          | m<n⇒m%n≡m (unconvertSB-bound-BE frameBytes (SignalDef.startBit sd) (SignalDef.bitLength sd) fb≤64)
          | m<n⇒m%n≡m (WellFormedSignalDef.bitLength-bound dwf)
          | unconvertStartBit-roundtrip frameBytes (SignalDef.startBit sd) (SignalDef.bitLength sd) len-pos fits msb-ge
          | T→true (≤⇒≤ᵇ len-pos)    -- enables physicalGate's `1 ≤ᵇ bl` branch
          | T→true (≤⇒≤ᵇ fits)      -- enables physicalGate's `csb + bl ∸ 1 <ᵇ fb*8` branch
          | T→true (≤⇒≤ᵇ msb-ge)    -- enables physicalGate's `bl ∸ 1 ≤ᵇ csb` branch
    = refl

  signal-roundtrip-go : ∀ frameBytes ctx n sd bo u p
    → WellFormedSignalDef sd → frameBytes ≤ 64
    → PhysicallyValid frameBytes (mkSignal n sd bo u p)
    → parseSignal frameBytes ctx (signalFields frameBytes (mkSignal n sd bo u p))
      ≡ inj₂ (mkSignal n sd bo u p)
  signal-roundtrip-go frameBytes ctx n sd LittleEndian u p dwf _ _ =
    signal-roundtrip-LE frameBytes ctx n sd u p dwf
  signal-roundtrip-go frameBytes ctx n sd BigEndian u p dwf fb≤64 (pv-BE _ lp fits msb) =
    signal-roundtrip-BE frameBytes ctx n sd u p dwf fb≤64 lp fits msb
  signal-roundtrip-go frameBytes ctx n sd BigEndian u p dwf fb≤64 (pv-LE ())

signal-roundtrip : ∀ frameBytes ctx sig
  → WellFormedSignal sig → frameBytes ≤ 64
  → PhysicallyValid frameBytes sig
  → parseSignal frameBytes ctx (signalFields frameBytes sig) ≡ inj₂ sig
signal-roundtrip frameBytes ctx sig wf fb≤64 pv = signal-roundtrip-go frameBytes ctx
  (DBCSignal.name sig) (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig)
  (DBCSignal.unit sig) (DBCSignal.presence sig) (WellFormedSignal.def-wf wf) fb≤64 pv

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
