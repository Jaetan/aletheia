{-# OPTIONS --safe --without-K #-}

-- Signal-level roundtrip proofs for the DBC formatter.
--
-- Purpose: Prove parseSignal (signalFields sig) ≡ inj₂ sig for well-formed signals.
-- Role: Middle layer — used by MessageRoundtrip for the signal-list component.
module Aletheia.DBC.Formatter.SignalRoundtrip where

open import Data.Nat using (ℕ; _+_)
open import Data.Nat.DivMod using (m<n⇒m%n≡m)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.String using (String)
open import Data.Rational using (ℚ)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Aletheia.DBC.Types using (DBCSignal; SignalPresence; Always; When)
open import Aletheia.DBC.Formatter using (ℕtoJSON; formatDBCSignal; formatByteOrder; formatPresence)
open import Aletheia.DBC.JSONParser using (parseSignal; parseSignalList)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.CAN.Endianness using (ByteOrder)
open import Aletheia.Protocol.JSON using (JSON; JObject; JString; JNumber; JBool; JArray)
open import Aletheia.DBC.Formatter.WellFormed using (WellFormedSignalDef; WellFormedSignal;
  getNat-ℕtoJSON; byteOrder-roundtrip)

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
  signalFields : DBCSignal → List (String × JSON)
  signalFields sig =
    let def = DBCSignal.signalDef sig
    in ("name"      , JString (DBCSignal.name sig)) ∷
       ("startBit"  , ℕtoJSON (SignalDef.startBit def)) ∷
       ("length"    , ℕtoJSON (SignalDef.bitLength def)) ∷
       ("byteOrder" , JString (formatByteOrder (DBCSignal.byteOrder sig))) ∷
       ("signed"    , JBool (SignalDef.isSigned def)) ∷
       ("factor"    , JNumber (SignalDef.factor def)) ∷
       ("offset"    , JNumber (SignalDef.offset def)) ∷
       ("minimum"   , JNumber (SignalDef.minimum def)) ∷
       ("maximum"   , JNumber (SignalDef.maximum def)) ∷
       ("unit"      , JString (DBCSignal.unit sig)) ∷
       formatPresence (DBCSignal.presence sig)

  signal-roundtrip-go : ∀ ctx n sd bo u p → WellFormedSignalDef sd
    → parseSignal ctx (signalFields (mkSignal n sd bo u p))
      ≡ inj₂ (mkSignal n sd bo u p)
  signal-roundtrip-go ctx n sd bo u Always dwf
    rewrite getNat-ℕtoJSON (SignalDef.startBit sd)
          | getNat-ℕtoJSON (SignalDef.bitLength sd)
          | byteOrder-roundtrip bo
          | m<n⇒m%n≡m (WellFormedSignalDef.startBit-bound dwf)
          | m<n⇒m%n≡m (WellFormedSignalDef.bitLength-bound dwf)
    = refl
  signal-roundtrip-go ctx n sd bo u (When mux v) dwf
    rewrite getNat-ℕtoJSON (SignalDef.startBit sd)
          | getNat-ℕtoJSON (SignalDef.bitLength sd)
          | byteOrder-roundtrip bo
          | getNat-ℕtoJSON v
          | m<n⇒m%n≡m (WellFormedSignalDef.startBit-bound dwf)
          | m<n⇒m%n≡m (WellFormedSignalDef.bitLength-bound dwf)
    = refl

signal-roundtrip : ∀ ctx sig → WellFormedSignal sig
  → parseSignal ctx (signalFields sig) ≡ inj₂ sig
signal-roundtrip ctx sig wf = signal-roundtrip-go ctx
  (DBCSignal.name sig) (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig)
  (DBCSignal.unit sig) (DBCSignal.presence sig) (WellFormedSignal.def-wf wf)

-- ============================================================================
-- SIGNAL LIST ROUNDTRIP
-- ============================================================================

signal-list-roundtrip : ∀ ctx sigs idx → All WellFormedSignal sigs
  → parseSignalList ctx (map formatDBCSignal sigs) idx ≡ inj₂ sigs
signal-list-roundtrip ctx [] idx [] = refl
signal-list-roundtrip ctx (sig ∷ sigs) idx (wf ∷ wfs)
  rewrite signal-roundtrip ctx sig wf
        | signal-list-roundtrip ctx sigs (idx + 1) wfs
  = refl
