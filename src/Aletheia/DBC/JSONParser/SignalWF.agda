-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Signal-level well-formedness proofs for the DBC JSON parser.
--
-- Purpose: Prove that if parseSignalFields/parseSignal succeeds, the result
-- is WellFormedSignal AND PhysicallyValid, and that the accepted signal's
-- internal geometry unconverts back to the SUBMITTED start bit / bit length
-- (the geometry-echo faithfulness: the kernel's JSON emission reproduces
-- what the caller sent — no clamp, no relocation).
-- Key insight: the witnesses come from the entry gate itself — inverting
-- `geometryRefusal ≡ nothing` (SignalGeometry.Properties) yields exactly
-- the frame-capacity conditions, the frame-capacity bridges
-- (Endianness.Properties.StartBit) lift them to the internal form, and
-- `convertStartBit-roundtrip`'s hypotheses are the BE gate conditions
-- verbatim — the gate is that lemma's consumer.
-- Role: Used by MessageWF for the signal-list component.
module Aletheia.DBC.JSONParser.SignalWF where
open import Aletheia.DBC.Identifier using (Identifier)
open import Aletheia.DBC.CanonicalReceivers using (mkCanonicalFromList)

open import Data.Nat using (ℕ; _+_; _*_; _<_; _≤_; s≤s)
open import Data.Nat.Properties using (≤-trans; <-≤-trans; *-monoˡ-≤)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.String using (String)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃₂)
open import Data.Maybe using (just; nothing)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Aletheia.JSON using (JNull; JBool; JNumber; JString; JArray; JObject;
  lookupChars; lookupArray)
open import Aletheia.CAN.Endianness using
  (ByteOrder; LittleEndian; BigEndian; convertStartBit; unconvertStartBit)
open import Aletheia.CAN.Endianness.Properties using
  (convertStartBit-roundtrip; convertStartBit-BE-fits; convertStartBit-BE-inFrame)
open import Aletheia.DBC.Types using (DBCSignal)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.DBC.JSONParser using (parseSignalFields; parseSignal; parseSignalList; lookupDecRat;
  parseByteOrder; parseSigned; parseSignalPresence; addSignalContext; physicalGate; validateIdent; validateIdentList;
  parseOptionalArray; parseCharsList; parseValueEntryList; lookupNatStrict)
open import Aletheia.DBC.Decidable.SignalGeometry using (geometryRefusal)
open import Aletheia.DBC.Decidable.SignalGeometry.Properties using
  (geometryRefusal-inv-LE; geometryRefusal-inv-BE)
open import Aletheia.DBC.Formatter.WellFormed using (WellFormedSignal;
  PhysicallyValid; pv-LE; pv-BE)

-- ============================================================================
-- POST-PRESENCE TAIL: gate inversion → WF × PV × geometry echo
-- ============================================================================

private
  -- Ceiling bridge: a capacity bound (< / ≤ frameBytes * 8) lifts to the
  -- type-level `max-physical-bits` ceiling when frameBytes ≤ 64
  -- (64 * 8 reduces to max-physical-bits definitionally).
  cap⇒ceiling-< : ∀ {frameBytes x} → frameBytes ≤ 64 → x < frameBytes * 8 → x < 512
  cap⇒ceiling-< fb≤64 x< = <-≤-trans x< (*-monoˡ-≤ 8 fb≤64)

  cap⇒ceiling-≤ : ∀ {frameBytes x} → frameBytes ≤ 64 → x ≤ frameBytes * 8 → x ≤ 512
  cap⇒ceiling-≤ fb≤64 x≤ = ≤-trans x≤ (*-monoˡ-≤ 8 fb≤64)

-- Result bundle for the accepted signal: well-formedness, physical
-- validity, and the geometry echo (the formatter's `unconvertStartBit`
-- applied to the stored internal geometry reproduces the submitted raw
-- start bit; the stored bit length IS the submitted one).
SignalGate : (frameBytes sb bl : ℕ) → DBCSignal → Set
SignalGate frameBytes sb bl sig =
  WellFormedSignal sig
  × PhysicallyValid frameBytes sig
  × (unconvertStartBit frameBytes (DBCSignal.byteOrder sig)
       (SignalDef.startBit (DBCSignal.signalDef sig))
       (SignalDef.bitLength (DBCSignal.signalDef sig)) ≡ sb)
  × (SignalDef.bitLength (DBCSignal.signalDef sig) ≡ bl)

-- Extract the full bundle after the with-chain reaches the gate.  Takes
-- byte order as an explicit parameter so we can pattern-match; the gate
-- verdict (`geometryRefusal`) is the ONLY scrutinee — its inversion
-- supplies every witness.
postPresence-gate :
  ∀ (frameBytes : ℕ) (ctx : String) (name : Identifier) (bo : ByteOrder)
    (sb bl : ℕ)
    isSigned factor offset minimum maximum unit presence receivers vds sig
  → frameBytes ≤ 64
  → addSignalContext ctx (physicalGate frameBytes bo sb bl (record
      { name = name
      ; signalDef = record
          { startBit = convertStartBit frameBytes bo sb bl
          ; bitLength = bl
          ; isSigned = isSigned
          ; factor = factor
          ; offset = offset
          ; minimum = minimum
          ; maximum = maximum
          }
      ; byteOrder = bo
      ; unit = unit
      ; presence = presence
      ; receivers = receivers
      ; valueDescriptions = vds
      }))
    ≡ inj₂ sig
  → SignalGate frameBytes sb bl sig
postPresence-gate frameBytes ctx name LittleEndian sb bl
  isSigned factor offset minimum maximum unit presence receivers vds sig fb≤64 eq
  with geometryRefusal frameBytes LittleEndian sb bl in g-eq | eq
... | just _  | ()
... | nothing | refl =
  let (lp , sbF , blF) = geometryRefusal-inv-LE frameBytes sb bl g-eq
  in record { def-wf = record
       { startBit-bound  = cap⇒ceiling-< fb≤64 sbF
       ; bitLength-bound = s≤s (cap⇒ceiling-≤ fb≤64 blF)
       } }
   , pv-LE refl lp sbF blF
   , refl
   , refl
postPresence-gate frameBytes ctx name BigEndian sb bl
  isSigned factor offset minimum maximum unit presence receivers vds sig fb≤64 eq
  with geometryRefusal frameBytes BigEndian sb bl in g-eq | eq
... | just _  | ()
... | nothing | refl =
  let (lp , sbF , blF , nw) = geometryRefusal-inv-BE frameBytes sb bl g-eq
  in record { def-wf = record
       { startBit-bound  = cap⇒ceiling-< fb≤64 (convertStartBit-BE-inFrame frameBytes sb bl sbF)
       ; bitLength-bound = s≤s (cap⇒ceiling-≤ fb≤64 blF)
       } }
   , pv-BE refl lp (convertStartBit-BE-fits frameBytes sb bl lp sbF nw)
   , convertStartBit-roundtrip frameBytes sb bl lp sbF nw
   , refl

-- ============================================================================
-- COMBINED SIGNAL FIELDS RESULT (single with-chain)
-- ============================================================================

-- If parseSignalFields succeeds, the submitted geometry exists, and the
-- result satisfies the full gate bundle against it.
parseSignalFields-full : ∀ frameBytes ctx name obj sig
  → frameBytes ≤ 64
  → parseSignalFields frameBytes ctx name obj ≡ inj₂ sig
  → ∃₂ λ sb bl →
        (lookupNatStrict "startBit" obj ≡ inj₂ sb)
      × (lookupNatStrict "length" obj ≡ inj₂ bl)
      × SignalGate frameBytes sb bl sig
parseSignalFields-full frameBytes ctx name obj sig fb≤64 eq
  with lookupNatStrict "startBit" obj | eq
... | inj₁ _ | ()
... | inj₂ sb | eq₁
  with lookupNatStrict "length" obj | eq₁
...   | inj₁ _ | ()
...   | inj₂ bl | eq₂
    with lookupChars "byteOrder" obj | eq₂
...     | nothing | ()
...     | just boStr | eq₃
      with parseByteOrder boStr | eq₃
...       | inj₁ _ | ()
...       | inj₂ bo | eq₄
        with parseSigned obj | eq₄
...         | inj₁ _ | ()
...         | inj₂ isSigned | eq₅
          with lookupDecRat "factor" obj | eq₅
...           | inj₁ _ | ()
...           | inj₂ factor | eq₆
            with lookupDecRat "offset" obj | eq₆
...             | inj₁ _ | ()
...             | inj₂ offset | eq₇
              with lookupDecRat "minimum" obj | eq₇
...               | inj₁ _ | ()
...               | inj₂ minimum | eq₈
                with lookupDecRat "maximum" obj | eq₈
...                 | inj₁ _ | ()
...                 | inj₂ maximum | eq₉
                  with lookupChars "unit" obj | eq₉
...                   | nothing | ()
...                   | just unit | eq₁₀
                    with parseSignalPresence obj | eq₁₀
...                     | inj₁ _ | ()
...                     | inj₂ presence | eq₁₁
                      with parseOptionalArray parseCharsList (lookupArray "receivers" obj) | eq₁₁
...                       | inj₁ _ | ()
...                       | inj₂ receivers | eq₁₂
                        with parseOptionalArray parseValueEntryList (lookupArray "valueDescriptions" obj) | eq₁₂
...                         | inj₁ _ | ()
...                         | inj₂ vds | eq₁₃
                          with validateIdent name | eq₁₃
...                           | inj₁ _ | ()
...                           | inj₂ nameId | eq₁₄
                            with validateIdentList receivers | eq₁₄
...                             | inj₁ _ | ()
...                             | inj₂ receiverIds | eq₁₅ =
                                  -- the with-abstraction replaced the two lookup
                                  -- occurrences in the goal with their patterns,
                                  -- so both lookup equations close by refl
                                  sb , bl , refl , refl ,
                                  postPresence-gate frameBytes ctx nameId bo sb bl
                                    isSigned factor offset minimum maximum unit presence
                                    (mkCanonicalFromList receiverIds) vds sig fb≤64 eq₁₅

-- ============================================================================
-- PROJECTIONS (backward-compatible API)
-- ============================================================================

parseSignalFields-wf×pv : ∀ frameBytes ctx name obj sig
  → frameBytes ≤ 64
  → parseSignalFields frameBytes ctx name obj ≡ inj₂ sig
  → WellFormedSignal sig × PhysicallyValid frameBytes sig
parseSignalFields-wf×pv frameBytes ctx name obj sig fb≤64 eq
  with parseSignalFields-full frameBytes ctx name obj sig fb≤64 eq
... | _ , _ , _ , _ , wf , pv , _ = wf , pv

parseSignalFields-wf : ∀ frameBytes ctx name obj sig
  → frameBytes ≤ 64
  → parseSignalFields frameBytes ctx name obj ≡ inj₂ sig → WellFormedSignal sig
parseSignalFields-wf frameBytes ctx name obj sig fb≤64 eq =
  proj₁ (parseSignalFields-wf×pv frameBytes ctx name obj sig fb≤64 eq)

parseSignalFields-pv : ∀ frameBytes ctx name obj sig
  → frameBytes ≤ 64
  → parseSignalFields frameBytes ctx name obj ≡ inj₂ sig → PhysicallyValid frameBytes sig
parseSignalFields-pv frameBytes ctx name obj sig fb≤64 eq =
  proj₂ (parseSignalFields-wf×pv frameBytes ctx name obj sig fb≤64 eq)

-- Geometry-echo faithfulness: the accepted signal's stored geometry maps
-- back (via the formatter's `unconvertStartBit`) to exactly the submitted
-- startBit/length.  `convertStartBit-roundtrip` is consumed by the BE arm
-- of `postPresence-gate` — its hypotheses are the entry gate's conditions.
parseSignalFields-echo : ∀ frameBytes ctx name obj sig
  → frameBytes ≤ 64
  → parseSignalFields frameBytes ctx name obj ≡ inj₂ sig
  → ∃₂ λ sb bl →
        (lookupNatStrict "startBit" obj ≡ inj₂ sb)
      × (lookupNatStrict "length" obj ≡ inj₂ bl)
      × (unconvertStartBit frameBytes (DBCSignal.byteOrder sig)
           (SignalDef.startBit (DBCSignal.signalDef sig))
           (SignalDef.bitLength (DBCSignal.signalDef sig)) ≡ sb)
      × (SignalDef.bitLength (DBCSignal.signalDef sig) ≡ bl)
parseSignalFields-echo frameBytes ctx name obj sig fb≤64 eq
  with parseSignalFields-full frameBytes ctx name obj sig fb≤64 eq
... | sb , bl , sb-look , bl-look , _ , _ , sb-echo , bl-echo =
      sb , bl , sb-look , bl-look , sb-echo , bl-echo

-- ============================================================================
-- SIGNAL WELL-FORMEDNESS
-- ============================================================================

-- If parseSignal succeeds, the result is well-formed.
parseSignal-wf : ∀ frameBytes ctx obj sig
  → frameBytes ≤ 64
  → parseSignal frameBytes ctx obj ≡ inj₂ sig → WellFormedSignal sig
parseSignal-wf frameBytes ctx obj sig fb≤64 eq
  with lookupChars "name" obj | eq
... | nothing | ()
... | just name | eq' = parseSignalFields-wf frameBytes _ name obj sig fb≤64 eq'

-- ============================================================================
-- SIGNAL LIST: SHARED LIFT COMBINATOR
-- ============================================================================

-- Lift a per-element proof over parseSignalList's traversal.
-- P is indexed by frameBytes so it can be either constant (WellFormedSignal)
-- or dependent (PhysicallyValid frameBytes).
private
  parseSignalList-lift : ∀ {P : ℕ → DBCSignal → Set}
    → (∀ frameBytes ctx obj sig → frameBytes ≤ 64
       → parseSignal frameBytes ctx obj ≡ inj₂ sig → P frameBytes sig)
    → ∀ frameBytes ctx jsons idx sigs
    → frameBytes ≤ 64
    → parseSignalList frameBytes ctx jsons idx ≡ inj₂ sigs → All (P frameBytes) sigs
  parseSignalList-lift _ frameBytes ctx [] idx .[] fb≤64 refl = []
  parseSignalList-lift f frameBytes ctx (JObject sigObj ∷ rest) idx sigs fb≤64 eq
    with parseSignal frameBytes ctx sigObj in sig-eq | eq
  ... | inj₁ _ | ()
  ... | inj₂ sig | eq₁
    with parseSignalList frameBytes ctx rest (idx + 1) in rest-eq | eq₁
  ...   | inj₁ _ | ()
  ...   | inj₂ sigs' | refl = f frameBytes ctx sigObj sig fb≤64 sig-eq ∷
                               parseSignalList-lift f frameBytes ctx rest (idx + 1) sigs' fb≤64 rest-eq
  parseSignalList-lift _ frameBytes ctx (JNull     ∷ _) idx sigs fb≤64 ()
  parseSignalList-lift _ frameBytes ctx (JBool _   ∷ _) idx sigs fb≤64 ()
  parseSignalList-lift _ frameBytes ctx (JNumber _ ∷ _) idx sigs fb≤64 ()
  parseSignalList-lift _ frameBytes ctx (JString _ ∷ _) idx sigs fb≤64 ()
  parseSignalList-lift _ frameBytes ctx (JArray _  ∷ _) idx sigs fb≤64 ()

-- ============================================================================
-- SIGNAL LIST WELL-FORMEDNESS
-- ============================================================================

-- If parseSignalList succeeds, all signals are well-formed.
parseSignalList-wf : ∀ frameBytes ctx jsons idx sigs
  → frameBytes ≤ 64
  → parseSignalList frameBytes ctx jsons idx ≡ inj₂ sigs → All WellFormedSignal sigs
parseSignalList-wf = parseSignalList-lift parseSignal-wf

-- ============================================================================
-- SIGNAL PHYSICAL VALIDITY
-- ============================================================================

-- If parseSignal succeeds, the result is physically valid.
parseSignal-pv : ∀ frameBytes ctx obj sig
  → frameBytes ≤ 64
  → parseSignal frameBytes ctx obj ≡ inj₂ sig → PhysicallyValid frameBytes sig
parseSignal-pv frameBytes ctx obj sig fb≤64 eq
  with lookupChars "name" obj | eq
... | nothing | ()
... | just name | eq' = parseSignalFields-pv frameBytes _ name obj sig fb≤64 eq'

-- If parseSignalList succeeds, all signals are physically valid.
parseSignalList-pv : ∀ frameBytes ctx jsons idx sigs
  → frameBytes ≤ 64
  → parseSignalList frameBytes ctx jsons idx ≡ inj₂ sigs
  → All (PhysicallyValid frameBytes) sigs
parseSignalList-pv = parseSignalList-lift parseSignal-pv
