{-# OPTIONS --without-K #-}

-- Foundations for the B.3.d Layer 3 Commit 3c attribute roundtrip
-- proofs (`BA_DEF_` / `BA_DEF_REL_` / `BA_DEF_DEF_` / `BA_` / `BA_REL_`).
--
-- After the 3c-pre refinement-type refactor, `AttrValue.AVInt` carries
-- `IntDecRat`, `AVHex`/`AVEnum` carry `NatDecRat`.  The DecRat path
-- covers every numeric form via `parseDecRat` (extended to accept
-- bare-integer wire shape — `BA_ "X" 50;`-style — by treating the
-- integer as `mkDecRat 50 0 0`).
--
-- This module hosts:
--   * `rawOfAssignValue` / `rawOfDefaultValue` — the typed `AttrValue
--     → RawAttrValue` map mirroring `emit*Value-chars`.  Numeric values
--     unwrap their refinement-type wrapper to expose the underlying
--     `DecRat` directly (no need for `fromℤ ∘ intDecRatToℤ` round-trip
--     since the refinement value already carries the canonical
--     integer-shape DecRat).
--   * Per-case `refine*Value` roundtrip lemmas — `refine*Value ty
--     (rawOf*Value [ty] v) ≡ just v` under the well-formedness
--     assumption `ValueMatchesType ty v`.
--
-- The `ATEnum` × `AVEnum` default-context case requires the new
-- Layer-4 debt `findLabel-nthLabel-roundtrip` (label uniqueness +
-- index bound).  Per `memory/project_b3d_layer4_owed_lemmas.md`, the
-- precondition is stated here as a hypothesis and discharged at
-- Layer 4.
module Aletheia.DBC.TextParser.Properties.Attributes.Common where

open import Data.Bool using (Bool; true; false; T)
open import Data.Char using (Char)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (List; []; _∷_; length) renaming (_++_ to _++ₗ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.String using (String; toList)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)

open import Aletheia.DBC.DecRat using (DecRat; mkDecRat; fromℤ; 0ᵈ)
open import Aletheia.DBC.DecRat.Refinement using
  ( IntDecRat; mkIntDecRat; mkIntDecRatFromℤ
  ; intDecRatToℤ; intDecRatToℤ-mkIntDecRatFromℤ
  ; mkIntDecRatFromℤ-intDecRatToℤ
  ; NatDecRat; mkNatDecRat; mkNatDecRatFromℕ
  ; natDecRatToℕ; natDecRatToℕ-mkNatDecRatFromℕ
  ; mkNatDecRatFromℕ-natDecRatToℕ)
open import Aletheia.DBC.Types using
  ( AttrScope; ASNetwork; ASNode; ASMessage; ASSignal; ASEnvVar
  ; ASNodeMsg; ASNodeSig
  ; AttrType; ATInt; ATFloat; ATString; ATEnum; ATHex
  ; AttrValue; AVInt; AVFloat; AVString; AVEnum; AVHex
  ; AttrTarget; ATgtNetwork; ATgtNode; ATgtMessage; ATgtSignal
  ; ATgtEnvVar; ATgtNodeMsg; ATgtNodeSig
  ; AttrDef; AttrDefault; AttrAssign
  ; DBCAttribute; DBCAttrDef; DBCAttrDefault; DBCAttrAssign
  ; attrDefNameStr; attrDefaultNameStr; attrAssignNameStr
  )
open import Aletheia.DBC.TextParser.Attributes using
  ( RawAttrValue; RavString; RavDecRat
  ; RawAttrDefault; mkRawAttrDefault
  ; RawAttrAssign; mkRawAttrAssign
  ; RawDBCAttribute; RawDef; RawDefault; RawAssign
  ; decRatToℤ?; decRatToℕ?
  ; findLabel
  ; refineDefaultValue; refineAssignValue
  )
open import Aletheia.DBC.TextFormatter.Attributes using
  (nthLabel)

-- ============================================================================
-- DECRAT PROJECTION ROUNDTRIPS (used by per-line proofs downstream)
-- ============================================================================

-- The integer-projection roundtrip on `IntDecRat` is structural — the
-- numerator extracted by `intDecRatToℤ` round-trips through `fromℤ` to
-- the same canonical DecRat, modulo `T`-witness irrelevance.  Used by
-- the 3c per-line proofs whenever they project an `IntDecRat` to wire
-- form (`showInt-chars (intDecRatToℤ v)`) and need to recover the
-- typed value.

decRatToℤ?-IntDecRat-value : ∀ v → decRatToℤ? (IntDecRat.value v) ≡ just (intDecRatToℤ v)
decRatToℤ?-IntDecRat-value (mkIntDecRat (mkDecRat _ zero    zero    _) _)  = refl
decRatToℤ?-IntDecRat-value (mkIntDecRat (mkDecRat _ zero    (suc _) _) ())
decRatToℤ?-IntDecRat-value (mkIntDecRat (mkDecRat _ (suc _) _       _) ())

decRatToℕ?-NatDecRat-value : ∀ v → decRatToℕ? (NatDecRat.value v) ≡ just (natDecRatToℕ v)
decRatToℕ?-NatDecRat-value (mkNatDecRat (mkDecRat (+ _)    zero    zero    _) _)  = refl
decRatToℕ?-NatDecRat-value (mkNatDecRat (mkDecRat (+ _)    zero    (suc _) _) ())
decRatToℕ?-NatDecRat-value (mkNatDecRat (mkDecRat (+ _)    (suc _) _       _) ())
decRatToℕ?-NatDecRat-value (mkNatDecRat (mkDecRat -[1+ _ ] _       _       _) ())

-- ============================================================================
-- WELL-FORMEDNESS — value constructor matches attribute type
-- ============================================================================
--
-- `DBCAttribute` carries `AttrValue` independently of the looked-up
-- `AttrType`; a hand-built DBC could (in principle) place an `AVFloat`
-- under an `ATInt`-typed name.  The roundtrip target only quantifies
-- over well-formed `DBCAttribute` lists, where each value's
-- constructor matches the looked-up def's type.  This relation
-- captures the pairing.

data ValueMatchesType : AttrType → AttrValue → Set where
  VMTInt    : ∀ {mn mx} z → ValueMatchesType (ATInt mn mx)   (AVInt z)
  VMTFloat  : ∀ {mn mx} d → ValueMatchesType (ATFloat mn mx) (AVFloat d)
  VMTString : ∀ s         → ValueMatchesType ATString        (AVString s)
  VMTEnum   : ∀ {ls} n    → ValueMatchesType (ATEnum ls)     (AVEnum n)
  VMTHex    : ∀ {mn mx} n → ValueMatchesType (ATHex mn mx)   (AVHex n)

-- ============================================================================
-- RAW VALUE EMISSION (formatter ↔ raw-form bridge)
-- ============================================================================
--
-- `rawOfAssignValue` mirrors `emitAssignValue-chars`: every numeric
-- value is normalised to `RavDecRat` carrying the underlying DecRat
-- of the refinement-type wrapper.

rawOfAssignValue : AttrValue → RawAttrValue
rawOfAssignValue (AVInt z)    = RavDecRat (IntDecRat.value z)
rawOfAssignValue (AVFloat d)  = RavDecRat d
rawOfAssignValue (AVString s) = RavString s
rawOfAssignValue (AVEnum n)   = RavDecRat (NatDecRat.value n)
rawOfAssignValue (AVHex n)    = RavDecRat (NatDecRat.value n)

-- `rawOfDefaultValue` mirrors `emitDefaultValue-chars`: ENUM defaults
-- emit the *label string* (not the index), routed through the AttrType
-- list of labels.  All other AttrType / AttrValue pairs are
-- defs-context-independent.
rawOfDefaultValue : AttrType → AttrValue → RawAttrValue
rawOfDefaultValue _           (AVInt z)    = RavDecRat (IntDecRat.value z)
rawOfDefaultValue _           (AVFloat d)  = RavDecRat d
rawOfDefaultValue _           (AVString s) = RavString s
rawOfDefaultValue (ATEnum ls) (AVEnum n)   = RavString (nthLabel (natDecRatToℕ n) ls)
rawOfDefaultValue _           (AVEnum _)   = RavString ""
rawOfDefaultValue _           (AVHex n)    = RavDecRat (NatDecRat.value n)

-- ============================================================================
-- ASSIGN VALUE — REFINE ROUNDTRIP
-- ============================================================================

refineAssignValue-rawOfAssign-roundtrip :
  ∀ ty v → ValueMatchesType ty v
  → refineAssignValue ty (rawOfAssignValue v) ≡ just v
refineAssignValue-rawOfAssign-roundtrip
  (ATInt _ _) (AVInt z) (VMTInt _)
  rewrite decRatToℤ?-IntDecRat-value z | mkIntDecRatFromℤ-intDecRatToℤ z = refl
refineAssignValue-rawOfAssign-roundtrip
  (ATFloat _ _) (AVFloat d) (VMTFloat _) = refl
refineAssignValue-rawOfAssign-roundtrip
  ATString (AVString s) (VMTString _) = refl
refineAssignValue-rawOfAssign-roundtrip
  (ATEnum _) (AVEnum n) (VMTEnum _)
  rewrite decRatToℕ?-NatDecRat-value n | mkNatDecRatFromℕ-natDecRatToℕ n = refl
refineAssignValue-rawOfAssign-roundtrip
  (ATHex _ _) (AVHex n) (VMTHex _)
  rewrite decRatToℕ?-NatDecRat-value n | mkNatDecRatFromℕ-natDecRatToℕ n = refl

-- ============================================================================
-- DEFAULT VALUE — REFINE ROUNDTRIP (non-enum cases)
-- ============================================================================

refineDefaultValue-rawOfDefault-roundtrip-AVInt :
  ∀ mn mx z
  → refineDefaultValue (ATInt mn mx) (rawOfDefaultValue (ATInt mn mx) (AVInt z))
    ≡ just (AVInt z)
refineDefaultValue-rawOfDefault-roundtrip-AVInt mn mx z
  rewrite decRatToℤ?-IntDecRat-value z | mkIntDecRatFromℤ-intDecRatToℤ z = refl

refineDefaultValue-rawOfDefault-roundtrip-AVFloat :
  ∀ mn mx d
  → refineDefaultValue (ATFloat mn mx) (rawOfDefaultValue (ATFloat mn mx) (AVFloat d))
    ≡ just (AVFloat d)
refineDefaultValue-rawOfDefault-roundtrip-AVFloat _ _ _ = refl

refineDefaultValue-rawOfDefault-roundtrip-AVString :
  ∀ s
  → refineDefaultValue ATString (rawOfDefaultValue ATString (AVString s))
    ≡ just (AVString s)
refineDefaultValue-rawOfDefault-roundtrip-AVString _ = refl

refineDefaultValue-rawOfDefault-roundtrip-AVHex :
  ∀ mn mx n
  → refineDefaultValue (ATHex mn mx) (rawOfDefaultValue (ATHex mn mx) (AVHex n))
    ≡ just (AVHex n)
refineDefaultValue-rawOfDefault-roundtrip-AVHex mn mx n
  rewrite decRatToℕ?-NatDecRat-value n | mkNatDecRatFromℕ-natDecRatToℕ n = refl

-- ============================================================================
-- DEFAULT VALUE — ENUM-DEFAULT BRIDGE LEMMA (Layer-4 debt)
-- ============================================================================
--
-- ENUM defaults wire as label strings (`"Normal"`); semantic form is
-- the 0-based label index (now wrapped in `NatDecRat`).  Roundtrip
-- closure requires the Layer-4 bridge `findLabel (nthLabel n ls) ls
-- ≡ just n`, which depends on label uniqueness + index bound — see
-- `memory/project_b3d_layer4_owed_lemmas.md` entries #4 / #5.

refineDefaultValue-rawOfDefault-roundtrip-AVEnum :
  ∀ ls n
  → findLabel (nthLabel (natDecRatToℕ n) ls) ls ≡ just (natDecRatToℕ n)
  → refineDefaultValue (ATEnum ls) (rawOfDefaultValue (ATEnum ls) (AVEnum n))
    ≡ just (AVEnum n)
refineDefaultValue-rawOfDefault-roundtrip-AVEnum ls n bridge
  rewrite bridge | mkNatDecRatFromℕ-natDecRatToℕ n = refl
