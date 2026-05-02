{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 4c task D — `refineAttributes` inverse under WF.
--
-- Two pieces:
--   1. **Passthrough**:
--      `collectRawDefs (map (rawOf defs) attrs) ≡ collectDefs attrs`.
--      Independent of `defs` because `rawOf` is the identity on
--      `DBCAttrDef` (the only constructor `collectRawDefs`/`collectDefs`
--      pick up).
--
--   2. **Inverse under WF**:
--      Under `All (WFAttribute (collectDefs attrs)) attrs`,
--      `refineAttributes (map (rawOf (collectDefs attrs)) attrs) ≡ just attrs`.
--
-- The list-level inverse iterates `refineAttribute defs (rawOf defs a)
-- ≡ just a` (per-element) along the list.  Per-element discharge case-
-- splits on the WFAttribute constructor and routes to the existing
-- `refine*Value-rawOf*-roundtrip-{AVInt,AVFloat,AVString,AVHex,AVEnum}`
-- lemmas in `Properties.Attributes.Common`.
module Aletheia.DBC.TextParser.Properties.Aggregator.Refine where

open import Data.Char  using (Char)
open import Data.List  using (List; []; _∷_; map)
  renaming (_++_ to _++ₗ_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Aletheia.DBC.DecRat.Refinement using
  ( IntDecRat; intDecRatToℤ; mkIntDecRatFromℤ-intDecRatToℤ
  ; NatDecRat; natDecRatToℕ; mkNatDecRatFromℕ-natDecRatToℕ)

open import Aletheia.DBC.Types using
  ( AttrDef; mkAttrDef
  ; AttrDefault; mkAttrDefault
  ; AttrAssign; mkAttrAssign
  ; AttrType; ATInt; ATFloat; ATString; ATEnum; ATHex
  ; AttrValue; AVInt; AVFloat; AVString; AVEnum; AVHex
  ; DBCAttribute; DBCAttrDef; DBCAttrDefault; DBCAttrAssign
  )

open import Aletheia.DBC.TextParser.Attributes using
  ( RawDBCAttribute; RawDef; RawDefault; RawAssign
  ; RawAttrDefault; mkRawAttrDefault
  ; RawAttrAssign; mkRawAttrAssign
  ; RawAttrValue; RavString; RavDecRat
  ; refineAttribute; refineAttributes; refineAll
  ; refineDefaultValue; refineAssignValue
  ; collectRawDefs; lookupDef
  ; decRatToℤ?; decRatToℕ?
  )
open import Aletheia.DBC.TextFormatter.Attributes using
  (collectDefs)

open import Aletheia.DBC.TextParser.Properties.Aggregator.Foundations using
  ( WFAttribute; wfDef; wfDefault; wfAssign
  ; DefaultEnumOK
  ; rawOf
  )

open import Aletheia.DBC.TextParser.Properties.Attributes.Common using
  ( ValueMatchesType
  ; VMTInt; VMTFloat; VMTString; VMTEnum; VMTHex
  ; refineAssignValue-rawOfAssign-roundtrip
  ; refineDefaultValue-rawOfDefault-roundtrip-AVInt
  ; refineDefaultValue-rawOfDefault-roundtrip-AVFloat
  ; refineDefaultValue-rawOfDefault-roundtrip-AVString
  ; refineDefaultValue-rawOfDefault-roundtrip-AVHex
  ; refineDefaultValue-rawOfDefault-roundtrip-AVEnum
  ; decRatToℤ?-IntDecRat-value
  ; decRatToℕ?-NatDecRat-value
  )

-- ============================================================================
-- 1. PASSTHROUGH — `collectRawDefs ∘ map (rawOf defs) ≡ collectDefs`
-- ============================================================================

collectRawDefs-rawOf :
    ∀ (defs : List AttrDef) (attrs : List DBCAttribute)
  → collectRawDefs (map (rawOf defs) attrs) ≡ collectDefs attrs
collectRawDefs-rawOf defs []                       = refl
collectRawDefs-rawOf defs (DBCAttrDef d ∷ rest)    =
  cong (d ∷_) (collectRawDefs-rawOf defs rest)
collectRawDefs-rawOf defs (DBCAttrDefault _ ∷ rest) =
  collectRawDefs-rawOf defs rest
collectRawDefs-rawOf defs (DBCAttrAssign _ ∷ rest)  =
  collectRawDefs-rawOf defs rest

-- ============================================================================
-- 2a. PER-ATTRIBUTE INVERSE — `refineAttribute defs (rawOf defs a) ≡ just a`
-- ============================================================================
--
-- WFAttribute case dispatch.  For each constructor we destructure the
-- AttrDefault / AttrAssign / AttrDef record so its fields are constructor-
-- form (so `rawOfDefaultValue-with-defs` reduces past `with value d`),
-- pattern-match on VMT to fix `attrType def` and `value d / value a`,
-- `rewrite lookup-eq` to discharge the parser-side `with lookupDef`
-- branch, then chain the value-shape `decRat*?-*-value` + `mk*FromX-*-Y`
-- rewrites that the existing per-AttrValue refine-roundtrip lemmas
-- (in `Properties.Attributes.Common`) use.

refineAttribute-rawOf-Def :
    ∀ (defs : List AttrDef) (d : AttrDef)
  → refineAttribute defs (rawOf defs (DBCAttrDef d)) ≡ just (DBCAttrDef d)
refineAttribute-rawOf-Def _ _ = refl

refineAttribute-rawOf-Default :
    ∀ (defs : List AttrDef) (d : AttrDefault) (def : AttrDef)
  → lookupDef (AttrDefault.name d) defs ≡ just def
  → ValueMatchesType (AttrDef.attrType def) (AttrDefault.value d)
  → DefaultEnumOK    (AttrDef.attrType def) (AttrDefault.value d)
  → refineAttribute defs (rawOf defs (DBCAttrDefault d)) ≡ just (DBCAttrDefault d)
refineAttribute-rawOf-Default defs
  (mkAttrDefault n .(AVInt z))
  (mkAttrDef _ _ .(ATInt _ _))
  lookup-eq (VMTInt z) _
  rewrite lookup-eq
        | decRatToℤ?-IntDecRat-value z
        | mkIntDecRatFromℤ-intDecRatToℤ z = refl
refineAttribute-rawOf-Default defs
  (mkAttrDefault n .(AVFloat q))
  (mkAttrDef _ _ .(ATFloat _ _))
  lookup-eq (VMTFloat q) _
  rewrite lookup-eq = refl
refineAttribute-rawOf-Default defs
  (mkAttrDefault n .(AVString s))
  (mkAttrDef _ _ .ATString)
  lookup-eq (VMTString s) _
  rewrite lookup-eq = refl
refineAttribute-rawOf-Default defs
  (mkAttrDefault n .(AVHex k))
  (mkAttrDef _ _ .(ATHex _ _))
  lookup-eq (VMTHex k) _
  rewrite lookup-eq
        | decRatToℕ?-NatDecRat-value k
        | mkNatDecRatFromℕ-natDecRatToℕ k = refl
refineAttribute-rawOf-Default defs
  (mkAttrDefault n .(AVEnum k))
  (mkAttrDef _ _ .(ATEnum _))
  lookup-eq (VMTEnum {ls} k) enumOK
  rewrite lookup-eq
        | enumOK
        | mkNatDecRatFromℕ-natDecRatToℕ k = refl

refineAttribute-rawOf-Assign :
    ∀ (defs : List AttrDef) (a : AttrAssign) (def : AttrDef)
  → lookupDef (AttrAssign.name a) defs ≡ just def
  → ValueMatchesType (AttrDef.attrType def) (AttrAssign.value a)
  → refineAttribute defs (rawOf defs (DBCAttrAssign a)) ≡ just (DBCAttrAssign a)
refineAttribute-rawOf-Assign defs
  (mkAttrAssign n tgt .(AVInt z))
  (mkAttrDef _ _ .(ATInt _ _))
  lookup-eq (VMTInt z)
  rewrite lookup-eq
        | decRatToℤ?-IntDecRat-value z
        | mkIntDecRatFromℤ-intDecRatToℤ z = refl
refineAttribute-rawOf-Assign defs
  (mkAttrAssign n tgt .(AVFloat q))
  (mkAttrDef _ _ .(ATFloat _ _))
  lookup-eq (VMTFloat q)
  rewrite lookup-eq = refl
refineAttribute-rawOf-Assign defs
  (mkAttrAssign n tgt .(AVString s))
  (mkAttrDef _ _ .ATString)
  lookup-eq (VMTString s)
  rewrite lookup-eq = refl
refineAttribute-rawOf-Assign defs
  (mkAttrAssign n tgt .(AVHex k))
  (mkAttrDef _ _ .(ATHex _ _))
  lookup-eq (VMTHex k)
  rewrite lookup-eq
        | decRatToℕ?-NatDecRat-value k
        | mkNatDecRatFromℕ-natDecRatToℕ k = refl
refineAttribute-rawOf-Assign defs
  (mkAttrAssign n tgt .(AVEnum k))
  (mkAttrDef _ _ .(ATEnum _))
  lookup-eq (VMTEnum k)
  rewrite lookup-eq
        | decRatToℕ?-NatDecRat-value k
        | mkNatDecRatFromℕ-natDecRatToℕ k = refl

refineAttribute-rawOf :
    ∀ (defs : List AttrDef) (a : DBCAttribute)
  → WFAttribute defs a
  → refineAttribute defs (rawOf defs a) ≡ just a
refineAttribute-rawOf defs (DBCAttrDef d)     (wfDef _ _)                  =
  refineAttribute-rawOf-Def     defs d
refineAttribute-rawOf defs (DBCAttrDefault d) (wfDefault _ def le vmt eok) =
  refineAttribute-rawOf-Default defs d def le vmt eok
refineAttribute-rawOf defs (DBCAttrAssign a)  (wfAssign  _ def le vmt)     =
  refineAttribute-rawOf-Assign  defs a def le vmt

-- ============================================================================
-- 2b. LIST-LEVEL INVERSE — `refineAll defs (map (rawOf defs) attrs) ≡ just attrs`
-- ============================================================================

refineAll-on-rawOf :
    ∀ (defs : List AttrDef) (attrs : List DBCAttribute)
  → All (WFAttribute defs) attrs
  → refineAll defs (map (rawOf defs) attrs) ≡ just attrs
refineAll-on-rawOf _    []           []          = refl
refineAll-on-rawOf defs (a ∷ attrs)  (wfa ∷ wfs)
  rewrite refineAttribute-rawOf defs a wfa
        | refineAll-on-rawOf defs attrs wfs = refl

-- ============================================================================
-- 2c. TOP-LEVEL — `refineAttributes (map (rawOf D) attrs) ≡ just attrs`
-- ============================================================================
--
-- `refineAttributes` is `refineAll (collectRawDefs raws) raws`.  When
-- `raws = map (rawOf (collectDefs attrs)) attrs`, we have
-- `collectRawDefs raws = collectDefs attrs` (passthrough), so the inner
-- defs argument matches the formatter-side ambient defs and the
-- per-attribute inverse fires uniformly.

refineAttributes-on-rawOf :
    ∀ (attrs : List DBCAttribute)
  → All (WFAttribute (collectDefs attrs)) attrs
  → refineAttributes (map (rawOf (collectDefs attrs)) attrs) ≡ just attrs
refineAttributes-on-rawOf attrs wfs
  rewrite collectRawDefs-rawOf (collectDefs attrs) attrs =
    refineAll-on-rawOf (collectDefs attrs) attrs wfs
