{-# OPTIONS --without-K #-}

-- Per-line-construct roundtrips for the DBC attribute section (B.3.d
-- Layer 3 Commit 3c) — facade module.
--
-- Re-exports `parseAttrDef-roundtrip` and `parseAttrDefRel-roundtrip`
-- from `Properties/Attributes/Def.agda`, plus their well-formedness
-- predicates (`WfAttrType`, `WfAttrDef-NotRel`, `WfAttrDef-Rel`).
-- Future commits in the 3c series add `parseRawAttrDefault-roundtrip`,
-- `parseRawAttrAssign-roundtrip`, `parseRawAttrRel-roundtrip`, and the
-- top-level `parseAttrLine-roundtrip` 5-way `<|>` dispatch composer.
--
-- Sub-files:
--   * Properties/Attributes/Common.agda — refinement-types bridges
--     (IntDecRat / NatDecRat construction lemmas, parseDecRat-suffix
--     compositions).
--   * Properties/Attributes/Type.agda   — per-tag attribute-type
--     roundtrips for `parseAttrTypeDecl` (5-way dispatch over INT /
--     FLOAT / STRING / ENUM / HEX).
--   * Properties/Attributes/Def.agda    — `parseAttrDef` and
--     `parseAttrDefRel` per-line construct roundtrips (this commit).
module Aletheia.DBC.TextParser.Properties.Attributes where

-- Refinement-types bridges (3c precursor).  Used by 3c.2 / 3c.3
-- per-line value proofs to roundtrip `AttrValue ↔ RawAttrValue` under
-- the well-formedness predicate `ValueMatchesType`.
open import Aletheia.DBC.TextParser.Properties.Attributes.Common public
  using ( ValueMatchesType; VMTInt; VMTFloat; VMTString; VMTEnum; VMTHex
        ; rawOfAssignValue; rawOfDefaultValue
        ; refineAssignValue-rawOfAssign-roundtrip
        ; refineDefaultValue-rawOfDefault-roundtrip-AVInt
        ; refineDefaultValue-rawOfDefault-roundtrip-AVFloat
        ; refineDefaultValue-rawOfDefault-roundtrip-AVString
        ; refineDefaultValue-rawOfDefault-roundtrip-AVHex
        ; refineDefaultValue-rawOfDefault-roundtrip-AVEnum)

-- Per-line construct roundtrips (3c.1).
open import Aletheia.DBC.TextParser.Properties.Attributes.Def public
  using ( WfAttrType; WfATInt; WfATFloat; WfATString; WfATEnum; WfATHex
        ; WfAttrDef-NotRel; Wf-Network; Wf-Node; Wf-Message; Wf-Signal; Wf-EnvVar
        ; WfAttrDef-Rel;    Wf-NodeMsg; Wf-NodeSig
        ; parseAttrDef-roundtrip
        ; parseAttrDefRel-roundtrip)

-- Per-line construct roundtrips (3c.2 — parseRawAttrDefault, BA_DEF_DEF_).
-- Three top-level cases by emit shape: RavString, RavDecRat-frac,
-- RavDecRat-bareInt.  Layer 4 dispatches typed AttrValue → raw form via
-- `Common.rawOfDefaultValue` and the matching value-emit equality.
open import Aletheia.DBC.TextParser.Properties.Attributes.Default public
  using ( parseRawAttrValue-roundtrip-RavString
        ; parseRawAttrValue-roundtrip-RavDecRatFrac
        ; parseRawAttrValue-roundtrip-RavDecRatBareInt
        ; parseRawAttrDefault-after-keyword
        ; parseRawAttrDefault-roundtrip-RavString
        ; parseRawAttrDefault-roundtrip-RavDecRatFrac
        ; parseRawAttrDefault-roundtrip-RavDecRatBareInt)
