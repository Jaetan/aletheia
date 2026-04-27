{-# OPTIONS --safe --without-K #-}

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

-- Per-line construct roundtrips (3c.3 — parseRawAttrAssign, BA_; and
-- parseRawAttrRel, BA_REL_).  21 dispatchers total: 5 standard targets ×
-- 3 emit shapes + 2 rel targets × 3 emit shapes.  See sub-facade
-- `Aletheia.DBC.TextParser.Properties.Attributes.Assign` for the full
-- catalog (per-target sub-files: Network/Node/Message/Signal/EnvVar/Rel).
open import Aletheia.DBC.TextParser.Properties.Attributes.Assign public
  using ( IdentNameStop
        -- Standard target dispatchers (parseRawAttrAssign):
        ; parseRawAttrAssign-roundtrip-ATgtNetwork-RavString
        ; parseRawAttrAssign-roundtrip-ATgtNetwork-RavDecRatFrac
        ; parseRawAttrAssign-roundtrip-ATgtNetwork-RavDecRatBareInt
        ; parseRawAttrAssign-roundtrip-ATgtNode-RavString
        ; parseRawAttrAssign-roundtrip-ATgtNode-RavDecRatFrac
        ; parseRawAttrAssign-roundtrip-ATgtNode-RavDecRatBareInt
        ; parseRawAttrAssign-roundtrip-ATgtMessage-RavString
        ; parseRawAttrAssign-roundtrip-ATgtMessage-RavDecRatFrac
        ; parseRawAttrAssign-roundtrip-ATgtMessage-RavDecRatBareInt
        ; parseRawAttrAssign-roundtrip-ATgtSignal-RavString
        ; parseRawAttrAssign-roundtrip-ATgtSignal-RavDecRatFrac
        ; parseRawAttrAssign-roundtrip-ATgtSignal-RavDecRatBareInt
        ; parseRawAttrAssign-roundtrip-ATgtEnvVar-RavString
        ; parseRawAttrAssign-roundtrip-ATgtEnvVar-RavDecRatFrac
        ; parseRawAttrAssign-roundtrip-ATgtEnvVar-RavDecRatBareInt
        -- Rel target dispatchers (parseRawAttrRel):
        ; parseRawAttrRel-roundtrip-ATgtNodeMsg-RavString
        ; parseRawAttrRel-roundtrip-ATgtNodeMsg-RavDecRatFrac
        ; parseRawAttrRel-roundtrip-ATgtNodeMsg-RavDecRatBareInt
        ; parseRawAttrRel-roundtrip-ATgtNodeSig-RavString
        ; parseRawAttrRel-roundtrip-ATgtNodeSig-RavDecRatFrac
        ; parseRawAttrRel-roundtrip-ATgtNodeSig-RavDecRatBareInt)

-- Per-line construct roundtrips (3c.4 — `parseAttrLine` 5-way `<|>`
-- dispatch composer).  31 dispatchers covering every input shape:
-- 2 alt1 (RawDef-Rel × {NodeMsg, NodeSig}), 3 alt2 (RawDefault × 3
-- emit shapes), 5 alt3 (RawDef-NotRel × {Network/Node/Message/Signal/
-- EnvVar}), 6 alt4 (RawAssign-Rel × 3 emit shapes), 15 alt5
-- (RawAssign × 5 standard targets × 3 emit shapes).
open import Aletheia.DBC.TextParser.Properties.Attributes.Line public
  using ( parseAttrLine-roundtrip-RawDef-Rel-NodeMsg
        ; parseAttrLine-roundtrip-RawDef-Rel-NodeSig
        ; parseAttrLine-roundtrip-RawDefault-RavString
        ; parseAttrLine-roundtrip-RawDefault-RavDecRatFrac
        ; parseAttrLine-roundtrip-RawDefault-RavDecRatBareInt
        ; parseAttrLine-roundtrip-RawDef-NotRel-Network
        ; parseAttrLine-roundtrip-RawDef-NotRel-Node
        ; parseAttrLine-roundtrip-RawDef-NotRel-Message
        ; parseAttrLine-roundtrip-RawDef-NotRel-Signal
        ; parseAttrLine-roundtrip-RawDef-NotRel-EnvVar
        ; parseAttrLine-roundtrip-RawAssign-ATgtNodeMsg-RavString
        ; parseAttrLine-roundtrip-RawAssign-ATgtNodeMsg-RavDecRatFrac
        ; parseAttrLine-roundtrip-RawAssign-ATgtNodeMsg-RavDecRatBareInt
        ; parseAttrLine-roundtrip-RawAssign-ATgtNodeSig-RavString
        ; parseAttrLine-roundtrip-RawAssign-ATgtNodeSig-RavDecRatFrac
        ; parseAttrLine-roundtrip-RawAssign-ATgtNodeSig-RavDecRatBareInt
        ; parseAttrLine-roundtrip-RawAssign-ATgtNetwork-RavString
        ; parseAttrLine-roundtrip-RawAssign-ATgtNetwork-RavDecRatFrac
        ; parseAttrLine-roundtrip-RawAssign-ATgtNetwork-RavDecRatBareInt
        ; parseAttrLine-roundtrip-RawAssign-ATgtNode-RavString
        ; parseAttrLine-roundtrip-RawAssign-ATgtNode-RavDecRatFrac
        ; parseAttrLine-roundtrip-RawAssign-ATgtNode-RavDecRatBareInt
        ; parseAttrLine-roundtrip-RawAssign-ATgtMessage-RavString
        ; parseAttrLine-roundtrip-RawAssign-ATgtMessage-RavDecRatFrac
        ; parseAttrLine-roundtrip-RawAssign-ATgtMessage-RavDecRatBareInt
        ; parseAttrLine-roundtrip-RawAssign-ATgtSignal-RavString
        ; parseAttrLine-roundtrip-RawAssign-ATgtSignal-RavDecRatFrac
        ; parseAttrLine-roundtrip-RawAssign-ATgtSignal-RavDecRatBareInt
        ; parseAttrLine-roundtrip-RawAssign-ATgtEnvVar-RavString
        ; parseAttrLine-roundtrip-RawAssign-ATgtEnvVar-RavDecRatFrac
        ; parseAttrLine-roundtrip-RawAssign-ATgtEnvVar-RavDecRatBareInt)
