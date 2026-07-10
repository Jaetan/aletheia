-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Per-line-construct roundtrips for the DBC attribute section — facade
-- module.
--
-- Re-exports `parseAttrDef-roundtrip` and `parseAttrDefRel-roundtrip`
-- from `Properties/Attributes/Def.agda`, plus their well-formedness
-- predicates (`WfAttrType`, `WfAttrDef-NotRel`, `WfAttrDef-Rel`).
-- Future commits add `parseRawAttrDefault-roundtrip`,
-- `parseRawAttrAssign-roundtrip`, `parseRawAttrRel-roundtrip`, and the
-- top-level `parseAttrLine-roundtrip` 5-way `<|>` dispatch composer.
--
-- Sub-files:
--   * Properties/Attributes/Common.agda — refinement-types bridges
--     (IntDecRat / NatDecRat construction lemmas, parseDecRat-suffix
--     compositions).
--   * Properties/Attributes/Def.agda    — `parseAttrDef` and
--     `parseAttrDefRel` per-line construct roundtrips — slim wrappers
--     around the universal `parseAttrDef-format-
--     roundtrip` / `parseAttrDefRel-format-roundtrip` (in `Format/
--     AttrDef.agda`).  The standalone per-tag `parseAttrTypeDecl-
--     roundtrip-AT*` lemmas (formerly in `Properties/Attributes/
--     Type.agda`) are subsumed by the universal Format DSL roundtrip;
--     `Properties/Attributes/Type.agda` was removed in the migration.
module Aletheia.DBC.TextParser.Properties.Attributes where

-- Refinement-types bridges.  Used by per-line value proofs to roundtrip
-- `AttrValue ↔ RawAttrValue` under
-- the well-formedness predicate `ValueMatchesType`.
open import Aletheia.DBC.TextParser.Properties.Attributes.Common public
  using ( )

-- Per-line construct roundtrips.
open import Aletheia.DBC.TextParser.Properties.Attributes.Def public
  using ( )

-- Per-line construct roundtrips (parseRawAttrDefault, BA_DEF_DEF_).
-- Three top-level cases by emit shape: RavString, RavDecRat-frac,
-- RavDecRat-bareInt.  The composer dispatches typed AttrValue → raw form via
-- `Common.rawOfDefaultValue` and the matching value-emit equality.
open import Aletheia.DBC.TextParser.Properties.Attributes.Default public
  using ( )

-- Per-line construct roundtrips (parseRawAttrAssign, BA_; and
-- parseRawAttrRel, BA_REL_).  21 dispatchers total: 5 standard targets ×
-- 3 emit shapes + 2 rel targets × 3 emit shapes.  See sub-facade
-- `Aletheia.DBC.TextParser.Properties.Attributes.Assign` for the full
-- catalog (per-target sub-files: Network/Node/Message/Signal/EnvVar/Rel).
open import Aletheia.DBC.TextParser.Properties.Attributes.Assign public
  using ( -- Standard target dispatchers (parseRawAttrAssign):
        -- Rel target dispatchers (parseRawAttrRel):
        )

-- Per-line construct roundtrips (`parseAttrLine` 5-way `<|>`
-- dispatch composer).  31 dispatchers covering every input shape:
-- 2 alt1 (RawDef-Rel × {NodeMsg, NodeSig}), 3 alt2 (RawDefault × 3
-- emit shapes), 5 alt3 (RawDef-NotRel × {Network/Node/Message/Signal/
-- EnvVar}), 6 alt4 (RawAssign-Rel × 3 emit shapes), 15 alt5
-- (RawAssign × 5 standard targets × 3 emit shapes).
open import Aletheia.DBC.TextParser.Properties.Attributes.Line public
  using ( )

-- alt5 dispatchers — extracted
-- into `Properties.Attributes.Line.Alt5` to bring `Line.agda` under
-- the 800-LOC trigger.  Re-exported here so the public API surface is
-- unchanged for downstream consumers (Frac / BareInt / String / Default
-- / Def dispatchers).
open import Aletheia.DBC.TextParser.Properties.Attributes.Line.Alt5 public
  using ( )
