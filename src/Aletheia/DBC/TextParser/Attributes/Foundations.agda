{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 3 3d.5.d 3c-A — cycle-break extraction of Attribute scope
-- parsers from `TextParser/Attributes.agda`.
--
-- Background: 3c-A migrates `parseAttrDef` / `parseAttrDefRel` onto the
-- Format DSL (`Format/AttrDef.agda`).  That requires `TextParser/
-- Attributes.agda` to import `Format`, but `Format` already imports
-- `Properties/Primitives`, which previously imported the scope parsers
-- from `TextParser/Attributes.agda` — a cycle.
--
-- Resolution mirrors the Topology split (3d.5.c-ε): the cycle-relevant
-- subset (the four parsers `Properties/Primitives` actually needs)
-- moves here, and `TextParser/Attributes.agda` re-exports them for
-- backward source compatibility.  No semantic change.
module Aletheia.DBC.TextParser.Attributes.Foundations where

open import Aletheia.Parser.Combinators using
  (Parser; pure; _<|>_; _*>_; _<*_; string)
open import Aletheia.DBC.TextParser.Lexer using (parseWS)

open import Aletheia.DBC.Types using
  ( AttrScope; ASNode; ASMessage; ASSignal; ASEnvVar
  ; ASNetwork; ASNodeMsg; ASNodeSig
  ; AttrType; ATString)

-- ============================================================================
-- SCOPE / TYPE LEXERS — moved from `TextParser/Attributes.agda`
-- ============================================================================

-- Standard scope keyword (BA_DEF_ payload when scope is non-network).
parseStandardScope : Parser AttrScope
parseStandardScope =
  (string "BU_" *> pure ASNode)    <|>
  (string "BO_" *> pure ASMessage) <|>
  (string "SG_" *> pure ASSignal)  <|>
  (string "EV_" *> pure ASEnvVar)

-- Relation scope keyword (BA_DEF_REL_ payload).
parseRelScope : Parser AttrScope
parseRelScope =
  (string "BU_BO_REL_" *> pure ASNodeMsg) <|>
  (string "BU_SG_REL_" *> pure ASNodeSig)

-- BA_DEF_ optional scope: either a standard-scope keyword followed by
-- its own `parseWS` separator, or `ASNetwork` when the scope keyword is
-- absent.  The `<*` chain ensures scope-parsed inputs consume trailing
-- whitespace so the caller can proceed straight to the attribute name.
parseOptionalStandardScope : Parser AttrScope
parseOptionalStandardScope =
  (parseStandardScope <* parseWS) <|> pure ASNetwork

-- `STRING` keyword — emits `ATString` directly.  `parseStringType-
-- roundtrip` (in `Properties/Primitives`) proves the parser is the
-- inverse of `emitAttrType-chars ATString`.
parseStringType : Parser AttrType
parseStringType = string "STRING" *> pure ATString
