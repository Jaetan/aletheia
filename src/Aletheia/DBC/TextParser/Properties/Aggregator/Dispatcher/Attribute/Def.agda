{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 4c — Universal-attribute roundtrip dispatcher for the
-- `DBCAttrDef` shape.
--
-- 7-way dispatch on `AttrDef.scope`:
--   * ASNetwork / ASNode / ASMessage / ASSignal / ASEnvVar
--     → forward to per-scope NotRel slim.
--   * ASNodeMsg / ASNodeSig → forward to per-scope Rel slim.
--
-- The slim's input shape (`emitAttrDef-chars (mkAttrDef name <Scope> ty) ++
-- outer-suffix`) is definitionally equal to the universal form
-- (`emitAttribute-chars defs (DBCAttrDef d) ++ outer`) once `d` is destructured
-- and `scope` pattern-matched, so no input bridge is needed.  Likewise the
-- result `RawDef (mkAttrDef ...)` matches `rawOf defs (DBCAttrDef d)` directly.
--
-- WfAttrType (carried by WFAttribute.wfDef) provides the ENUM-non-empty
-- precondition that the slim's `parseAttrDef-roundtrip` requires.
module Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Attribute.Def where

open import Data.Char  using (Char)
open import Data.List  using (List; []; _∷_)
  renaming (_++_ to _++ₗ_)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)

open import Aletheia.Parser.Combinators using
  (Position; ParseResult; mkResult; advancePositions)

open import Aletheia.DBC.Types using
  ( AttrDef; mkAttrDef
  ; AttrScope
  ; ASNetwork; ASNode; ASMessage; ASSignal; ASEnvVar
  ; ASNodeMsg; ASNodeSig
  ; DBCAttribute; DBCAttrDef
  )

open import Aletheia.DBC.TextFormatter.Attributes using
  (emitAttribute-chars; emitAttrDef-chars)

open import Aletheia.DBC.TextParser.Attributes using
  ( RawDBCAttribute; RawDef
  ; parseAttrLine
  )

open import Aletheia.DBC.TextParser.Properties.Aggregator.Foundations using
  (rawOf; WFAttribute; wfDef)

open import Aletheia.DBC.TextParser.Properties.Attributes.Def using
  (WfAttrType)
open import Aletheia.DBC.TextParser.Properties.Attributes.Line using
  ( parseAttrLine-roundtrip-RawDef-NotRel-Network
  ; parseAttrLine-roundtrip-RawDef-NotRel-Node
  ; parseAttrLine-roundtrip-RawDef-NotRel-Message
  ; parseAttrLine-roundtrip-RawDef-NotRel-Signal
  ; parseAttrLine-roundtrip-RawDef-NotRel-EnvVar
  ; parseAttrLine-roundtrip-RawDef-Rel-NodeMsg
  ; parseAttrLine-roundtrip-RawDef-Rel-NodeSig
  )

open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (SuffixStops)
open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  (isNewlineStart)

-- ============================================================================
-- TOP-LEVEL DEF DISPATCHER  (7-way on scope)
-- ============================================================================

parseAttrLine-on-emit-RawDef :
    ∀ (defs : List AttrDef) (pos : Position)
      (d : AttrDef) (outer : List Char)
  → WFAttribute defs (DBCAttrDef d)
  → SuffixStops isNewlineStart outer
  → parseAttrLine pos
      (emitAttribute-chars defs (DBCAttrDef d) ++ₗ outer)
    ≡ just (mkResult
              (rawOf defs (DBCAttrDef d))
              (advancePositions pos
                 (emitAttribute-chars defs (DBCAttrDef d)))
              outer)
parseAttrLine-on-emit-RawDef defs pos
  (mkAttrDef name ASNetwork ty) outer (wfDef _ wf-ty) ss-NL =
    parseAttrLine-roundtrip-RawDef-NotRel-Network pos name ty outer wf-ty ss-NL
parseAttrLine-on-emit-RawDef defs pos
  (mkAttrDef name ASNode ty) outer (wfDef _ wf-ty) ss-NL =
    parseAttrLine-roundtrip-RawDef-NotRel-Node pos name ty outer wf-ty ss-NL
parseAttrLine-on-emit-RawDef defs pos
  (mkAttrDef name ASMessage ty) outer (wfDef _ wf-ty) ss-NL =
    parseAttrLine-roundtrip-RawDef-NotRel-Message pos name ty outer wf-ty ss-NL
parseAttrLine-on-emit-RawDef defs pos
  (mkAttrDef name ASSignal ty) outer (wfDef _ wf-ty) ss-NL =
    parseAttrLine-roundtrip-RawDef-NotRel-Signal pos name ty outer wf-ty ss-NL
parseAttrLine-on-emit-RawDef defs pos
  (mkAttrDef name ASEnvVar ty) outer (wfDef _ wf-ty) ss-NL =
    parseAttrLine-roundtrip-RawDef-NotRel-EnvVar pos name ty outer wf-ty ss-NL
parseAttrLine-on-emit-RawDef defs pos
  (mkAttrDef name ASNodeMsg ty) outer (wfDef _ wf-ty) ss-NL =
    parseAttrLine-roundtrip-RawDef-Rel-NodeMsg pos name ty outer wf-ty ss-NL
parseAttrLine-on-emit-RawDef defs pos
  (mkAttrDef name ASNodeSig ty) outer (wfDef _ wf-ty) ss-NL =
    parseAttrLine-roundtrip-RawDef-Rel-NodeSig pos name ty outer wf-ty ss-NL
