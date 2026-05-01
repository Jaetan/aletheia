{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 4c — Foundations for the universal aggregator.
--
-- Closes the typed/raw asymmetry between the formatter (which emits
-- bytes from `DBCAttribute` with ambient `defs`) and the parser (which
-- yields `RawDBCAttribute` and refines later).  Provides the typed
-- shadow `TopStmtTyped` used by the body bridge so the polymorphic
-- `many-η-roundtrip` helper applies at TopStmt level via a `lift`.
--
-- Layered against existing infrastructure:
--   * `Properties.Attributes.Common` — value-level `rawOfAssignValue` /
--     `rawOfDefaultValue` + per-AttrType refine-roundtrip lemmas
--     (`ValueMatchesType` predicate + 5 `refine*Value-rawOf*-roundtrip`
--     lemmas).  This module lifts those to whole-attribute level.
--   * `TextFormatter.Attributes` — `collectDefs` / `lookupDef` /
--     `emitAttribute-chars` (typed-side).
--   * `TextParser.Attributes` — `refineAttribute` / `lookupDef` /
--     `RawDBCAttribute` constructors.
--   * `TextFormatter.TopLevel` — section emitters (`emitValueTables-
--     chars`, `emitMessages-chars`, …).
--   * `TextParser.TopLevel` — `TopStmt` + `parseTopStmt` + `partition-
--     TopStmts`.
--
-- The WF predicate is structural: each `DBCAttribute` constructor has
-- its own WF rule, and AVEnum default carries the Layer-4 bridge
-- `findLabel ∘ nthLabel ≡ just n` as a precondition (label uniqueness +
-- index bound — see `memory/project_b3d_layer4_owed_lemmas.md`).
module Aletheia.DBC.TextParser.Properties.Aggregator.Foundations where

open import Data.Char  using (Char)
open import Data.List  using (List; []; _∷_; foldr; map)
  renaming (_++_ to _++ₗ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat   using (ℕ)
open import Data.Unit  using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Aletheia.DBC.DecRat            using (DecRat)
open import Aletheia.DBC.DecRat.Refinement using
  ( IntDecRat; NatDecRat; intDecRatToℤ; natDecRatToℕ)
open import Aletheia.DBC.Types using
  ( DBC; DBCMessage; ValueTable; EnvironmentVar; DBCComment; SignalGroup
  ; Node
  ; AttrType; ATInt; ATFloat; ATString; ATEnum; ATHex
  ; AttrValue; AVInt; AVFloat; AVString; AVEnum; AVHex
  ; AttrDef; AttrDefault; AttrAssign
  ; DBCAttribute; DBCAttrDef; DBCAttrDefault; DBCAttrAssign
  )
open import Aletheia.DBC.TextParser.Attributes using
  ( RawDBCAttribute; RawDef; RawDefault; RawAssign
  ; RawAttrValue;    RavString; RavDecRat
  ; RawAttrDefault;  mkRawAttrDefault
  ; RawAttrAssign;   mkRawAttrAssign
  ; refineAttribute
  ; collectRawDefs
  ; findLabel
  )
open import Aletheia.DBC.TextParser.Attributes as ParserAttrs using ()
open import Aletheia.DBC.TextFormatter.Attributes using
  ( collectDefs
  ; nthLabel
  )
open import Aletheia.DBC.TextFormatter.Attributes as FmtAttrs using ()
open import Aletheia.DBC.TextParser.TopLevel using
  ( TopStmt; TSValueTable; TSMessage; TSEnvVar; TSComment
  ; TSAttribute; TSSignalGroup
  ; TSBOTxBu; TSValueDesc; TSSigValType; TSSigMulVal
  )

open import Aletheia.DBC.TextFormatter.Topology    using (emitMessage-chars)
open import Aletheia.DBC.TextFormatter.ValueTables  using (emitValueTable-chars)
open import Aletheia.DBC.TextFormatter.EnvVars      using (emitEnvVar-chars)
open import Aletheia.DBC.TextFormatter.Comments     using (emitComment-chars)
open import Aletheia.DBC.TextFormatter.SignalGroups using (emitSignalGroup-chars)
open import Aletheia.DBC.TextFormatter.Attributes   using (emitAttribute-chars)

open import Aletheia.DBC.TextParser.Properties.Attributes.Common using
  ( ValueMatchesType
  ; VMTInt; VMTFloat; VMTString; VMTEnum; VMTHex
  ; rawOfAssignValue
  ; rawOfDefaultValue
  ; refineAssignValue-rawOfAssign-roundtrip
  ; refineDefaultValue-rawOfDefault-roundtrip-AVInt
  ; refineDefaultValue-rawOfDefault-roundtrip-AVFloat
  ; refineDefaultValue-rawOfDefault-roundtrip-AVString
  ; refineDefaultValue-rawOfDefault-roundtrip-AVHex
  ; refineDefaultValue-rawOfDefault-roundtrip-AVEnum
  )

-- ============================================================================
-- WHOLE-ATTRIBUTE TYPED → RAW LIFT
-- ============================================================================
--
-- `rawOf defs a` produces the canonical `RawDBCAttribute` that
-- `parseAttrLine` yields when given the bytes of `emitAttribute-chars
-- defs a`.  Mirrors the formatter's `emitDefaultValue-chars` per-AVEnum
-- defs lookup (only AVEnum-default depends on `defs`).

private
  -- Helper: dispatch the AttrDefault value to its raw form, threading
  -- `defs` only when the value is `AVEnum`.  Mirrors the formatter
  -- exactly: non-enum values are defs-independent; AVEnum routes
  -- through `lookupDef` and `nthLabel`.
  rawOfDefaultValue-with-defs :
      List AttrDef → AttrDefault → RawAttrValue
  rawOfDefaultValue-with-defs defs d
      with AttrDefault.value d
  ... | AVInt z    = RavDecRat (IntDecRat.value z)
  ... | AVFloat q  = RavDecRat q
  ... | AVString s = RavString s
  ... | AVHex n    = RavDecRat (NatDecRat.value n)
  ... | AVEnum n
      with ParserAttrs.lookupDef (AttrDefault.name d) defs
  ...   | nothing = RavString []
  ...   | just def
      with AttrDef.attrType def
  ...     | ATEnum labels = RavString (nthLabel (natDecRatToℕ n) labels)
  ...     | ATInt _ _     = RavString []
  ...     | ATFloat _ _   = RavString []
  ...     | ATString      = RavString []
  ...     | ATHex _ _     = RavString []

rawOf : List AttrDef → DBCAttribute → RawDBCAttribute
rawOf _    (DBCAttrDef d)     = RawDef d
rawOf defs (DBCAttrDefault d) =
  RawDefault (mkRawAttrDefault
                (AttrDefault.name d)
                (rawOfDefaultValue-with-defs defs d))
rawOf _    (DBCAttrAssign a)  =
  RawAssign (mkRawAttrAssign
              (AttrAssign.name a)
              (AttrAssign.target a)
              (rawOfAssignValue (AttrAssign.value a)))

-- ============================================================================
-- WELL-FORMEDNESS PREDICATE (Layer 4c — bundles per-attribute structural
-- preconditions for `refineAttribute defs (rawOf defs a) ≡ just a`).
-- ============================================================================
--
-- `WFAttribute defs a` requires: for default/assign attrs, the name
-- resolves to a def in `defs`, the value's constructor matches the def's
-- type, and (for ATEnum × AVEnum default context) the label-uniqueness
-- bridge `findLabel (nthLabel n labels) labels ≡ just n` holds.

-- Vacuous unless the value is AVEnum under a default in an ATEnum def.
DefaultEnumOK : AttrType → AttrValue → Set
DefaultEnumOK (ATEnum labels) (AVEnum n) =
  findLabel (nthLabel (natDecRatToℕ n) labels) labels ≡ just (natDecRatToℕ n)
DefaultEnumOK _               _          = ⊤

data WFAttribute (defs : List AttrDef) : DBCAttribute → Set where
  wfDef     : ∀ d → WFAttribute defs (DBCAttrDef d)
  wfDefault :
      ∀ d def
    → ParserAttrs.lookupDef (AttrDefault.name d) defs ≡ just def
    → ValueMatchesType (AttrDef.attrType def) (AttrDefault.value d)
    → DefaultEnumOK     (AttrDef.attrType def) (AttrDefault.value d)
    → WFAttribute defs (DBCAttrDefault d)
  wfAssign  :
      ∀ a def
    → ParserAttrs.lookupDef (AttrAssign.name a) defs ≡ just def
    → ValueMatchesType (AttrDef.attrType def) (AttrAssign.value a)
    → WFAttribute defs (DBCAttrAssign a)

-- ============================================================================
-- TYPED TopStmt SHADOW (carries `DBCAttribute`, not `RawDBCAttribute`).
-- ============================================================================
--
-- Layer 4c bridges between the typed formatter and the raw-yielding
-- parser by introducing a typed shadow of `TopStmt`.  Drop constructors
-- (TSBOTxBu / TSValueDesc / TSSigValType / TSSigMulVal) are not in this
-- shadow — they are parser-only.

data TopStmtTyped : Set where
  TVT : ValueTable     → TopStmtTyped
  TM  : DBCMessage     → TopStmtTyped
  TEV : EnvironmentVar → TopStmtTyped
  TCM : DBCComment     → TopStmtTyped
  TAT : DBCAttribute   → TopStmtTyped
  TSG : SignalGroup    → TopStmtTyped

-- Lift typed shadow → parser-side `TopStmt`.  Attributes are routed
-- through `rawOf defs`; non-attributes are constructor-renames.
liftTopStmt : List AttrDef → TopStmtTyped → TopStmt
liftTopStmt _    (TVT vt) = TSValueTable vt
liftTopStmt _    (TM  m)  = TSMessage m
liftTopStmt _    (TEV ev) = TSEnvVar ev
liftTopStmt _    (TCM cm) = TSComment cm
liftTopStmt defs (TAT a)  = TSAttribute (rawOf defs a)
liftTopStmt _    (TSG sg) = TSSignalGroup sg

-- ============================================================================
-- TYPED TopStmt EMITTER
-- ============================================================================
--
-- 6-case dispatch.  For attributes, threads `defs` through to the
-- typed-side formatter (`emitAttribute-chars`); other cases ignore
-- `defs`.  This is the function the polymorphic `many-η-roundtrip-with-
-- lift` helper instantiates as its emitter.

emitTopStmt-chars : List AttrDef → TopStmtTyped → List Char
emitTopStmt-chars _    (TVT vt) = emitValueTable-chars vt
emitTopStmt-chars _    (TM  m)  = emitMessage-chars m
emitTopStmt-chars _    (TEV ev) = emitEnvVar-chars ev
emitTopStmt-chars _    (TCM cm) = emitComment-chars cm
emitTopStmt-chars defs (TAT a)  = emitAttribute-chars defs a
emitTopStmt-chars _    (TSG sg) = emitSignalGroup-chars sg

-- ============================================================================
-- DBC → typed top-stmt list (formatChars order).
-- ============================================================================
--
-- Concatenates the 6 list-shaped sections in the same order
-- `formatChars-body` emits them.  The preamble (VERSION/NS_/BS_/BU_) is
-- handled separately at the top level — it's not in the `many parseTop-
-- Stmt` body.

toTopStmtsTyped : DBC → List TopStmtTyped
toTopStmtsTyped d =
  map TVT (DBC.valueTables     d) ++ₗ
  map TM  (DBC.messages        d) ++ₗ
  map TEV (DBC.environmentVars d) ++ₗ
  map TCM (DBC.comments        d) ++ₗ
  map TAT (DBC.attributes      d) ++ₗ
  map TSG (DBC.signalGroups    d)
