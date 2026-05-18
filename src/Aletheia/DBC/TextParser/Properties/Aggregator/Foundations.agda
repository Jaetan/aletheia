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
open import Data.List  using (List; []; map)
  renaming (_++_ to _++ₗ_)
open import Data.Maybe using (just; nothing)
open import Data.Unit  using (⊤)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Aletheia.DBC.DecRat.Refinement using
  ( IntDecRat; NatDecRat; natDecRatToℕ)
open import Aletheia.DBC.Types using
  ( DBC; DBCMessage; ValueTable; EnvironmentVar; DBCComment; SignalGroup
  ; clearVdsMsg
  ; AttrType; ATInt; ATFloat; ATString; ATEnum; ATHex
  ; AttrValue; AVInt; AVFloat; AVString; AVEnum; AVHex
  ; AttrDef; AttrDefault; AttrAssign
  ; DBCAttribute; DBCAttrDef; DBCAttrDefault; DBCAttrAssign
  )
open import Aletheia.DBC.TextParser.Attributes using
  ( RawDBCAttribute; RawDef; RawDefault; RawAssign
  ; RawAttrValue;    RavString; RavDecRat
  ; mkRawAttrDefault
  ; mkRawAttrAssign
  ; refineAttribute
  ; findLabel
  )
open import Aletheia.DBC.TextParser.Attributes as ParserAttrs using ()
open import Aletheia.DBC.TextParser.ValueTables using (RawValueDesc)
open import Aletheia.DBC.TextParser.ValueDescriptions using (collectFromMessages)
open import Aletheia.DBC.TextFormatter.Attributes using
  ( collectDefs
  ; nthLabel
  )
open import Aletheia.DBC.TextParser.TopLevel using
  ( TopStmt; TSValueTable; TSMessage; TSEnvVar; TSComment
  ; TSAttribute; TSSignalGroup
  ; TSBOTxBu; TSValueDesc; TSSigValType; TSSigMulVal
  )

open import Aletheia.DBC.TextFormatter.Topology    using (emitMessage-chars)
open import Aletheia.DBC.TextFormatter.ValueTables  using
  (emitValueTable-chars; emitValueDescription-chars)
open import Aletheia.DBC.TextFormatter.EnvVars      using (emitEnvVar-chars)
open import Aletheia.DBC.TextFormatter.Comments     using (emitComment-chars)
open import Aletheia.DBC.TextFormatter.SignalGroups using (emitSignalGroup-chars)
open import Aletheia.DBC.TextFormatter.Attributes   using (emitAttribute-chars)

open import Aletheia.DBC.TextParser.Properties.Attributes.Common using
  ( ValueMatchesType
  ; rawOfAssignValue
  ; rawOfDefaultValue
  )
open import Aletheia.DBC.TextParser.Properties.Attributes.Def using
  (WfAttrType)

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
  wfDef     : ∀ d → WfAttrType (AttrDef.attrType d) → WFAttribute defs (DBCAttrDef d)
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
-- parser by introducing a typed shadow of `TopStmt`.  Parser-only
-- constructors of `TopStmt` not lifted into this typed shadow
-- (`TSBOTxBu` / `TSSigValType` / `TSSigMulVal`) are absent here.
-- `TSValueDesc` carries `RawValueDesc` post-E.4 at the parser side; its
-- typed-shadow lift `TVD` lands at E.5.

data TopStmtTyped : Set where
  TVT : ValueTable     → TopStmtTyped
  TM  : DBCMessage     → TopStmtTyped
  TEV : EnvironmentVar → TopStmtTyped
  TCM : DBCComment     → TopStmtTyped
  TAT : DBCAttribute   → TopStmtTyped
  TSG : SignalGroup    → TopStmtTyped
  -- Track E.5–E.7: VAL_ payload at the typed-shadow level.  `TVD rvd`
  -- mirrors `TopStmt.TSValueDesc rvd`; the typed-shadow shape is
  -- monomorphic since `RawValueDesc` is parser-level (the refined form
  -- lives nested under `messages[i].signals[j].valueDescriptions`, not
  -- as a flat top-level field on `DBC`).  E.7 wires the chunk into
  -- `toTopStmtsTyped` via `collectFromMessages` per the C1 sort key
  -- `(message-index, signal-index, val-desc-index)`.
  TVD : RawValueDesc   → TopStmtTyped

-- Lift typed shadow → parser-side `TopStmt`.  Attributes are routed
-- through `rawOf defs`; non-attributes are constructor-renames.
-- E.9a: TM case lifts `m` through `clearVdsMsg`.  `parseMessage` produces
-- signals with `vds = []` (because `buildSignal` hardcodes the field —
-- VAL_ entries arrive at DBC level via TVD top-stmts), so the per-message
-- dispatcher slim claims the parsed result equals `TSMessage (clearVdsMsg
-- m)`.  Aligning `liftTopStmt`'s TM case keeps the body bridge's RHS
-- (typed shadow lifted to `TopStmt`) coincident with the parser-produced
-- list.  At the Universal layer, `partitionTopStmts` extracts
-- `CollectedTop.messages = map clearVdsMsg d.messages`; `buildDBC`
-- composes with `attachValueDescs (collectFromMessages d.messages)
-- (map clearVdsMsg d.messages) ≡ d.messages` (E.6 + E.9a bridge) to
-- recover the original.
liftTopStmt : List AttrDef → TopStmtTyped → TopStmt
liftTopStmt _    (TVT vt)  = TSValueTable vt
liftTopStmt _    (TM  m)   = TSMessage (clearVdsMsg m)
liftTopStmt _    (TEV ev)  = TSEnvVar ev
liftTopStmt _    (TCM cm)  = TSComment cm
liftTopStmt defs (TAT a)   = TSAttribute (rawOf defs a)
liftTopStmt _    (TSG sg)  = TSSignalGroup sg
liftTopStmt _    (TVD rvd) = TSValueDesc rvd

-- ============================================================================
-- TYPED TopStmt EMITTER
-- ============================================================================
--
-- 6-case dispatch.  For attributes, threads `defs` through to the
-- typed-side formatter (`emitAttribute-chars`); other cases ignore
-- `defs`.  This is the function the polymorphic `many-η-roundtrip-with-
-- lift` helper instantiates as its emitter.

emitTopStmt-chars : List AttrDef → TopStmtTyped → List Char
emitTopStmt-chars _    (TVT vt)  = emitValueTable-chars vt
emitTopStmt-chars _    (TM  m)   = emitMessage-chars m
emitTopStmt-chars _    (TEV ev)  = emitEnvVar-chars ev
emitTopStmt-chars _    (TCM cm)  = emitComment-chars cm
emitTopStmt-chars defs (TAT a)   = emitAttribute-chars defs a
emitTopStmt-chars _    (TSG sg)  = emitSignalGroup-chars sg
emitTopStmt-chars _    (TVD rvd) = emitValueDescription-chars rvd

-- ============================================================================
-- DBC → typed top-stmt list (formatChars order).
-- ============================================================================
--
-- Concatenates the 7 list-shaped sections in the same order
-- `formatChars-body` emits them.  The preamble (VERSION/NS_/BS_/BU_) is
-- handled separately at the top level — it's not in the `many parseTop-
-- Stmt` body.  The TVD chunk (E.7) is sourced via `collectFromMessages`
-- so partition's inverse (`attachValueDescs ∘ collectFromMessages ≡ id`,
-- E.6) closes the universal aggregator.

toTopStmtsTyped : DBC → List TopStmtTyped
toTopStmtsTyped d =
  map TVT (DBC.valueTables     d) ++ₗ
  map TM  (DBC.messages        d) ++ₗ
  map TVD (collectFromMessages (DBC.messages d)) ++ₗ
  map TEV (DBC.environmentVars d) ++ₗ
  map TCM (DBC.comments        d) ++ₗ
  map TAT (DBC.attributes      d) ++ₗ
  map TSG (DBC.signalGroups    d)
