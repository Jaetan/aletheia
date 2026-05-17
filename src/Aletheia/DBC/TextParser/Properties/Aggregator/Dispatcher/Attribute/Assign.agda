{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 4c — AttrAssign-level dispatcher.
--
-- Composes the 3 emit-shape dispatchers (String / Frac / BareInt) into
-- the universal AttrAssign roundtrip:
--   `parseAttrLine pos (emitAttribute-chars defs (DBCAttrAssign a) ++ outer)
--      ≡ just (mkResult (rawOf defs (DBCAttrAssign a))
--                       (advancePositions pos (emitAttribute-chars defs ...))
--                       outer)`
--
-- 5-way dispatch on `AttrAssign.value`:
--   * AVString s → forward to `parseAttrLine-on-emit-RawAssign-AVString`.
--   * AVFloat d  → forward to `parseAttrLine-on-emit-RawAssign-AVFloat`.
--   * AVInt z'   → 7-target dispatch through BareInt's per-target slims
--                  with value-bridge `cong RavDecRat (fromℤ-intDecRatToℤ z')`.
--   * AVHex n    → 7-target dispatch through BareInt with bridge
--                  `cong RavDecRat (fromℕ-natDecRatToℕ n)`.
--   * AVEnum n   → same as AVHex (assignment context emits the index, not the
--                  label; only default context routes through `nthLabel`).
--
-- The input bytes of `emitAttribute-chars defs (DBCAttrAssign (mkAttrAssign
-- name target value))` reduce definitionally to the spelled-out emit form
-- the per-target BareInt slim consumes (with `z` = `intDecRatToℤ z'` for AVInt
-- or `+ natDecRatToℕ n` for AVHex/AVEnum); no input bridge is needed.
module Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Attribute.Assign where

open import Data.Char  using (Char)
open import Data.Integer using (ℤ; +_)
open import Data.List  using (List; []; _∷_)
  renaming (_++_ to _++ₗ_)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; subst)

open import Aletheia.Parser.Combinators using
  (Position; ParseResult; mkResult; advancePositions)

open import Aletheia.DBC.DecRat using (DecRat; fromℤ)
open import Aletheia.DBC.DecRat.Refinement using
  ( IntDecRat; NatDecRat
  ; intDecRatToℤ; natDecRatToℕ
  ; fromℤ-intDecRatToℤ
  ; fromℕ-natDecRatToℕ
  )
open import Aletheia.DBC.Identifier using (Identifier)
open import Aletheia.DBC.Types using
  ( AttrDef
  ; AttrTarget; ATgtNetwork; ATgtNode; ATgtMessage; ATgtSignal; ATgtEnvVar
  ; ATgtNodeMsg; ATgtNodeSig
  ; AttrValue; AVInt; AVFloat; AVString; AVEnum; AVHex
  ; AttrAssign; mkAttrAssign
  ; DBCAttribute; DBCAttrAssign
  )

open import Aletheia.DBC.TextFormatter.Attributes using
  ( emitAttribute-chars
  ; emitAttrAssign-chars
  )

open import Aletheia.DBC.TextParser.Attributes using
  ( RawDBCAttribute; RawAssign; mkRawAttrAssign
  ; RawAttrValue;   RavDecRat; RavString
  ; parseAttrLine
  )

open import Aletheia.DBC.TextParser.Properties.Aggregator.Foundations using
  (rawOf)
open import Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Attribute.Foundations using
  (IdentNameStop-of)

open import Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Attribute.Assign.String using
  (parseAttrLine-on-emit-RawAssign-AVString)
open import Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Attribute.Assign.Frac using
  (parseAttrLine-on-emit-RawAssign-AVFloat)
open import Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Attribute.Assign.BareInt using
  ( parseAttrLine-on-RavBareInt-Network
  ; parseAttrLine-on-RavBareInt-Node
  ; parseAttrLine-on-RavBareInt-Message
  ; parseAttrLine-on-RavBareInt-Signal
  ; parseAttrLine-on-RavBareInt-EnvVar
  ; parseAttrLine-on-RavBareInt-NodeMsg
  ; parseAttrLine-on-RavBareInt-NodeSig
  )

open import Aletheia.DBC.TextParser.Properties.Attributes.Assign.Network using
  (module TraceNetwork)
open import Aletheia.DBC.TextParser.Properties.Attributes.Assign.Node using
  (module TraceNode)
open import Aletheia.DBC.TextParser.Properties.Attributes.Assign.Message using
  (module TraceMessage)
open import Aletheia.DBC.TextParser.Properties.Attributes.Assign.Signal using
  (module TraceSignal)
open import Aletheia.DBC.TextParser.Properties.Attributes.Assign.EnvVar using
  (module TraceEnvVar)
open import Aletheia.DBC.TextParser.Properties.Attributes.Assign.Rel using
  (module TraceNodeMsg; module TraceNodeSig)

open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (SuffixStops)
open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  (isNewlineStart)
open import Aletheia.DBC.TextFormatter.Emitter using
  (showInt-chars; showℕ-dec-chars; quoteStringLit-chars)
open import Aletheia.DBC.TextFormatter.Topology using (rawCanIdℕ)

open import Data.Product using (proj₁; proj₂)


-- R22 continuation of R21 cluster 9 AGDA-D-15.1: the 21 value-bridge
-- helpers (lines 122-771 in the pre-split file, ~650 LOC) moved to a
-- sibling submodule.  Helpers are public there; this module imports
-- them back for the TOP-LEVEL ASSIGN DISPATCHER below.  The parent's
-- existing walk reaches the sibling via this import — no new walk
-- root needed.
open import Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Attribute.Assign.Bridges using
  ( on-AVInt-Network; on-AVInt-Node; on-AVInt-Message; on-AVInt-Signal
  ; on-AVInt-EnvVar; on-AVInt-NodeMsg; on-AVInt-NodeSig
  ; on-AVHex-Network; on-AVHex-Node; on-AVHex-Message; on-AVHex-Signal
  ; on-AVHex-EnvVar; on-AVHex-NodeMsg; on-AVHex-NodeSig
  ; on-AVEnum-Network; on-AVEnum-Node; on-AVEnum-Message; on-AVEnum-Signal
  ; on-AVEnum-EnvVar; on-AVEnum-NodeMsg; on-AVEnum-NodeSig
  )

-- ============================================================================
-- TOP-LEVEL ASSIGN DISPATCHER  (5-way on value × 7-way on target)
-- ============================================================================
--
-- Constructor pattern-matches on `value` first, then for AVInt/AVHex/AVEnum
-- pattern-matches on `target` to route to the per-target value-bridge helper.
-- AVString/AVFloat forward to the unified target-dispatchers in their own
-- modules (which already pattern-match on `target` internally).

parseAttrLine-on-emit-RawAssign :
    ∀ (defs : List AttrDef) (pos : Position)
      (name : List Char) (target : AttrTarget) (value : AttrValue)
      (outer : List Char)
  → IdentNameStop-of target
  → SuffixStops isNewlineStart outer
  → parseAttrLine pos
      (emitAttribute-chars defs
         (DBCAttrAssign (mkAttrAssign name target value))
       ++ₗ outer)
    ≡ just (mkResult
              (rawOf defs
                 (DBCAttrAssign (mkAttrAssign name target value)))
              (advancePositions pos
                 (emitAttribute-chars defs
                    (DBCAttrAssign (mkAttrAssign name target value))))
              outer)
parseAttrLine-on-emit-RawAssign defs pos name target (AVString s) outer t-stop ss-NL =
  parseAttrLine-on-emit-RawAssign-AVString defs pos name target s outer t-stop ss-NL
parseAttrLine-on-emit-RawAssign defs pos name target (AVFloat d) outer t-stop ss-NL =
  parseAttrLine-on-emit-RawAssign-AVFloat defs pos name target d outer t-stop ss-NL
parseAttrLine-on-emit-RawAssign defs pos name ATgtNetwork (AVInt z') outer _ ss-NL =
  on-AVInt-Network defs pos name z' outer ss-NL
parseAttrLine-on-emit-RawAssign defs pos name (ATgtNode n) (AVInt z') outer n-stop ss-NL =
  on-AVInt-Node defs pos name n z' outer n-stop ss-NL
parseAttrLine-on-emit-RawAssign defs pos name (ATgtMessage cid) (AVInt z') outer _ ss-NL =
  on-AVInt-Message defs pos name cid z' outer ss-NL
parseAttrLine-on-emit-RawAssign defs pos name (ATgtSignal cid sig) (AVInt z') outer sig-stop ss-NL =
  on-AVInt-Signal defs pos name cid sig z' outer sig-stop ss-NL
parseAttrLine-on-emit-RawAssign defs pos name (ATgtEnvVar ev) (AVInt z') outer ev-stop ss-NL =
  on-AVInt-EnvVar defs pos name ev z' outer ev-stop ss-NL
parseAttrLine-on-emit-RawAssign defs pos name (ATgtNodeMsg n cid) (AVInt z') outer n-stop ss-NL =
  on-AVInt-NodeMsg defs pos name n cid z' outer n-stop ss-NL
parseAttrLine-on-emit-RawAssign defs pos name (ATgtNodeSig n cid sig) (AVInt z') outer stops ss-NL =
  on-AVInt-NodeSig defs pos name n cid sig z' outer stops ss-NL
parseAttrLine-on-emit-RawAssign defs pos name ATgtNetwork (AVHex n) outer _ ss-NL =
  on-AVHex-Network defs pos name n outer ss-NL
parseAttrLine-on-emit-RawAssign defs pos name (ATgtNode nd) (AVHex n) outer n-stop ss-NL =
  on-AVHex-Node defs pos name nd n outer n-stop ss-NL
parseAttrLine-on-emit-RawAssign defs pos name (ATgtMessage cid) (AVHex n) outer _ ss-NL =
  on-AVHex-Message defs pos name cid n outer ss-NL
parseAttrLine-on-emit-RawAssign defs pos name (ATgtSignal cid sig) (AVHex n) outer sig-stop ss-NL =
  on-AVHex-Signal defs pos name cid sig n outer sig-stop ss-NL
parseAttrLine-on-emit-RawAssign defs pos name (ATgtEnvVar ev) (AVHex n) outer ev-stop ss-NL =
  on-AVHex-EnvVar defs pos name ev n outer ev-stop ss-NL
parseAttrLine-on-emit-RawAssign defs pos name (ATgtNodeMsg nd cid) (AVHex n) outer n-stop ss-NL =
  on-AVHex-NodeMsg defs pos name nd cid n outer n-stop ss-NL
parseAttrLine-on-emit-RawAssign defs pos name (ATgtNodeSig nd cid sig) (AVHex n) outer stops ss-NL =
  on-AVHex-NodeSig defs pos name nd cid sig n outer stops ss-NL
parseAttrLine-on-emit-RawAssign defs pos name ATgtNetwork (AVEnum n) outer _ ss-NL =
  on-AVEnum-Network defs pos name n outer ss-NL
parseAttrLine-on-emit-RawAssign defs pos name (ATgtNode nd) (AVEnum n) outer n-stop ss-NL =
  on-AVEnum-Node defs pos name nd n outer n-stop ss-NL
parseAttrLine-on-emit-RawAssign defs pos name (ATgtMessage cid) (AVEnum n) outer _ ss-NL =
  on-AVEnum-Message defs pos name cid n outer ss-NL
parseAttrLine-on-emit-RawAssign defs pos name (ATgtSignal cid sig) (AVEnum n) outer sig-stop ss-NL =
  on-AVEnum-Signal defs pos name cid sig n outer sig-stop ss-NL
parseAttrLine-on-emit-RawAssign defs pos name (ATgtEnvVar ev) (AVEnum n) outer ev-stop ss-NL =
  on-AVEnum-EnvVar defs pos name ev n outer ev-stop ss-NL
parseAttrLine-on-emit-RawAssign defs pos name (ATgtNodeMsg nd cid) (AVEnum n) outer n-stop ss-NL =
  on-AVEnum-NodeMsg defs pos name nd cid n outer n-stop ss-NL
parseAttrLine-on-emit-RawAssign defs pos name (ATgtNodeSig nd cid sig) (AVEnum n) outer stops ss-NL =
  on-AVEnum-NodeSig defs pos name nd cid sig n outer stops ss-NL
