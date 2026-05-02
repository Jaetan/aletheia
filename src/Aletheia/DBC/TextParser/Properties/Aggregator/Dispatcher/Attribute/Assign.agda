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

-- ============================================================================
-- VALUE-BRIDGE HELPERS  (per-target × {AVInt, AVHex, AVEnum})
-- ============================================================================
--
-- Each helper:
--   1. Calls the corresponding BareInt slim with `z = intDecRatToℤ z'` (AVInt)
--      or `z = + natDecRatToℕ n` (AVHex/AVEnum).
--   2. Transports through `cong (λ q → mkResult (RawAssign (mkRawAttrAssign
--      name target (RavDecRat q))) traced outer) bridge` to lift `fromℤ z` to
--      `IntDecRat.value z'` / `NatDecRat.value n`.
--
-- The `subst` payload predicate is the universal goal's RHS (spelled out).

private
  -- ============================================================================
  -- AVInt × 7 targets  (bridge: fromℤ-intDecRatToℤ z')
  -- ============================================================================

  on-AVInt-Network :
      ∀ (defs : List AttrDef) (pos : Position) (name : List Char) (z' : IntDecRat)
        (outer : List Char)
    → SuffixStops isNewlineStart outer
    → parseAttrLine pos
        (emitAttribute-chars defs
           (DBCAttrAssign (mkAttrAssign name ATgtNetwork (AVInt z')))
         ++ₗ outer)
      ≡ just (mkResult
                (RawAssign (mkRawAttrAssign name ATgtNetwork
                              (RavDecRat (IntDecRat.value z'))))
                (TraceNetwork.pos9 pos name (showInt-chars (intDecRatToℤ z')) outer)
                outer)
  on-AVInt-Network defs pos name z' outer ss-NL =
    subst
      (λ q → parseAttrLine pos
                (emitAttribute-chars defs
                   (DBCAttrAssign (mkAttrAssign name ATgtNetwork (AVInt z')))
                 ++ₗ outer)
               ≡ just (mkResult
                         (RawAssign (mkRawAttrAssign name ATgtNetwork (RavDecRat q)))
                         (TraceNetwork.pos9 pos name
                            (showInt-chars (intDecRatToℤ z')) outer)
                         outer))
      (fromℤ-intDecRatToℤ z')
      (parseAttrLine-on-RavBareInt-Network pos name (intDecRatToℤ z') outer ss-NL)

  on-AVInt-Node :
      ∀ (defs : List AttrDef) (pos : Position) (name : List Char) (n : Identifier)
        (z' : IntDecRat) (outer : List Char)
    → IdentNameStop-of (ATgtNode n)
    → SuffixStops isNewlineStart outer
    → parseAttrLine pos
        (emitAttribute-chars defs
           (DBCAttrAssign (mkAttrAssign name (ATgtNode n) (AVInt z')))
         ++ₗ outer)
      ≡ just (mkResult
                (RawAssign (mkRawAttrAssign name (ATgtNode n)
                              (RavDecRat (IntDecRat.value z'))))
                (TraceNode.pos9 pos name n (showInt-chars (intDecRatToℤ z')) outer)
                outer)
  on-AVInt-Node defs pos name n z' outer n-stop ss-NL =
    subst
      (λ q → parseAttrLine pos
                (emitAttribute-chars defs
                   (DBCAttrAssign (mkAttrAssign name (ATgtNode n) (AVInt z')))
                 ++ₗ outer)
               ≡ just (mkResult
                         (RawAssign (mkRawAttrAssign name (ATgtNode n) (RavDecRat q)))
                         (TraceNode.pos9 pos name n
                            (showInt-chars (intDecRatToℤ z')) outer)
                         outer))
      (fromℤ-intDecRatToℤ z')
      (parseAttrLine-on-RavBareInt-Node pos name n (intDecRatToℤ z') outer n-stop ss-NL)

  on-AVInt-Message :
      ∀ (defs : List AttrDef) (pos : Position) (name : List Char)
        (cid : _) (z' : IntDecRat) (outer : List Char)
    → SuffixStops isNewlineStart outer
    → parseAttrLine pos
        (emitAttribute-chars defs
           (DBCAttrAssign (mkAttrAssign name (ATgtMessage cid) (AVInt z')))
         ++ₗ outer)
      ≡ just (mkResult
                (RawAssign (mkRawAttrAssign name (ATgtMessage cid)
                              (RavDecRat (IntDecRat.value z'))))
                (TraceMessage.pos9 pos name cid
                   (showInt-chars (intDecRatToℤ z')) outer)
                outer)
  on-AVInt-Message defs pos name cid z' outer ss-NL =
    subst
      (λ q → parseAttrLine pos
                (emitAttribute-chars defs
                   (DBCAttrAssign (mkAttrAssign name (ATgtMessage cid) (AVInt z')))
                 ++ₗ outer)
               ≡ just (mkResult
                         (RawAssign (mkRawAttrAssign name (ATgtMessage cid)
                                       (RavDecRat q)))
                         (TraceMessage.pos9 pos name cid
                            (showInt-chars (intDecRatToℤ z')) outer)
                         outer))
      (fromℤ-intDecRatToℤ z')
      (parseAttrLine-on-RavBareInt-Message pos name cid (intDecRatToℤ z') outer ss-NL)

  on-AVInt-Signal :
      ∀ (defs : List AttrDef) (pos : Position) (name : List Char)
        (cid : _) (sig : Identifier) (z' : IntDecRat) (outer : List Char)
    → IdentNameStop-of (ATgtSignal cid sig)
    → SuffixStops isNewlineStart outer
    → parseAttrLine pos
        (emitAttribute-chars defs
           (DBCAttrAssign (mkAttrAssign name (ATgtSignal cid sig) (AVInt z')))
         ++ₗ outer)
      ≡ just (mkResult
                (RawAssign (mkRawAttrAssign name (ATgtSignal cid sig)
                              (RavDecRat (IntDecRat.value z'))))
                (TraceSignal.pos9 pos name cid sig
                   (showInt-chars (intDecRatToℤ z')) outer)
                outer)
  on-AVInt-Signal defs pos name cid sig z' outer sig-stop ss-NL =
    subst
      (λ q → parseAttrLine pos
                (emitAttribute-chars defs
                   (DBCAttrAssign (mkAttrAssign name (ATgtSignal cid sig) (AVInt z')))
                 ++ₗ outer)
               ≡ just (mkResult
                         (RawAssign (mkRawAttrAssign name (ATgtSignal cid sig)
                                       (RavDecRat q)))
                         (TraceSignal.pos9 pos name cid sig
                            (showInt-chars (intDecRatToℤ z')) outer)
                         outer))
      (fromℤ-intDecRatToℤ z')
      (parseAttrLine-on-RavBareInt-Signal pos name cid sig (intDecRatToℤ z')
         outer sig-stop ss-NL)

  on-AVInt-EnvVar :
      ∀ (defs : List AttrDef) (pos : Position) (name : List Char)
        (ev : Identifier) (z' : IntDecRat) (outer : List Char)
    → IdentNameStop-of (ATgtEnvVar ev)
    → SuffixStops isNewlineStart outer
    → parseAttrLine pos
        (emitAttribute-chars defs
           (DBCAttrAssign (mkAttrAssign name (ATgtEnvVar ev) (AVInt z')))
         ++ₗ outer)
      ≡ just (mkResult
                (RawAssign (mkRawAttrAssign name (ATgtEnvVar ev)
                              (RavDecRat (IntDecRat.value z'))))
                (TraceEnvVar.pos9 pos name ev
                   (showInt-chars (intDecRatToℤ z')) outer)
                outer)
  on-AVInt-EnvVar defs pos name ev z' outer ev-stop ss-NL =
    subst
      (λ q → parseAttrLine pos
                (emitAttribute-chars defs
                   (DBCAttrAssign (mkAttrAssign name (ATgtEnvVar ev) (AVInt z')))
                 ++ₗ outer)
               ≡ just (mkResult
                         (RawAssign (mkRawAttrAssign name (ATgtEnvVar ev)
                                       (RavDecRat q)))
                         (TraceEnvVar.pos9 pos name ev
                            (showInt-chars (intDecRatToℤ z')) outer)
                         outer))
      (fromℤ-intDecRatToℤ z')
      (parseAttrLine-on-RavBareInt-EnvVar pos name ev (intDecRatToℤ z')
         outer ev-stop ss-NL)

  on-AVInt-NodeMsg :
      ∀ (defs : List AttrDef) (pos : Position) (name : List Char)
        (n : Identifier) (cid : _) (z' : IntDecRat) (outer : List Char)
    → IdentNameStop-of (ATgtNodeMsg n cid)
    → SuffixStops isNewlineStart outer
    → parseAttrLine pos
        (emitAttribute-chars defs
           (DBCAttrAssign (mkAttrAssign name (ATgtNodeMsg n cid) (AVInt z')))
         ++ₗ outer)
      ≡ just (mkResult
                (RawAssign (mkRawAttrAssign name (ATgtNodeMsg n cid)
                              (RavDecRat (IntDecRat.value z'))))
                (TraceNodeMsg.pos9 pos name n cid
                   (showInt-chars (intDecRatToℤ z')) outer)
                outer)
  on-AVInt-NodeMsg defs pos name n cid z' outer n-stop ss-NL =
    subst
      (λ q → parseAttrLine pos
                (emitAttribute-chars defs
                   (DBCAttrAssign (mkAttrAssign name (ATgtNodeMsg n cid) (AVInt z')))
                 ++ₗ outer)
               ≡ just (mkResult
                         (RawAssign (mkRawAttrAssign name (ATgtNodeMsg n cid)
                                       (RavDecRat q)))
                         (TraceNodeMsg.pos9 pos name n cid
                            (showInt-chars (intDecRatToℤ z')) outer)
                         outer))
      (fromℤ-intDecRatToℤ z')
      (parseAttrLine-on-RavBareInt-NodeMsg pos name n cid (intDecRatToℤ z')
         outer n-stop ss-NL)

  on-AVInt-NodeSig :
      ∀ (defs : List AttrDef) (pos : Position) (name : List Char)
        (n : Identifier) (cid : _) (sig : Identifier) (z' : IntDecRat)
        (outer : List Char)
    → IdentNameStop-of (ATgtNodeSig n cid sig)
    → SuffixStops isNewlineStart outer
    → parseAttrLine pos
        (emitAttribute-chars defs
           (DBCAttrAssign (mkAttrAssign name (ATgtNodeSig n cid sig) (AVInt z')))
         ++ₗ outer)
      ≡ just (mkResult
                (RawAssign (mkRawAttrAssign name (ATgtNodeSig n cid sig)
                              (RavDecRat (IntDecRat.value z'))))
                (TraceNodeSig.pos9 pos name n cid sig
                   (showInt-chars (intDecRatToℤ z')) outer)
                outer)
  on-AVInt-NodeSig defs pos name n cid sig z' outer stops ss-NL =
    subst
      (λ q → parseAttrLine pos
                (emitAttribute-chars defs
                   (DBCAttrAssign
                      (mkAttrAssign name (ATgtNodeSig n cid sig) (AVInt z')))
                 ++ₗ outer)
               ≡ just (mkResult
                         (RawAssign (mkRawAttrAssign name (ATgtNodeSig n cid sig)
                                       (RavDecRat q)))
                         (TraceNodeSig.pos9 pos name n cid sig
                            (showInt-chars (intDecRatToℤ z')) outer)
                         outer))
      (fromℤ-intDecRatToℤ z')
      (parseAttrLine-on-RavBareInt-NodeSig pos name n cid sig (intDecRatToℤ z')
         outer (proj₁ stops) (proj₂ stops) ss-NL)

  -- ============================================================================
  -- AVHex × 7 targets  (bridge: fromℕ-natDecRatToℕ n)
  -- ============================================================================

  on-AVHex-Network :
      ∀ (defs : List AttrDef) (pos : Position) (name : List Char)
        (n : NatDecRat) (outer : List Char)
    → SuffixStops isNewlineStart outer
    → parseAttrLine pos
        (emitAttribute-chars defs
           (DBCAttrAssign (mkAttrAssign name ATgtNetwork (AVHex n)))
         ++ₗ outer)
      ≡ just (mkResult
                (RawAssign (mkRawAttrAssign name ATgtNetwork
                              (RavDecRat (NatDecRat.value n))))
                (TraceNetwork.pos9 pos name (showℕ-dec-chars (natDecRatToℕ n)) outer)
                outer)
  on-AVHex-Network defs pos name n outer ss-NL =
    subst
      (λ q → parseAttrLine pos
                (emitAttribute-chars defs
                   (DBCAttrAssign (mkAttrAssign name ATgtNetwork (AVHex n)))
                 ++ₗ outer)
               ≡ just (mkResult
                         (RawAssign (mkRawAttrAssign name ATgtNetwork (RavDecRat q)))
                         (TraceNetwork.pos9 pos name
                            (showℕ-dec-chars (natDecRatToℕ n)) outer)
                         outer))
      (fromℕ-natDecRatToℕ n)
      (parseAttrLine-on-RavBareInt-Network pos name (+ natDecRatToℕ n) outer ss-NL)

  on-AVHex-Node :
      ∀ (defs : List AttrDef) (pos : Position) (name : List Char)
        (nd : Identifier) (n : NatDecRat) (outer : List Char)
    → IdentNameStop-of (ATgtNode nd)
    → SuffixStops isNewlineStart outer
    → parseAttrLine pos
        (emitAttribute-chars defs
           (DBCAttrAssign (mkAttrAssign name (ATgtNode nd) (AVHex n)))
         ++ₗ outer)
      ≡ just (mkResult
                (RawAssign (mkRawAttrAssign name (ATgtNode nd)
                              (RavDecRat (NatDecRat.value n))))
                (TraceNode.pos9 pos name nd
                   (showℕ-dec-chars (natDecRatToℕ n)) outer)
                outer)
  on-AVHex-Node defs pos name nd n outer n-stop ss-NL =
    subst
      (λ q → parseAttrLine pos
                (emitAttribute-chars defs
                   (DBCAttrAssign (mkAttrAssign name (ATgtNode nd) (AVHex n)))
                 ++ₗ outer)
               ≡ just (mkResult
                         (RawAssign (mkRawAttrAssign name (ATgtNode nd) (RavDecRat q)))
                         (TraceNode.pos9 pos name nd
                            (showℕ-dec-chars (natDecRatToℕ n)) outer)
                         outer))
      (fromℕ-natDecRatToℕ n)
      (parseAttrLine-on-RavBareInt-Node pos name nd (+ natDecRatToℕ n)
         outer n-stop ss-NL)

  on-AVHex-Message :
      ∀ (defs : List AttrDef) (pos : Position) (name : List Char)
        (cid : _) (n : NatDecRat) (outer : List Char)
    → SuffixStops isNewlineStart outer
    → parseAttrLine pos
        (emitAttribute-chars defs
           (DBCAttrAssign (mkAttrAssign name (ATgtMessage cid) (AVHex n)))
         ++ₗ outer)
      ≡ just (mkResult
                (RawAssign (mkRawAttrAssign name (ATgtMessage cid)
                              (RavDecRat (NatDecRat.value n))))
                (TraceMessage.pos9 pos name cid
                   (showℕ-dec-chars (natDecRatToℕ n)) outer)
                outer)
  on-AVHex-Message defs pos name cid n outer ss-NL =
    subst
      (λ q → parseAttrLine pos
                (emitAttribute-chars defs
                   (DBCAttrAssign (mkAttrAssign name (ATgtMessage cid) (AVHex n)))
                 ++ₗ outer)
               ≡ just (mkResult
                         (RawAssign (mkRawAttrAssign name (ATgtMessage cid)
                                       (RavDecRat q)))
                         (TraceMessage.pos9 pos name cid
                            (showℕ-dec-chars (natDecRatToℕ n)) outer)
                         outer))
      (fromℕ-natDecRatToℕ n)
      (parseAttrLine-on-RavBareInt-Message pos name cid (+ natDecRatToℕ n)
         outer ss-NL)

  on-AVHex-Signal :
      ∀ (defs : List AttrDef) (pos : Position) (name : List Char)
        (cid : _) (sig : Identifier) (n : NatDecRat) (outer : List Char)
    → IdentNameStop-of (ATgtSignal cid sig)
    → SuffixStops isNewlineStart outer
    → parseAttrLine pos
        (emitAttribute-chars defs
           (DBCAttrAssign (mkAttrAssign name (ATgtSignal cid sig) (AVHex n)))
         ++ₗ outer)
      ≡ just (mkResult
                (RawAssign (mkRawAttrAssign name (ATgtSignal cid sig)
                              (RavDecRat (NatDecRat.value n))))
                (TraceSignal.pos9 pos name cid sig
                   (showℕ-dec-chars (natDecRatToℕ n)) outer)
                outer)
  on-AVHex-Signal defs pos name cid sig n outer sig-stop ss-NL =
    subst
      (λ q → parseAttrLine pos
                (emitAttribute-chars defs
                   (DBCAttrAssign (mkAttrAssign name (ATgtSignal cid sig) (AVHex n)))
                 ++ₗ outer)
               ≡ just (mkResult
                         (RawAssign (mkRawAttrAssign name (ATgtSignal cid sig)
                                       (RavDecRat q)))
                         (TraceSignal.pos9 pos name cid sig
                            (showℕ-dec-chars (natDecRatToℕ n)) outer)
                         outer))
      (fromℕ-natDecRatToℕ n)
      (parseAttrLine-on-RavBareInt-Signal pos name cid sig (+ natDecRatToℕ n)
         outer sig-stop ss-NL)

  on-AVHex-EnvVar :
      ∀ (defs : List AttrDef) (pos : Position) (name : List Char)
        (ev : Identifier) (n : NatDecRat) (outer : List Char)
    → IdentNameStop-of (ATgtEnvVar ev)
    → SuffixStops isNewlineStart outer
    → parseAttrLine pos
        (emitAttribute-chars defs
           (DBCAttrAssign (mkAttrAssign name (ATgtEnvVar ev) (AVHex n)))
         ++ₗ outer)
      ≡ just (mkResult
                (RawAssign (mkRawAttrAssign name (ATgtEnvVar ev)
                              (RavDecRat (NatDecRat.value n))))
                (TraceEnvVar.pos9 pos name ev
                   (showℕ-dec-chars (natDecRatToℕ n)) outer)
                outer)
  on-AVHex-EnvVar defs pos name ev n outer ev-stop ss-NL =
    subst
      (λ q → parseAttrLine pos
                (emitAttribute-chars defs
                   (DBCAttrAssign (mkAttrAssign name (ATgtEnvVar ev) (AVHex n)))
                 ++ₗ outer)
               ≡ just (mkResult
                         (RawAssign (mkRawAttrAssign name (ATgtEnvVar ev)
                                       (RavDecRat q)))
                         (TraceEnvVar.pos9 pos name ev
                            (showℕ-dec-chars (natDecRatToℕ n)) outer)
                         outer))
      (fromℕ-natDecRatToℕ n)
      (parseAttrLine-on-RavBareInt-EnvVar pos name ev (+ natDecRatToℕ n)
         outer ev-stop ss-NL)

  on-AVHex-NodeMsg :
      ∀ (defs : List AttrDef) (pos : Position) (name : List Char)
        (nd : Identifier) (cid : _) (n : NatDecRat) (outer : List Char)
    → IdentNameStop-of (ATgtNodeMsg nd cid)
    → SuffixStops isNewlineStart outer
    → parseAttrLine pos
        (emitAttribute-chars defs
           (DBCAttrAssign (mkAttrAssign name (ATgtNodeMsg nd cid) (AVHex n)))
         ++ₗ outer)
      ≡ just (mkResult
                (RawAssign (mkRawAttrAssign name (ATgtNodeMsg nd cid)
                              (RavDecRat (NatDecRat.value n))))
                (TraceNodeMsg.pos9 pos name nd cid
                   (showℕ-dec-chars (natDecRatToℕ n)) outer)
                outer)
  on-AVHex-NodeMsg defs pos name nd cid n outer n-stop ss-NL =
    subst
      (λ q → parseAttrLine pos
                (emitAttribute-chars defs
                   (DBCAttrAssign (mkAttrAssign name (ATgtNodeMsg nd cid) (AVHex n)))
                 ++ₗ outer)
               ≡ just (mkResult
                         (RawAssign (mkRawAttrAssign name (ATgtNodeMsg nd cid)
                                       (RavDecRat q)))
                         (TraceNodeMsg.pos9 pos name nd cid
                            (showℕ-dec-chars (natDecRatToℕ n)) outer)
                         outer))
      (fromℕ-natDecRatToℕ n)
      (parseAttrLine-on-RavBareInt-NodeMsg pos name nd cid (+ natDecRatToℕ n)
         outer n-stop ss-NL)

  on-AVHex-NodeSig :
      ∀ (defs : List AttrDef) (pos : Position) (name : List Char)
        (nd : Identifier) (cid : _) (sig : Identifier) (n : NatDecRat)
        (outer : List Char)
    → IdentNameStop-of (ATgtNodeSig nd cid sig)
    → SuffixStops isNewlineStart outer
    → parseAttrLine pos
        (emitAttribute-chars defs
           (DBCAttrAssign (mkAttrAssign name (ATgtNodeSig nd cid sig) (AVHex n)))
         ++ₗ outer)
      ≡ just (mkResult
                (RawAssign (mkRawAttrAssign name (ATgtNodeSig nd cid sig)
                              (RavDecRat (NatDecRat.value n))))
                (TraceNodeSig.pos9 pos name nd cid sig
                   (showℕ-dec-chars (natDecRatToℕ n)) outer)
                outer)
  on-AVHex-NodeSig defs pos name nd cid sig n outer stops ss-NL =
    subst
      (λ q → parseAttrLine pos
                (emitAttribute-chars defs
                   (DBCAttrAssign
                      (mkAttrAssign name (ATgtNodeSig nd cid sig) (AVHex n)))
                 ++ₗ outer)
               ≡ just (mkResult
                         (RawAssign (mkRawAttrAssign name (ATgtNodeSig nd cid sig)
                                       (RavDecRat q)))
                         (TraceNodeSig.pos9 pos name nd cid sig
                            (showℕ-dec-chars (natDecRatToℕ n)) outer)
                         outer))
      (fromℕ-natDecRatToℕ n)
      (parseAttrLine-on-RavBareInt-NodeSig pos name nd cid sig (+ natDecRatToℕ n)
         outer (proj₁ stops) (proj₂ stops) ss-NL)

  -- ============================================================================
  -- AVEnum × 7 targets  (assignment context: same emit shape as AVHex; only
  -- default context routes through `nthLabel`).  Bridge identical.
  -- ============================================================================

  on-AVEnum-Network :
      ∀ (defs : List AttrDef) (pos : Position) (name : List Char)
        (n : NatDecRat) (outer : List Char)
    → SuffixStops isNewlineStart outer
    → parseAttrLine pos
        (emitAttribute-chars defs
           (DBCAttrAssign (mkAttrAssign name ATgtNetwork (AVEnum n)))
         ++ₗ outer)
      ≡ just (mkResult
                (RawAssign (mkRawAttrAssign name ATgtNetwork
                              (RavDecRat (NatDecRat.value n))))
                (TraceNetwork.pos9 pos name (showℕ-dec-chars (natDecRatToℕ n)) outer)
                outer)
  on-AVEnum-Network defs pos name n outer ss-NL =
    subst
      (λ q → parseAttrLine pos
                (emitAttribute-chars defs
                   (DBCAttrAssign (mkAttrAssign name ATgtNetwork (AVEnum n)))
                 ++ₗ outer)
               ≡ just (mkResult
                         (RawAssign (mkRawAttrAssign name ATgtNetwork (RavDecRat q)))
                         (TraceNetwork.pos9 pos name
                            (showℕ-dec-chars (natDecRatToℕ n)) outer)
                         outer))
      (fromℕ-natDecRatToℕ n)
      (parseAttrLine-on-RavBareInt-Network pos name (+ natDecRatToℕ n) outer ss-NL)

  on-AVEnum-Node :
      ∀ (defs : List AttrDef) (pos : Position) (name : List Char)
        (nd : Identifier) (n : NatDecRat) (outer : List Char)
    → IdentNameStop-of (ATgtNode nd)
    → SuffixStops isNewlineStart outer
    → parseAttrLine pos
        (emitAttribute-chars defs
           (DBCAttrAssign (mkAttrAssign name (ATgtNode nd) (AVEnum n)))
         ++ₗ outer)
      ≡ just (mkResult
                (RawAssign (mkRawAttrAssign name (ATgtNode nd)
                              (RavDecRat (NatDecRat.value n))))
                (TraceNode.pos9 pos name nd
                   (showℕ-dec-chars (natDecRatToℕ n)) outer)
                outer)
  on-AVEnum-Node defs pos name nd n outer n-stop ss-NL =
    subst
      (λ q → parseAttrLine pos
                (emitAttribute-chars defs
                   (DBCAttrAssign (mkAttrAssign name (ATgtNode nd) (AVEnum n)))
                 ++ₗ outer)
               ≡ just (mkResult
                         (RawAssign (mkRawAttrAssign name (ATgtNode nd) (RavDecRat q)))
                         (TraceNode.pos9 pos name nd
                            (showℕ-dec-chars (natDecRatToℕ n)) outer)
                         outer))
      (fromℕ-natDecRatToℕ n)
      (parseAttrLine-on-RavBareInt-Node pos name nd (+ natDecRatToℕ n)
         outer n-stop ss-NL)

  on-AVEnum-Message :
      ∀ (defs : List AttrDef) (pos : Position) (name : List Char)
        (cid : _) (n : NatDecRat) (outer : List Char)
    → SuffixStops isNewlineStart outer
    → parseAttrLine pos
        (emitAttribute-chars defs
           (DBCAttrAssign (mkAttrAssign name (ATgtMessage cid) (AVEnum n)))
         ++ₗ outer)
      ≡ just (mkResult
                (RawAssign (mkRawAttrAssign name (ATgtMessage cid)
                              (RavDecRat (NatDecRat.value n))))
                (TraceMessage.pos9 pos name cid
                   (showℕ-dec-chars (natDecRatToℕ n)) outer)
                outer)
  on-AVEnum-Message defs pos name cid n outer ss-NL =
    subst
      (λ q → parseAttrLine pos
                (emitAttribute-chars defs
                   (DBCAttrAssign (mkAttrAssign name (ATgtMessage cid) (AVEnum n)))
                 ++ₗ outer)
               ≡ just (mkResult
                         (RawAssign (mkRawAttrAssign name (ATgtMessage cid)
                                       (RavDecRat q)))
                         (TraceMessage.pos9 pos name cid
                            (showℕ-dec-chars (natDecRatToℕ n)) outer)
                         outer))
      (fromℕ-natDecRatToℕ n)
      (parseAttrLine-on-RavBareInt-Message pos name cid (+ natDecRatToℕ n)
         outer ss-NL)

  on-AVEnum-Signal :
      ∀ (defs : List AttrDef) (pos : Position) (name : List Char)
        (cid : _) (sig : Identifier) (n : NatDecRat) (outer : List Char)
    → IdentNameStop-of (ATgtSignal cid sig)
    → SuffixStops isNewlineStart outer
    → parseAttrLine pos
        (emitAttribute-chars defs
           (DBCAttrAssign (mkAttrAssign name (ATgtSignal cid sig) (AVEnum n)))
         ++ₗ outer)
      ≡ just (mkResult
                (RawAssign (mkRawAttrAssign name (ATgtSignal cid sig)
                              (RavDecRat (NatDecRat.value n))))
                (TraceSignal.pos9 pos name cid sig
                   (showℕ-dec-chars (natDecRatToℕ n)) outer)
                outer)
  on-AVEnum-Signal defs pos name cid sig n outer sig-stop ss-NL =
    subst
      (λ q → parseAttrLine pos
                (emitAttribute-chars defs
                   (DBCAttrAssign (mkAttrAssign name (ATgtSignal cid sig) (AVEnum n)))
                 ++ₗ outer)
               ≡ just (mkResult
                         (RawAssign (mkRawAttrAssign name (ATgtSignal cid sig)
                                       (RavDecRat q)))
                         (TraceSignal.pos9 pos name cid sig
                            (showℕ-dec-chars (natDecRatToℕ n)) outer)
                         outer))
      (fromℕ-natDecRatToℕ n)
      (parseAttrLine-on-RavBareInt-Signal pos name cid sig (+ natDecRatToℕ n)
         outer sig-stop ss-NL)

  on-AVEnum-EnvVar :
      ∀ (defs : List AttrDef) (pos : Position) (name : List Char)
        (ev : Identifier) (n : NatDecRat) (outer : List Char)
    → IdentNameStop-of (ATgtEnvVar ev)
    → SuffixStops isNewlineStart outer
    → parseAttrLine pos
        (emitAttribute-chars defs
           (DBCAttrAssign (mkAttrAssign name (ATgtEnvVar ev) (AVEnum n)))
         ++ₗ outer)
      ≡ just (mkResult
                (RawAssign (mkRawAttrAssign name (ATgtEnvVar ev)
                              (RavDecRat (NatDecRat.value n))))
                (TraceEnvVar.pos9 pos name ev
                   (showℕ-dec-chars (natDecRatToℕ n)) outer)
                outer)
  on-AVEnum-EnvVar defs pos name ev n outer ev-stop ss-NL =
    subst
      (λ q → parseAttrLine pos
                (emitAttribute-chars defs
                   (DBCAttrAssign (mkAttrAssign name (ATgtEnvVar ev) (AVEnum n)))
                 ++ₗ outer)
               ≡ just (mkResult
                         (RawAssign (mkRawAttrAssign name (ATgtEnvVar ev)
                                       (RavDecRat q)))
                         (TraceEnvVar.pos9 pos name ev
                            (showℕ-dec-chars (natDecRatToℕ n)) outer)
                         outer))
      (fromℕ-natDecRatToℕ n)
      (parseAttrLine-on-RavBareInt-EnvVar pos name ev (+ natDecRatToℕ n)
         outer ev-stop ss-NL)

  on-AVEnum-NodeMsg :
      ∀ (defs : List AttrDef) (pos : Position) (name : List Char)
        (nd : Identifier) (cid : _) (n : NatDecRat) (outer : List Char)
    → IdentNameStop-of (ATgtNodeMsg nd cid)
    → SuffixStops isNewlineStart outer
    → parseAttrLine pos
        (emitAttribute-chars defs
           (DBCAttrAssign (mkAttrAssign name (ATgtNodeMsg nd cid) (AVEnum n)))
         ++ₗ outer)
      ≡ just (mkResult
                (RawAssign (mkRawAttrAssign name (ATgtNodeMsg nd cid)
                              (RavDecRat (NatDecRat.value n))))
                (TraceNodeMsg.pos9 pos name nd cid
                   (showℕ-dec-chars (natDecRatToℕ n)) outer)
                outer)
  on-AVEnum-NodeMsg defs pos name nd cid n outer n-stop ss-NL =
    subst
      (λ q → parseAttrLine pos
                (emitAttribute-chars defs
                   (DBCAttrAssign (mkAttrAssign name (ATgtNodeMsg nd cid) (AVEnum n)))
                 ++ₗ outer)
               ≡ just (mkResult
                         (RawAssign (mkRawAttrAssign name (ATgtNodeMsg nd cid)
                                       (RavDecRat q)))
                         (TraceNodeMsg.pos9 pos name nd cid
                            (showℕ-dec-chars (natDecRatToℕ n)) outer)
                         outer))
      (fromℕ-natDecRatToℕ n)
      (parseAttrLine-on-RavBareInt-NodeMsg pos name nd cid (+ natDecRatToℕ n)
         outer n-stop ss-NL)

  on-AVEnum-NodeSig :
      ∀ (defs : List AttrDef) (pos : Position) (name : List Char)
        (nd : Identifier) (cid : _) (sig : Identifier) (n : NatDecRat)
        (outer : List Char)
    → IdentNameStop-of (ATgtNodeSig nd cid sig)
    → SuffixStops isNewlineStart outer
    → parseAttrLine pos
        (emitAttribute-chars defs
           (DBCAttrAssign (mkAttrAssign name (ATgtNodeSig nd cid sig) (AVEnum n)))
         ++ₗ outer)
      ≡ just (mkResult
                (RawAssign (mkRawAttrAssign name (ATgtNodeSig nd cid sig)
                              (RavDecRat (NatDecRat.value n))))
                (TraceNodeSig.pos9 pos name nd cid sig
                   (showℕ-dec-chars (natDecRatToℕ n)) outer)
                outer)
  on-AVEnum-NodeSig defs pos name nd cid sig n outer stops ss-NL =
    subst
      (λ q → parseAttrLine pos
                (emitAttribute-chars defs
                   (DBCAttrAssign
                      (mkAttrAssign name (ATgtNodeSig nd cid sig) (AVEnum n)))
                 ++ₗ outer)
               ≡ just (mkResult
                         (RawAssign (mkRawAttrAssign name (ATgtNodeSig nd cid sig)
                                       (RavDecRat q)))
                         (TraceNodeSig.pos9 pos name nd cid sig
                            (showℕ-dec-chars (natDecRatToℕ n)) outer)
                         outer))
      (fromℕ-natDecRatToℕ n)
      (parseAttrLine-on-RavBareInt-NodeSig pos name nd cid sig (+ natDecRatToℕ n)
         outer (proj₁ stops) (proj₂ stops) ss-NL)

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
