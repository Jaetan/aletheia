{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 4c — Universal-attribute roundtrip dispatcher for the
-- RawAssign × RavDecRat (bareInt form) shape (7 targets).
--
-- Mirror of `Assign/String.agda` with `showInt-chars z` (z : ℤ) replacing
-- `quoteStringLit-chars s`.  Output: `RavDecRat (fromℤ z)`.
--
-- 7 separate per-target functions take spelled-out input shapes (no
-- `emitAttribute-chars` wrapper) since AVInt/AVHex/AVEnum all dispatch
-- here with different value-bridge forms.  The AttrAssign-level
-- dispatcher (`Assign.agda`) passes:
--   * AVInt z'   ⟹ z = intDecRatToℤ z'   + value-bridge IntDecRat.value z' ≡ fromℤ ...
--   * AVHex n    ⟹ z = + natDecRatToℕ n  + value-bridge NatDecRat.value n  ≡ fromℤ ...
--   * AVEnum n   ⟹ z = + natDecRatToℕ n  + same NatDecRat bridge
module Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Attribute.Assign.BareInt where

open import Data.Char  using (Char)
open import Data.Integer using (ℤ; +_)
open import Data.List  using (List; []; _∷_)
  renaming (_++_ to _++ₗ_)
open import Data.List.Properties using ()
  renaming (++-assoc to ++ₗ-assoc)
open import Data.Maybe using (just)
open import Data.Product using (proj₁; proj₂)
open import Data.String using (String; toList)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Aletheia.Parser.Combinators using
  (Position; ParseResult; mkResult; advancePositions)

open import Aletheia.CAN.Frame using (CANId)
open import Aletheia.DBC.DecRat using (DecRat; fromℤ)
open import Aletheia.DBC.Identifier using (Identifier)

open import Aletheia.DBC.TextFormatter.Topology using (rawCanIdℕ)
open import Aletheia.DBC.TextFormatter.Emitter using
  (quoteStringLit-chars; showInt-chars; showℕ-dec-chars)

open import Aletheia.DBC.TextParser.Attributes using
  (RawDBCAttribute; RawAssign; mkRawAttrAssign
  ; RawAttrValue;   RavDecRat
  ; parseAttrLine)

open import Aletheia.DBC.Types using
  ( AttrTarget; ATgtNetwork; ATgtNode; ATgtMessage; ATgtSignal; ATgtEnvVar
  ; ATgtNodeMsg; ATgtNodeSig)

open import Aletheia.DBC.TextParser.Properties.Attributes.Line using
  ( parseAttrLine-roundtrip-RawAssign-ATgtNetwork-RavDecRatBareInt
  ; parseAttrLine-roundtrip-RawAssign-ATgtNode-RavDecRatBareInt
  ; parseAttrLine-roundtrip-RawAssign-ATgtMessage-RavDecRatBareInt
  ; parseAttrLine-roundtrip-RawAssign-ATgtSignal-RavDecRatBareInt
  ; parseAttrLine-roundtrip-RawAssign-ATgtEnvVar-RavDecRatBareInt
  ; parseAttrLine-roundtrip-RawAssign-ATgtNodeMsg-RavDecRatBareInt
  ; parseAttrLine-roundtrip-RawAssign-ATgtNodeSig-RavDecRatBareInt
  )

open import Aletheia.DBC.TextParser.Properties.Attributes.Assign using
  (IdentNameStop)
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

-- ============================================================================
-- INPUT BRIDGES — same shape as String.agda, with `showInt-chars z`
-- ============================================================================

private
  trail-bridge :
      ∀ (V outer : List Char)
    → (' ' ∷ V ++ₗ toList ";\n") ++ₗ outer
      ≡ ' ' ∷ V ++ₗ toList ";\n" ++ₗ outer
  trail-bridge V outer =
    cong (' ' ∷_) (++ₗ-assoc V (toList ";\n") outer)

  network-input-bridge :
      ∀ (name : List Char) (z : ℤ) (outer : List Char)
    → (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
         ' ' ∷ showInt-chars z ++ₗ toList ";\n") ++ₗ outer
      ≡ toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
         ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer
  network-input-bridge name z outer =
    trans (++ₗ-assoc (toList "BA_ ") _ outer)
      (cong (toList "BA_ " ++ₗ_)
        (trans (++ₗ-assoc (quoteStringLit-chars name) _ outer)
          (cong (quoteStringLit-chars name ++ₗ_)
                (trail-bridge (showInt-chars z) outer))))

  node-input-bridge :
      ∀ (name : List Char) (n : Identifier) (z : ℤ) (outer : List Char)
    → (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
         toList " BU_ " ++ₗ Identifier.name n ++ₗ
         ' ' ∷ showInt-chars z ++ₗ toList ";\n") ++ₗ outer
      ≡ toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
         toList " BU_ " ++ₗ Identifier.name n ++ₗ
         ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer
  node-input-bridge name n z outer =
    trans (++ₗ-assoc (toList "BA_ ") _ outer)
      (cong (toList "BA_ " ++ₗ_)
        (trans (++ₗ-assoc (quoteStringLit-chars name) _ outer)
          (cong (quoteStringLit-chars name ++ₗ_)
            (trans (++ₗ-assoc (toList " BU_ ") _ outer)
              (cong (toList " BU_ " ++ₗ_)
                (trans (++ₗ-assoc (Identifier.name n) _ outer)
                  (cong (Identifier.name n ++ₗ_)
                        (trail-bridge (showInt-chars z) outer))))))))

  message-input-bridge :
      ∀ (name : List Char) (cid : CANId) (z : ℤ) (outer : List Char)
    → (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
         toList " BO_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
         ' ' ∷ showInt-chars z ++ₗ toList ";\n") ++ₗ outer
      ≡ toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
         toList " BO_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
         ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer
  message-input-bridge name cid z outer =
    trans (++ₗ-assoc (toList "BA_ ") _ outer)
      (cong (toList "BA_ " ++ₗ_)
        (trans (++ₗ-assoc (quoteStringLit-chars name) _ outer)
          (cong (quoteStringLit-chars name ++ₗ_)
            (trans (++ₗ-assoc (toList " BO_ ") _ outer)
              (cong (toList " BO_ " ++ₗ_)
                (trans (++ₗ-assoc (showℕ-dec-chars (rawCanIdℕ cid)) _ outer)
                  (cong (showℕ-dec-chars (rawCanIdℕ cid) ++ₗ_)
                        (trail-bridge (showInt-chars z) outer))))))))

  private-signal-trail :
      ∀ (sig-name : List Char) (V : List Char) (outer : List Char)
    → (' ' ∷ sig-name ++ₗ ' ' ∷ V ++ₗ toList ";\n") ++ₗ outer
      ≡ ' ' ∷ sig-name ++ₗ ' ' ∷ V ++ₗ toList ";\n" ++ₗ outer
  private-signal-trail sig-name V outer =
    cong (' ' ∷_)
      (trans (++ₗ-assoc sig-name _ outer)
        (cong (sig-name ++ₗ_) (trail-bridge V outer)))

  signal-input-bridge :
      ∀ (name : List Char) (cid : CANId) (sig : Identifier) (z : ℤ) (outer : List Char)
    → (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
         toList " SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
         ' ' ∷ Identifier.name sig ++ₗ
         ' ' ∷ showInt-chars z ++ₗ toList ";\n") ++ₗ outer
      ≡ toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
         toList " SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
         ' ' ∷ Identifier.name sig ++ₗ
         ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer
  signal-input-bridge name cid sig z outer =
    trans (++ₗ-assoc (toList "BA_ ") _ outer)
      (cong (toList "BA_ " ++ₗ_)
        (trans (++ₗ-assoc (quoteStringLit-chars name) _ outer)
          (cong (quoteStringLit-chars name ++ₗ_)
            (trans (++ₗ-assoc (toList " SG_ ") _ outer)
              (cong (toList " SG_ " ++ₗ_)
                (trans (++ₗ-assoc (showℕ-dec-chars (rawCanIdℕ cid)) _ outer)
                  (cong (showℕ-dec-chars (rawCanIdℕ cid) ++ₗ_)
                        (private-signal-trail
                           (Identifier.name sig)
                           (showInt-chars z) outer))))))))

  envvar-input-bridge :
      ∀ (name : List Char) (ev : Identifier) (z : ℤ) (outer : List Char)
    → (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
         toList " EV_ " ++ₗ Identifier.name ev ++ₗ
         ' ' ∷ showInt-chars z ++ₗ toList ";\n") ++ₗ outer
      ≡ toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
         toList " EV_ " ++ₗ Identifier.name ev ++ₗ
         ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer
  envvar-input-bridge name ev z outer =
    trans (++ₗ-assoc (toList "BA_ ") _ outer)
      (cong (toList "BA_ " ++ₗ_)
        (trans (++ₗ-assoc (quoteStringLit-chars name) _ outer)
          (cong (quoteStringLit-chars name ++ₗ_)
            (trans (++ₗ-assoc (toList " EV_ ") _ outer)
              (cong (toList " EV_ " ++ₗ_)
                (trans (++ₗ-assoc (Identifier.name ev) _ outer)
                  (cong (Identifier.name ev ++ₗ_)
                        (trail-bridge (showInt-chars z) outer))))))))

  nodemsg-input-bridge :
      ∀ (name : List Char) (n : Identifier) (cid : CANId) (z : ℤ) (outer : List Char)
    → (toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
         toList " BU_BO_REL_ " ++ₗ Identifier.name n ++ₗ
         ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
         ' ' ∷ showInt-chars z ++ₗ toList ";\n") ++ₗ outer
      ≡ toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
         toList " BU_BO_REL_ " ++ₗ Identifier.name n ++ₗ
         ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
         ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer
  nodemsg-input-bridge name n cid z outer =
    trans (++ₗ-assoc (toList "BA_REL_ ") _ outer)
      (cong (toList "BA_REL_ " ++ₗ_)
        (trans (++ₗ-assoc (quoteStringLit-chars name) _ outer)
          (cong (quoteStringLit-chars name ++ₗ_)
            (trans (++ₗ-assoc (toList " BU_BO_REL_ ") _ outer)
              (cong (toList " BU_BO_REL_ " ++ₗ_)
                (trans (++ₗ-assoc (Identifier.name n) _ outer)
                  (cong (Identifier.name n ++ₗ_)
                        (private-signal-trail
                           (showℕ-dec-chars (rawCanIdℕ cid))
                           (showInt-chars z) outer))))))))

  nodesig-input-bridge :
      ∀ (name : List Char) (n : Identifier) (cid : CANId) (sig : Identifier)
        (z : ℤ) (outer : List Char)
    → (toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
         toList " BU_SG_REL_ " ++ₗ Identifier.name n ++ₗ
         toList " SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
         ' ' ∷ Identifier.name sig ++ₗ
         ' ' ∷ showInt-chars z ++ₗ toList ";\n") ++ₗ outer
      ≡ toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
         toList " BU_SG_REL_ " ++ₗ Identifier.name n ++ₗ
         toList " SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
         ' ' ∷ Identifier.name sig ++ₗ
         ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer
  nodesig-input-bridge name n cid sig z outer =
    trans (++ₗ-assoc (toList "BA_REL_ ") _ outer)
      (cong (toList "BA_REL_ " ++ₗ_)
        (trans (++ₗ-assoc (quoteStringLit-chars name) _ outer)
          (cong (quoteStringLit-chars name ++ₗ_)
            (trans (++ₗ-assoc (toList " BU_SG_REL_ ") _ outer)
              (cong (toList " BU_SG_REL_ " ++ₗ_)
                (trans (++ₗ-assoc (Identifier.name n) _ outer)
                  (cong (Identifier.name n ++ₗ_)
                    (trans (++ₗ-assoc (toList " SG_ ") _ outer)
                      (cong (toList " SG_ " ++ₗ_)
                        (trans (++ₗ-assoc (showℕ-dec-chars (rawCanIdℕ cid)) _ outer)
                          (cong (showℕ-dec-chars (rawCanIdℕ cid) ++ₗ_)
                                (private-signal-trail
                                   (Identifier.name sig)
                                   (showInt-chars z) outer))))))))))))

-- ============================================================================
-- 7 PER-TARGET DISPATCHERS — spelled-out emit form, parameterized by ℤ
--
-- The dispatcher's input is the spelled-out emit form (with `showInt-
-- chars z` literal); the AttrAssign-level dispatcher (`Assign.agda`)
-- is responsible for bridging from `emitAttribute-chars defs (DBCAttr-
-- Assign (mkAttrAssign name target value))` (which reduces to the same
-- spelled-out form when `value` is AVInt/AVHex/AVEnum) and for the
-- per-AVx value bridge `RavDecRat (fromℤ z) ↔ RavDecRat (X.value v)`.
-- ============================================================================

parseAttrLine-on-RavBareInt-Network :
    ∀ (pos : Position) (name : List Char) (z : ℤ) (outer : List Char)
  → SuffixStops isNewlineStart outer
  → parseAttrLine pos
      ((toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
         ' ' ∷ showInt-chars z ++ₗ toList ";\n") ++ₗ outer)
    ≡ just (mkResult
              (RawAssign (mkRawAttrAssign name ATgtNetwork (RavDecRat (fromℤ z))))
              (TraceNetwork.pos9 pos name (showInt-chars z) outer)
              outer)
parseAttrLine-on-RavBareInt-Network pos name z outer ss-NL =
  subst
    (λ inp → parseAttrLine pos inp
              ≡ just (mkResult
                        (RawAssign (mkRawAttrAssign name ATgtNetwork (RavDecRat (fromℤ z))))
                        (TraceNetwork.pos9 pos name (showInt-chars z) outer)
                        outer))
    (sym (network-input-bridge name z outer))
    (parseAttrLine-roundtrip-RawAssign-ATgtNetwork-RavDecRatBareInt
       pos name z outer ss-NL)

parseAttrLine-on-RavBareInt-Node :
    ∀ (pos : Position) (name : List Char) (n : Identifier) (z : ℤ) (outer : List Char)
  → IdentNameStop n
  → SuffixStops isNewlineStart outer
  → parseAttrLine pos
      ((toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
         toList " BU_ " ++ₗ Identifier.name n ++ₗ
         ' ' ∷ showInt-chars z ++ₗ toList ";\n") ++ₗ outer)
    ≡ just (mkResult
              (RawAssign (mkRawAttrAssign name (ATgtNode n) (RavDecRat (fromℤ z))))
              (TraceNode.pos9 pos name n (showInt-chars z) outer)
              outer)
parseAttrLine-on-RavBareInt-Node pos name n z outer n-stop ss-NL =
  subst
    (λ inp → parseAttrLine pos inp
              ≡ just (mkResult
                        (RawAssign (mkRawAttrAssign name (ATgtNode n) (RavDecRat (fromℤ z))))
                        (TraceNode.pos9 pos name n (showInt-chars z) outer)
                        outer))
    (sym (node-input-bridge name n z outer))
    (parseAttrLine-roundtrip-RawAssign-ATgtNode-RavDecRatBareInt
       pos name n z outer n-stop ss-NL)

parseAttrLine-on-RavBareInt-Message :
    ∀ (pos : Position) (name : List Char) (cid : CANId) (z : ℤ) (outer : List Char)
  → SuffixStops isNewlineStart outer
  → parseAttrLine pos
      ((toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
         toList " BO_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
         ' ' ∷ showInt-chars z ++ₗ toList ";\n") ++ₗ outer)
    ≡ just (mkResult
              (RawAssign (mkRawAttrAssign name (ATgtMessage cid) (RavDecRat (fromℤ z))))
              (TraceMessage.pos9 pos name cid (showInt-chars z) outer)
              outer)
parseAttrLine-on-RavBareInt-Message pos name cid z outer ss-NL =
  subst
    (λ inp → parseAttrLine pos inp
              ≡ just (mkResult
                        (RawAssign (mkRawAttrAssign name (ATgtMessage cid) (RavDecRat (fromℤ z))))
                        (TraceMessage.pos9 pos name cid (showInt-chars z) outer)
                        outer))
    (sym (message-input-bridge name cid z outer))
    (parseAttrLine-roundtrip-RawAssign-ATgtMessage-RavDecRatBareInt
       pos name cid z outer ss-NL)

parseAttrLine-on-RavBareInt-Signal :
    ∀ (pos : Position) (name : List Char) (cid : CANId) (sig : Identifier)
      (z : ℤ) (outer : List Char)
  → IdentNameStop sig
  → SuffixStops isNewlineStart outer
  → parseAttrLine pos
      ((toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
         toList " SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
         ' ' ∷ Identifier.name sig ++ₗ
         ' ' ∷ showInt-chars z ++ₗ toList ";\n") ++ₗ outer)
    ≡ just (mkResult
              (RawAssign (mkRawAttrAssign name (ATgtSignal cid sig) (RavDecRat (fromℤ z))))
              (TraceSignal.pos9 pos name cid sig (showInt-chars z) outer)
              outer)
parseAttrLine-on-RavBareInt-Signal pos name cid sig z outer sig-stop ss-NL =
  subst
    (λ inp → parseAttrLine pos inp
              ≡ just (mkResult
                        (RawAssign (mkRawAttrAssign name (ATgtSignal cid sig) (RavDecRat (fromℤ z))))
                        (TraceSignal.pos9 pos name cid sig (showInt-chars z) outer)
                        outer))
    (sym (signal-input-bridge name cid sig z outer))
    (parseAttrLine-roundtrip-RawAssign-ATgtSignal-RavDecRatBareInt
       pos name cid sig z outer sig-stop ss-NL)

parseAttrLine-on-RavBareInt-EnvVar :
    ∀ (pos : Position) (name : List Char) (ev : Identifier) (z : ℤ) (outer : List Char)
  → IdentNameStop ev
  → SuffixStops isNewlineStart outer
  → parseAttrLine pos
      ((toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
         toList " EV_ " ++ₗ Identifier.name ev ++ₗ
         ' ' ∷ showInt-chars z ++ₗ toList ";\n") ++ₗ outer)
    ≡ just (mkResult
              (RawAssign (mkRawAttrAssign name (ATgtEnvVar ev) (RavDecRat (fromℤ z))))
              (TraceEnvVar.pos9 pos name ev (showInt-chars z) outer)
              outer)
parseAttrLine-on-RavBareInt-EnvVar pos name ev z outer ev-stop ss-NL =
  subst
    (λ inp → parseAttrLine pos inp
              ≡ just (mkResult
                        (RawAssign (mkRawAttrAssign name (ATgtEnvVar ev) (RavDecRat (fromℤ z))))
                        (TraceEnvVar.pos9 pos name ev (showInt-chars z) outer)
                        outer))
    (sym (envvar-input-bridge name ev z outer))
    (parseAttrLine-roundtrip-RawAssign-ATgtEnvVar-RavDecRatBareInt
       pos name ev z outer ev-stop ss-NL)

parseAttrLine-on-RavBareInt-NodeMsg :
    ∀ (pos : Position) (name : List Char) (n : Identifier) (cid : CANId)
      (z : ℤ) (outer : List Char)
  → IdentNameStop n
  → SuffixStops isNewlineStart outer
  → parseAttrLine pos
      ((toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
         toList " BU_BO_REL_ " ++ₗ Identifier.name n ++ₗ
         ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
         ' ' ∷ showInt-chars z ++ₗ toList ";\n") ++ₗ outer)
    ≡ just (mkResult
              (RawAssign (mkRawAttrAssign name (ATgtNodeMsg n cid) (RavDecRat (fromℤ z))))
              (TraceNodeMsg.pos9 pos name n cid (showInt-chars z) outer)
              outer)
parseAttrLine-on-RavBareInt-NodeMsg pos name n cid z outer n-stop ss-NL =
  subst
    (λ inp → parseAttrLine pos inp
              ≡ just (mkResult
                        (RawAssign (mkRawAttrAssign name (ATgtNodeMsg n cid) (RavDecRat (fromℤ z))))
                        (TraceNodeMsg.pos9 pos name n cid (showInt-chars z) outer)
                        outer))
    (sym (nodemsg-input-bridge name n cid z outer))
    (parseAttrLine-roundtrip-RawAssign-ATgtNodeMsg-RavDecRatBareInt
       pos name n cid z outer n-stop ss-NL)

parseAttrLine-on-RavBareInt-NodeSig :
    ∀ (pos : Position) (name : List Char) (n : Identifier) (cid : CANId)
      (sig : Identifier) (z : ℤ) (outer : List Char)
  → IdentNameStop n → IdentNameStop sig
  → SuffixStops isNewlineStart outer
  → parseAttrLine pos
      ((toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
         toList " BU_SG_REL_ " ++ₗ Identifier.name n ++ₗ
         toList " SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
         ' ' ∷ Identifier.name sig ++ₗ
         ' ' ∷ showInt-chars z ++ₗ toList ";\n") ++ₗ outer)
    ≡ just (mkResult
              (RawAssign (mkRawAttrAssign name (ATgtNodeSig n cid sig) (RavDecRat (fromℤ z))))
              (TraceNodeSig.pos9 pos name n cid sig (showInt-chars z) outer)
              outer)
parseAttrLine-on-RavBareInt-NodeSig pos name n cid sig z outer n-stop sig-stop ss-NL =
  subst
    (λ inp → parseAttrLine pos inp
              ≡ just (mkResult
                        (RawAssign (mkRawAttrAssign name (ATgtNodeSig n cid sig) (RavDecRat (fromℤ z))))
                        (TraceNodeSig.pos9 pos name n cid sig (showInt-chars z) outer)
                        outer))
    (sym (nodesig-input-bridge name n cid sig z outer))
    (parseAttrLine-roundtrip-RawAssign-ATgtNodeSig-RavDecRatBareInt
       pos name n cid sig z outer n-stop sig-stop ss-NL)
