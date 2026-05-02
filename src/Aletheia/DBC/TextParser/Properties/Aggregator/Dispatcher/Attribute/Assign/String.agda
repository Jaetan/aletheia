{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 4c — Universal-attribute roundtrip dispatcher for the
-- RawAssign × RavString shape (7 targets).
--
-- Per target:
--   * Input bridge: `(emitAttrAssign-chars a) ++ outer ≡ slim-input-
--     shape`.  N-1 ++ₗ-assoc applications where N is the # of `++`
--     segments in the emit; one inner cong-step at the `' ' ∷` cons
--     boundary uses ++ₗ-assoc inside the cons.
--   * Position bridge: `TraceXxx.pos9 pos … outer ≡ advancePositions
--     pos (emitAttrAssign-chars a)` reduces by `refl` for all 7
--     targets — the formatter's emit form and TraceXxx.pos9's body
--     share the same chunking (`toList ";\n" ≡ ';' ∷ '\n' ∷ []` is
--     the only definitional reduction needed).
--
-- The universal lemma at this shape takes typed `(name, target,
-- AVString s)` parameters and routes to the matching slim, dispatching
-- on `target` via constructor pattern-match (no `with`).
module Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Attribute.Assign.String where

open import Data.Char  using (Char)
open import Data.List  using (List; []; _∷_)
  renaming (_++_ to _++ₗ_)
open import Data.List.Properties using ()
  renaming (++-assoc to ++ₗ-assoc)
open import Data.Maybe using (just)
open import Data.String using (String; toList)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Aletheia.Parser.Combinators using
  (Position; ParseResult; mkResult; advancePositions)

open import Aletheia.CAN.Frame using (CANId)
open import Aletheia.DBC.Identifier using (Identifier)
open import Aletheia.DBC.Types using
  ( AttrDef
  ; AttrTarget; ATgtNetwork; ATgtNode; ATgtMessage; ATgtSignal; ATgtEnvVar
  ; ATgtNodeMsg; ATgtNodeSig
  ; AttrValue; AVString
  ; AttrAssign; mkAttrAssign
  ; DBCAttribute; DBCAttrAssign
  )

open import Aletheia.DBC.TextFormatter.Attributes using
  (emitAttribute-chars; emitAttrAssign-chars)
open import Aletheia.DBC.TextFormatter.Topology using (rawCanIdℕ)
open import Aletheia.DBC.TextFormatter.Emitter using
  (quoteStringLit-chars; showℕ-dec-chars)

open import Aletheia.DBC.TextParser.Attributes using
  (RawDBCAttribute; RawAssign; mkRawAttrAssign
  ; RawAttrValue;   RavString
  ; parseAttrLine)

open import Aletheia.DBC.TextParser.Properties.Aggregator.Foundations using
  (rawOf)
open import Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Attribute.Foundations using
  (IdentNameStop-of)

open import Aletheia.DBC.TextParser.Properties.Attributes.Line using
  ( parseAttrLine-roundtrip-RawAssign-ATgtNetwork-RavString
  ; parseAttrLine-roundtrip-RawAssign-ATgtNode-RavString
  ; parseAttrLine-roundtrip-RawAssign-ATgtMessage-RavString
  ; parseAttrLine-roundtrip-RawAssign-ATgtSignal-RavString
  ; parseAttrLine-roundtrip-RawAssign-ATgtEnvVar-RavString
  ; parseAttrLine-roundtrip-RawAssign-ATgtNodeMsg-RavString
  ; parseAttrLine-roundtrip-RawAssign-ATgtNodeSig-RavString
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

open import Data.Product using (proj₁; proj₂)

-- ============================================================================
-- INPUT BRIDGES — `(emit) ++ outer ≡ slim-input-shape` per target
-- ============================================================================
--
-- Each bridge applies (N-1) ++ₗ-assoc steps, cong-wrapped through the
-- closed and abstract prefixes.  Pattern: `trans (++ₗ-assoc A rest outer)
-- (cong (A ++_) <recurse on rest>)`, terminating with one inner step that
-- uses ++ₗ-assoc inside a `' ' ∷` cons.

private
  -- Helper: bridge the trailing `(' ' ∷ V ++ toList ";\n") ++ outer ≡
  -- ' ' ∷ (V ++ (toList ";\n" ++ outer))`.  Used in every target.
  trail-bridge :
      ∀ (V outer : List Char)
    → (' ' ∷ V ++ₗ toList ";\n") ++ₗ outer
      ≡ ' ' ∷ V ++ₗ toList ";\n" ++ₗ outer
  trail-bridge V outer =
    cong (' ' ∷_) (++ₗ-assoc V (toList ";\n") outer)

  -- Network: 4 segments — toList "BA_ " ++ qname ++ ' ' ∷ vstr ++ toList ";\n"
  network-input-bridge :
      ∀ (name s outer : List Char)
    → (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
         ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n") ++ₗ outer
      ≡ toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
         ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n" ++ₗ outer
  network-input-bridge name s outer =
    trans
      (++ₗ-assoc (toList "BA_ ")
                 (quoteStringLit-chars name ++ₗ
                  ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n")
                 outer)
      (cong (toList "BA_ " ++ₗ_)
        (trans
          (++ₗ-assoc (quoteStringLit-chars name)
                     (' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n")
                     outer)
          (cong (quoteStringLit-chars name ++ₗ_)
                (trail-bridge (quoteStringLit-chars s) outer))))

  -- Node: 6 segments — toList "BA_ " ++ qname ++ toList " BU_ " ++ cs-node ++
  --                    ' ' ∷ vstr ++ toList ";\n"
  node-input-bridge :
      ∀ (name : List Char) (n : Identifier) (s outer : List Char)
    → (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
         toList " BU_ " ++ₗ Identifier.name n ++ₗ
         ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n") ++ₗ outer
      ≡ toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
         toList " BU_ " ++ₗ Identifier.name n ++ₗ
         ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n" ++ₗ outer
  node-input-bridge name n s outer =
    trans
      (++ₗ-assoc (toList "BA_ ") _ outer)
      (cong (toList "BA_ " ++ₗ_)
        (trans
          (++ₗ-assoc (quoteStringLit-chars name) _ outer)
          (cong (quoteStringLit-chars name ++ₗ_)
            (trans
              (++ₗ-assoc (toList " BU_ ") _ outer)
              (cong (toList " BU_ " ++ₗ_)
                (trans
                  (++ₗ-assoc (Identifier.name n) _ outer)
                  (cong (Identifier.name n ++ₗ_)
                        (trail-bridge (quoteStringLit-chars s) outer))))))))

  -- Message: 6 segments — toList "BA_ " ++ qname ++ toList " BO_ " ++ cs-id ++
  --                       ' ' ∷ vstr ++ toList ";\n"
  message-input-bridge :
      ∀ (name : List Char) (cid : CANId) (s outer : List Char)
    → (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
         toList " BO_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
         ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n") ++ₗ outer
      ≡ toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
         toList " BO_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
         ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n" ++ₗ outer
  message-input-bridge name cid s outer =
    trans
      (++ₗ-assoc (toList "BA_ ") _ outer)
      (cong (toList "BA_ " ++ₗ_)
        (trans
          (++ₗ-assoc (quoteStringLit-chars name) _ outer)
          (cong (quoteStringLit-chars name ++ₗ_)
            (trans
              (++ₗ-assoc (toList " BO_ ") _ outer)
              (cong (toList " BO_ " ++ₗ_)
                (trans
                  (++ₗ-assoc (showℕ-dec-chars (rawCanIdℕ cid)) _ outer)
                  (cong (showℕ-dec-chars (rawCanIdℕ cid) ++ₗ_)
                        (trail-bridge (quoteStringLit-chars s) outer))))))))

  -- Signal: 7 segments — toList "BA_ " ++ qname ++ toList " SG_ " ++ cs-id ++
  --                      ' ' ∷ Identifier.name sig ++ ' ' ∷ vstr ++ toList ";\n"
  --
  -- Trail differs from Network/Node/Message: there's an extra `' ' ∷ sig`
  -- segment before the `' ' ∷ vstr` segment.  Inner trail bridge applies
  -- once for the sig-then-value and once for the value-then-tail.
  private-signal-trail :
      ∀ (sig-name s outer : List Char)
    → (' ' ∷ sig-name ++ₗ ' ' ∷ s ++ₗ toList ";\n") ++ₗ outer
      ≡ ' ' ∷ sig-name ++ₗ ' ' ∷ s ++ₗ toList ";\n" ++ₗ outer
  private-signal-trail sig-name s outer =
    cong (' ' ∷_)
      (trans
        (++ₗ-assoc sig-name _ outer)
        (cong (sig-name ++ₗ_)
          (trail-bridge s outer)))

  signal-input-bridge :
      ∀ (name : List Char) (cid : CANId) (sig : Identifier) (s outer : List Char)
    → (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
         toList " SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
         ' ' ∷ Identifier.name sig ++ₗ
         ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n") ++ₗ outer
      ≡ toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
         toList " SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
         ' ' ∷ Identifier.name sig ++ₗ
         ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n" ++ₗ outer
  signal-input-bridge name cid sig s outer =
    trans
      (++ₗ-assoc (toList "BA_ ") _ outer)
      (cong (toList "BA_ " ++ₗ_)
        (trans
          (++ₗ-assoc (quoteStringLit-chars name) _ outer)
          (cong (quoteStringLit-chars name ++ₗ_)
            (trans
              (++ₗ-assoc (toList " SG_ ") _ outer)
              (cong (toList " SG_ " ++ₗ_)
                (trans
                  (++ₗ-assoc (showℕ-dec-chars (rawCanIdℕ cid)) _ outer)
                  (cong (showℕ-dec-chars (rawCanIdℕ cid) ++ₗ_)
                        (private-signal-trail
                           (Identifier.name sig)
                           (quoteStringLit-chars s) outer))))))))

  -- EnvVar: 6 segments — toList "BA_ " ++ qname ++ toList " EV_ " ++
  --                      Identifier.name ev ++ ' ' ∷ vstr ++ toList ";\n"
  envvar-input-bridge :
      ∀ (name : List Char) (ev : Identifier) (s outer : List Char)
    → (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
         toList " EV_ " ++ₗ Identifier.name ev ++ₗ
         ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n") ++ₗ outer
      ≡ toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
         toList " EV_ " ++ₗ Identifier.name ev ++ₗ
         ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n" ++ₗ outer
  envvar-input-bridge name ev s outer =
    trans
      (++ₗ-assoc (toList "BA_ ") _ outer)
      (cong (toList "BA_ " ++ₗ_)
        (trans
          (++ₗ-assoc (quoteStringLit-chars name) _ outer)
          (cong (quoteStringLit-chars name ++ₗ_)
            (trans
              (++ₗ-assoc (toList " EV_ ") _ outer)
              (cong (toList " EV_ " ++ₗ_)
                (trans
                  (++ₗ-assoc (Identifier.name ev) _ outer)
                  (cong (Identifier.name ev ++ₗ_)
                        (trail-bridge (quoteStringLit-chars s) outer))))))))

  -- NodeMsg: 7 segments — toList "BA_REL_ " ++ qname ++ toList " BU_BO_REL_ "
  --                       ++ Identifier.name n ++ ' ' ∷ cs-id ++
  --                       ' ' ∷ vstr ++ toList ";\n"
  nodemsg-input-bridge :
      ∀ (name : List Char) (n : Identifier) (cid : CANId) (s outer : List Char)
    → (toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
         toList " BU_BO_REL_ " ++ₗ Identifier.name n ++ₗ
         ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
         ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n") ++ₗ outer
      ≡ toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
         toList " BU_BO_REL_ " ++ₗ Identifier.name n ++ₗ
         ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
         ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n" ++ₗ outer
  nodemsg-input-bridge name n cid s outer =
    trans
      (++ₗ-assoc (toList "BA_REL_ ") _ outer)
      (cong (toList "BA_REL_ " ++ₗ_)
        (trans
          (++ₗ-assoc (quoteStringLit-chars name) _ outer)
          (cong (quoteStringLit-chars name ++ₗ_)
            (trans
              (++ₗ-assoc (toList " BU_BO_REL_ ") _ outer)
              (cong (toList " BU_BO_REL_ " ++ₗ_)
                (trans
                  (++ₗ-assoc (Identifier.name n) _ outer)
                  (cong (Identifier.name n ++ₗ_)
                        (private-signal-trail
                           (showℕ-dec-chars (rawCanIdℕ cid))
                           (quoteStringLit-chars s) outer))))))))

  -- NodeSig: 8 segments — toList "BA_REL_ " ++ qname ++ toList " BU_SG_REL_ "
  --                       ++ Identifier.name n ++ toList " SG_ " ++ cs-id ++
  --                       ' ' ∷ Identifier.name sig ++ ' ' ∷ vstr ++ toList ";\n"
  --
  -- Note: emit body uses `toList " SG_ "` between n and cid, but the slim's
  -- input shape `toList " BU_SG_REL_ " ++ Identifier.name n ++ toList " SG_ "
  -- ++ ...` — we still need the bridge through " SG_ ".  No `' ' ∷` boundary
  -- before " SG_ ".
  nodesig-input-bridge :
      ∀ (name : List Char) (n : Identifier) (cid : CANId) (sig : Identifier)
        (s outer : List Char)
    → (toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
         toList " BU_SG_REL_ " ++ₗ Identifier.name n ++ₗ
         toList " SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
         ' ' ∷ Identifier.name sig ++ₗ
         ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n") ++ₗ outer
      ≡ toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
         toList " BU_SG_REL_ " ++ₗ Identifier.name n ++ₗ
         toList " SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
         ' ' ∷ Identifier.name sig ++ₗ
         ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n" ++ₗ outer
  nodesig-input-bridge name n cid sig s outer =
    trans
      (++ₗ-assoc (toList "BA_REL_ ") _ outer)
      (cong (toList "BA_REL_ " ++ₗ_)
        (trans
          (++ₗ-assoc (quoteStringLit-chars name) _ outer)
          (cong (quoteStringLit-chars name ++ₗ_)
            (trans
              (++ₗ-assoc (toList " BU_SG_REL_ ") _ outer)
              (cong (toList " BU_SG_REL_ " ++ₗ_)
                (trans
                  (++ₗ-assoc (Identifier.name n) _ outer)
                  (cong (Identifier.name n ++ₗ_)
                    (trans
                      (++ₗ-assoc (toList " SG_ ") _ outer)
                      (cong (toList " SG_ " ++ₗ_)
                        (trans
                          (++ₗ-assoc (showℕ-dec-chars (rawCanIdℕ cid)) _ outer)
                          (cong (showℕ-dec-chars (rawCanIdℕ cid) ++ₗ_)
                                (private-signal-trail
                                   (Identifier.name sig)
                                   (quoteStringLit-chars s) outer))))))))))))

-- ============================================================================
-- 7-TARGET DISPATCHER — typed (target × AVString s) → universal lemma
-- ============================================================================
--
-- Constructor pattern-match on `target` directly (per
-- `feedback_with_abstraction_traps.md`).  IdentNameStop preconditions
-- are owed: discharged universally at the outer Universal layer from
-- `Identifier.valid`.

parseAttrLine-on-emit-RawAssign-AVString :
    ∀ (defs : List AttrDef) (pos : Position)
      (name : List Char) (target : AttrTarget) (s : List Char)
      (outer : List Char)
  → IdentNameStop-of target
  → SuffixStops isNewlineStart outer
  → parseAttrLine pos
      (emitAttribute-chars defs
         (DBCAttrAssign (mkAttrAssign name target (AVString s)))
       ++ₗ outer)
    ≡ just (mkResult
              (rawOf defs
                 (DBCAttrAssign (mkAttrAssign name target (AVString s))))
              (advancePositions pos
                 (emitAttribute-chars defs
                    (DBCAttrAssign (mkAttrAssign name target (AVString s)))))
              outer)
parseAttrLine-on-emit-RawAssign-AVString defs pos name ATgtNetwork s outer _ ss-NL =
  subst
    (λ inp → parseAttrLine pos inp ≡
             just (mkResult
                     (RawAssign (mkRawAttrAssign name ATgtNetwork (RavString s)))
                     (TraceNetwork.pos9 pos name (quoteStringLit-chars s) outer)
                     outer))
    (sym (network-input-bridge name s outer))
    (parseAttrLine-roundtrip-RawAssign-ATgtNetwork-RavString
       pos name s outer ss-NL)
parseAttrLine-on-emit-RawAssign-AVString defs pos name (ATgtNode n) s outer n-stop ss-NL =
  subst
    (λ inp → parseAttrLine pos inp ≡
             just (mkResult
                     (RawAssign (mkRawAttrAssign name (ATgtNode n) (RavString s)))
                     (TraceNode.pos9 pos name n (quoteStringLit-chars s) outer)
                     outer))
    (sym (node-input-bridge name n s outer))
    (parseAttrLine-roundtrip-RawAssign-ATgtNode-RavString
       pos name n s outer n-stop ss-NL)
parseAttrLine-on-emit-RawAssign-AVString defs pos name (ATgtMessage cid) s outer _ ss-NL =
  subst
    (λ inp → parseAttrLine pos inp ≡
             just (mkResult
                     (RawAssign (mkRawAttrAssign name (ATgtMessage cid) (RavString s)))
                     (TraceMessage.pos9 pos name cid (quoteStringLit-chars s) outer)
                     outer))
    (sym (message-input-bridge name cid s outer))
    (parseAttrLine-roundtrip-RawAssign-ATgtMessage-RavString
       pos name cid s outer ss-NL)
parseAttrLine-on-emit-RawAssign-AVString defs pos name (ATgtSignal cid sig) s outer sig-stop ss-NL =
  subst
    (λ inp → parseAttrLine pos inp ≡
             just (mkResult
                     (RawAssign (mkRawAttrAssign name (ATgtSignal cid sig) (RavString s)))
                     (TraceSignal.pos9 pos name cid sig (quoteStringLit-chars s) outer)
                     outer))
    (sym (signal-input-bridge name cid sig s outer))
    (parseAttrLine-roundtrip-RawAssign-ATgtSignal-RavString
       pos name cid sig s outer sig-stop ss-NL)
parseAttrLine-on-emit-RawAssign-AVString defs pos name (ATgtEnvVar ev) s outer ev-stop ss-NL =
  subst
    (λ inp → parseAttrLine pos inp ≡
             just (mkResult
                     (RawAssign (mkRawAttrAssign name (ATgtEnvVar ev) (RavString s)))
                     (TraceEnvVar.pos9 pos name ev (quoteStringLit-chars s) outer)
                     outer))
    (sym (envvar-input-bridge name ev s outer))
    (parseAttrLine-roundtrip-RawAssign-ATgtEnvVar-RavString
       pos name ev s outer ev-stop ss-NL)
parseAttrLine-on-emit-RawAssign-AVString defs pos name (ATgtNodeMsg n cid) s outer n-stop ss-NL =
  subst
    (λ inp → parseAttrLine pos inp ≡
             just (mkResult
                     (RawAssign (mkRawAttrAssign name (ATgtNodeMsg n cid) (RavString s)))
                     (TraceNodeMsg.pos9 pos name n cid (quoteStringLit-chars s) outer)
                     outer))
    (sym (nodemsg-input-bridge name n cid s outer))
    (parseAttrLine-roundtrip-RawAssign-ATgtNodeMsg-RavString
       pos name n cid s outer n-stop ss-NL)
parseAttrLine-on-emit-RawAssign-AVString defs pos name (ATgtNodeSig n cid sig) s outer stops ss-NL =
  subst
    (λ inp → parseAttrLine pos inp ≡
             just (mkResult
                     (RawAssign (mkRawAttrAssign name (ATgtNodeSig n cid sig) (RavString s)))
                     (TraceNodeSig.pos9 pos name n cid sig (quoteStringLit-chars s) outer)
                     outer))
    (sym (nodesig-input-bridge name n cid sig s outer))
    (parseAttrLine-roundtrip-RawAssign-ATgtNodeSig-RavString
       pos name n cid sig s outer (proj₁ stops) (proj₂ stops) ss-NL)
