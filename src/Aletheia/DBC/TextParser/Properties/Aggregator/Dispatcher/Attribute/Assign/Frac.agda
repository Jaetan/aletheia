{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 4c — Universal-attribute roundtrip dispatcher for the
-- RawAssign × RavDecRat (frac form) shape (7 targets).
--
-- Mirror of `Assign/String.agda` with:
--   * value-form: `showDecRat-dec-chars d` (was `quoteStringLit-chars s`)
--   * raw output: `RavDecRat d` (was `RavString s`)
--   * AVx case: `AVFloat d` (was `AVString s`).  This is the only `AVx`
--     constructor that emits via `showDecRat-dec-chars`, so the value
--     bridge at the AttrAssign-level is `refl` (no IntDecRat / NatDecRat
--     conversion needed).
module Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Attribute.Assign.Frac where

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
open import Aletheia.DBC.DecRat using (DecRat)
open import Aletheia.DBC.Identifier using (Identifier)
open import Aletheia.DBC.Types using
  ( AttrDef
  ; AttrTarget; ATgtNetwork; ATgtNode; ATgtMessage; ATgtSignal; ATgtEnvVar
  ; ATgtNodeMsg; ATgtNodeSig
  ; AttrValue; AVFloat
  ; AttrAssign; mkAttrAssign
  ; DBCAttribute; DBCAttrAssign
  )

open import Aletheia.DBC.TextFormatter.Attributes using
  (emitAttribute-chars; emitAttrAssign-chars)
open import Aletheia.DBC.TextFormatter.Topology using (rawCanIdℕ)
open import Aletheia.DBC.TextFormatter.Emitter using
  (quoteStringLit-chars; showDecRat-dec-chars; showℕ-dec-chars)

open import Aletheia.DBC.TextParser.Attributes using
  (RawDBCAttribute; RawAssign; mkRawAttrAssign
  ; RawAttrValue;   RavDecRat
  ; parseAttrLine)

open import Aletheia.DBC.TextParser.Properties.Aggregator.Foundations using
  (rawOf)
open import Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Attribute.Foundations using
  (IdentNameStop-of)

open import Aletheia.DBC.TextParser.Properties.Attributes.Line using
  ( parseAttrLine-roundtrip-RawAssign-ATgtNetwork-RavDecRatFrac
  ; parseAttrLine-roundtrip-RawAssign-ATgtNode-RavDecRatFrac
  ; parseAttrLine-roundtrip-RawAssign-ATgtMessage-RavDecRatFrac
  ; parseAttrLine-roundtrip-RawAssign-ATgtSignal-RavDecRatFrac
  ; parseAttrLine-roundtrip-RawAssign-ATgtEnvVar-RavDecRatFrac
  ; parseAttrLine-roundtrip-RawAssign-ATgtNodeMsg-RavDecRatFrac
  ; parseAttrLine-roundtrip-RawAssign-ATgtNodeSig-RavDecRatFrac
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
-- INPUT BRIDGES — same shape as String.agda, with `showDecRat-dec-chars d`
-- replacing `quoteStringLit-chars s`
-- ============================================================================

private
  trail-bridge :
      ∀ (V outer : List Char)
    → (' ' ∷ V ++ₗ toList ";\n") ++ₗ outer
      ≡ ' ' ∷ V ++ₗ toList ";\n" ++ₗ outer
  trail-bridge V outer =
    cong (' ' ∷_) (++ₗ-assoc V (toList ";\n") outer)

  network-input-bridge :
      ∀ (name : List Char) (d : DecRat) (outer : List Char)
    → (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
         ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n") ++ₗ outer
      ≡ toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
         ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n" ++ₗ outer
  network-input-bridge name d outer =
    trans (++ₗ-assoc (toList "BA_ ") _ outer)
      (cong (toList "BA_ " ++ₗ_)
        (trans (++ₗ-assoc (quoteStringLit-chars name) _ outer)
          (cong (quoteStringLit-chars name ++ₗ_)
                (trail-bridge (showDecRat-dec-chars d) outer))))

  node-input-bridge :
      ∀ (name : List Char) (n : Identifier) (d : DecRat) (outer : List Char)
    → (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
         toList " BU_ " ++ₗ Identifier.name n ++ₗ
         ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n") ++ₗ outer
      ≡ toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
         toList " BU_ " ++ₗ Identifier.name n ++ₗ
         ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n" ++ₗ outer
  node-input-bridge name n d outer =
    trans (++ₗ-assoc (toList "BA_ ") _ outer)
      (cong (toList "BA_ " ++ₗ_)
        (trans (++ₗ-assoc (quoteStringLit-chars name) _ outer)
          (cong (quoteStringLit-chars name ++ₗ_)
            (trans (++ₗ-assoc (toList " BU_ ") _ outer)
              (cong (toList " BU_ " ++ₗ_)
                (trans (++ₗ-assoc (Identifier.name n) _ outer)
                  (cong (Identifier.name n ++ₗ_)
                        (trail-bridge (showDecRat-dec-chars d) outer))))))))

  message-input-bridge :
      ∀ (name : List Char) (cid : CANId) (d : DecRat) (outer : List Char)
    → (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
         toList " BO_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
         ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n") ++ₗ outer
      ≡ toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
         toList " BO_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
         ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n" ++ₗ outer
  message-input-bridge name cid d outer =
    trans (++ₗ-assoc (toList "BA_ ") _ outer)
      (cong (toList "BA_ " ++ₗ_)
        (trans (++ₗ-assoc (quoteStringLit-chars name) _ outer)
          (cong (quoteStringLit-chars name ++ₗ_)
            (trans (++ₗ-assoc (toList " BO_ ") _ outer)
              (cong (toList " BO_ " ++ₗ_)
                (trans (++ₗ-assoc (showℕ-dec-chars (rawCanIdℕ cid)) _ outer)
                  (cong (showℕ-dec-chars (rawCanIdℕ cid) ++ₗ_)
                        (trail-bridge (showDecRat-dec-chars d) outer))))))))

  private-signal-trail :
      ∀ (sig-name : List Char) (V : List Char) (outer : List Char)
    → (' ' ∷ sig-name ++ₗ ' ' ∷ V ++ₗ toList ";\n") ++ₗ outer
      ≡ ' ' ∷ sig-name ++ₗ ' ' ∷ V ++ₗ toList ";\n" ++ₗ outer
  private-signal-trail sig-name V outer =
    cong (' ' ∷_)
      (trans (++ₗ-assoc sig-name _ outer)
        (cong (sig-name ++ₗ_) (trail-bridge V outer)))

  signal-input-bridge :
      ∀ (name : List Char) (cid : CANId) (sig : Identifier) (d : DecRat) (outer : List Char)
    → (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
         toList " SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
         ' ' ∷ Identifier.name sig ++ₗ
         ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n") ++ₗ outer
      ≡ toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
         toList " SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
         ' ' ∷ Identifier.name sig ++ₗ
         ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n" ++ₗ outer
  signal-input-bridge name cid sig d outer =
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
                           (showDecRat-dec-chars d) outer))))))))

  envvar-input-bridge :
      ∀ (name : List Char) (ev : Identifier) (d : DecRat) (outer : List Char)
    → (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
         toList " EV_ " ++ₗ Identifier.name ev ++ₗ
         ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n") ++ₗ outer
      ≡ toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
         toList " EV_ " ++ₗ Identifier.name ev ++ₗ
         ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n" ++ₗ outer
  envvar-input-bridge name ev d outer =
    trans (++ₗ-assoc (toList "BA_ ") _ outer)
      (cong (toList "BA_ " ++ₗ_)
        (trans (++ₗ-assoc (quoteStringLit-chars name) _ outer)
          (cong (quoteStringLit-chars name ++ₗ_)
            (trans (++ₗ-assoc (toList " EV_ ") _ outer)
              (cong (toList " EV_ " ++ₗ_)
                (trans (++ₗ-assoc (Identifier.name ev) _ outer)
                  (cong (Identifier.name ev ++ₗ_)
                        (trail-bridge (showDecRat-dec-chars d) outer))))))))

  nodemsg-input-bridge :
      ∀ (name : List Char) (n : Identifier) (cid : CANId) (d : DecRat) (outer : List Char)
    → (toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
         toList " BU_BO_REL_ " ++ₗ Identifier.name n ++ₗ
         ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
         ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n") ++ₗ outer
      ≡ toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
         toList " BU_BO_REL_ " ++ₗ Identifier.name n ++ₗ
         ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
         ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n" ++ₗ outer
  nodemsg-input-bridge name n cid d outer =
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
                           (showDecRat-dec-chars d) outer))))))))

  nodesig-input-bridge :
      ∀ (name : List Char) (n : Identifier) (cid : CANId) (sig : Identifier)
        (d : DecRat) (outer : List Char)
    → (toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
         toList " BU_SG_REL_ " ++ₗ Identifier.name n ++ₗ
         toList " SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
         ' ' ∷ Identifier.name sig ++ₗ
         ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n") ++ₗ outer
      ≡ toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
         toList " BU_SG_REL_ " ++ₗ Identifier.name n ++ₗ
         toList " SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
         ' ' ∷ Identifier.name sig ++ₗ
         ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n" ++ₗ outer
  nodesig-input-bridge name n cid sig d outer =
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
                                   (showDecRat-dec-chars d) outer))))))))))))

-- ============================================================================
-- 7-TARGET DISPATCHER — typed (target × AVFloat d)
-- ============================================================================

parseAttrLine-on-emit-RawAssign-AVFloat :
    ∀ (defs : List AttrDef) (pos : Position)
      (name : List Char) (target : AttrTarget) (d : DecRat)
      (outer : List Char)
  → IdentNameStop-of target
  → SuffixStops isNewlineStart outer
  → parseAttrLine pos
      (emitAttribute-chars defs
         (DBCAttrAssign (mkAttrAssign name target (AVFloat d)))
       ++ₗ outer)
    ≡ just (mkResult
              (rawOf defs
                 (DBCAttrAssign (mkAttrAssign name target (AVFloat d))))
              (advancePositions pos
                 (emitAttribute-chars defs
                    (DBCAttrAssign (mkAttrAssign name target (AVFloat d)))))
              outer)
parseAttrLine-on-emit-RawAssign-AVFloat defs pos name ATgtNetwork d outer _ ss-NL =
  subst
    (λ inp → parseAttrLine pos inp ≡
             just (mkResult
                     (RawAssign (mkRawAttrAssign name ATgtNetwork (RavDecRat d)))
                     (TraceNetwork.pos9 pos name (showDecRat-dec-chars d) outer)
                     outer))
    (sym (network-input-bridge name d outer))
    (parseAttrLine-roundtrip-RawAssign-ATgtNetwork-RavDecRatFrac
       pos name d outer ss-NL)
parseAttrLine-on-emit-RawAssign-AVFloat defs pos name (ATgtNode n) d outer n-stop ss-NL =
  subst
    (λ inp → parseAttrLine pos inp ≡
             just (mkResult
                     (RawAssign (mkRawAttrAssign name (ATgtNode n) (RavDecRat d)))
                     (TraceNode.pos9 pos name n (showDecRat-dec-chars d) outer)
                     outer))
    (sym (node-input-bridge name n d outer))
    (parseAttrLine-roundtrip-RawAssign-ATgtNode-RavDecRatFrac
       pos name n d outer n-stop ss-NL)
parseAttrLine-on-emit-RawAssign-AVFloat defs pos name (ATgtMessage cid) d outer _ ss-NL =
  subst
    (λ inp → parseAttrLine pos inp ≡
             just (mkResult
                     (RawAssign (mkRawAttrAssign name (ATgtMessage cid) (RavDecRat d)))
                     (TraceMessage.pos9 pos name cid (showDecRat-dec-chars d) outer)
                     outer))
    (sym (message-input-bridge name cid d outer))
    (parseAttrLine-roundtrip-RawAssign-ATgtMessage-RavDecRatFrac
       pos name cid d outer ss-NL)
parseAttrLine-on-emit-RawAssign-AVFloat defs pos name (ATgtSignal cid sig) d outer sig-stop ss-NL =
  subst
    (λ inp → parseAttrLine pos inp ≡
             just (mkResult
                     (RawAssign (mkRawAttrAssign name (ATgtSignal cid sig) (RavDecRat d)))
                     (TraceSignal.pos9 pos name cid sig (showDecRat-dec-chars d) outer)
                     outer))
    (sym (signal-input-bridge name cid sig d outer))
    (parseAttrLine-roundtrip-RawAssign-ATgtSignal-RavDecRatFrac
       pos name cid sig d outer sig-stop ss-NL)
parseAttrLine-on-emit-RawAssign-AVFloat defs pos name (ATgtEnvVar ev) d outer ev-stop ss-NL =
  subst
    (λ inp → parseAttrLine pos inp ≡
             just (mkResult
                     (RawAssign (mkRawAttrAssign name (ATgtEnvVar ev) (RavDecRat d)))
                     (TraceEnvVar.pos9 pos name ev (showDecRat-dec-chars d) outer)
                     outer))
    (sym (envvar-input-bridge name ev d outer))
    (parseAttrLine-roundtrip-RawAssign-ATgtEnvVar-RavDecRatFrac
       pos name ev d outer ev-stop ss-NL)
parseAttrLine-on-emit-RawAssign-AVFloat defs pos name (ATgtNodeMsg n cid) d outer n-stop ss-NL =
  subst
    (λ inp → parseAttrLine pos inp ≡
             just (mkResult
                     (RawAssign (mkRawAttrAssign name (ATgtNodeMsg n cid) (RavDecRat d)))
                     (TraceNodeMsg.pos9 pos name n cid (showDecRat-dec-chars d) outer)
                     outer))
    (sym (nodemsg-input-bridge name n cid d outer))
    (parseAttrLine-roundtrip-RawAssign-ATgtNodeMsg-RavDecRatFrac
       pos name n cid d outer n-stop ss-NL)
parseAttrLine-on-emit-RawAssign-AVFloat defs pos name (ATgtNodeSig n cid sig) d outer stops ss-NL =
  subst
    (λ inp → parseAttrLine pos inp ≡
             just (mkResult
                     (RawAssign (mkRawAttrAssign name (ATgtNodeSig n cid sig) (RavDecRat d)))
                     (TraceNodeSig.pos9 pos name n cid sig (showDecRat-dec-chars d) outer)
                     outer))
    (sym (nodesig-input-bridge name n cid sig d outer))
    (parseAttrLine-roundtrip-RawAssign-ATgtNodeSig-RavDecRatFrac
       pos name n cid sig d outer (proj₁ stops) (proj₂ stops) ss-NL)
