-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- `parseAttrLine` 5-way `<|>` dispatch composer roundtrip.
--
-- `parseAttrLine` dispatches on a `BA_`-prefixed input via a 5-way
-- `<|>` chain (longest-keyword-first by `infixl 3` left-assoc):
--
--   parseAttrLine =
--     (parseAttrDefRel     >>= λ d → pure (RawDef d))     <|>   -- alt1
--     (parseRawAttrDefault >>= λ d → pure (RawDefault d)) <|>   -- alt2
--     (parseAttrDef        >>= λ d → pure (RawDef d))     <|>   -- alt3
--     (parseRawAttrRel     >>= λ a → pure (RawAssign a))  <|>   -- alt4
--     (parseRawAttrAssign  >>= λ a → pure (RawAssign a))        -- alt5
--
-- 31 dispatchers cover every input shape the emitter can produce:
-- 2 alt1 (per rel scope: ASNodeMsg / ASNodeSig), 3 alt2 (per emit
-- shape: RavString / RavDecRatFrac / RavDecRatBareInt), 5 alt3 (per
-- standard scope: ASNetwork / ASNode / ASMessage / ASSignal /
-- ASEnvVar), 6 alt4 (NodeMsg/NodeSig × 3 emit shapes), 15 alt5
-- (Network/Node/Message/Signal/EnvVar × 3 emit shapes).
--
-- Cross-construct failures fire by `refl`-level character-mismatch on
-- the input's char 4 or char 7.  Five group-level lift-altK helpers
-- factor the 0/1/2/3/4 leading fails through the `<|>` chain.
--
-- Pattern mirrors Commit 3b's `parseComment-roundtrip` (5-way
-- `CommentTarget` dispatch with cross-keyword failures).

module Aletheia.DBC.TextParser.Properties.Attributes.Line where

open import Data.Char using (Char)
open import Data.Integer using (ℤ)
open import Data.List using (List; _∷_) renaming (_++_ to _++ₗ_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (proj₂)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans)

open import Aletheia.Parser.Combinators
  using (Position; Parser; ParseResult; mkResult; advancePositions;
         _>>=_; pure; _<|>_)

open import Aletheia.CAN.Frame using (CANId)
open import Aletheia.DBC.DecRat using (DecRat; fromℤ)
open import Aletheia.DBC.Types using
  ( mkAttrDef
  ; ASNetwork; ASNode; ASMessage; ASSignal; ASEnvVar
  ; ASNodeMsg; ASNodeSig
  ; ATgtNodeMsg; ATgtNodeSig)
open import Aletheia.DBC.Identifier using (Identifier)

open import Aletheia.DBC.TextFormatter.Attributes using
  (emitAttrDef-chars)
open import Aletheia.DBC.TextFormatter.Topology using (rawCanIdℕ)
open import Aletheia.DBC.TextFormatter.Emitter using
  (quoteStringLit-chars; showDecRat-dec-chars; showInt-chars; showℕ-dec-chars)

open import Aletheia.DBC.TextParser.Attributes
  using ( parseAttrLine; parseAttrDef; parseAttrDefRel; parseRawAttrDefault
        ; parseRawAttrAssign; parseRawAttrRel
        ; RawDBCAttribute; RawDef; RawDefault; RawAssign
        ; mkRawAttrAssign; mkRawAttrDefault
        ; RavString; RavDecRat)

open import Aletheia.DBC.TextParser.Properties.Primitives using
  (alt-right-nothing; alt-left-just)
open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (bind-just-step; SuffixStops)

open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  (isNewlineStart)

-- Lower-level dispatchers
open import Aletheia.DBC.TextParser.Properties.Attributes.Def using
  ( WfAttrType
  ; Wf-Network; Wf-Node; Wf-Message; Wf-Signal; Wf-EnvVar
  ; Wf-NodeMsg; Wf-NodeSig
  ; parseAttrDef-roundtrip; parseAttrDefRel-roundtrip)

import Aletheia.DBC.TextParser.Properties.Attributes.Default as DefaultProofs
open DefaultProofs using
  ( parseRawAttrDefault-roundtrip-RavString
  ; parseRawAttrDefault-roundtrip-RavDecRatFrac
  ; parseRawAttrDefault-roundtrip-RavDecRatBareInt)

open import Aletheia.DBC.TextParser.Properties.Attributes.Assign using
  ( IdentNameStop
  ; parseRawAttrRel-roundtrip-ATgtNodeMsg-RavString
  ; parseRawAttrRel-roundtrip-ATgtNodeMsg-RavDecRatFrac
  ; parseRawAttrRel-roundtrip-ATgtNodeMsg-RavDecRatBareInt
  ; parseRawAttrRel-roundtrip-ATgtNodeSig-RavString
  ; parseRawAttrRel-roundtrip-ATgtNodeSig-RavDecRatFrac
  ; parseRawAttrRel-roundtrip-ATgtNodeSig-RavDecRatBareInt)

-- Trace modules for end-position references in dispatcher result types.
-- Imported as aliased modules — `using (X)` doesn't work for parameterised
-- submodules.  Default-Trace was made public to support this.
import Aletheia.DBC.TextParser.Properties.Attributes.Assign.Rel     as RelProofs

-- ============================================================================
-- 5-way <|> lift helpers
-- ============================================================================
--
-- Each helper takes a success witness for the K-th alt and (K-1) leading
-- fails, lifting to a `parseAttrLine` success at the same `(value,
-- end-pos, suffix)`.
--
-- `parseAttrLine` is `((((P1 <|> P2) <|> P3) <|> P4) <|> P5)` by the
-- `infixl 3` left-assoc rule.  Definitionally equal modulo unfolding of
-- the `Pk` aliases below.

-- P1-P5 lifted from private to public so the
-- extracted alt-K dispatchers in `Line/AltN.agda` siblings can
-- reference them in their `where`-clause type annotations
-- (`alt5-eq : proj₂ (P5 pos input) ≡ just …`).
P1 : Parser RawDBCAttribute
P1 = parseAttrDefRel >>= λ d → pure (RawDef d)

P2 : Parser RawDBCAttribute
P2 = parseRawAttrDefault >>= λ d → pure (RawDefault d)

P3 : Parser RawDBCAttribute
P3 = parseAttrDef >>= λ d → pure (RawDef d)

P4 : Parser RawDBCAttribute
P4 = parseRawAttrRel >>= λ a → pure (RawAssign a)

P5 : Parser RawDBCAttribute
P5 = parseRawAttrAssign >>= λ a → pure (RawAssign a)

parseAttrLine-≡-alt-chain :
    parseAttrLine ≡ ((((P1 <|> P2) <|> P3) <|> P4) <|> P5)
parseAttrLine-≡-alt-chain = refl

-- alt1 succeeds — 4 alt-left-just lifts (no leading fails).
parseAttrLine-lift-alt1 :
    ∀ (pos : Position) (input : List Char) (r : ParseResult RawDBCAttribute)
  → proj₂ (P1 pos input) ≡ just r
  → proj₂ (parseAttrLine pos input) ≡ just r
parseAttrLine-lift-alt1 pos input r alt1-eq =
  alt-left-just (((P1 <|> P2) <|> P3) <|> P4) P5 pos input r
    (alt-left-just ((P1 <|> P2) <|> P3) P4 pos input r
      (alt-left-just (P1 <|> P2) P3 pos input r
        (alt-left-just P1 P2 pos input r alt1-eq)))

-- alt2 succeeds, 1 leading fail (P1).
parseAttrLine-lift-alt2 :
    ∀ (pos : Position) (input : List Char) (r : ParseResult RawDBCAttribute)
  → proj₂ (P1 pos input) ≡ nothing
  → proj₂ (P2 pos input) ≡ just r
  → proj₂ (parseAttrLine pos input) ≡ just r
parseAttrLine-lift-alt2 pos input r p1-fail alt2-eq =
  alt-left-just (((P1 <|> P2) <|> P3) <|> P4) P5 pos input r
    (alt-left-just ((P1 <|> P2) <|> P3) P4 pos input r
      (alt-left-just (P1 <|> P2) P3 pos input r
        (trans (alt-right-nothing P1 P2 pos input p1-fail) alt2-eq)))

-- alt3 succeeds, 2 leading fails (P1, P2).
parseAttrLine-lift-alt3 :
    ∀ (pos : Position) (input : List Char) (r : ParseResult RawDBCAttribute)
  → proj₂ (P1 pos input) ≡ nothing
  → proj₂ (P2 pos input) ≡ nothing
  → proj₂ (P3 pos input) ≡ just r
  → proj₂ (parseAttrLine pos input) ≡ just r
parseAttrLine-lift-alt3 pos input r p1-fail p2-fail alt3-eq =
  alt-left-just (((P1 <|> P2) <|> P3) <|> P4) P5 pos input r
    (alt-left-just ((P1 <|> P2) <|> P3) P4 pos input r
      (trans (alt-right-nothing (P1 <|> P2) P3 pos input
                (trans (alt-right-nothing P1 P2 pos input p1-fail) p2-fail))
             alt3-eq))

-- alt4 succeeds, 3 leading fails (P1, P2, P3).
parseAttrLine-lift-alt4 :
    ∀ (pos : Position) (input : List Char) (r : ParseResult RawDBCAttribute)
  → proj₂ (P1 pos input) ≡ nothing
  → proj₂ (P2 pos input) ≡ nothing
  → proj₂ (P3 pos input) ≡ nothing
  → proj₂ (P4 pos input) ≡ just r
  → proj₂ (parseAttrLine pos input) ≡ just r
parseAttrLine-lift-alt4 pos input r p1-fail p2-fail p3-fail alt4-eq =
  alt-left-just (((P1 <|> P2) <|> P3) <|> P4) P5 pos input r
    (trans (alt-right-nothing ((P1 <|> P2) <|> P3) P4 pos input
              (trans (alt-right-nothing (P1 <|> P2) P3 pos input
                       (trans (alt-right-nothing P1 P2 pos input p1-fail)
                              p2-fail))
                     p3-fail))
           alt4-eq)

-- alt5 succeeds, 4 leading fails (P1, P2, P3, P4).
parseAttrLine-lift-alt5 :
    ∀ (pos : Position) (input : List Char) (r : ParseResult RawDBCAttribute)
  → proj₂ (P1 pos input) ≡ nothing
  → proj₂ (P2 pos input) ≡ nothing
  → proj₂ (P3 pos input) ≡ nothing
  → proj₂ (P4 pos input) ≡ nothing
  → proj₂ (P5 pos input) ≡ just r
  → proj₂ (parseAttrLine pos input) ≡ just r
parseAttrLine-lift-alt5 pos input r p1-fail p2-fail p3-fail p4-fail alt5-eq =
  trans (alt-right-nothing (((P1 <|> P2) <|> P3) <|> P4) P5 pos input
          (trans (alt-right-nothing ((P1 <|> P2) <|> P3) P4 pos input
                   (trans (alt-right-nothing (P1 <|> P2) P3 pos input
                            (trans (alt-right-nothing P1 P2 pos input p1-fail)
                                   p2-fail))
                          p3-fail))
                 p4-fail))
        alt5-eq

-- ============================================================================
-- alt5 dispatchers — see `Line/Alt5.agda`
-- ============================================================================
--
-- The 15 alt5 dispatchers (RawAssign × {Network/Node/Message/Signal/
-- EnvVar} × 3 emit shapes; ~383 LOC) moved to
-- `Properties/Attributes/Line/Alt5.agda`.  Re-exported from
-- `Properties/Attributes.agda`
-- facade.  Sibling imports `parseAttrLine-lift-alt5` and the `P5` alias
-- from this module (one-way; no cycle).

-- ============================================================================
-- alt4 dispatchers — RawAssign × {NodeMsg, NodeSig} × 3 emit shapes
-- ============================================================================
--
-- 3 leading fails (P1, P2, P3).  Input shape `BA_REL_ ...`; each leading
-- alt fails on char 4 ('R' ≠ 'D').

-- ATgtNodeMsg × 3
parseAttrLine-roundtrip-RawAssign-ATgtNodeMsg-RavString :
    ∀ pos (name : List Char) (n : Identifier) (cid : CANId) (s : List Char)
      (outer-suffix : List Char)
  → IdentNameStop n
  → SuffixStops isNewlineStart outer-suffix
  → proj₂ (parseAttrLine pos
      (toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " BU_BO_REL_ " ++ₗ Identifier.name n ++ₗ
        ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
        ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n" ++ₗ outer-suffix))
    ≡ just (mkResult
              (RawAssign (mkRawAttrAssign name (ATgtNodeMsg n cid) (RavString s)))
              (RelProofs.TraceNodeMsg.pos9 pos name n cid (quoteStringLit-chars s) outer-suffix)
              outer-suffix)
parseAttrLine-roundtrip-RawAssign-ATgtNodeMsg-RavString pos name n cid s outer-suffix n-stop ss-NL =
  parseAttrLine-lift-alt4 pos input _ refl refl refl
    (bind-just-step parseRawAttrRel (λ a → pure (RawAssign a))
       pos input _ _ _
       (parseRawAttrRel-roundtrip-ATgtNodeMsg-RavString
          pos name n cid s outer-suffix n-stop ss-NL))
  where
    input : List Char
    input = toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
            toList " BU_BO_REL_ " ++ₗ Identifier.name n ++ₗ
            ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
            ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n" ++ₗ outer-suffix

parseAttrLine-roundtrip-RawAssign-ATgtNodeMsg-RavDecRatFrac :
    ∀ pos (name : List Char) (n : Identifier) (cid : CANId) (d : DecRat)
      (outer-suffix : List Char)
  → IdentNameStop n
  → SuffixStops isNewlineStart outer-suffix
  → proj₂ (parseAttrLine pos
      (toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " BU_BO_REL_ " ++ₗ Identifier.name n ++ₗ
        ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
        ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n" ++ₗ outer-suffix))
    ≡ just (mkResult
              (RawAssign (mkRawAttrAssign name (ATgtNodeMsg n cid) (RavDecRat d)))
              (RelProofs.TraceNodeMsg.pos9 pos name n cid (showDecRat-dec-chars d) outer-suffix)
              outer-suffix)
parseAttrLine-roundtrip-RawAssign-ATgtNodeMsg-RavDecRatFrac pos name n cid d outer-suffix n-stop ss-NL =
  parseAttrLine-lift-alt4 pos input _ refl refl refl
    (bind-just-step parseRawAttrRel (λ a → pure (RawAssign a))
       pos input _ _ _
       (parseRawAttrRel-roundtrip-ATgtNodeMsg-RavDecRatFrac
          pos name n cid d outer-suffix n-stop ss-NL))
  where
    input : List Char
    input = toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
            toList " BU_BO_REL_ " ++ₗ Identifier.name n ++ₗ
            ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
            ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n" ++ₗ outer-suffix

parseAttrLine-roundtrip-RawAssign-ATgtNodeMsg-RavDecRatBareInt :
    ∀ pos (name : List Char) (n : Identifier) (cid : CANId) (z : ℤ)
      (outer-suffix : List Char)
  → IdentNameStop n
  → SuffixStops isNewlineStart outer-suffix
  → proj₂ (parseAttrLine pos
      (toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " BU_BO_REL_ " ++ₗ Identifier.name n ++ₗ
        ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
        ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer-suffix))
    ≡ just (mkResult
              (RawAssign (mkRawAttrAssign name (ATgtNodeMsg n cid) (RavDecRat (fromℤ z))))
              (RelProofs.TraceNodeMsg.pos9 pos name n cid (showInt-chars z) outer-suffix)
              outer-suffix)
parseAttrLine-roundtrip-RawAssign-ATgtNodeMsg-RavDecRatBareInt pos name n cid z outer-suffix n-stop ss-NL =
  parseAttrLine-lift-alt4 pos input _ refl refl refl
    (bind-just-step parseRawAttrRel (λ a → pure (RawAssign a))
       pos input _ _ _
       (parseRawAttrRel-roundtrip-ATgtNodeMsg-RavDecRatBareInt
          pos name n cid z outer-suffix n-stop ss-NL))
  where
    input : List Char
    input = toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
            toList " BU_BO_REL_ " ++ₗ Identifier.name n ++ₗ
            ' ' ∷ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
            ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer-suffix

-- ATgtNodeSig × 3
parseAttrLine-roundtrip-RawAssign-ATgtNodeSig-RavString :
    ∀ pos (name : List Char) (n : Identifier) (cid : CANId) (sig : Identifier)
      (s : List Char) (outer-suffix : List Char)
  → IdentNameStop n → IdentNameStop sig
  → SuffixStops isNewlineStart outer-suffix
  → proj₂ (parseAttrLine pos
      (toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " BU_SG_REL_ " ++ₗ Identifier.name n ++ₗ
        toList " SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
        ' ' ∷ Identifier.name sig ++ₗ
        ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n" ++ₗ outer-suffix))
    ≡ just (mkResult
              (RawAssign (mkRawAttrAssign name (ATgtNodeSig n cid sig) (RavString s)))
              (RelProofs.TraceNodeSig.pos9 pos name n cid sig (quoteStringLit-chars s) outer-suffix)
              outer-suffix)
parseAttrLine-roundtrip-RawAssign-ATgtNodeSig-RavString pos name n cid sig s outer-suffix
  n-stop sig-stop ss-NL =
  parseAttrLine-lift-alt4 pos input _ refl refl refl
    (bind-just-step parseRawAttrRel (λ a → pure (RawAssign a))
       pos input _ _ _
       (parseRawAttrRel-roundtrip-ATgtNodeSig-RavString
          pos name n cid sig s outer-suffix n-stop sig-stop ss-NL))
  where
    input : List Char
    input = toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
            toList " BU_SG_REL_ " ++ₗ Identifier.name n ++ₗ
            toList " SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
            ' ' ∷ Identifier.name sig ++ₗ
            ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n" ++ₗ outer-suffix

parseAttrLine-roundtrip-RawAssign-ATgtNodeSig-RavDecRatFrac :
    ∀ pos (name : List Char) (n : Identifier) (cid : CANId) (sig : Identifier)
      (d : DecRat) (outer-suffix : List Char)
  → IdentNameStop n → IdentNameStop sig
  → SuffixStops isNewlineStart outer-suffix
  → proj₂ (parseAttrLine pos
      (toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " BU_SG_REL_ " ++ₗ Identifier.name n ++ₗ
        toList " SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
        ' ' ∷ Identifier.name sig ++ₗ
        ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n" ++ₗ outer-suffix))
    ≡ just (mkResult
              (RawAssign (mkRawAttrAssign name (ATgtNodeSig n cid sig) (RavDecRat d)))
              (RelProofs.TraceNodeSig.pos9 pos name n cid sig (showDecRat-dec-chars d) outer-suffix)
              outer-suffix)
parseAttrLine-roundtrip-RawAssign-ATgtNodeSig-RavDecRatFrac pos name n cid sig d outer-suffix
  n-stop sig-stop ss-NL =
  parseAttrLine-lift-alt4 pos input _ refl refl refl
    (bind-just-step parseRawAttrRel (λ a → pure (RawAssign a))
       pos input _ _ _
       (parseRawAttrRel-roundtrip-ATgtNodeSig-RavDecRatFrac
          pos name n cid sig d outer-suffix n-stop sig-stop ss-NL))
  where
    input : List Char
    input = toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
            toList " BU_SG_REL_ " ++ₗ Identifier.name n ++ₗ
            toList " SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
            ' ' ∷ Identifier.name sig ++ₗ
            ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n" ++ₗ outer-suffix

parseAttrLine-roundtrip-RawAssign-ATgtNodeSig-RavDecRatBareInt :
    ∀ pos (name : List Char) (n : Identifier) (cid : CANId) (sig : Identifier)
      (z : ℤ) (outer-suffix : List Char)
  → IdentNameStop n → IdentNameStop sig
  → SuffixStops isNewlineStart outer-suffix
  → proj₂ (parseAttrLine pos
      (toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " BU_SG_REL_ " ++ₗ Identifier.name n ++ₗ
        toList " SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
        ' ' ∷ Identifier.name sig ++ₗ
        ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer-suffix))
    ≡ just (mkResult
              (RawAssign (mkRawAttrAssign name (ATgtNodeSig n cid sig) (RavDecRat (fromℤ z))))
              (RelProofs.TraceNodeSig.pos9 pos name n cid sig (showInt-chars z) outer-suffix)
              outer-suffix)
parseAttrLine-roundtrip-RawAssign-ATgtNodeSig-RavDecRatBareInt pos name n cid sig z outer-suffix
  n-stop sig-stop ss-NL =
  parseAttrLine-lift-alt4 pos input _ refl refl refl
    (bind-just-step parseRawAttrRel (λ a → pure (RawAssign a))
       pos input _ _ _
       (parseRawAttrRel-roundtrip-ATgtNodeSig-RavDecRatBareInt
          pos name n cid sig z outer-suffix n-stop sig-stop ss-NL))
  where
    input : List Char
    input = toList "BA_REL_ " ++ₗ quoteStringLit-chars name ++ₗ
            toList " BU_SG_REL_ " ++ₗ Identifier.name n ++ₗ
            toList " SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
            ' ' ∷ Identifier.name sig ++ₗ
            ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer-suffix

-- ============================================================================
-- alt3 dispatchers — RawDef-NotRel × {Network/Node/Message/Signal/EnvVar}
-- ============================================================================
--
-- 2 leading fails (P1, P2).  Input shape `BA_DEF_<sp>...`; alt1 expects 'R'
-- and alt2 expects 'D' at char 7 but finds ' '.  Per-scope dispatch needed
-- because `emitAttrDef-chars d` only reduces when scope is concrete.

parseAttrLine-roundtrip-RawDef-NotRel-Network :
    ∀ pos (name : List Char) (ty : _) (outer-suffix : List Char)
  → WfAttrType ty
  → SuffixStops isNewlineStart outer-suffix
  → proj₂ (parseAttrLine pos
      (emitAttrDef-chars (mkAttrDef name ASNetwork ty) ++ₗ outer-suffix))
    ≡ just (mkResult
              (RawDef (mkAttrDef name ASNetwork ty))
              (advancePositions pos
                (emitAttrDef-chars (mkAttrDef name ASNetwork ty)))
              outer-suffix)
parseAttrLine-roundtrip-RawDef-NotRel-Network pos name ty outer-suffix wf-ty ss-NL =
  parseAttrLine-lift-alt3 pos input _ refl refl
    (bind-just-step parseAttrDef (λ d → pure (RawDef d))
       pos input _ _ _
       (parseAttrDef-roundtrip (mkAttrDef name ASNetwork ty) pos outer-suffix
          (Wf-Network wf-ty) ss-NL))
  where
    input : List Char
    input = emitAttrDef-chars (mkAttrDef name ASNetwork ty) ++ₗ outer-suffix

parseAttrLine-roundtrip-RawDef-NotRel-Node :
    ∀ pos (name : List Char) (ty : _) (outer-suffix : List Char)
  → WfAttrType ty
  → SuffixStops isNewlineStart outer-suffix
  → proj₂ (parseAttrLine pos
      (emitAttrDef-chars (mkAttrDef name ASNode ty) ++ₗ outer-suffix))
    ≡ just (mkResult
              (RawDef (mkAttrDef name ASNode ty))
              (advancePositions pos
                (emitAttrDef-chars (mkAttrDef name ASNode ty)))
              outer-suffix)
parseAttrLine-roundtrip-RawDef-NotRel-Node pos name ty outer-suffix wf-ty ss-NL =
  parseAttrLine-lift-alt3 pos input _ refl refl
    (bind-just-step parseAttrDef (λ d → pure (RawDef d))
       pos input _ _ _
       (parseAttrDef-roundtrip (mkAttrDef name ASNode ty) pos outer-suffix
          (Wf-Node wf-ty) ss-NL))
  where
    input : List Char
    input = emitAttrDef-chars (mkAttrDef name ASNode ty) ++ₗ outer-suffix

parseAttrLine-roundtrip-RawDef-NotRel-Message :
    ∀ pos (name : List Char) (ty : _) (outer-suffix : List Char)
  → WfAttrType ty
  → SuffixStops isNewlineStart outer-suffix
  → proj₂ (parseAttrLine pos
      (emitAttrDef-chars (mkAttrDef name ASMessage ty) ++ₗ outer-suffix))
    ≡ just (mkResult
              (RawDef (mkAttrDef name ASMessage ty))
              (advancePositions pos
                (emitAttrDef-chars (mkAttrDef name ASMessage ty)))
              outer-suffix)
parseAttrLine-roundtrip-RawDef-NotRel-Message pos name ty outer-suffix wf-ty ss-NL =
  parseAttrLine-lift-alt3 pos input _ refl refl
    (bind-just-step parseAttrDef (λ d → pure (RawDef d))
       pos input _ _ _
       (parseAttrDef-roundtrip (mkAttrDef name ASMessage ty) pos outer-suffix
          (Wf-Message wf-ty) ss-NL))
  where
    input : List Char
    input = emitAttrDef-chars (mkAttrDef name ASMessage ty) ++ₗ outer-suffix

parseAttrLine-roundtrip-RawDef-NotRel-Signal :
    ∀ pos (name : List Char) (ty : _) (outer-suffix : List Char)
  → WfAttrType ty
  → SuffixStops isNewlineStart outer-suffix
  → proj₂ (parseAttrLine pos
      (emitAttrDef-chars (mkAttrDef name ASSignal ty) ++ₗ outer-suffix))
    ≡ just (mkResult
              (RawDef (mkAttrDef name ASSignal ty))
              (advancePositions pos
                (emitAttrDef-chars (mkAttrDef name ASSignal ty)))
              outer-suffix)
parseAttrLine-roundtrip-RawDef-NotRel-Signal pos name ty outer-suffix wf-ty ss-NL =
  parseAttrLine-lift-alt3 pos input _ refl refl
    (bind-just-step parseAttrDef (λ d → pure (RawDef d))
       pos input _ _ _
       (parseAttrDef-roundtrip (mkAttrDef name ASSignal ty) pos outer-suffix
          (Wf-Signal wf-ty) ss-NL))
  where
    input : List Char
    input = emitAttrDef-chars (mkAttrDef name ASSignal ty) ++ₗ outer-suffix

parseAttrLine-roundtrip-RawDef-NotRel-EnvVar :
    ∀ pos (name : List Char) (ty : _) (outer-suffix : List Char)
  → WfAttrType ty
  → SuffixStops isNewlineStart outer-suffix
  → proj₂ (parseAttrLine pos
      (emitAttrDef-chars (mkAttrDef name ASEnvVar ty) ++ₗ outer-suffix))
    ≡ just (mkResult
              (RawDef (mkAttrDef name ASEnvVar ty))
              (advancePositions pos
                (emitAttrDef-chars (mkAttrDef name ASEnvVar ty)))
              outer-suffix)
parseAttrLine-roundtrip-RawDef-NotRel-EnvVar pos name ty outer-suffix wf-ty ss-NL =
  parseAttrLine-lift-alt3 pos input _ refl refl
    (bind-just-step parseAttrDef (λ d → pure (RawDef d))
       pos input _ _ _
       (parseAttrDef-roundtrip (mkAttrDef name ASEnvVar ty) pos outer-suffix
          (Wf-EnvVar wf-ty) ss-NL))
  where
    input : List Char
    input = emitAttrDef-chars (mkAttrDef name ASEnvVar ty) ++ₗ outer-suffix

-- ============================================================================
-- alt2 dispatchers — RawDefault × 3 emit shapes
-- ============================================================================
--
-- 1 leading fail (P1).  Input shape `BA_DEF_DEF_ ...`; alt1 expects 'R'
-- at char 7 but finds 'D'.

parseAttrLine-roundtrip-RawDefault-RavString :
    ∀ pos (name : List Char) (s : List Char) (outer-suffix : List Char)
  → SuffixStops isNewlineStart outer-suffix
  → proj₂ (parseAttrLine pos
      (toList "BA_DEF_DEF_ " ++ₗ quoteStringLit-chars name ++ₗ
        ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n" ++ₗ outer-suffix))
    ≡ just (mkResult
              (RawDefault (mkRawAttrDefault name (RavString s)))
              (DefaultProofs.Trace.pos8 pos name (quoteStringLit-chars s) outer-suffix)
              outer-suffix)
parseAttrLine-roundtrip-RawDefault-RavString pos name s outer-suffix ss-NL =
  parseAttrLine-lift-alt2 pos input _ refl
    (bind-just-step parseRawAttrDefault (λ d → pure (RawDefault d))
       pos input _ _ _
       (parseRawAttrDefault-roundtrip-RavString
          pos name s outer-suffix ss-NL))
  where
    input : List Char
    input = toList "BA_DEF_DEF_ " ++ₗ quoteStringLit-chars name ++ₗ
            ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n" ++ₗ outer-suffix

parseAttrLine-roundtrip-RawDefault-RavDecRatFrac :
    ∀ pos (name : List Char) (d : DecRat) (outer-suffix : List Char)
  → SuffixStops isNewlineStart outer-suffix
  → proj₂ (parseAttrLine pos
      (toList "BA_DEF_DEF_ " ++ₗ quoteStringLit-chars name ++ₗ
        ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n" ++ₗ outer-suffix))
    ≡ just (mkResult
              (RawDefault (mkRawAttrDefault name (RavDecRat d)))
              (DefaultProofs.Trace.pos8 pos name (showDecRat-dec-chars d) outer-suffix)
              outer-suffix)
parseAttrLine-roundtrip-RawDefault-RavDecRatFrac pos name d outer-suffix ss-NL =
  parseAttrLine-lift-alt2 pos input _ refl
    (bind-just-step parseRawAttrDefault (λ d → pure (RawDefault d))
       pos input _ _ _
       (parseRawAttrDefault-roundtrip-RavDecRatFrac
          pos name d outer-suffix ss-NL))
  where
    input : List Char
    input = toList "BA_DEF_DEF_ " ++ₗ quoteStringLit-chars name ++ₗ
            ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n" ++ₗ outer-suffix

parseAttrLine-roundtrip-RawDefault-RavDecRatBareInt :
    ∀ pos (name : List Char) (z : ℤ) (outer-suffix : List Char)
  → SuffixStops isNewlineStart outer-suffix
  → proj₂ (parseAttrLine pos
      (toList "BA_DEF_DEF_ " ++ₗ quoteStringLit-chars name ++ₗ
        ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer-suffix))
    ≡ just (mkResult
              (RawDefault (mkRawAttrDefault name (RavDecRat (fromℤ z))))
              (DefaultProofs.Trace.pos8 pos name (showInt-chars z) outer-suffix)
              outer-suffix)
parseAttrLine-roundtrip-RawDefault-RavDecRatBareInt pos name z outer-suffix ss-NL =
  parseAttrLine-lift-alt2 pos input _ refl
    (bind-just-step parseRawAttrDefault (λ d → pure (RawDefault d))
       pos input _ _ _
       (parseRawAttrDefault-roundtrip-RavDecRatBareInt
          pos name z outer-suffix ss-NL))
  where
    input : List Char
    input = toList "BA_DEF_DEF_ " ++ₗ quoteStringLit-chars name ++ₗ
            ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer-suffix

-- ============================================================================
-- alt1 dispatchers — RawDef-Rel × {NodeMsg, NodeSig}
-- ============================================================================
--
-- 0 leading fails — alt1 succeeds first (string "BA_DEF_REL_" matches the
-- whole prefix).  Per-scope dispatch needed because `emitAttrDef-chars d`
-- only reduces when scope is concrete.

parseAttrLine-roundtrip-RawDef-Rel-NodeMsg :
    ∀ pos (name : List Char) (ty : _) (outer-suffix : List Char)
  → WfAttrType ty
  → SuffixStops isNewlineStart outer-suffix
  → proj₂ (parseAttrLine pos
      (emitAttrDef-chars (mkAttrDef name ASNodeMsg ty) ++ₗ outer-suffix))
    ≡ just (mkResult
              (RawDef (mkAttrDef name ASNodeMsg ty))
              (advancePositions pos
                (emitAttrDef-chars (mkAttrDef name ASNodeMsg ty)))
              outer-suffix)
parseAttrLine-roundtrip-RawDef-Rel-NodeMsg pos name ty outer-suffix wf-ty ss-NL =
  parseAttrLine-lift-alt1 pos input _
    (bind-just-step parseAttrDefRel (λ d → pure (RawDef d))
       pos input _ _ _
       (parseAttrDefRel-roundtrip (mkAttrDef name ASNodeMsg ty) pos outer-suffix
          (Wf-NodeMsg wf-ty) ss-NL))
  where
    input : List Char
    input = emitAttrDef-chars (mkAttrDef name ASNodeMsg ty) ++ₗ outer-suffix

parseAttrLine-roundtrip-RawDef-Rel-NodeSig :
    ∀ pos (name : List Char) (ty : _) (outer-suffix : List Char)
  → WfAttrType ty
  → SuffixStops isNewlineStart outer-suffix
  → proj₂ (parseAttrLine pos
      (emitAttrDef-chars (mkAttrDef name ASNodeSig ty) ++ₗ outer-suffix))
    ≡ just (mkResult
              (RawDef (mkAttrDef name ASNodeSig ty))
              (advancePositions pos
                (emitAttrDef-chars (mkAttrDef name ASNodeSig ty)))
              outer-suffix)
parseAttrLine-roundtrip-RawDef-Rel-NodeSig pos name ty outer-suffix wf-ty ss-NL =
  parseAttrLine-lift-alt1 pos input _
    (bind-just-step parseAttrDefRel (λ d → pure (RawDef d))
       pos input _ _ _
       (parseAttrDefRel-roundtrip (mkAttrDef name ASNodeSig ty) pos outer-suffix
          (Wf-NodeSig wf-ty) ss-NL))
  where
    input : List Char
    input = emitAttrDef-chars (mkAttrDef name ASNodeSig ty) ++ₗ outer-suffix
