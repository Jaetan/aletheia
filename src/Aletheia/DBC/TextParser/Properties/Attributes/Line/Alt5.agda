-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- alt5 dispatchers for `parseAttrLine`.
--
-- Extracted from `Properties/Attributes/Line.agda` to bring the parent
-- under the 800-LOC
-- trigger.  15 dispatchers: RawAssign × {Network/Node/Message/Signal/
-- EnvVar} × 3 emit shapes (RavString / RavDecRatFrac / RavDecRatBareInt).
--
-- All dispatchers use `parseAttrLine-lift-alt5` from the parent
-- (one-way dependency).  Re-exported from `Properties/Attributes.agda`
-- facade for downstream consumers (the Frac / BareInt / String /
-- Default / Def dispatchers).
module Aletheia.DBC.TextParser.Properties.Attributes.Line.Alt5 where

open import Data.Char using (Char)
open import Data.Integer using (ℤ)
open import Data.List using (List; _∷_) renaming (_++_ to _++ₗ_)
open import Data.Maybe using (just)
open import Data.Product using (proj₂)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)

open import Aletheia.Parser.Combinators
  using (mkResult; pure)

open import Aletheia.CAN.Frame using (CANId)
open import Aletheia.DBC.DecRat using (DecRat; fromℤ)
open import Aletheia.DBC.Identifier using (Identifier)

open import Aletheia.DBC.TextFormatter.Emitter using
  (quoteStringLit-chars; showDecRat-dec-chars; showInt-chars; showℕ-dec-chars)
open import Aletheia.DBC.TextFormatter.Topology using (rawCanIdℕ)

open import Aletheia.DBC.TextParser.Attributes
  using ( parseAttrLine; parseRawAttrAssign
        ; RawAssign
        ; mkRawAttrAssign
        ; RavString; RavDecRat)

open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (bind-just-step; SuffixStops)

open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  (isNewlineStart)

open import Aletheia.DBC.TextParser.Properties.Attributes.Assign using
  ( IdentNameStop
  ; parseRawAttrAssign-roundtrip-ATgtNetwork-RavString
  ; parseRawAttrAssign-roundtrip-ATgtNetwork-RavDecRatFrac
  ; parseRawAttrAssign-roundtrip-ATgtNetwork-RavDecRatBareInt
  ; parseRawAttrAssign-roundtrip-ATgtNode-RavString
  ; parseRawAttrAssign-roundtrip-ATgtNode-RavDecRatFrac
  ; parseRawAttrAssign-roundtrip-ATgtNode-RavDecRatBareInt
  ; parseRawAttrAssign-roundtrip-ATgtMessage-RavString
  ; parseRawAttrAssign-roundtrip-ATgtMessage-RavDecRatFrac
  ; parseRawAttrAssign-roundtrip-ATgtMessage-RavDecRatBareInt
  ; parseRawAttrAssign-roundtrip-ATgtSignal-RavString
  ; parseRawAttrAssign-roundtrip-ATgtSignal-RavDecRatFrac
  ; parseRawAttrAssign-roundtrip-ATgtSignal-RavDecRatBareInt
  ; parseRawAttrAssign-roundtrip-ATgtEnvVar-RavString
  ; parseRawAttrAssign-roundtrip-ATgtEnvVar-RavDecRatFrac
  ; parseRawAttrAssign-roundtrip-ATgtEnvVar-RavDecRatBareInt)

open import Aletheia.DBC.Types using
  ( ATgtNetwork; ATgtNode; ATgtMessage; ATgtSignal; ATgtEnvVar)

-- Trace modules for end-position references in dispatcher result types.
import Aletheia.DBC.TextParser.Properties.Attributes.Assign.Network as NetworkProofs
import Aletheia.DBC.TextParser.Properties.Attributes.Assign.Node    as NodeProofs
import Aletheia.DBC.TextParser.Properties.Attributes.Assign.Message as MessageProofs
import Aletheia.DBC.TextParser.Properties.Attributes.Assign.Signal  as SignalProofs
import Aletheia.DBC.TextParser.Properties.Attributes.Assign.EnvVar  as EnvVarProofs

-- The alt5 lift helper + P5 alias from the parent (one-way).
open import Aletheia.DBC.TextParser.Properties.Attributes.Line using
  (parseAttrLine-lift-alt5; P5)

-- ============================================================================
-- alt5 dispatchers — RawAssign × {Network/Node/Message/Signal/EnvVar} × 3 emit shapes
-- ============================================================================
--
-- Deepest fail-chain (4 leading fails), input shape `BA_<sp>...`.  Each
-- leading-fail proof closes by `refl` because the input reduces to
-- `'B' ∷ 'A' ∷ '_' ∷ ' ' ∷ ...` (concrete char 4 ≠ 'D'/'R').

parseAttrLine-roundtrip-RawAssign-ATgtNetwork-RavString :
    ∀ pos (name : List Char) (s : List Char) (outer-suffix : List Char)
  → SuffixStops isNewlineStart outer-suffix
  → proj₂ (parseAttrLine pos
      (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
        ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n" ++ₗ outer-suffix))
    ≡ just (mkResult
              (RawAssign (mkRawAttrAssign name ATgtNetwork (RavString s)))
              (NetworkProofs.TraceNetwork.pos9 pos name (quoteStringLit-chars s) outer-suffix)
              outer-suffix)
parseAttrLine-roundtrip-RawAssign-ATgtNetwork-RavString pos name s outer-suffix ss-NL =
  parseAttrLine-lift-alt5 pos input _
    refl  -- P1 fails on 'B'∷'A'∷'_'∷' ' (string "BA_DEF_REL_" expects 'D' at char 4)
    refl  -- P2 fails — string "BA_DEF_DEF_" expects 'D' at char 4
    refl  -- P3 fails — string "BA_DEF_" expects 'D' at char 4
    refl  -- P4 fails — string "BA_REL_" expects 'R' at char 4
    alt5-eq
  where
    input : List Char
    input = toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
            ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n" ++ₗ outer-suffix

    alt5-eq : proj₂ (P5 pos input)
              ≡ just (mkResult
                       (RawAssign (mkRawAttrAssign name ATgtNetwork (RavString s)))
                       (NetworkProofs.TraceNetwork.pos9 pos name (quoteStringLit-chars s) outer-suffix)
                       outer-suffix)
    alt5-eq = bind-just-step parseRawAttrAssign (λ a → pure (RawAssign a))
                pos input
                (mkRawAttrAssign name ATgtNetwork (RavString s))
                (NetworkProofs.TraceNetwork.pos9 pos name (quoteStringLit-chars s) outer-suffix)
                outer-suffix
                (parseRawAttrAssign-roundtrip-ATgtNetwork-RavString
                   pos name s outer-suffix ss-NL)

parseAttrLine-roundtrip-RawAssign-ATgtNetwork-RavDecRatFrac :
    ∀ pos (name : List Char) (d : DecRat) (outer-suffix : List Char)
  → SuffixStops isNewlineStart outer-suffix
  → proj₂ (parseAttrLine pos
      (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
        ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n" ++ₗ outer-suffix))
    ≡ just (mkResult
              (RawAssign (mkRawAttrAssign name ATgtNetwork (RavDecRat d)))
              (NetworkProofs.TraceNetwork.pos9 pos name (showDecRat-dec-chars d) outer-suffix)
              outer-suffix)
parseAttrLine-roundtrip-RawAssign-ATgtNetwork-RavDecRatFrac pos name d outer-suffix ss-NL =
  parseAttrLine-lift-alt5 pos input _ refl refl refl refl
    (bind-just-step parseRawAttrAssign (λ a → pure (RawAssign a))
       pos input _ _ _
       (parseRawAttrAssign-roundtrip-ATgtNetwork-RavDecRatFrac
          pos name d outer-suffix ss-NL))
  where
    input : List Char
    input = toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
            ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n" ++ₗ outer-suffix

parseAttrLine-roundtrip-RawAssign-ATgtNetwork-RavDecRatBareInt :
    ∀ pos (name : List Char) (z : ℤ) (outer-suffix : List Char)
  → SuffixStops isNewlineStart outer-suffix
  → proj₂ (parseAttrLine pos
      (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
        ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer-suffix))
    ≡ just (mkResult
              (RawAssign (mkRawAttrAssign name ATgtNetwork (RavDecRat (fromℤ z))))
              (NetworkProofs.TraceNetwork.pos9 pos name (showInt-chars z) outer-suffix)
              outer-suffix)
parseAttrLine-roundtrip-RawAssign-ATgtNetwork-RavDecRatBareInt pos name z outer-suffix ss-NL =
  parseAttrLine-lift-alt5 pos input _ refl refl refl refl
    (bind-just-step parseRawAttrAssign (λ a → pure (RawAssign a))
       pos input _ _ _
       (parseRawAttrAssign-roundtrip-ATgtNetwork-RavDecRatBareInt
          pos name z outer-suffix ss-NL))
  where
    input : List Char
    input = toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
            ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer-suffix

-- ATgtNode × 3
parseAttrLine-roundtrip-RawAssign-ATgtNode-RavString :
    ∀ pos (name : List Char) (n : Identifier) (s : List Char) (outer-suffix : List Char)
  → IdentNameStop n
  → SuffixStops isNewlineStart outer-suffix
  → proj₂ (parseAttrLine pos
      (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " BU_ " ++ₗ Identifier.name n ++ₗ
        ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n" ++ₗ outer-suffix))
    ≡ just (mkResult
              (RawAssign (mkRawAttrAssign name (ATgtNode n) (RavString s)))
              (NodeProofs.TraceNode.pos9 pos name n (quoteStringLit-chars s) outer-suffix)
              outer-suffix)
parseAttrLine-roundtrip-RawAssign-ATgtNode-RavString pos name n s outer-suffix n-stop ss-NL =
  parseAttrLine-lift-alt5 pos input _ refl refl refl refl
    (bind-just-step parseRawAttrAssign (λ a → pure (RawAssign a))
       pos input _ _ _
       (parseRawAttrAssign-roundtrip-ATgtNode-RavString
          pos name n s outer-suffix n-stop ss-NL))
  where
    input : List Char
    input = toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
            toList " BU_ " ++ₗ Identifier.name n ++ₗ
            ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n" ++ₗ outer-suffix

parseAttrLine-roundtrip-RawAssign-ATgtNode-RavDecRatFrac :
    ∀ pos (name : List Char) (n : Identifier) (d : DecRat) (outer-suffix : List Char)
  → IdentNameStop n
  → SuffixStops isNewlineStart outer-suffix
  → proj₂ (parseAttrLine pos
      (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " BU_ " ++ₗ Identifier.name n ++ₗ
        ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n" ++ₗ outer-suffix))
    ≡ just (mkResult
              (RawAssign (mkRawAttrAssign name (ATgtNode n) (RavDecRat d)))
              (NodeProofs.TraceNode.pos9 pos name n (showDecRat-dec-chars d) outer-suffix)
              outer-suffix)
parseAttrLine-roundtrip-RawAssign-ATgtNode-RavDecRatFrac pos name n d outer-suffix n-stop ss-NL =
  parseAttrLine-lift-alt5 pos input _ refl refl refl refl
    (bind-just-step parseRawAttrAssign (λ a → pure (RawAssign a))
       pos input _ _ _
       (parseRawAttrAssign-roundtrip-ATgtNode-RavDecRatFrac
          pos name n d outer-suffix n-stop ss-NL))
  where
    input : List Char
    input = toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
            toList " BU_ " ++ₗ Identifier.name n ++ₗ
            ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n" ++ₗ outer-suffix

parseAttrLine-roundtrip-RawAssign-ATgtNode-RavDecRatBareInt :
    ∀ pos (name : List Char) (n : Identifier) (z : ℤ) (outer-suffix : List Char)
  → IdentNameStop n
  → SuffixStops isNewlineStart outer-suffix
  → proj₂ (parseAttrLine pos
      (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " BU_ " ++ₗ Identifier.name n ++ₗ
        ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer-suffix))
    ≡ just (mkResult
              (RawAssign (mkRawAttrAssign name (ATgtNode n) (RavDecRat (fromℤ z))))
              (NodeProofs.TraceNode.pos9 pos name n (showInt-chars z) outer-suffix)
              outer-suffix)
parseAttrLine-roundtrip-RawAssign-ATgtNode-RavDecRatBareInt pos name n z outer-suffix n-stop ss-NL =
  parseAttrLine-lift-alt5 pos input _ refl refl refl refl
    (bind-just-step parseRawAttrAssign (λ a → pure (RawAssign a))
       pos input _ _ _
       (parseRawAttrAssign-roundtrip-ATgtNode-RavDecRatBareInt
          pos name n z outer-suffix n-stop ss-NL))
  where
    input : List Char
    input = toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
            toList " BU_ " ++ₗ Identifier.name n ++ₗ
            ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer-suffix

-- ATgtMessage × 3
parseAttrLine-roundtrip-RawAssign-ATgtMessage-RavString :
    ∀ pos (name : List Char) (cid : CANId) (s : List Char) (outer-suffix : List Char)
  → SuffixStops isNewlineStart outer-suffix
  → proj₂ (parseAttrLine pos
      (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " BO_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
        ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n" ++ₗ outer-suffix))
    ≡ just (mkResult
              (RawAssign (mkRawAttrAssign name (ATgtMessage cid) (RavString s)))
              (MessageProofs.TraceMessage.pos9 pos name cid (quoteStringLit-chars s) outer-suffix)
              outer-suffix)
parseAttrLine-roundtrip-RawAssign-ATgtMessage-RavString pos name cid s outer-suffix ss-NL =
  parseAttrLine-lift-alt5 pos input _ refl refl refl refl
    (bind-just-step parseRawAttrAssign (λ a → pure (RawAssign a))
       pos input _ _ _
       (parseRawAttrAssign-roundtrip-ATgtMessage-RavString
          pos name cid s outer-suffix ss-NL))
  where
    input : List Char
    input = toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
            toList " BO_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
            ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n" ++ₗ outer-suffix

parseAttrLine-roundtrip-RawAssign-ATgtMessage-RavDecRatFrac :
    ∀ pos (name : List Char) (cid : CANId) (d : DecRat) (outer-suffix : List Char)
  → SuffixStops isNewlineStart outer-suffix
  → proj₂ (parseAttrLine pos
      (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " BO_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
        ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n" ++ₗ outer-suffix))
    ≡ just (mkResult
              (RawAssign (mkRawAttrAssign name (ATgtMessage cid) (RavDecRat d)))
              (MessageProofs.TraceMessage.pos9 pos name cid (showDecRat-dec-chars d) outer-suffix)
              outer-suffix)
parseAttrLine-roundtrip-RawAssign-ATgtMessage-RavDecRatFrac pos name cid d outer-suffix ss-NL =
  parseAttrLine-lift-alt5 pos input _ refl refl refl refl
    (bind-just-step parseRawAttrAssign (λ a → pure (RawAssign a))
       pos input _ _ _
       (parseRawAttrAssign-roundtrip-ATgtMessage-RavDecRatFrac
          pos name cid d outer-suffix ss-NL))
  where
    input : List Char
    input = toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
            toList " BO_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
            ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n" ++ₗ outer-suffix

parseAttrLine-roundtrip-RawAssign-ATgtMessage-RavDecRatBareInt :
    ∀ pos (name : List Char) (cid : CANId) (z : ℤ) (outer-suffix : List Char)
  → SuffixStops isNewlineStart outer-suffix
  → proj₂ (parseAttrLine pos
      (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " BO_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
        ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer-suffix))
    ≡ just (mkResult
              (RawAssign (mkRawAttrAssign name (ATgtMessage cid) (RavDecRat (fromℤ z))))
              (MessageProofs.TraceMessage.pos9 pos name cid (showInt-chars z) outer-suffix)
              outer-suffix)
parseAttrLine-roundtrip-RawAssign-ATgtMessage-RavDecRatBareInt pos name cid z outer-suffix ss-NL =
  parseAttrLine-lift-alt5 pos input _ refl refl refl refl
    (bind-just-step parseRawAttrAssign (λ a → pure (RawAssign a))
       pos input _ _ _
       (parseRawAttrAssign-roundtrip-ATgtMessage-RavDecRatBareInt
          pos name cid z outer-suffix ss-NL))
  where
    input : List Char
    input = toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
            toList " BO_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
            ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer-suffix

-- ATgtSignal × 3
parseAttrLine-roundtrip-RawAssign-ATgtSignal-RavString :
    ∀ pos (name : List Char) (cid : CANId) (sig : Identifier) (s : List Char)
      (outer-suffix : List Char)
  → IdentNameStop sig
  → SuffixStops isNewlineStart outer-suffix
  → proj₂ (parseAttrLine pos
      (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
        ' ' ∷ Identifier.name sig ++ₗ
        ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n" ++ₗ outer-suffix))
    ≡ just (mkResult
              (RawAssign (mkRawAttrAssign name (ATgtSignal cid sig) (RavString s)))
              (SignalProofs.TraceSignal.pos9 pos name cid sig (quoteStringLit-chars s) outer-suffix)
              outer-suffix)
parseAttrLine-roundtrip-RawAssign-ATgtSignal-RavString pos name cid sig s outer-suffix sig-stop ss-NL =
  parseAttrLine-lift-alt5 pos input _ refl refl refl refl
    (bind-just-step parseRawAttrAssign (λ a → pure (RawAssign a))
       pos input _ _ _
       (parseRawAttrAssign-roundtrip-ATgtSignal-RavString
          pos name cid sig s outer-suffix sig-stop ss-NL))
  where
    input : List Char
    input = toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
            toList " SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
            ' ' ∷ Identifier.name sig ++ₗ
            ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n" ++ₗ outer-suffix

parseAttrLine-roundtrip-RawAssign-ATgtSignal-RavDecRatFrac :
    ∀ pos (name : List Char) (cid : CANId) (sig : Identifier) (d : DecRat)
      (outer-suffix : List Char)
  → IdentNameStop sig
  → SuffixStops isNewlineStart outer-suffix
  → proj₂ (parseAttrLine pos
      (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
        ' ' ∷ Identifier.name sig ++ₗ
        ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n" ++ₗ outer-suffix))
    ≡ just (mkResult
              (RawAssign (mkRawAttrAssign name (ATgtSignal cid sig) (RavDecRat d)))
              (SignalProofs.TraceSignal.pos9 pos name cid sig (showDecRat-dec-chars d) outer-suffix)
              outer-suffix)
parseAttrLine-roundtrip-RawAssign-ATgtSignal-RavDecRatFrac pos name cid sig d outer-suffix sig-stop ss-NL =
  parseAttrLine-lift-alt5 pos input _ refl refl refl refl
    (bind-just-step parseRawAttrAssign (λ a → pure (RawAssign a))
       pos input _ _ _
       (parseRawAttrAssign-roundtrip-ATgtSignal-RavDecRatFrac
          pos name cid sig d outer-suffix sig-stop ss-NL))
  where
    input : List Char
    input = toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
            toList " SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
            ' ' ∷ Identifier.name sig ++ₗ
            ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n" ++ₗ outer-suffix

parseAttrLine-roundtrip-RawAssign-ATgtSignal-RavDecRatBareInt :
    ∀ pos (name : List Char) (cid : CANId) (sig : Identifier) (z : ℤ)
      (outer-suffix : List Char)
  → IdentNameStop sig
  → SuffixStops isNewlineStart outer-suffix
  → proj₂ (parseAttrLine pos
      (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
        ' ' ∷ Identifier.name sig ++ₗ
        ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer-suffix))
    ≡ just (mkResult
              (RawAssign (mkRawAttrAssign name (ATgtSignal cid sig) (RavDecRat (fromℤ z))))
              (SignalProofs.TraceSignal.pos9 pos name cid sig (showInt-chars z) outer-suffix)
              outer-suffix)
parseAttrLine-roundtrip-RawAssign-ATgtSignal-RavDecRatBareInt pos name cid sig z outer-suffix sig-stop ss-NL =
  parseAttrLine-lift-alt5 pos input _ refl refl refl refl
    (bind-just-step parseRawAttrAssign (λ a → pure (RawAssign a))
       pos input _ _ _
       (parseRawAttrAssign-roundtrip-ATgtSignal-RavDecRatBareInt
          pos name cid sig z outer-suffix sig-stop ss-NL))
  where
    input : List Char
    input = toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
            toList " SG_ " ++ₗ showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
            ' ' ∷ Identifier.name sig ++ₗ
            ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer-suffix

-- ATgtEnvVar × 3
parseAttrLine-roundtrip-RawAssign-ATgtEnvVar-RavString :
    ∀ pos (name : List Char) (ev : Identifier) (s : List Char) (outer-suffix : List Char)
  → IdentNameStop ev
  → SuffixStops isNewlineStart outer-suffix
  → proj₂ (parseAttrLine pos
      (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " EV_ " ++ₗ Identifier.name ev ++ₗ
        ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n" ++ₗ outer-suffix))
    ≡ just (mkResult
              (RawAssign (mkRawAttrAssign name (ATgtEnvVar ev) (RavString s)))
              (EnvVarProofs.TraceEnvVar.pos9 pos name ev (quoteStringLit-chars s) outer-suffix)
              outer-suffix)
parseAttrLine-roundtrip-RawAssign-ATgtEnvVar-RavString pos name ev s outer-suffix ev-stop ss-NL =
  parseAttrLine-lift-alt5 pos input _ refl refl refl refl
    (bind-just-step parseRawAttrAssign (λ a → pure (RawAssign a))
       pos input _ _ _
       (parseRawAttrAssign-roundtrip-ATgtEnvVar-RavString
          pos name ev s outer-suffix ev-stop ss-NL))
  where
    input : List Char
    input = toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
            toList " EV_ " ++ₗ Identifier.name ev ++ₗ
            ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n" ++ₗ outer-suffix

parseAttrLine-roundtrip-RawAssign-ATgtEnvVar-RavDecRatFrac :
    ∀ pos (name : List Char) (ev : Identifier) (d : DecRat) (outer-suffix : List Char)
  → IdentNameStop ev
  → SuffixStops isNewlineStart outer-suffix
  → proj₂ (parseAttrLine pos
      (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " EV_ " ++ₗ Identifier.name ev ++ₗ
        ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n" ++ₗ outer-suffix))
    ≡ just (mkResult
              (RawAssign (mkRawAttrAssign name (ATgtEnvVar ev) (RavDecRat d)))
              (EnvVarProofs.TraceEnvVar.pos9 pos name ev (showDecRat-dec-chars d) outer-suffix)
              outer-suffix)
parseAttrLine-roundtrip-RawAssign-ATgtEnvVar-RavDecRatFrac pos name ev d outer-suffix ev-stop ss-NL =
  parseAttrLine-lift-alt5 pos input _ refl refl refl refl
    (bind-just-step parseRawAttrAssign (λ a → pure (RawAssign a))
       pos input _ _ _
       (parseRawAttrAssign-roundtrip-ATgtEnvVar-RavDecRatFrac
          pos name ev d outer-suffix ev-stop ss-NL))
  where
    input : List Char
    input = toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
            toList " EV_ " ++ₗ Identifier.name ev ++ₗ
            ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n" ++ₗ outer-suffix

parseAttrLine-roundtrip-RawAssign-ATgtEnvVar-RavDecRatBareInt :
    ∀ pos (name : List Char) (ev : Identifier) (z : ℤ) (outer-suffix : List Char)
  → IdentNameStop ev
  → SuffixStops isNewlineStart outer-suffix
  → proj₂ (parseAttrLine pos
      (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
        toList " EV_ " ++ₗ Identifier.name ev ++ₗ
        ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer-suffix))
    ≡ just (mkResult
              (RawAssign (mkRawAttrAssign name (ATgtEnvVar ev) (RavDecRat (fromℤ z))))
              (EnvVarProofs.TraceEnvVar.pos9 pos name ev (showInt-chars z) outer-suffix)
              outer-suffix)
parseAttrLine-roundtrip-RawAssign-ATgtEnvVar-RavDecRatBareInt pos name ev z outer-suffix ev-stop ss-NL =
  parseAttrLine-lift-alt5 pos input _ refl refl refl refl
    (bind-just-step parseRawAttrAssign (λ a → pure (RawAssign a))
       pos input _ _ _
       (parseRawAttrAssign-roundtrip-ATgtEnvVar-RavDecRatBareInt
          pos name ev z outer-suffix ev-stop ss-NL))
  where
    input : List Char
    input = toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
            toList " EV_ " ++ₗ Identifier.name ev ++ₗ
            ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer-suffix

