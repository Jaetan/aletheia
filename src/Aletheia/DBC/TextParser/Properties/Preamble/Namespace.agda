-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Slim `parseNamespace-roundtrip` derived from the universal Format DSL
-- roundtrip.
--
-- The earlier form was a hand-written ~864-line bind-chain proof through
-- 25-keyword inductive `manyHelper-parseNSLine-body` + per-branch
-- `parseNSLine-blank` / `parseNSLine-keyword` lemmas + length bounds.
--
-- Now `parseNamespace = parse nsFmt >>= λ _ → pure tt`
-- (in `TextParser.Preamble`), and the roundtrip reduces to:
--
--   1. The universal `parseNamespace-format-roundtrip` (from
--      `Format.Preamble`), which consumes the entire `"NS_ :\n" + 25
--      keyword lines + 1 trailing blank line` block via the discard-
--      iso over `many nsLineFmt`.
--   2. The `pure tt` step (one `bind-just-step`).
--   3. Position alignment via the bridge `emit nsFmt tt ≡
--      emitNamespace-chars` (`refl`).
--
-- `isNSLineStart` precondition migrates upstream to `Format.Preamble`;
-- this module re-exports it for source compatibility with the section
-- facade `Properties.Preamble`.
module Aletheia.DBC.TextParser.Properties.Preamble.Namespace where

open import Data.Char using (Char)
open import Data.List using (List) renaming (_++_ to _++ₗ_)
open import Data.Maybe using (just)
open import Data.Product using (proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; sym; trans; cong)

open import Aletheia.Parser.Combinators using
  (Parser; Position; mkResult; advancePositions; pure)
open import Aletheia.DBC.TextParser.Preamble using (parseNamespace)
open import Aletheia.DBC.TextFormatter.Preamble using (emitNamespace-chars)

open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (SuffixStops; bind-just-step)

open import Aletheia.DBC.TextParser.Format using
  (emit; parse)
open import Aletheia.DBC.TextParser.Format.Preamble as FmtNs using
  (nsFmt)

-- ============================================================================
-- RE-EXPORT — `isNSLineStart` migrated to `Format.Preamble`
-- ============================================================================

open import Aletheia.DBC.TextParser.Format.Preamble public
  using (isNSLineStart)

-- ============================================================================
-- SLIM `parseNamespace-roundtrip`
-- ============================================================================

parseNamespace-roundtrip : ∀ (pos : Position) (suffix : List Char)
  → SuffixStops isNSLineStart suffix
  → proj₂ (parseNamespace pos (emitNamespace-chars ++ₗ suffix))
    ≡ just (mkResult tt
             (advancePositions pos emitNamespace-chars) suffix)
parseNamespace-roundtrip pos suffix outer-stop =
  trans (cong (λ inp → proj₂ (parseNamespace pos (inp ++ₗ suffix)))
              (sym bridge))
    (trans step-format step-pure)
  where
    bridge : emit nsFmt tt ≡ emitNamespace-chars
    bridge = FmtNs.emit-nsFmt-eq-emitNamespace-chars

    pos-line : Position
    pos-line = advancePositions pos (emit nsFmt tt)

    cont-pure : ⊤ → Parser ⊤
    cont-pure _ = pure tt

    -- Step 1: parse nsFmt succeeds via the universal roundtrip,
    -- consuming the entire `"NS_ :\n" + 25 keyword lines + 1 trailing
    -- blank` block.
    step-format :
      proj₂ (parseNamespace pos (emit nsFmt tt ++ₗ suffix))
      ≡ proj₂ (cont-pure tt pos-line suffix)
    step-format =
      bind-just-step (parse nsFmt) cont-pure
                     pos (emit nsFmt tt ++ₗ suffix)
                     tt pos-line suffix
                     (FmtNs.parseNamespace-format-roundtrip
                       pos suffix outer-stop)

    -- Step 2: pure tt with position aligned via the bridge.
    pos-eq : pos-line ≡ advancePositions pos emitNamespace-chars
    pos-eq = cong (advancePositions pos) bridge

    step-pure :
      proj₂ (cont-pure tt pos-line suffix)
      ≡ just (mkResult tt
               (advancePositions pos emitNamespace-chars) suffix)
    step-pure = cong (λ p → just (mkResult tt p suffix)) pos-eq
