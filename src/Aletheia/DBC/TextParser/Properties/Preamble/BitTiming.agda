-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Slim `parseBitTiming-roundtrip` derived from the universal Format DSL
-- roundtrip.
--
-- The earlier form was a hand-written ~226-line bind-chain proof through
-- 7 parser primitives.
--
-- Now `parseBitTiming = parse bitTimingFmt >>= λ _ → many
-- parseNewline >>= λ _ → pure tt` (in `TextParser.Preamble`), and the
-- roundtrip reduces to the same 3-step bind chain as
-- `parseVersion-roundtrip`:
--
--   1. Bridge `emit-bitTimingFmt-eq-emitBitTiming-chars-prefix` (DSL
--      emit + trailing `\n` ≡ existing `emitBitTiming-chars`).
--   2. Universal `parseBitTiming-format-roundtrip`.
--   3. Trailing `many parseNewline` consuming the formatter's section-
--      blank `\n`.
--   4. 2-stage pos-eq.
module Aletheia.DBC.TextParser.Properties.Preamble.BitTiming where

open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; length) renaming (_++_ to _++ₗ_)
open import Data.List.Properties using () renaming (++-assoc to ++ₗ-assoc)
open import Data.Maybe using (just)
open import Data.Product using (proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; sym; trans; cong)

open import Aletheia.Parser.Combinators using
  (Parser; Position; mkResult; advancePosition; advancePositions;
   pure; _>>=_; many)
open import Aletheia.DBC.TextParser.Lexer using (parseNewline)
open import Aletheia.DBC.TextParser.Preamble using (parseBitTiming)
open import Aletheia.DBC.TextFormatter.Preamble using (emitBitTiming-chars)

open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (SuffixStops; bind-just-step; advancePositions-++)
open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  (isNewlineStart; many-parseNewline-one-LF-stop)

open import Aletheia.DBC.TextParser.Format using
  (emit; parse)
open import Aletheia.DBC.TextParser.Format.Preamble as FmtBs using
  (bitTimingFmt)

parseBitTiming-roundtrip :
    ∀ (pos : Position) (suffix : List Char)
  → SuffixStops isNewlineStart suffix
  → proj₂ (parseBitTiming pos (emitBitTiming-chars ++ₗ suffix))
    ≡ just (mkResult tt
             (advancePositions pos emitBitTiming-chars)
             suffix)
parseBitTiming-roundtrip pos suffix nl-stop =
  trans (cong (λ inp → proj₂ (parseBitTiming pos (inp ++ₗ suffix)))
              (sym bridge))
    (trans step-shape
      (trans step-format
        (trans step-many-newline
          step-pure)))
  where
    bridge : emit bitTimingFmt tt ++ₗ '\n' ∷ [] ≡ emitBitTiming-chars
    bridge = FmtBs.emit-bitTimingFmt-eq-emitBitTiming-chars-prefix

    pos-line : Position
    pos-line = advancePositions pos (emit bitTimingFmt tt)

    pos-after-nl : Position
    pos-after-nl = advancePosition pos-line '\n'

    cont-line : ⊤ → Parser ⊤
    cont-line _ = many parseNewline >>= λ _ → pure tt

    cont-blanks : List Char → Parser ⊤
    cont-blanks _ = pure tt

    step-shape :
      proj₂ (parseBitTiming pos
              ((emit bitTimingFmt tt ++ₗ '\n' ∷ []) ++ₗ suffix))
      ≡ proj₂ (parseBitTiming pos (emit bitTimingFmt tt ++ₗ '\n' ∷ suffix))
    step-shape = cong (λ inp → proj₂ (parseBitTiming pos inp))
                      (++ₗ-assoc (emit bitTimingFmt tt) ('\n' ∷ []) suffix)

    step-format :
      proj₂ (parseBitTiming pos (emit bitTimingFmt tt ++ₗ '\n' ∷ suffix))
      ≡ proj₂ (cont-line tt pos-line ('\n' ∷ suffix))
    step-format =
      bind-just-step (parse bitTimingFmt) cont-line
                     pos (emit bitTimingFmt tt ++ₗ '\n' ∷ suffix)
                     tt pos-line ('\n' ∷ suffix)
                     (FmtBs.parseBitTiming-format-roundtrip
                       pos ('\n' ∷ suffix))

    step-many-newline :
      proj₂ (cont-line tt pos-line ('\n' ∷ suffix))
      ≡ proj₂ (cont-blanks ('\n' ∷ []) pos-after-nl suffix)
    step-many-newline =
      bind-just-step (many parseNewline) cont-blanks
                     pos-line ('\n' ∷ suffix)
                     ('\n' ∷ []) pos-after-nl suffix
                     (many-parseNewline-one-LF-stop
                       pos-line suffix (length suffix) nl-stop)

    pos-eq : pos-after-nl ≡ advancePositions pos emitBitTiming-chars
    pos-eq =
      trans
        (sym (advancePositions-++ pos (emit bitTimingFmt tt) ('\n' ∷ [])))
        (cong (advancePositions pos) bridge)

    step-pure :
      proj₂ (cont-blanks ('\n' ∷ []) pos-after-nl suffix)
      ≡ just (mkResult tt
               (advancePositions pos emitBitTiming-chars)
               suffix)
    step-pure = cong (λ p → just (mkResult tt p suffix)) pos-eq
