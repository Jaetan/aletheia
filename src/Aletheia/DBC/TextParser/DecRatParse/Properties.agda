-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- DBC DecRat parser — roundtrip proof facade.  Target theorem:
--
--   parseDecRatFrac-roundtrip : ∀ d → runParser parseDecRat
--                              (showDecRat-dec-chars d) ≡ just (d , _)
--
-- stated over `List Char` (not `String`), per-primitive rather than at the
-- `String` boundary.
-- Sidesteps the `toList-++ₛ` substrate gap: the emitter primitive
-- `showDecRat-dec-chars` and the parser's input list stream stay in
-- `List Char` end-to-end, so no `String`-level append lemma is needed.
--
-- Proof structure — five submodules, each well under the 800-LOC
-- trigger:
--
--   * `Properties.Phase1Digits`     (Phase 1; ~300 LOC) — arithmetic /
--     list-level lemmas, digit-converter-generic foldl.
--   * `Properties.Phase2Many`       (Phase 2; ~230 LOC) —
--     `manyHelper-satisfy-prefix` + parser-machinery lemmas.
--   * `Properties.Phase3Naturals`   (Phase 3; ~800 LOC) — parseNatural
--     roundtrip, canonicalisation extractors, mag-* arithmetic for
--     Phase 4.
--   * `Properties.Phase4Composition` (Phases 4 + 5; ~380 LOC) — per-sign
--     branches + the suffix=[] top-level dispatcher.
--   * `Properties.Phase6Suffix`     (Phase 6 + 6.5 + 6.6 + 6.7; ~940
--     LOC) — suffix-aware variants, bareInt-form roundtrip, refined-
--     parser wrappers.
--
-- This facade re-exports every public name from the five submodules so
-- existing consumers (`Properties/Primitives.agda` + walk roots in
-- `tools/check_properties.py`) see no surface change.  No definitions
-- live here; all phase content is in the submodules.
module Aletheia.DBC.TextParser.DecRatParse.Properties where

open import Aletheia.DBC.TextParser.DecRatParse.Properties.Phase1Digits      public
open import Aletheia.DBC.TextParser.DecRatParse.Properties.Phase2Many        public
open import Aletheia.DBC.TextParser.DecRatParse.Properties.Phase3Naturals    public
open import Aletheia.DBC.TextParser.DecRatParse.Properties.Phase4Composition public
open import Aletheia.DBC.TextParser.DecRatParse.Properties.Phase6Suffix      public
