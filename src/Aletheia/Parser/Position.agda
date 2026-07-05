-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Source-position tracking for the parser combinators.
--
-- A leaf module (no parser dependencies) so that position CONSUMERS —
-- the error vocabulary (`Aletheia.Error`), the response serializer's
-- structured line/column extras, and their large downstream closures —
-- can name `Position` without importing the combinator library, keeping
-- them out of the recheck closure of every combinator change.
module Aletheia.Parser.Position where

open import Data.Bool using (true; false)
open import Data.Char using (Char; _≈ᵇ_)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; suc; _<ᵇ_)

-- Source position (line and column numbers)
record Position : Set where
  constructor mkPos
  field
    line : ℕ
    column : ℕ

open Position public

-- Initial position (start of input)
initialPosition : Position
initialPosition = mkPos 1 1

-- Advance position by one character
advancePosition : Position → Char → Position
advancePosition pos c with c ≈ᵇ '\n'
... | true  = mkPos (suc (line pos)) 1
... | false = mkPos (line pos) (suc (column pos))

-- Advance position by a list of characters
advancePositions : Position → List Char → Position
advancePositions pos [] = pos
advancePositions pos (c ∷ cs) = advancePositions (advancePosition pos c) cs

-- Furthest-position merge: lexicographic max on (line, column). Used by
-- the combinators' failure-watermark plumbing (`_<|>_` merges the depths
-- of failed alternatives; `_>>=_` merges sequential watermarks) so a
-- failed parse reports the deepest point ANY branch reached.
maxₚ : Position → Position → Position
maxₚ p q with line p <ᵇ line q
... | true  = q
... | false with line q <ᵇ line p
...   | true  = p
...   | false with column p <ᵇ column q
...     | true  = q
...     | false = p
