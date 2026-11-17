-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Microsecond text → time bound entry point for the FFI.
--
-- A loader's `within_us` is a text; `aletheia_parse_time_bound`, the
-- Haskell shim's wrapper around `parseTimeBound`, reads it so that no
-- binding decides what a time bound is.  The text is read as the decimal
-- entry reads a decimal (the whole text, its value held to the rational
-- component bound, a refusal naming the field `decimal`), then decided as
-- the property parse decides a time bound (`timeBound`): a whole,
-- non-negative number of microseconds at most `max-time-bound`, refused
-- otherwise with the property parse's own reason.
module Aletheia.LTL.TimeBoundEntry where

open import Data.Char using (Char)
open import Data.List using (List)
open import Data.Nat using (ℕ)
open import Data.Product using (uncurry)
open import Data.String using (String; toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Aletheia.Parser.Combinators using (value; runParserPartial)
open import Aletheia.DBC.TextParser.DecRatParse using (parseDecRat)
open import Aletheia.DBC.TextParser.Consumed using (consumed)
open import Aletheia.DBC.DecRat using (toℚ)
open import Aletheia.DBC.Bounds using (magnitude)
open import Aletheia.Error using (Error; PropertyRefused)
open import Aletheia.LTL.JSON using (timeBound; parseFailError)

parseTimeBound-chars : List Char → Error ⊎ ℕ
parseTimeBound-chars cs with uncurry consumed (runParserPartial parseDecRat cs)
... | inj₁ e = inj₁ e
... | inj₂ res with magnitude "decimal" (value res)
...   | inj₁ e = inj₁ e
...   | inj₂ _ with timeBound (toℚ (value res))
...     | inj₁ pf = inj₁ (parseFailError PropertyRefused pf)
...     | inj₂ n  = inj₂ n

-- FFI entry: the microseconds a text denotes, or the refusal.
parseTimeBound : String → Error ⊎ ℕ
parseTimeBound s = parseTimeBound-chars (toList s)
