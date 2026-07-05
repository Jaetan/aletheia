-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Character-class predicates shared by the parser combinators and
-- non-parser vocabulary modules (`Aletheia.DBC.Identifier`).
--
-- A leaf module (no parser dependencies) for the same reason as
-- `Aletheia.Parser.Position`: identifier validity is part of the DBC
-- type vocabulary, and routing it through the combinator library would
-- put the whole error/type closure inside every combinator change's
-- recheck set.
module Aletheia.Parser.CharClass where

open import Data.Bool using (Bool; _∧_; _∨_; not)
open import Data.Char using (Char)
open import Data.Char.Base using (isDigit; isAlpha; isLower)

-- isUpper: stdlib only has isLower, so define isUpper as "alpha but not lower"
isUpper : Char → Bool
isUpper c = isAlpha c ∧ not (isLower c)

-- isAlphaNum: simple composition of stdlib functions
isAlphaNum : Char → Bool
isAlphaNum c = isAlpha c ∨ isDigit c
