-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Decimal-string → rational entry point for the FFI.
--
-- This is the kernel-side single source of truth for "parse a user-entered
-- decimal into an exact rational".  Every binding (Python / Go / C++ / Rust)
-- routes decimal input through `aletheia_parse_decimal` (the Haskell shim
-- wrapper around `parseDecimal`) instead of re-implementing a float→rational
-- heuristic, so the accepted grammar cannot drift between languages.
--
-- The float principle: a decimal is an *exact* rational (a `DecRat`,
-- denominator 2^a·5^b), never a float64.  A `float` only ever appears when a
-- value is finally printed for a human; nothing internal to the program is a
-- float.  This module is the input half of that contract.
--
-- Grammar (delegated wholesale to `parseDecRat`):
--     -?digits          (bare integer)
--     -?digits.digits+  (mandatory fraction)
-- No leading '+', no bare '.5', no scientific notation.  See
-- `Aletheia.DBC.TextParser.DecRatParse`.
--
-- `fromResult` is intentionally STRICTER than the library `runParser`
-- (Combinators), which discards trailing input: full consumption is required,
-- so "3.14xyz" is rejected rather than silently truncated to 3.14.  It is a
-- standalone named helper (not an inline `with runParserPartial …`) so the
-- roundtrip proof in `DecimalEntry.Properties` can close by `cong fromResult`
-- — an inline `with` abstracts the scrutinee and blocks the rewrite.
module Aletheia.DBC.TextParser.DecimalEntry where

open import Data.String using (String; toList)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Rational.Base using (ℚ)

open import Aletheia.Parser.Combinators using (runParserPartial; ParseResult; mkResult)
open import Aletheia.DBC.TextParser.DecRatParse using (parseDecRat)
open import Aletheia.DBC.DecRat using (DecRat; toℚ)

-- Accept a parse only when the whole input was consumed.
fromResult : Maybe (ParseResult DecRat) → Maybe DecRat
fromResult nothing                       = nothing
fromResult (just (mkResult d _ []))      = just d
fromResult (just (mkResult _ _ (_ ∷ _))) = nothing

-- Parse a decimal-character stream into a canonical `DecRat`.
parseDecimal-chars : List Char → Maybe DecRat
parseDecimal-chars cs = fromResult (runParserPartial parseDecRat cs)

-- FFI entry: parse a decimal string into the exact rational it denotes.
-- `nothing` means "not a valid decimal literal".  The shim turns the result
-- into the wire envelope (`{numerator,denominator}` on success, an error
-- envelope otherwise) and catches Int64 overflow at the marshaling boundary.
parseDecimal : String → Maybe ℚ
parseDecimal s = map toℚ (parseDecimal-chars (toList s))
