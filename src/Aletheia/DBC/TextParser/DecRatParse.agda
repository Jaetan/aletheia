-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- DBC decimal-rational parser, terminal for `scale`, `offset`, `min`,
-- `max`, environment-variable bounds, value-table keys and every attribute
-- numeric slot.
--
-- Two shapes accepted, in `<|>` order:
--
--   1. Frac form (Shape B emitter `showDecRat-dec`):
--        decrat ::= "-"? digit+ "." digit+
--      The formatter always emits a `'.'` plus at least one fractional
--      digit for every numeric DBC slot it writes as DecRat.
--
--   2. Bare-int form:
--        decrat ::= "-"? digit+
--      Admits cantools-style attribute values like `BA_ "X" BO_ 400 50;`.
--
-- The frac form is tried first, so `42.5` commits to the longer match
-- rather than splitting into `42` and a leftover `.5`; `<|>` restores the
-- parser state when the frac form fails.  Unlike the JSON grammar, the DBC
-- grammar has no scientific notation.
--
-- Both shapes hand their digit runs to `Aletheia.DBC.DecRat.Literal`, the
-- one literal core shared with the JSON grammar, which folds the digits
-- only when the value fits the component bound and holds the literal at
-- 2^64 otherwise, so a literal of any length costs time linear in its
-- length.  The roundtrip proofs in
-- `Aletheia.DBC.TextParser.DecRatParse.Properties` rest on the core's
-- exactness theorem.
module Aletheia.DBC.TextParser.DecRatParse where

open import Data.List using (List; [])
open import Data.Integer using (ℤ; +_)

open import Aletheia.Parser.Combinators using
  (Parser; pure; fail; _>>=_; _<|>_; char; digit; optional; some)
open import Aletheia.DBC.DecRat using (DecRat)
open import Aletheia.DBC.DecRat.Refinement using
  (IntDecRat; mkIntDecRat; isIntegerᵇ;
   NatDecRat; mkNatDecRat; isNonNegIntegerᵇ)
open import Aletheia.DBC.TextParser.Lexer using (parseDigits)
open import Aletheia.DBC.DecRat.Literal using (decimalLiteral)
open import Aletheia.Prelude using (ifᵀ_then_else_)

-- Frac form (Shape B): `"-?" nat "." digit+`.  Matches `showDecRat-dec`
-- exactly; the per-shape roundtrip proofs in
-- `Aletheia.DBC.TextParser.DecRatParse.Properties` are stated about this
-- inner parser (`parseDecRatFrac-roundtrip-suffix` and friends).
parseDecRatFrac : Parser DecRat
parseDecRatFrac = do
  neg ← optional (char '-')
  int ← parseDigits
  _   ← char '.'
  fd  ← some digit
  pure (decimalLiteral neg int fd (+ 0))

-- Bare-int form: `"-?" digit+`, read as a `DecRat` with denominator 1.
-- No suffix-bound `.` check is performed here: the surrounding `<|>` in
-- `parseDecRat` commits to the frac form first when applicable, so this
-- branch only fires after the frac form has failed.
parseDecRatBareInt : Parser DecRat
parseDecRatBareInt = do
  neg ← optional (char '-')
  int ← parseDigits
  pure (decimalLiteral neg int [] (+ 0))

-- Parse a DBC decimal rational: try the frac form first, fall through to
-- the bare-int form.  The `<|>` backtracks to the original parser state
-- on left-branch failure (see `Aletheia.Parser.Combinators._<|>_`), so
-- partial consumption by the frac branch is harmless.
parseDecRat : Parser DecRat
parseDecRat = parseDecRatFrac <|> parseDecRatBareInt

-- ============================================================================
-- REFINED PARSERS — IntDecRat / NatDecRat
-- ============================================================================
--
-- Run `parseDecRat`, then check the result's structural shape against the
-- refinement predicate (`isIntegerᵇ` or `isNonNegIntegerᵇ`); on success
-- carry the witness through to the refined record, on failure abort the
-- parser via `fail`.  The runtime check happens once at the parser
-- boundary; downstream code carries the proof at the type level, per the
-- project-wide convention "all numbers are DecRat except on the frame
-- hot-path" with refinement types.
--
-- Wire grammar: cantools always emits integer/natural attribute bounds
-- without a fractional part (`BA_DEF_ "X" INT 0 100;`, not
-- `BA_DEF_ "X" INT 0.0 100.0;`).  The frac branch of `parseDecRat`
-- therefore fails on well-formed input and the bare-int branch fires;
-- the predicate check is a guarantee, not a coercion.  Malformed input
-- like `BA_DEF_ "X" INT 0.5 100;` is rejected by the predicate check.

parseIntDecRat : Parser IntDecRat
parseIntDecRat = parseDecRat >>= λ d →
  ifᵀ isIntegerᵇ d
    then (λ wf → pure (mkIntDecRat d wf))
    else fail

parseNatDecRat : Parser NatDecRat
parseNatDecRat = parseDecRat >>= λ d →
  ifᵀ isNonNegIntegerᵇ d
    then (λ wf → pure (mkNatDecRat d wf))
    else fail
