-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Decimal-string → rational entry point for the FFI.
--
-- The kernel is the single source of truth for what a valid decimal is:
-- every binding (Python / Go / C++ / Rust) routes decimal input through
-- `aletheia_parse_decimal`, the Haskell shim's wrapper around `parseDecimal`,
-- so neither the grammar nor the bound can drift between languages.
--
-- The float principle: a decimal is an *exact* rational (a `DecRat`,
-- denominator 2^a·5^b), never a float64.  A `float` only ever appears when a
-- value is finally printed for a human.  This module is the input half of
-- that contract.
--
-- Grammar (delegated wholesale to `parseDecRat`):
--     -?digits          (bare integer)
--     -?digits.digits+  (mandatory fraction)
-- No leading '+', no bare '.5', no scientific notation.  See
-- `Aletheia.DBC.TextParser.DecRatParse`.
--
-- The whole text must parse (`consumed`): "3.14xyz" is refused as trailing
-- input rather than read as 3.14.  The value is then held to the one bound
-- every number in a command or a DBC is held to, `SmallDecRat`: a reduced
-- component past `max-rational-component-magnitude` is refused with the
-- bound error naming the field `decimal`.  The shim only reads the verdict:
-- an error is rendered as every kernel refusal is, and a `WireRational`'s
-- two components fit the wire's signed 64-bit slots by its erased proof.
module Aletheia.DBC.TextParser.DecimalEntry where

open import Data.Char using (Char)
open import Data.Integer using (ℤ; ∣_∣)
open import Data.List using (List)
open import Data.Nat using (ℕ; _*_; _^_)
open import Data.Product using (_×_; uncurry)
open import Data.String using (String; toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Aletheia.Parser.Combinators using (ParseResult; value; runParserPartial)
open import Aletheia.DBC.TextParser.DecRatParse using (parseDecRat)
open import Aletheia.DBC.TextParser.Consumed using (consumed)
open import Aletheia.DBC.DecRat using (DecRat)
open import Aletheia.DBC.DecRat.Magnitude using (SmallNat; SmallDecRat; smallDecRat-components)
open import Aletheia.DBC.Bounds using (Checked; [_]; magnitude)
open import Aletheia.Error using (Error; DBCTextParseError; DBCTextParseErr)

-- The rational as the wire carries it: lowest terms over a positive
-- denominator (the `DecRat` canonical invariant), each component at most
-- `max-rational-component-magnitude`.
record WireRational : Set where
  constructor mkWireRational
  field
    numerator   : ℤ
    denominator : ℕ
    @0 small    : SmallNat ∣ numerator ∣ × SmallNat denominator

wireOf : (d : DecRat) → @0 SmallDecRat d → WireRational
wireOf d small =
  mkWireRational (DecRat.numerator d) (2 ^ DecRat.twoExp d * 5 ^ DecRat.fiveExp d)
                 (smallDecRat-components d small)

-- The bound's verdict on a parsed decimal.
fromChecked : (d : DecRat) → Checked (SmallDecRat d) → Error ⊎ WireRational
fromChecked _ (inj₁ e)         = inj₁ e
fromChecked d (inj₂ [ small ]) = inj₂ (wireOf d small)

decide : DBCTextParseError ⊎ ParseResult DecRat → Error ⊎ WireRational
decide (inj₁ e)   = inj₁ (DBCTextParseErr e)
decide (inj₂ res) = fromChecked (value res) (magnitude "decimal" (value res))

parseDecimal-chars : List Char → Error ⊎ WireRational
parseDecimal-chars cs = decide (uncurry consumed (runParserPartial parseDecRat cs))

-- FFI entry: the exact rational a decimal string denotes, or the refusal.
parseDecimal : String → Error ⊎ WireRational
parseDecimal s = parseDecimal-chars (toList s)
