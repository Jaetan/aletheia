-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Correctness of `parseDecimal-chars` as a weak inverse of the decimal
-- emitter.  `parseDecimal` is the FFI's decimal→rational entry point; this
-- module proves it recovers exactly what the kernel's own decimal output
-- functions emit:
--
--   parseDecimal-chars (showDecRat-dec-chars d) ≡ just d
--   parseDecimal-chars (showInt-chars z)        ≡ just (fromℤ z)
--
-- i.e. the parser is a left inverse of the emitter on the emitter's image
-- (the canonical "<sign><int>.<frac>" form) and of the bare-integer printer
-- (the common user-typed "42").  Both are immediate corollaries of the
-- already-proven suffix-aware roundtrips in
-- `…DecRatParse.Properties.Phase6Suffix`, specialised to full consumption
-- (`suffix ≡ []`): `++-identityʳ` drops the empty suffix to line the emitter
-- output up with `runParserPartial`, then `cong fromResult` routes the
-- `just (mkResult d _ [])` result through the full-consume clause.
--
-- The statement is at `List Char` level (plus a `map toℚ` corollary at the
-- ℚ layer the FFI returns).  A `String`-level statement would pull in the
-- `toList∘fromList` substrate axiom (`Substrate.Unsafe`) for no added
-- assurance: `Data.String.toList` is itself total and `--safe`; only a
-- theorem *about* the String roundtrip needs the axiom.
module Aletheia.DBC.TextParser.DecimalEntry.Properties where

open import Data.List using ([])
open import Data.List.Properties using (++-identityʳ)
open import Data.Maybe using (just; map)
open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; cong; sym; trans)

open import Aletheia.Parser.Combinators using (runParserPartial; initialPosition)
open import Aletheia.DBC.TextParser.DecRatParse using (parseDecRat)
open import Aletheia.DBC.TextParser.DecRatParse.Properties.Phase2Many using ([]-stop)
open import Aletheia.DBC.TextParser.DecRatParse.Properties.Phase6Suffix using
  (parseDecRat-roundtrip-suffix; parseDecRat-bareInt-roundtrip-suffix)
open import Aletheia.DBC.TextFormatter.Emitter using (showDecRat-dec-chars; showInt-chars)
open import Aletheia.DBC.DecRat using (toℚ; fromℤ)
open import Aletheia.DBC.TextParser.DecimalEntry using (fromResult; parseDecimal-chars)

-- The parser recovers every DecRat from its canonical decimal text.
parseDecimal-chars-roundtrip : ∀ d → parseDecimal-chars (showDecRat-dec-chars d) ≡ just d
parseDecimal-chars-roundtrip d =
  trans (cong (λ x → fromResult (proj₂ (runParserPartial parseDecRat x)))
              (sym (++-identityʳ (showDecRat-dec-chars d))))
        (cong fromResult
              (parseDecRat-roundtrip-suffix d initialPosition [] []-stop))

-- The ℚ layer the FFI actually returns: parse-of-emit yields toℚ d.
parseDecimal-chars-toℚ-roundtrip :
  ∀ d → map toℚ (parseDecimal-chars (showDecRat-dec-chars d)) ≡ just (toℚ d)
parseDecimal-chars-toℚ-roundtrip d = cong (map toℚ) (parseDecimal-chars-roundtrip d)

-- '.' ≢ '_' discharges the bare-int roundtrip's side condition at suffix ≡ []
-- (headOr [] '_' reduces to '_').
dot≢us : '.' ≢ '_'
dot≢us ()

-- The parser also recovers a bare integer from its plain printed form — the
-- common "42" a user types, which the DecRat emitter never produces ("42.0").
parseDecimal-chars-bareInt-roundtrip :
  ∀ z → parseDecimal-chars (showInt-chars z) ≡ just (fromℤ z)
parseDecimal-chars-bareInt-roundtrip z =
  trans (cong (λ x → fromResult (proj₂ (runParserPartial parseDecRat x)))
              (sym (++-identityʳ (showInt-chars z))))
        (cong fromResult
              (parseDecRat-bareInt-roundtrip-suffix z initialPosition [] []-stop dot≢us))
