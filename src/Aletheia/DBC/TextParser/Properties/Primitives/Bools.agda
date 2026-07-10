-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Tier A single-char keyword roundtrips.
--
-- Extracted from Properties/Primitives.agda; companion to
-- `Properties/Primitives/MuxMarker.agda`.  Both functions
-- are pure single-char dispatchers — `parseByteOrderDigit` for `'0'` /
-- `'1'` and `parseSignFlag` for `'+'` / `'-'` — and reduce
-- definitionally on closed chars, hence the four-line `refl` proofs.
module Aletheia.DBC.TextParser.Properties.Primitives.Bools where

open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char)
open import Data.List using (List) renaming (_++_ to _++ₗ_)
open import Data.Maybe using (just)
open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Aletheia.Parser.Combinators using
  (Position; mkResult; advancePositions)
open import Aletheia.DBC.TextParser.Topology.Foundations using
  (parseByteOrderDigit; parseSignFlag)
open import Aletheia.DBC.TextFormatter.Topology using
  (emitByteOrderDigit-chars; emitSignFlag-chars)
open import Aletheia.CAN.Endianness using
  (ByteOrder; LittleEndian; BigEndian)

-- ByteOrder digit — one-character match.  The emitter produces a single
-- concrete char (`'0'` or `'1'`); the parser's `(char '0' *> …) <|>
-- (char '1' *> …)` reduces definitionally on closed chars so both cases
-- are `refl`.  No suffix precondition: the parser consumes exactly one
-- char and leaves the tail untouched.
parseByteOrderDigit-roundtrip : ∀ (pos : Position) (bo : ByteOrder)
                                  (suffix : List Char)
  → proj₂ (parseByteOrderDigit pos (emitByteOrderDigit-chars bo ++ₗ suffix))
    ≡ just (mkResult bo (advancePositions pos
                           (emitByteOrderDigit-chars bo)) suffix)
parseByteOrderDigit-roundtrip _ LittleEndian _ = refl
parseByteOrderDigit-roundtrip _ BigEndian    _ = refl

-- Sign flag — DBC historical encoding: `'+'` = unsigned (false), `'-'` =
-- signed (true).  Same single-char dispatch pattern as ByteOrder;
-- definitional reduction on closed chars closes both cases.
parseSignFlag-roundtrip : ∀ (pos : Position) (b : Bool) (suffix : List Char)
  → proj₂ (parseSignFlag pos (emitSignFlag-chars b ++ₗ suffix))
    ≡ just (mkResult b (advancePositions pos (emitSignFlag-chars b))
                     suffix)
parseSignFlag-roundtrip _ true  _ = refl
parseSignFlag-roundtrip _ false _ = refl
