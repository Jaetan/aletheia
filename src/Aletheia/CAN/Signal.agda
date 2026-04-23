{-# OPTIONS --safe --without-K #-}

-- CAN signal definitions with physical scaling and metadata.
--
-- Purpose: Define signal structure matching DBC specifications.
-- Fields: name, bit position/length, byte order, signed/unsigned, scaling (factor/offset),
--         min/max bounds, unit, presence (always/conditional).
-- Role: Used by DBC.Types to represent signal definitions, by Encoding for extraction/injection.
--
-- Design: Captures both raw bit-level layout and physical value transformations.
module Aletheia.CAN.Signal where

open import Aletheia.CAN.Frame using (BitPosition)
open import Aletheia.DBC.DecRat using (DecRat)
open import Data.Nat using (ℕ)
open import Data.Rational using (ℚ)
open import Data.Bool using (Bool)

-- Post-extraction physical value stays ℚ: the arithmetic (applyScaling /
-- removeScaling / inBounds) operates in ℚ, and DecRat is only the on-disk
-- decimal-roundtrip storage form for factor / offset / minimum / maximum.
SignalValue : Set
SignalValue = ℚ

record SignalDef : Set where
  field
    startBit : BitPosition
    bitLength : ℕ
    isSigned : Bool
    factor : DecRat
    offset : DecRat
    minimum : DecRat
    maximum : DecRat
