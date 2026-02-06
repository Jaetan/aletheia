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

open import Aletheia.CAN.Frame
open import Data.Nat using (ℕ)
open import Data.Rational using (ℚ)
open import Data.Bool using (Bool)
open import Data.Maybe using (Maybe)

SignalValue : Set
SignalValue = ℚ

record SignalDef : Set where
  field
    startBit : BitPosition
    bitLength : ℕ
    isSigned : Bool
    factor : ℚ
    offset : ℚ
    minimum : ℚ
    maximum : ℚ
