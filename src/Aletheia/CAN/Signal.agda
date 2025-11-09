{-# OPTIONS --safe --without-K #-}

module Aletheia.CAN.Signal where

open import Aletheia.CAN.Frame
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Rational using (ℚ)
open import Data.Bool using (Bool)
open import Data.Maybe using (Maybe)

SignalValue : Set
SignalValue = ℚ

record SignalDef : Set where
  field
    startBit : BitPosition
    bitLength : Fin 65
    isSigned : Bool
    factor : ℚ
    offset : ℚ
    minimum : ℚ
    maximum : ℚ
