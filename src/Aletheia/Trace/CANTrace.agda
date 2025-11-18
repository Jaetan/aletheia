{-# OPTIONS --safe --without-K --guardedness #-}

module Aletheia.Trace.CANTrace where

open import Aletheia.Trace.Stream
open import Aletheia.CAN.Frame
open import Data.Nat using (ℕ)

record TimedFrame : Set where
  field
    timestamp : ℕ
    frame : CANFrame

CANTrace : Set
CANTrace = Trace TimedFrame
