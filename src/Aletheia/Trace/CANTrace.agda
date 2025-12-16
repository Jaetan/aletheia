{-# OPTIONS --safe --without-K #-}

-- CAN trace types for temporal logic.
--
-- Purpose: Define timed CAN frame structure for LTL model checking.
-- Types: TimedFrame (CAN frame with timestamp).
-- Role: Used by LTL.Incremental and LTL.Coinductive for property checking.
module Aletheia.Trace.CANTrace where

open import Aletheia.CAN.Frame
open import Data.Nat using (ℕ)

-- Timestamp in microseconds (µs)
-- Standard unit for CAN bus timing: 1 second = 1,000,000 µs
Timestamp : Set
Timestamp = ℕ

record TimedFrame : Set where
  field
    timestamp : Timestamp  -- Time in microseconds since trace start
    frame : CANFrame
