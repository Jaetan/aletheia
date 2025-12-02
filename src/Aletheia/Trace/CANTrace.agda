{-# OPTIONS --safe --without-K --guardedness #-}

-- CAN trace types and predicates for temporal logic.
--
-- Purpose: Define trace structure for LTL model checking.
-- Types: Trace (list/colist of TimedFrames), trace predicates.
-- Role: Used by LTL.Incremental and LTL.Coinductive for property checking.
--
-- Design: Supports both finite (List) and infinite (DelayedColist) traces.
module Aletheia.Trace.CANTrace where

open import Aletheia.Trace.Stream
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

CANTrace : Set
CANTrace = Trace TimedFrame
