{-# OPTIONS --safe --without-K #-}

-- CAN trace types for temporal logic.
--
-- Purpose: Define timed CAN frame structure for LTL model checking.
-- Types: TimedFrame (CAN frame with timestamp).
-- Role: Used by LTL.Coalgebra and LTL.Semantics for property checking.
module Aletheia.Trace.CANTrace where

open import Aletheia.CAN.Frame using (CANFrame)
open import Aletheia.CAN.DLC using (dlcToBytes)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- Timestamp in microseconds (µs)
-- Standard unit for CAN bus timing: 1 second = 1,000,000 µs
Timestamp : Set
Timestamp = ℕ

record TimedFrame : Set where
  field
    timestamp   : Timestamp  -- Time in microseconds since trace start
    payloadSize : ℕ
    frame       : CANFrame payloadSize
    .dlcValid   : payloadSize ≡ dlcToBytes (CANFrame.dlc frame)

open TimedFrame public
