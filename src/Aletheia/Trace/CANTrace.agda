{-# OPTIONS --safe --without-K #-}

-- CAN trace types for temporal logic.
--
-- Purpose: Define timed CAN frame structure for LTL model checking.
-- Types: TimedFrame (CAN frame with timestamp).
-- Role: Used by LTL.Coalgebra and LTL.Semantics for property checking.
module Aletheia.Trace.CANTrace where

open import Aletheia.CAN.Frame using (CANFrame)
open import Aletheia.CAN.DLC using (dlcToBytes)
open import Data.Nat using (ℕ; _≤_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_)
open import Data.Unit using (⊤)
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

-- Monotonic traces: timestamps are non-decreasing.
-- Metric LTL operators (MetricEventually, MetricAlways) use truncated subtraction
-- (_∸_) on timestamps. Non-monotonic timestamps produce silently wrong verdicts.
-- Bindings enforce this at runtime; this predicate enables formal reasoning.
Monotonic : List TimedFrame → Set
Monotonic [] = ⊤
Monotonic (_ ∷ []) = ⊤
Monotonic (f₁ ∷ f₂ ∷ rest) = timestamp f₁ ≤ timestamp f₂ × Monotonic (f₂ ∷ rest)
