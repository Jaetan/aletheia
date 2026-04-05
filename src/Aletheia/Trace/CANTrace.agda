{-# OPTIONS --safe --without-K #-}

-- CAN trace types for temporal logic.
--
-- Purpose: Define timed CAN frame structure for LTL model checking.
-- Types: TimedFrame (CAN data frame with timestamp and optional CAN-FD metadata),
--        TraceEvent (data / error / remote frame on the bus).
-- Role: Used by LTL.Coalgebra and LTL.Semantics for property checking.
--
-- Design: TraceEvent models all CAN bus event types. LTL evaluation operates
-- on TimedFrame (data frames only) — error and remote frames carry no payload
-- for signal extraction and are handled at the protocol layer.
module Aletheia.Trace.CANTrace where

open import Aletheia.CAN.Frame using (CANFrame; CANId)
open import Aletheia.CAN.DLC using (dlcToBytes)
open import Data.Bool using (Bool)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ; _≤_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- Timestamp in microseconds (µs)
-- Standard unit for CAN bus timing: 1 second = 1,000,000 µs
Timestamp : Set
Timestamp = ℕ

-- A CAN data frame with timestamp and optional CAN-FD metadata.
-- brs/esi are Nothing for CAN 2.0B frames, Just for CAN-FD frames.
record TimedFrame : Set where
  field
    timestamp   : Timestamp  -- Time in microseconds since trace start
    payloadSize : ℕ
    frame       : CANFrame payloadSize
    .dlcValid   : payloadSize ≡ dlcToBytes (CANFrame.dlc frame)
    brs         : Maybe Bool -- Bit Rate Switch (CAN-FD only)
    esi         : Maybe Bool -- Error State Indicator (CAN-FD only)

open TimedFrame public

-- A CAN bus event: data frame, error frame, or remote frame.
--
-- Error frames carry no ID or payload — they signal a bus error detected
-- by a node's CAN controller.
--
-- Remote frames carry an ID but no payload — they request transmission
-- of the data frame with the matching ID (CAN 2.0B only; deprecated in CAN-FD).
data TraceEvent : Set where
  Data   : TimedFrame → TraceEvent
  Error  : Timestamp → TraceEvent
  Remote : Timestamp → CANId → TraceEvent

-- Extract timestamp from any trace event.
eventTimestamp : TraceEvent → Timestamp
eventTimestamp (Data tf) = timestamp tf
eventTimestamp (Error ts) = ts
eventTimestamp (Remote ts _) = ts

-- Monotonic data-frame traces: timestamps are non-decreasing.
-- Metric LTL operators (MetricEventually, MetricAlways) use truncated subtraction
-- (_∸_) on timestamps. Non-monotonic timestamps produce silently wrong verdicts.
-- Bindings enforce this at runtime; this predicate enables formal reasoning.
Monotonic : List TimedFrame → Set
Monotonic [] = ⊤
Monotonic (_ ∷ []) = ⊤
Monotonic (f₁ ∷ f₂ ∷ rest) = timestamp f₁ ≤ timestamp f₂ × Monotonic (f₂ ∷ rest)
