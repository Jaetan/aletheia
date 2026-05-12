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
--
-- Timestamps are `Timestamp μs` (microseconds since trace start), refined via
-- an erased unit phantom in `Aletheia.Trace.Time`. The unit is fixed at μs
-- because every binding (C++ `std::chrono::microseconds`, Go
-- `Timestamp{Microseconds int64}`, Python docstrings, the binary protocol)
-- uses microseconds consistently. The type-level unit prevents accidental
-- mixing with raw ℕ counts or other-unit durations inside the Agda core.
module Aletheia.Trace.CANTrace where

open import Aletheia.CAN.Frame using (CANFrame; CANId)
open import Aletheia.CAN.DLC using (dlcBytes)
open import Aletheia.Trace.Time public
  using (TimeUnit; ns; μs; ms; s; Timestamp; mkTs; tsValue; _≤ᵗ_)
open import Data.Bool using (Bool)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- A CAN data frame with timestamp and optional CAN-FD metadata.
--
-- brs/esi convention (ISO 11898-1:2015 §10.4.2 / §10.4.3, R19P2 cluster 18
-- — AGDA-D-10.1 closure): bindings populate `Just b` for CAN-FD frames
-- carrying a Bit Rate Switch / Error State Indicator bit, and `Nothing`
-- for CAN 2.0B frames where the bits do not exist on the wire.  The Agda
-- kernel does not consume these fields — they are pass-through metadata
-- surfaced to binding consumers via the FFI response and JSON wire shape.
-- Phase 5.1 scope keeps LTL atomic predicates signal-level only; bus-bit
-- predicates (BRS-set / ESI-set as truth values) would require lifting
-- the Maybe Bool to the predicate vocabulary and are deferred to Phase 6.
record TimedFrame : Set where
  field
    timestamp   : Timestamp μs  -- Microseconds since trace start
    payloadSize : ℕ
    frame       : CANFrame payloadSize
    .dlcValid   : payloadSize ≡ dlcBytes (CANFrame.dlc frame)
    brs         : Maybe Bool -- Bit Rate Switch (CAN-FD only)
    esi         : Maybe Bool -- Error State Indicator (CAN-FD only)

open TimedFrame public

-- A CAN bus event: data frame, error frame, or remote frame.
--
-- Error frames carry no ID or payload — they signal a bus error detected
-- by a node's CAN controller. Aletheia intentionally does NOT model the
-- CAN error code (form / stuff / CRC / ack / bit) because its scope is
-- signal-level LTL checking on the decoded payload, not bus-health
-- monitoring: once a frame is rejected at the CAN controller layer it is
-- not delivered to the signal-extraction pipeline, and the bus-level
-- diagnostic is the concern of a separate tool (candump, CANalyzer, etc.).
-- An error event is thus a pass-through "gap" in the data stream whose only
-- relevance to LTL is the timestamp (so metric operators can observe the
-- passage of time without a data frame).
--
-- Remote frames carry an ID but no payload — they request transmission
-- of the data frame with the matching ID (CAN 2.0B only; deprecated in
-- CAN-FD). The DLC field on the wire is purely an RTR hint and carries
-- zero data bytes; it is intentionally not modelled here because there is
-- no payload to extract signals from, and the DLC of the eventual *data*
-- reply is governed by the DBC definition of the responding message — not
-- by the request frame. A remote frame is therefore a pass-through event
-- whose only LTL-relevant field is the CAN ID (for ID-scoped predicates)
-- and the timestamp.
-- Deliberately omitted CAN 2.0B / ISO 11898-1 events:
--
-- (a) Overload frames (CAN 2.0B §3.1.5) — bus-level inter-frame fillers
--     emitted by stations that need extra time before the next data frame.
--     Carry no signal payload; the only observable is timing pressure on
--     subsequent frames, which is already captured by the timestamp delta
--     between adjacent `Data` events.  Since Aletheia's LTL atomic
--     predicates are signal-level (not bit-level / frame-format-level),
--     overload frames have no observable to predicate against.
--
-- (b) Single-shot transmission failure events (ISO 11898-1 §6.6, "tx
--     attempts exhausted" reported by the local controller) — driver-side
--     condition with no on-bus emission; for trace replay they would
--     appear as a *gap* (the frame was never broadcast), not a distinct
--     event type.  Aletheia's trace model is the on-bus byte stream, so
--     the gap is the natural representation: the `Data` frame for that
--     ID simply does not appear at the expected timestamp, and any
--     freshness / liveness predicate over it will report the violation.
--
-- This is the Phase 5.1 "minimal trace, signal-level LTL" scope; the
-- ADT can be extended later if the LTL atomic-predicate vocabulary is
-- broadened to bit-level / frame-format-level checks (see PROJECT_STATUS.md
-- Phase 6 candidate-goal list — none currently planned).  R19 Phase 2
-- cluster 5 — AGDA-D-10.3 audit closure.
data TraceEvent : Set where
  Data   : TimedFrame → TraceEvent
  Error  : Timestamp μs → TraceEvent
  Remote : Timestamp μs → CANId → TraceEvent

-- Extract timestamp from any trace event.
eventTimestamp : TraceEvent → Timestamp μs
eventTimestamp (Data tf) = timestamp tf
eventTimestamp (Error ts) = ts
eventTimestamp (Remote ts _) = ts

-- Raw-ℕ timestamp accessor for metric LTL arithmetic.
-- Equal to `tsValue (timestamp tf)` — kept as a separate name so that
-- metric operators in Coalgebra / Semantics / Adequacy can grep-match on
-- `timestampℕ curr` when they need the raw microsecond count while the
-- refined `timestamp : TimedFrame → Timestamp μs` field is reserved for
-- code paths that care about the unit.
timestampℕ : TimedFrame → ℕ
timestampℕ tf = tsValue (timestamp tf)

-- Monotonic data-frame traces: timestamps are non-decreasing.
-- Metric LTL operators (MetricEventually, MetricAlways) use truncated subtraction
-- (_∸_) on timestamps. Non-monotonic timestamps produce silently wrong verdicts.
-- Bindings enforce this at runtime; this predicate enables formal reasoning.
Monotonic : List TimedFrame → Set
Monotonic [] = ⊤
Monotonic (_ ∷ []) = ⊤
Monotonic (f₁ ∷ f₂ ∷ rest) = timestamp f₁ ≤ᵗ timestamp f₂ × Monotonic (f₂ ∷ rest)
