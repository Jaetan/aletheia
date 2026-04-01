{-# OPTIONS --safe --without-K #-}

-- LTL property result types for the streaming protocol.
--
-- Purpose: Define PropertyResult and CounterexampleData for LTL checking.
-- Types: CounterexampleData (violation evidence), PropertyResult (Violation/Satisfaction/StreamComplete).
-- Role: Used by Protocol.StreamState, Protocol.Message, and Protocol.ResponseFormat.
module Aletheia.Protocol.Response where

open import Data.String using (String)
open import Data.Nat using (ℕ)

-- Counterexample data for LTL violations
record CounterexampleData : Set where
  constructor mkCounterexampleData
  field
    timestamp : ℕ       -- Timestamp (microseconds) of violating frame
    reason : String     -- Human-readable reason

-- Property checking result for streaming protocol
-- Emitted when a property is decided (early termination or at EndStream)
data PropertyResult : Set where
  -- Property violated (failed early or at EndStream)
  Violation    : ℕ → CounterexampleData → PropertyResult
  -- Property satisfied (succeeded early or at EndStream)
  Satisfaction : ℕ → PropertyResult
  -- Stream complete marker (all properties decided)
  StreamComplete : PropertyResult
