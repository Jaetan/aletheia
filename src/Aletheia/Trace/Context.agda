{-# OPTIONS --safe --without-K --guardedness #-}

-- Trace context with signal extraction and DBC lookup.
--
-- Purpose: Combine CAN frames with DBC context for signal evaluation.
-- Types: TimedFrame (Frame + timestamp), Context (DBC + current frame).
-- Operations: extractSignalValue (context + signal name → physical value).
-- Role: Bridge between raw frames and LTL signal predicates.
--
-- Design: Provides unified interface for signal access during LTL checking.
module Aletheia.Trace.Context where

open import Aletheia.CAN.Frame
open import Aletheia.DBC.Types
open import Aletheia.Trace.CANTrace using (TimedFrame) public
open import Data.Nat using (ℕ)
open import Data.List using (List; length)

-- Re-export TimedFrame record accessors
open TimedFrame public

-- ============================================================================
-- TRACE CONTEXT
-- ============================================================================

-- Bundles DBC file with trace data
-- Makes APIs cleaner and easier to extend with metadata
record TraceContext : Set where
  constructor mkTraceContext
  field
    dbc : DBC
    frames : List TimedFrame

open TraceContext public

-- Helper: Get DBC from context
getDBC : TraceContext → DBC
getDBC = dbc

-- Helper: Get frames from context
getFrames : TraceContext → List TimedFrame
getFrames = frames

-- Helper: Get frame count
frameCount : TraceContext → ℕ
frameCount ctx = length (frames ctx)
