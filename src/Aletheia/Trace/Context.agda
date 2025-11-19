{-# OPTIONS --safe --without-K --guardedness #-}

module Aletheia.Trace.Context where

open import Aletheia.CAN.Frame
open import Aletheia.DBC.Types
open import Aletheia.Trace.CANTrace using (TimedFrame) public
open import Data.Nat using (ℕ)
open import Data.List using (List)

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
  where open import Data.List using (length)
