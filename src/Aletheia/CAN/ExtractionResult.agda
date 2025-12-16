{-# OPTIONS --safe --without-K #-}

-- Result type for signal extraction operations.
--
-- Purpose: Represent success/failure of signal extraction with error messages.
-- Types: ExtractionResult A = Success A | NotFound String | InvalidFrame String.
-- Role: Error handling for CAN.Encoding operations.
--
-- Design: Simple sum type for explicit error propagation (no exceptions in Agda).
module Aletheia.CAN.ExtractionResult where

open import Data.String using (String) renaming (_++_ to _++ₛ_)
open import Data.Rational using (ℚ)
open import Data.Rational.Show using (show)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)

-- ============================================================================
-- EXTRACTION RESULT TYPE
-- ============================================================================

-- Result of signal extraction with detailed error information
-- Replaces Maybe ℚ to distinguish different failure modes
data ExtractionResult : Set where
  -- Success: Signal extracted and scaled
  Success : ℚ → ExtractionResult

  -- Signal not found in DBC
  SignalNotInDBC : (signalName : String) → ExtractionResult

  -- Signal exists but is multiplexed out (not present in this frame)
  SignalNotPresent : (signalName : String) → (reason : String) → ExtractionResult

  -- Signal extracted but value out of bounds
  ValueOutOfBounds : (signalName : String) → (value : ℚ) → (minimum : ℚ) → (maximum : ℚ) → ExtractionResult

  -- Bit extraction or scaling failed
  ExtractionFailed : (signalName : String) → (reason : String) → ExtractionResult

-- ============================================================================
-- HELPER FUNCTIONS
-- ============================================================================

-- Check if extraction succeeded
isSuccess : ExtractionResult → Bool
isSuccess (Success _) = true
isSuccess _ = false

-- Get value from successful extraction (returns Nothing on failure)
getValue : ExtractionResult → Maybe ℚ
getValue (Success v) = just v
getValue _ = nothing

-- Format extraction result as error message
formatError : ExtractionResult → String
formatError (Success v) = "Success: " ++ₛ show v
formatError (SignalNotInDBC sigName) =
  "Signal '" ++ₛ sigName ++ₛ "' not found in DBC file"
formatError (SignalNotPresent sigName reason) =
  "Signal '" ++ₛ sigName ++ₛ "' not present in frame (" ++ₛ reason ++ₛ ")"
formatError (ValueOutOfBounds sigName value min max) =
  "Signal '" ++ₛ sigName ++ₛ "' value out of bounds: " ++ₛ
  show value ++ₛ " not in [" ++ₛ show min ++ₛ ", " ++ₛ show max ++ₛ "]"
formatError (ExtractionFailed sigName reason) =
  "Failed to extract signal '" ++ₛ sigName ++ₛ "': " ++ₛ reason
