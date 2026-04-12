{-# OPTIONS --safe --without-K #-}

-- Result type for signal extraction operations.
--
-- Purpose: Represent success/failure of signal extraction with error messages.
-- Types: ExtractionResult = Success | SignalNotInDBC | SignalNotPresent | ValueOutOfBounds | ExtractionFailed.
-- Role: Error handling for CAN.Encoding operations.
--
-- Design: Simple sum type for explicit error propagation (no exceptions in Agda).
module Aletheia.CAN.ExtractionResult where

open import Data.Rational using (ℚ)
open import Data.Maybe using (Maybe; just; nothing)
open import Aletheia.Error using (ExtractionError)

-- ============================================================================
-- EXTRACTION RESULT TYPE
-- ============================================================================

-- Result of signal extraction with detailed error information
-- Replaces Maybe ℚ to distinguish different failure modes
data ExtractionResult : Set where
  -- Success: Signal extracted and scaled
  Success : ℚ → ExtractionResult

  -- Signal not found in DBC
  SignalNotInDBC : ExtractionResult

  -- Signal exists but is multiplexed out (not present in this frame)
  SignalNotPresent : (reason : ExtractionError) → ExtractionResult

  -- Signal extracted but value out of bounds
  ValueOutOfBounds : (value : ℚ) → (minimum : ℚ) → (maximum : ℚ) → ExtractionResult

  -- Bit extraction or scaling failed (typed via ExtractionError to unify all errors).
  ExtractionFailed : (reason : ExtractionError) → ExtractionResult

-- ============================================================================
-- HELPER FUNCTIONS
-- ============================================================================

-- Get value from successful extraction (returns Nothing on failure)
getValue : ExtractionResult → Maybe ℚ
getValue (Success v) = just v
getValue _ = nothing

