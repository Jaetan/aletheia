{-# OPTIONS --safe --without-K #-}

-- LTL formula evaluation utilities.
--
-- Purpose: Provide shared evaluation logic for LTL formulas at single frames.
-- Operations: evalAtFrame (evaluate non-temporal operators at a frame).
-- Role: Shared evaluation logic for LTL.Incremental and LTL.Coinductive.
--
-- Design: Polymorphic over frame type, parameterized by temporal operator default.
module Aletheia.LTL.Evaluation where

open import Aletheia.LTL.Syntax
open import Data.Bool using (Bool; not; _∧_; _∨_)

-- ============================================================================
-- SINGLE-FRAME EVALUATION
-- ============================================================================

-- Evaluate formula at a single frame (handles non-temporal operators)
-- For temporal operators (Next, Always, Eventually, Until, *Within), returns the provided default.
--
-- Parameters:
--   temporalDefault : Default value for temporal operators
--                     - Use 'false' when temporal operators cannot be evaluated on single frame
--                     - Use 'true' when temporal operators are handled by external state machine
--
-- Handles: Atomic, Not, And, Or (structurally recursive)
-- Defers: Next, Always, Eventually, Until, EventuallyWithin, AlwaysWithin
evalAtFrame : ∀ {A : Set} → Bool → A → LTL (A → Bool) → Bool
evalAtFrame temporalDefault frame (Atomic pred) = pred frame
evalAtFrame temporalDefault frame (Not φ) = not (evalAtFrame temporalDefault frame φ)
evalAtFrame temporalDefault frame (And φ ψ) =
  evalAtFrame temporalDefault frame φ ∧ evalAtFrame temporalDefault frame ψ
evalAtFrame temporalDefault frame (Or φ ψ) =
  evalAtFrame temporalDefault frame φ ∨ evalAtFrame temporalDefault frame ψ
evalAtFrame temporalDefault _ (Next _) = temporalDefault
evalAtFrame temporalDefault _ (Always _) = temporalDefault
evalAtFrame temporalDefault _ (Eventually _) = temporalDefault
evalAtFrame temporalDefault _ (Until _ _) = temporalDefault
evalAtFrame temporalDefault _ (EventuallyWithin _ _) = temporalDefault
evalAtFrame temporalDefault _ (AlwaysWithin _ _) = temporalDefault
