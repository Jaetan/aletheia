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

-- ============================================================================
-- INFINITE EXTENSION EVALUATION
-- ============================================================================

-- Evaluate formula on infinite extension of a single frame (frame repeats forever).
--
-- Semantics: When a frame repeats infinitely (f, f, f, ...), temporal operators
-- reduce to their inner formulas:
--   - Next φ: "next frame satisfies φ" → "f satisfies φ" (next is f)
--   - Always φ: "all frames satisfy φ" → "f satisfies φ" (all frames are f)
--   - Eventually φ: "some frame satisfies φ" → "f satisfies φ" (only frame is f)
--   - Until φ ψ: "φ until ψ" → "ψ holds" (ψ must hold immediately or never)
--
-- This function recursively strips temporal operators, evaluating at the repeating frame.
-- Used for infinite extension semantics in coinductive LTL evaluation.
evalAtInfiniteExtension : ∀ {A : Set} → A → LTL (A → Bool) → Bool
evalAtInfiniteExtension frame (Atomic pred) = pred frame
evalAtInfiniteExtension frame (Not φ) = not (evalAtInfiniteExtension frame φ)
evalAtInfiniteExtension frame (And φ ψ) =
  evalAtInfiniteExtension frame φ ∧ evalAtInfiniteExtension frame ψ
evalAtInfiniteExtension frame (Or φ ψ) =
  evalAtInfiniteExtension frame φ ∨ evalAtInfiniteExtension frame ψ

-- Temporal operators: strip and recurse on inner formula
-- Rationale: On infinite extension, all temporal operators reduce to their innermost formula
evalAtInfiniteExtension frame (Next φ) = evalAtInfiniteExtension frame φ
evalAtInfiniteExtension frame (Always φ) = evalAtInfiniteExtension frame φ
evalAtInfiniteExtension frame (Eventually φ) = evalAtInfiniteExtension frame φ

-- Until: "φ Until ψ" on infinite extension means ψ must hold (or never will)
-- Since all future frames are the same, ψ either holds now or never
evalAtInfiniteExtension frame (Until φ ψ) = evalAtInfiniteExtension frame ψ

-- Time-bounded operators: strip time bounds on infinite extension
-- Rationale: On infinite extension of a single frame, time progression is meaningless
-- The frame either satisfies the inner formula or doesn't
evalAtInfiniteExtension frame (EventuallyWithin _ φ) = evalAtInfiniteExtension frame φ
evalAtInfiniteExtension frame (AlwaysWithin _ φ) = evalAtInfiniteExtension frame φ
