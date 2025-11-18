{-# OPTIONS --safe --without-K #-}

module Aletheia.LTL.Checker where

open import Aletheia.LTL.Syntax
open import Aletheia.LTL.Semantics
open import Aletheia.Trace.Stream
open import Aletheia.Trace.CANTrace
open import Aletheia.LTL.SignalPredicate
open import Aletheia.CAN.Frame
open import Aletheia.DBC.Types
open import Data.Bool using (Bool; true; false)
open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Rational using (ℚ)

-- ============================================================================
-- MODEL CHECKER
-- ============================================================================

-- For Phase 2A, the model checker is straightforward: it evaluates the
-- LTL formula against the trace using the bounded semantics.
--
-- Phase 2B will extend this with:
-- - Counterexample generation (witness of violation)
-- - Minimal counterexample (shrinking)
-- - Structured result type (Success | Violation with counterexample)

-- Helper: Convert Maybe Bool to Bool (Nothing → false)
fromMaybeBool : Maybe Bool → Bool
fromMaybeBool (just b) = b
fromMaybeBool nothing = false

-- Helper: Map atoms in LTL formula
mapAtoms : ∀ {A B : Set} → (A → B) → LTL A → LTL B
mapAtoms f (Atomic a) = Atomic (f a)
mapAtoms f (Not φ) = Not (mapAtoms f φ)
mapAtoms f (And φ ψ) = And (mapAtoms f φ) (mapAtoms f ψ)
mapAtoms f (Or φ ψ) = Or (mapAtoms f φ) (mapAtoms f ψ)
mapAtoms f (Next φ) = Next (mapAtoms f φ)
mapAtoms f (Always φ) = Always (mapAtoms f φ)
mapAtoms f (Eventually φ) = Eventually (mapAtoms f φ)
mapAtoms f (Until φ ψ) = Until (mapAtoms f φ) (mapAtoms f ψ)
mapAtoms f (EventuallyWithin n φ) = EventuallyWithin n (mapAtoms f φ)
mapAtoms f (AlwaysWithin n φ) = AlwaysWithin n (mapAtoms f φ)

-- Check a CAN trace against an LTL formula over signal predicates
-- Returns true if the trace satisfies the formula
checkTrace : DBC → List TimedFrame → LTL SignalPredicate → Bool
checkTrace dbc frames formula = satisfiesAt frames ltlFormula
  where
    -- Convert SignalPredicate atoms to (TimedFrame → Bool) predicates
    evalAtom : SignalPredicate → (TimedFrame → Bool)
    evalAtom pred timedFrame =
      fromMaybeBool (evalPredicate pred dbc (TimedFrame.frame timedFrame))

    -- Map LTL formula from SignalPredicate atoms to Bool-valued predicates
    ltlFormula : LTL (TimedFrame → Bool)
    ltlFormula = mapAtoms evalAtom formula

-- Simple result type (Phase 2A)
data CheckResult : Set where
  Satisfied : CheckResult
  Violated : CheckResult

boolToResult : Bool → CheckResult
boolToResult true = Satisfied
boolToResult false = Violated

-- User-facing checker with result type
check : DBC → List TimedFrame → LTL SignalPredicate → CheckResult
check dbc frames formula = boolToResult (checkTrace dbc frames formula)
