{-# OPTIONS --safe --without-K #-}

module Aletheia.LTL.DSL.Python where

open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Data.Rational using (ℚ)

-- ============================================================================
-- PYTHON DSL AST (Phase 2A)
-- ============================================================================

-- Comparison operators for signal predicates
data ComparisonOp : Set where
  LT GT LE GE EQ NE : ComparisonOp

-- Python expressions (predicates over signals)
data PythonExpr : Set where
  -- Basic signal reference
  Signal : String → PythonExpr

  -- Constant value
  Constant : ℚ → PythonExpr

  -- Generic comparison: signal op value
  Compare : PythonExpr → ComparisonOp → PythonExpr → PythonExpr

  -- Range comparison: min ≤ signal ≤ max
  -- Python: Signal("Speed").between(0, 8000)
  -- Maps to: SignalPredicate.Between "Speed" (0 / 1) (8000 / 1)
  Between : String → ℚ → ℚ → PythonExpr

  -- Temporal change detection: |signal_now - signal_prev| ≥ delta
  -- Python: Signal("Speed").changed_by(10)
  -- Maps to: SignalPredicate.ChangedBy "Speed" (10 / 1)
  ChangedBy : String → ℚ → PythonExpr

-- Python LTL formulas (temporal operators over predicates)
data PythonLTL : Set where
  -- Atomic predicate (base case)
  Expr : PythonExpr → PythonLTL

  -- Logical operators
  Not : PythonLTL → PythonLTL
  And : PythonLTL → PythonLTL → PythonLTL
  Or : PythonLTL → PythonLTL → PythonLTL

  -- Temporal operators (unbounded)
  Always : PythonLTL → PythonLTL       -- □φ (always holds)
  Eventually : PythonLTL → PythonLTL   -- ◇φ (eventually holds)
  Never : PythonLTL → PythonLTL        -- □¬φ (never holds, syntactic sugar)

  -- Temporal operators (bounded)
  EventuallyWithin : ℕ → PythonLTL → PythonLTL  -- ◇≤n φ (within n steps)
  AlwaysWithin : ℕ → PythonLTL → PythonLTL      -- □≤n φ (for next n steps)

  -- Binary temporal operators
  Implies : PythonLTL → PythonLTL → PythonLTL   -- φ → ψ (logical implication)
  Until : PythonLTL → PythonLTL → PythonLTL     -- φ U ψ (φ until ψ)
