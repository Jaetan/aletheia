{-# OPTIONS --safe --without-K #-}

module Aletheia.LTL.DSL.Yaml where

open import Data.String using (String)
open import Data.Nat using (ℕ)
open import Data.Rational using (ℚ)

-- ============================================================================
-- SCHEMA-SPECIFIC YAML REPRESENTATION
-- ============================================================================

-- YAML representation matching our LTL property schema exactly
-- This has bounded recursion matching the structure of our DSL

-- Comparison operators (as strings in YAML)
data CompOpYaml : Set where
  LT-yaml GT-yaml LE-yaml GE-yaml EQ-yaml NE-yaml : CompOpYaml

-- Expression-level YAML fields (no recursion - these are leaves)
data ExprYaml : Set where
  -- compare: {signal, op, value}
  CompareYaml : String → CompOpYaml → ℚ → ExprYaml

  -- between: {signal, min, max}
  BetweenYaml : String → ℚ → ℚ → ExprYaml

  -- changed_by: {signal, delta}
  ChangedByYaml : String → ℚ → ExprYaml

  -- signal: {name}
  SignalYaml : String → ExprYaml

  -- constant: {value}
  ConstantYaml : ℚ → ExprYaml

-- Property-level YAML (can contain expressions or nested properties)
data PropertyYaml : Set where
  -- Atomic expression (base case)
  ExprProperty : ExprYaml → PropertyYaml

  -- Simple temporal operators (contain expressions)
  AlwaysYaml : ExprYaml → PropertyYaml
  EventuallyYaml : ExprYaml → PropertyYaml
  NeverYaml : ExprYaml → PropertyYaml

  -- Bounded temporal operators (contain expressions)
  EventuallyWithinYaml : ℕ → ExprYaml → PropertyYaml
  AlwaysWithinYaml : ℕ → ExprYaml → PropertyYaml

  -- Compound operators (recursive - contain sub-properties)
  NotYaml : PropertyYaml → PropertyYaml
  AndYaml : PropertyYaml → PropertyYaml → PropertyYaml
  OrYaml : PropertyYaml → PropertyYaml → PropertyYaml
  ImpliesYaml : PropertyYaml → PropertyYaml → PropertyYaml
  UntilYaml : PropertyYaml → PropertyYaml → PropertyYaml

-- Note: This representation is structurally recursive with clear termination:
-- - ExprYaml has no recursion (base case)
-- - PropertyYaml can contain ExprYaml (smaller) or PropertyYaml (same size, but bounded by input)
-- - Recursion is direct and obvious to Agda's termination checker

-- ============================================================================
-- DEPTH BOUNDS (for fuel verification)
-- ============================================================================

open import Data.Nat using (zero; suc; _⊔_)

-- Compute nesting depth of a property
depth : PropertyYaml → ℕ
depth (ExprProperty _) = zero
depth (AlwaysYaml _) = suc zero
depth (EventuallyYaml _) = suc zero
depth (NeverYaml _) = suc zero
depth (EventuallyWithinYaml _ _) = suc zero
depth (AlwaysWithinYaml _ _) = suc zero
depth (NotYaml sub) = suc (depth sub)
depth (AndYaml left right) = suc (depth left ⊔ depth right)
depth (OrYaml left right) = suc (depth left ⊔ depth right)
depth (ImpliesYaml ante cons) = suc (depth ante ⊔ depth cons)
depth (UntilYaml left right) = suc (depth left ⊔ depth right)

-- Note: While PropertyYaml allows arbitrary nesting in principle,
-- realistic properties have bounded depth. Our 10 example properties
-- have maximum depth 4. Parser uses fuel = 100 for safety margin.
