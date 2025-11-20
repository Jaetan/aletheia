{-# OPTIONS --safe --without-K --guardedness #-}

module Aletheia.LTL.DSL.Translate where

open import Aletheia.LTL.Syntax
open import Aletheia.LTL.DSL.Yaml
open import Aletheia.LTL.SignalPredicate using (SignalPredicate; Equals; LessThan; GreaterThan; Between; ChangedBy)
open import Data.String using (String)
open import Data.Rational using (ℚ)
open import Data.Maybe using (Maybe; just; nothing)

-- ============================================================================
-- DIRECT TRANSLATION: PropertyYaml → LTL SignalPredicate
-- ============================================================================

-- Translation result type
-- Nothing = unsupported/invalid input
-- Just φ = successfully translated formula
TranslationResult : Set
TranslationResult = Maybe (LTL SignalPredicate)

-- ============================================================================
-- EXPRESSION TRANSLATION (ExprYaml → SignalPredicate)
-- ============================================================================

-- Translate comparison operator and build appropriate predicate
-- LE and GE need to be wrapped with Not at the LTL level
translateExpr : ExprYaml → TranslationResult

-- Compare with direct mappings
translateExpr (CompareYaml sig EQ-yaml val) =
  just (Atomic (Equals sig val))

translateExpr (CompareYaml sig LT-yaml val) =
  just (Atomic (LessThan sig val))

translateExpr (CompareYaml sig GT-yaml val) =
  just (Atomic (GreaterThan sig val))

-- LE: x ≤ v ≡ ¬(x > v)
translateExpr (CompareYaml sig LE-yaml val) =
  just (Not (Atomic (GreaterThan sig val)))

-- GE: x ≥ v ≡ ¬(x < v)
translateExpr (CompareYaml sig GE-yaml val) =
  just (Not (Atomic (LessThan sig val)))

-- NE: x ≠ v ≡ ¬(x = v)
translateExpr (CompareYaml sig NE-yaml val) =
  just (Not (Atomic (Equals sig val)))

-- Direct mappings for Between and ChangedBy
translateExpr (BetweenYaml sig min max) =
  just (Atomic (Between sig min max))

translateExpr (ChangedByYaml sig delta) =
  just (Atomic (ChangedBy sig delta))

-- Signal/Constant alone are not valid predicates
translateExpr (SignalYaml _) = nothing
translateExpr (ConstantYaml _) = nothing

-- ============================================================================
-- PROPERTY TRANSLATION (PropertyYaml → LTL SignalPredicate)
-- ============================================================================

-- Translate a PropertyYaml formula to core LTL
translate : PropertyYaml → TranslationResult

-- Expression property
translate (ExprProperty e) = translateExpr e

-- Simple temporal operators with expression formulas
translate (AlwaysYaml expr) with translateExpr expr
... | nothing = nothing
... | just φ = just (Always φ)

translate (EventuallyYaml expr) with translateExpr expr
... | nothing = nothing
... | just φ = just (Eventually φ)

-- Never φ = Always (Not φ)
translate (NeverYaml expr) with translateExpr expr
... | nothing = nothing
... | just φ = just (Always (Not φ))

-- Bounded temporal operators
translate (EventuallyWithinYaml n expr) with translateExpr expr
... | nothing = nothing
... | just φ = just (EventuallyWithin n φ)

translate (AlwaysWithinYaml n expr) with translateExpr expr
... | nothing = nothing
... | just φ = just (AlwaysWithin n φ)

-- Compound operators with recursive sub-properties
translate (NotYaml sub) with translate sub
... | nothing = nothing
... | just φ = just (Not φ)

translate (AndYaml left right) with translate left | translate right
... | just φ | just ψ = just (And φ ψ)
... | _ | _ = nothing

translate (OrYaml left right) with translate left | translate right
... | just φ | just ψ = just (Or φ ψ)
... | _ | _ = nothing

-- Implies φ ψ = Or (Not φ) ψ
translate (ImpliesYaml ante cons) with translate ante | translate cons
... | just φ | just ψ = just (Or (Not φ) ψ)
... | _ | _ = nothing

translate (UntilYaml left right) with translate left | translate right
... | just φ | just ψ = just (Until φ ψ)
... | _ | _ = nothing

-- ============================================================================
-- TOTAL TRANSLATION (for Phase 3 - proofs)
-- ============================================================================

-- TODO: Prove that translation preserves semantics
-- translateSound : ∀ φ trace → satisfiesYaml φ trace ≡ satisfies (translate φ) trace
