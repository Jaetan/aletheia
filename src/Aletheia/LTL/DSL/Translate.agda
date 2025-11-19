{-# OPTIONS --safe --without-K #-}

module Aletheia.LTL.DSL.Translate where

open import Aletheia.LTL.Syntax
open import Aletheia.LTL.DSL.Python
open import Aletheia.LTL.SignalPredicate using (SignalPredicate; Equals; LessThan; GreaterThan; Between; ChangedBy)
open import Data.String using (String)
open import Data.Rational using (ℚ)
open import Data.Maybe using (Maybe; just; nothing)

-- ============================================================================
-- TRANSLATION: PythonLTL → LTL SignalPredicate
-- ============================================================================

-- Translation result type
-- Nothing = unsupported/invalid input
-- Just φ = successfully translated formula
TranslationResult : Set
TranslationResult = Maybe (LTL SignalPredicate)

-- ============================================================================
-- EXPRESSION TRANSLATION
-- ============================================================================

-- Translate a Python expression to an LTL formula over SignalPredicates
-- Some expressions (LE, GE, NE) require wrapping with Not at the LTL level
translateExpr : PythonExpr → TranslationResult

-- Signal alone is not a valid predicate (needs comparison)
translateExpr (Signal _) = nothing

-- Constant alone is not a valid predicate
translateExpr (Constant _) = nothing

-- Compare with direct mappings
translateExpr (Compare (Signal s) EQ (Constant v)) =
  just (Atomic (Equals s v))

translateExpr (Compare (Signal s) LT (Constant v)) =
  just (Atomic (LessThan s v))

translateExpr (Compare (Signal s) GT (Constant v)) =
  just (Atomic (GreaterThan s v))

-- LE: x ≤ v ≡ ¬(x > v)
translateExpr (Compare (Signal s) LE (Constant v)) =
  just (Not (Atomic (GreaterThan s v)))

-- GE: x ≥ v ≡ ¬(x < v)
translateExpr (Compare (Signal s) GE (Constant v)) =
  just (Not (Atomic (LessThan s v)))

-- NE: x ≠ v ≡ ¬(x = v)
translateExpr (Compare (Signal s) NE (Constant v)) =
  just (Not (Atomic (Equals s v)))

-- Direct mappings for Between and ChangedBy
translateExpr (Between s min max) =
  just (Atomic (Between s min max))

translateExpr (ChangedBy s delta) =
  just (Atomic (ChangedBy s delta))

-- All other patterns (complex expressions) not supported
translateExpr _ = nothing

-- ============================================================================
-- FORMULA TRANSLATION
-- ============================================================================

-- Translate a Python LTL formula to core LTL
-- Uses mutual recursion with helper for Maybe binding
translate : PythonLTL → TranslationResult

translate (Expr e) = translateExpr e

translate (Not φ) with translate φ
... | nothing = nothing
... | just φ' = just (Not φ')

translate (And φ ψ) with translate φ | translate ψ
... | just φ' | just ψ' = just (And φ' ψ')
... | _ | _ = nothing

translate (Or φ ψ) with translate φ | translate ψ
... | just φ' | just ψ' = just (Or φ' ψ')
... | _ | _ = nothing

translate (Always φ) with translate φ
... | nothing = nothing
... | just φ' = just (Always φ')

translate (Eventually φ) with translate φ
... | nothing = nothing
... | just φ' = just (Eventually φ')

-- Never φ = Always (Not φ)
translate (Never φ) with translate φ
... | nothing = nothing
... | just φ' = just (Always (Not φ'))

translate (EventuallyWithin n φ) with translate φ
... | nothing = nothing
... | just φ' = just (EventuallyWithin n φ')

translate (AlwaysWithin n φ) with translate φ
... | nothing = nothing
... | just φ' = just (AlwaysWithin n φ')

-- Implies φ ψ = Or (Not φ) ψ
translate (Implies φ ψ) with translate φ | translate ψ
... | just φ' | just ψ' = just (Or (Not φ') ψ')
... | _ | _ = nothing

translate (Until φ ψ) with translate φ | translate ψ
... | just φ' | just ψ' = just (Until φ' ψ')
... | _ | _ = nothing

-- ============================================================================
-- TOTAL TRANSLATION (for Phase 3 - proofs)
-- ============================================================================

-- TODO: Prove that translation preserves semantics
-- translateSound : ∀ φ trace → satisfiesPython φ trace ≡ satisfies (translate φ) trace
