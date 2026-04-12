{-# OPTIONS --safe --without-K #-}

-- Signal predicate types and TruthVal logic.
--
-- Purpose: Define atomic predicates over signal values and the four-valued
-- truth type used for predicate evaluation.
-- TruthVal: True, False, Unknown (never observed), Pending (delta, no prev).
-- Predicates: ValuePredicate (single-value), DeltaPredicate (two-value),
--   SignalPredicate (combined).
-- Role: Core types imported by LTL modules, Cache, and Evaluation.
module Aletheia.LTL.SignalPredicate.Types where

open import Aletheia.Prelude
open import Data.Rational using (ℚ)

-- ============================================================================
-- SIGNAL EVALUATION VALUES (Extended Kleene logic)
-- ============================================================================

data TruthVal : Set where
  True    : TruthVal
  False   : TruthVal
  Unknown : TruthVal
  Pending : TruthVal

-- Negation: ¬ Unknown = Unknown, ¬ Pending = Pending
notTV : TruthVal → TruthVal
notTV True    = False
notTV False   = True
notTV Unknown = Unknown
notTV Pending = Pending

-- Conjunction with short-circuit semantics
_∧TV_ : TruthVal → TruthVal → TruthVal
False   ∧TV _       = False
_       ∧TV False   = False
True    ∧TV y       = y
x       ∧TV True    = x
Pending ∧TV _       = Pending
_       ∧TV Pending = Pending
Unknown ∧TV Unknown = Unknown

-- Disjunction with short-circuit semantics
_∨TV_ : TruthVal → TruthVal → TruthVal
True    ∨TV _       = True
_       ∨TV True    = True
False   ∨TV y       = y
x       ∨TV False   = x
Pending ∨TV _       = Pending
_       ∨TV Pending = Pending
Unknown ∨TV Unknown = Unknown

-- Implication: a → b ≡ ¬a ∨ b
_→TV_ : TruthVal → TruthVal → TruthVal
a →TV b = notTV a ∨TV b

-- Lift Bool to TruthVal
fromBool : Bool → TruthVal
fromBool true  = True
fromBool false = False

-- ============================================================================
-- SIGNAL PREDICATES
-- ============================================================================

-- Single-value predicates: evaluated given one signal value (ℚ → Bool)
data ValuePredicate : Set where
  Equals             : (signalName : String) → (value : ℚ) → ValuePredicate
  LessThan           : (signalName : String) → (value : ℚ) → ValuePredicate
  GreaterThan        : (signalName : String) → (value : ℚ) → ValuePredicate
  LessThanOrEqual    : (signalName : String) → (value : ℚ) → ValuePredicate
  GreaterThanOrEqual : (signalName : String) → (value : ℚ) → ValuePredicate
  Between            : (signalName : String) → (min : ℚ) → (max : ℚ) → ValuePredicate

-- Extract signal name from a value predicate
valuePredicateSignal : ValuePredicate → String
valuePredicateSignal (Equals n _)             = n
valuePredicateSignal (LessThan n _)           = n
valuePredicateSignal (GreaterThan n _)        = n
valuePredicateSignal (LessThanOrEqual n _)    = n
valuePredicateSignal (GreaterThanOrEqual n _) = n
valuePredicateSignal (Between n _ _)          = n

-- Delta predicates: require two values (previous and current)
data DeltaPredicate : Set where
  ChangedBy    : (signalName : String) → (delta : ℚ) → DeltaPredicate
  StableWithin : (signalName : String) → (tolerance : ℚ) → DeltaPredicate

-- Extract signal name from a delta predicate
deltaPredicateSignal : DeltaPredicate → String
deltaPredicateSignal (ChangedBy n _)    = n
deltaPredicateSignal (StableWithin n _) = n

-- Combined signal predicate type
data SignalPredicate : Set where
  ValueP : ValuePredicate → SignalPredicate
  DeltaP : DeltaPredicate → SignalPredicate
