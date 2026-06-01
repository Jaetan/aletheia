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

open import Aletheia.Prelude using (Bool; List; false; true; ℚ)
open import Data.Char using (Char)
open import Data.Rational using ()
open import Aletheia.DBC.Identifier using (Identifier)

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
  Equals             : (signalName : Identifier) → (value : ℚ) → ValuePredicate
  LessThan           : (signalName : Identifier) → (value : ℚ) → ValuePredicate
  GreaterThan        : (signalName : Identifier) → (value : ℚ) → ValuePredicate
  LessThanOrEqual    : (signalName : Identifier) → (value : ℚ) → ValuePredicate
  GreaterThanOrEqual : (signalName : Identifier) → (value : ℚ) → ValuePredicate
  Between            : (signalName : Identifier) → (min : ℚ) → (max : ℚ) → ValuePredicate

-- Extract signal name from a value predicate.  Projects the underlying
-- `Identifier.name` (a `List Char`) so the streaming evaluation + cache
-- hot path keeps comparing char lists via `_≡csᵇ_` — the Identifier
-- witness rides along in the stored field but is not re-examined per frame.
valuePredicateSignal : ValuePredicate → List Char
valuePredicateSignal (Equals n _)             = Identifier.name n
valuePredicateSignal (LessThan n _)           = Identifier.name n
valuePredicateSignal (GreaterThan n _)        = Identifier.name n
valuePredicateSignal (LessThanOrEqual n _)    = Identifier.name n
valuePredicateSignal (GreaterThanOrEqual n _) = Identifier.name n
valuePredicateSignal (Between n _ _)          = Identifier.name n

-- Delta predicates: require two values (previous and current)
data DeltaPredicate : Set where
  ChangedBy    : (signalName : Identifier) → (delta : ℚ) → DeltaPredicate
  StableWithin : (signalName : Identifier) → (tolerance : ℚ) → DeltaPredicate

-- Extract signal name from a delta predicate
deltaPredicateSignal : DeltaPredicate → List Char
deltaPredicateSignal (ChangedBy n _)    = Identifier.name n
deltaPredicateSignal (StableWithin n _) = Identifier.name n

-- Combined signal predicate type
data SignalPredicate : Set where
  ValueP : ValuePredicate → SignalPredicate
  DeltaP : DeltaPredicate → SignalPredicate

-- Associate a SignalPredicate with its target signal name.  Lifted from
-- `SignalPredicate.Evaluation.Properties` (where it was originally defined
-- as a proof helper) to make it reachable from the runtime EndStream
-- warning walker (`Protocol.Handlers.handleEndStream` per R21
-- AGDA-D-12.1).  The Properties module re-uses this definition.
signalOf : SignalPredicate → List Char
signalOf (ValueP vp) = valuePredicateSignal vp
signalOf (DeltaP dp) = deltaPredicateSignal dp
