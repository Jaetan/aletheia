{-# OPTIONS --safe --without-K #-}

-- Signal predicates for LTL properties (equals, lessThan, greaterThan, between, changedBy).
--
-- Purpose: Define atomic predicates over signal values extracted from CAN frames.
-- Predicates: Equals, LessThan, GreaterThan, Between (range), ChangedBy (delta from previous).
-- Role: Instantiate LTL.Syntax with signal-specific predicates for CAN verification.
--
-- Design: Operates on physical values (ℚ) after signal extraction and scaling.
--
-- Signal Evaluation Values:
--   TruthVal represents predicate evaluation results with explicit Unknown/Pending states.
--   - True    : signal observed, predicate holds
--   - False   : signal observed, predicate violated
--   - Unknown : signal never observed (no cached value available)
--   - Pending : not enough data yet (delta predicates with no previous value)
--
--   This enables last-known-value semantics where signals persist in a cache
--   and Unknown only occurs when a signal has never been seen.
module Aletheia.LTL.SignalPredicate where

open import Aletheia.Prelude
open import Data.Rational as Rat using (_-_; ∣_∣; _≤?_; _<?_)
open import Data.Maybe as M using (map)
open import Data.String.Properties renaming (_≟_ to _≟ₛ_)
open import Function using (case_of_)

open import Aletheia.CAN.Frame using (CANFrame)
open import Aletheia.CAN.SignalExtraction using (extractSignalWithContext)
open import Aletheia.CAN.ExtractionResult using (getValue)
open import Aletheia.DBC.Types using (DBC)

-- ============================================================================
-- SIGNAL EVALUATION VALUES (Extended Kleene logic)
-- ============================================================================

-- Signal predicate evaluation results.
-- Extends Kleene's strong three-valued logic with Pending for delta predicates.
--
-- Truth values:
--   True    → predicate definitely holds
--   False   → predicate definitely violated
--   Unknown → signal never observed, truth value undetermined
--   Pending → not enough data yet (e.g., delta predicate with no previous value)
--
-- Propagation through LTL operators:
--   - Safety (always): Unknown means "no violation yet" → Continue
--   - Liveness (eventually): Unknown at deadline → Violated
--   - Bounded safety (for_at_least): Unknown during interval → Violated
--
-- Kleene semantics for connectives:
--   ¬ Unknown = Unknown,  ¬ Pending = Pending
--   True  ∧ Unknown = Unknown    False ∧ Unknown = False  (short-circuit)
--   True  ∨ Unknown = True       False ∨ Unknown = Unknown (short-circuit)

data TruthVal : Set where
  True    : TruthVal
  False   : TruthVal
  Unknown : TruthVal
  Pending : TruthVal  -- Not enough data yet (e.g., delta predicate with no previous value)

-- Decidable equality on TruthVal
_≟TV_ : (x y : TruthVal) → Dec (x ≡ y)
True    ≟TV True    = yes refl
True    ≟TV False   = no λ ()
True    ≟TV Unknown = no λ ()
True    ≟TV Pending = no λ ()
False   ≟TV True    = no λ ()
False   ≟TV False   = yes refl
False   ≟TV Unknown = no λ ()
False   ≟TV Pending = no λ ()
Unknown ≟TV True    = no λ ()
Unknown ≟TV False   = no λ ()
Unknown ≟TV Unknown = yes refl
Unknown ≟TV Pending = no λ ()
Pending ≟TV True    = no λ ()
Pending ≟TV False   = no λ ()
Pending ≟TV Unknown = no λ ()
Pending ≟TV Pending = yes refl

-- Negation: ¬ Unknown = Unknown, ¬ Pending = Pending
notTV : TruthVal → TruthVal
notTV True    = False
notTV False   = True
notTV Unknown = Unknown
notTV Pending = Pending

-- Conjunction with short-circuit semantics
-- Pending behaves like Unknown in Kleene logic
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

-- Lift Bool to TruthVal (for comparison results)
fromBool : Bool → TruthVal
fromBool true  = True
fromBool false = False

-- ============================================================================
-- COMPARISON HELPERS
-- ============================================================================

-- Efficient Boolean comparison operators on rationals.
-- These are wrappers around decidable comparisons for runtime checking.

_==ℚ_ : ℚ → ℚ → Bool
x ==ℚ y = ⌊ x Rat.≟ y ⌋

_≤ℚ_ : ℚ → ℚ → Bool
x ≤ℚ y = ⌊ x Rat.≤? y ⌋

_<ℚ_ : ℚ → ℚ → Bool
x <ℚ y = ⌊ x Rat.<? y ⌋

_>ℚ_ : ℚ → ℚ → Bool
x >ℚ y = y <ℚ x

_≥ℚ_ : ℚ → ℚ → Bool
x ≥ℚ y = y ≤ℚ x

-- ============================================================================
-- SIGNAL PREDICATES (Split into single-value and delta predicates)
-- ============================================================================

-- Single-value predicates: can be evaluated given one signal value.
-- These form the clean abstraction where evaluation is: ℚ → Bool
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

-- Delta predicates: require two values (previous and current).
data DeltaPredicate : Set where
  ChangedBy : (signalName : String) → (delta : ℚ) → DeltaPredicate

-- Extract signal name from a delta predicate
deltaPredicateSignal : DeltaPredicate → String
deltaPredicateSignal (ChangedBy n _) = n

-- Combined signal predicate type (for use in LTL formulas)
data SignalPredicate : Set where
  ValueP : ValuePredicate → SignalPredicate
  DeltaP : DeltaPredicate → SignalPredicate

-- ============================================================================
-- HELPER FUNCTIONS
-- ============================================================================

-- Extract signal value using new extraction with multiplexing support
extractTruthValue : String → DBC → CANFrame → Maybe ℚ
extractTruthValue sigName dbc frame = getValue (extractSignalWithContext dbc frame sigName)

-- ============================================================================
-- SIGNAL CACHE
-- ============================================================================

-- Cached signal value with observation timestamp.
record CachedSignal : Set where
  constructor mkCachedSignal
  field
    value        : ℚ
    lastObserved : ℕ  -- timestamp in microseconds

-- Signal cache: association list mapping signal names to cached values.
SignalCache : Set
SignalCache = List (String × CachedSignal)

-- Empty cache
emptyCache : SignalCache
emptyCache = []

-- Lookup a signal in the cache
lookupCache : String → SignalCache → Maybe CachedSignal
lookupCache _ [] = nothing
lookupCache name ((n , cached) ∷ rest) =
  if ⌊ name ≟ₛ n ⌋ then just cached else lookupCache name rest

-- Update or insert a signal value in the cache
updateCache : String → ℚ → ℕ → SignalCache → SignalCache
updateCache name val ts [] = (name , mkCachedSignal val ts) ∷ []
updateCache name val ts ((n , cached) ∷ rest) =
  if ⌊ name ≟ₛ n ⌋
  then (name , mkCachedSignal val ts) ∷ rest
  else (n , cached) ∷ updateCache name val ts rest

-- ============================================================================
-- PURE PREDICATE EVALUATION (internal — used by TV variants below)
-- ============================================================================

private
  -- Evaluate a value predicate given a signal value (pure comparison)
  evalValuePredicate : ValuePredicate → ℚ → Bool
  evalValuePredicate (Equals _ v) x             = x ==ℚ v
  evalValuePredicate (LessThan _ v) x           = x <ℚ v
  evalValuePredicate (GreaterThan _ v) x        = x >ℚ v
  evalValuePredicate (LessThanOrEqual _ v) x    = x ≤ℚ v
  evalValuePredicate (GreaterThanOrEqual _ v) x = x ≥ℚ v
  evalValuePredicate (Between _ lo hi) x        = lo ≤ℚ x ∧ x ≤ℚ hi

  -- Evaluate a delta predicate given previous and current values
  evalDeltaPredicate : DeltaPredicate → ℚ → ℚ → Bool
  evalDeltaPredicate (ChangedBy _ delta) prev curr = ⌊ ∣ curr Rat.- prev ∣ Rat.≤? delta ⌋

-- ============================================================================
-- THREE-VALUED PREDICATE EVALUATION
-- ============================================================================

-- Get signal value: try frame first, then cache
getTruthValue : String → DBC → SignalCache → CANFrame → Maybe ℚ
getTruthValue sigName dbc cache frame =
  case extractTruthValue sigName dbc frame of λ where
    (just v) → just v
    nothing  → M.map CachedSignal.value (lookupCache sigName cache)

-- Evaluate value predicate with cache fallback
evalValuePredicateTV : DBC → SignalCache → ValuePredicate → CANFrame → TruthVal
evalValuePredicateTV dbc cache vp frame =
  case getTruthValue (valuePredicateSignal vp) dbc cache frame of λ where
    (just v) → fromBool (evalValuePredicate vp v)
    nothing  → Unknown

-- Evaluate delta predicate with cache
evalDeltaPredicateTV : DBC → SignalCache → DeltaPredicate → CANFrame → TruthVal
evalDeltaPredicateTV dbc cache dp frame =
  let sigName = deltaPredicateSignal dp
      currVal = getTruthValue sigName dbc cache frame
      prevVal = M.map CachedSignal.value (lookupCache sigName cache)
  in case currVal of λ where
    nothing   → Unknown
    (just cv) → case prevVal of λ where
      nothing   → Pending  -- First observation: no previous value to compare
      (just pv) → fromBool (evalDeltaPredicate dp pv cv)

-- Evaluate any signal predicate with cache
evalPredicateTV : DBC → SignalCache → SignalPredicate → CANFrame → TruthVal
evalPredicateTV dbc cache (ValueP vp) frame = evalValuePredicateTV dbc cache vp frame
evalPredicateTV dbc cache (DeltaP dp) frame = evalDeltaPredicateTV dbc cache dp frame

