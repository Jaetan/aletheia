{-# OPTIONS --safe --without-K #-}

-- Signal predicates for LTL properties (equals, lessThan, greaterThan, between, changedBy).
--
-- Purpose: Define atomic predicates over signal values extracted from CAN frames.
-- Predicates: Equals, LessThan, GreaterThan, Between (range), ChangedBy (delta from previous).
-- Role: Instantiate LTL.Syntax with signal-specific predicates for CAN verification.
--
-- Design: Operates on physical values (ℚ) after signal extraction and scaling.
--
-- Three-Valued Logic:
--   ThreeVal represents predicate evaluation results with explicit Unknown state.
--   - Known true  : signal observed, predicate holds
--   - Known false : signal observed, predicate violated
--   - Unknown     : signal never observed (no cached value available)
--
--   This enables last-known-value semantics where signals persist in a cache
--   and Unknown only occurs when a signal has never been seen.
module Aletheia.LTL.SignalPredicate where

open import Aletheia.Prelude
open import Data.Rational as Rat using (_/_; _-_; ∣_∣; _≤?_; _<?_)
open import Data.Maybe using (_>>=_)
open import Function using (case_of_)

open import Aletheia.CAN.Frame
open import Aletheia.CAN.Signal
open import Aletheia.CAN.Encoding
open import Aletheia.CAN.SignalExtraction
open import Aletheia.CAN.ExtractionResult
open import Aletheia.DBC.Types
open import Aletheia.LTL.Syntax using (LTL; mapLTL)
open import Aletheia.Trace.CANTrace using (TimedFrame)

-- ============================================================================
-- THREE-VALUED LOGIC (Kleene strong three-valued logic)
-- ============================================================================

-- Three-valued logic for predicate evaluation.
-- Uses Kleene's strong three-valued logic semantics.
--
-- Truth values:
--   True    → predicate definitely holds
--   False   → predicate definitely violated
--   Unknown → signal never observed, truth value undetermined
--
-- Propagation through LTL operators:
--   - Safety (always): Unknown means "no violation yet" → Continue
--   - Liveness (eventually): Unknown at deadline → Violated
--   - Bounded safety (for_at_least): Unknown during interval → Violated
--
-- Kleene semantics for connectives:
--   ¬ Unknown = Unknown
--   True  ∧ Unknown = Unknown    False ∧ Unknown = False  (short-circuit)
--   True  ∨ Unknown = True       False ∨ Unknown = Unknown (short-circuit)

data ThreeVal : Set where
  True    : ThreeVal
  False   : ThreeVal
  Unknown : ThreeVal

-- Decidable equality on ThreeVal
_≟TV_ : (x y : ThreeVal) → Dec (x ≡ y)
True    ≟TV True    = yes refl
True    ≟TV False   = no λ ()
True    ≟TV Unknown = no λ ()
False   ≟TV True    = no λ ()
False   ≟TV False   = yes refl
False   ≟TV Unknown = no λ ()
Unknown ≟TV True    = no λ ()
Unknown ≟TV False   = no λ ()
Unknown ≟TV Unknown = yes refl

-- Negation: ¬ Unknown = Unknown
notTV : ThreeVal → ThreeVal
notTV True    = False
notTV False   = True
notTV Unknown = Unknown

-- Conjunction with short-circuit semantics
_∧TV_ : ThreeVal → ThreeVal → ThreeVal
False   ∧TV _       = False
_       ∧TV False   = False
True    ∧TV y       = y
x       ∧TV True    = x
Unknown ∧TV Unknown = Unknown

-- Disjunction with short-circuit semantics
_∨TV_ : ThreeVal → ThreeVal → ThreeVal
True    ∨TV _       = True
_       ∨TV True    = True
False   ∨TV y       = y
x       ∨TV False   = x
Unknown ∨TV Unknown = Unknown

-- Implication: a → b ≡ ¬a ∨ b
_→TV_ : ThreeVal → ThreeVal → ThreeVal
a →TV b = notTV a ∨TV b

-- Lift Bool to ThreeVal (for comparison results)
fromBool : Bool → ThreeVal
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

-- Evaluate a value predicate given a signal value (pure comparison)
evalValuePredicate : ValuePredicate → ℚ → Bool
evalValuePredicate (Equals _ v) x             = x ==ℚ v
evalValuePredicate (LessThan _ v) x           = x <ℚ v
evalValuePredicate (GreaterThan _ v) x        = x >ℚ v
evalValuePredicate (LessThanOrEqual _ v) x    = x ≤ℚ v
evalValuePredicate (GreaterThanOrEqual _ v) x = x ≥ℚ v
evalValuePredicate (Between _ lo hi) x        = lo ≤ℚ x ∧ x ≤ℚ hi

-- Delta predicates: require two values (previous and current).
data DeltaPredicate : Set where
  ChangedBy : (signalName : String) → (delta : ℚ) → DeltaPredicate

-- Extract signal name from a delta predicate
deltaPredicateSignal : DeltaPredicate → String
deltaPredicateSignal (ChangedBy n _) = n

-- Evaluate a delta predicate given previous and current values
evalDeltaPredicate : DeltaPredicate → ℚ → ℚ → Bool
evalDeltaPredicate (ChangedBy _ delta) prev curr = ⌊ ∣ curr Rat.- prev ∣ Rat.≤? delta ⌋

-- Combined signal predicate type (for use in LTL formulas)
data SignalPredicate : Set where
  ValueP : ValuePredicate → SignalPredicate
  DeltaP : DeltaPredicate → SignalPredicate

-- Extract the signal name from any predicate
getSignalName : SignalPredicate → String
getSignalName (ValueP vp) = valuePredicateSignal vp
getSignalName (DeltaP dp) = deltaPredicateSignal dp

-- ============================================================================
-- HELPER FUNCTIONS
-- ============================================================================

-- Extract signal value using new extraction with multiplexing support
extractSignalValue : String → DBC → CANFrame → Maybe ℚ
extractSignalValue sigName dbc frame = getValue (extractSignalWithContext dbc frame sigName)

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
  where
    open import Data.String.Properties renaming (_≟_ to _≟ₛ_)

-- Update or insert a signal value in the cache
updateCache : String → ℚ → ℕ → SignalCache → SignalCache
updateCache name val ts [] = (name , mkCachedSignal val ts) ∷ []
updateCache name val ts ((n , cached) ∷ rest) =
  if ⌊ name ≟ₛ n ⌋
  then (name , mkCachedSignal val ts) ∷ rest
  else (n , cached) ∷ updateCache name val ts rest
  where
    open import Data.String.Properties renaming (_≟_ to _≟ₛ_)

-- ============================================================================
-- THREE-VALUED PREDICATE EVALUATION
-- ============================================================================

-- Get signal value: try frame first, then cache
getSignalValue : String → DBC → SignalCache → CANFrame → Maybe ℚ
getSignalValue sigName dbc cache frame =
  case extractSignalValue sigName dbc frame of λ where
    (just v) → just v
    nothing  → Data.Maybe.map CachedSignal.value (lookupCache sigName cache)

-- Evaluate value predicate with cache fallback
evalValuePredicateTV : DBC → SignalCache → ValuePredicate → CANFrame → ThreeVal
evalValuePredicateTV dbc cache vp frame =
  case getSignalValue (valuePredicateSignal vp) dbc cache frame of λ where
    (just v) → fromBool (evalValuePredicate vp v)
    nothing  → Unknown

-- Evaluate delta predicate with cache
evalDeltaPredicateTV : DBC → SignalCache → DeltaPredicate → CANFrame → ThreeVal
evalDeltaPredicateTV dbc cache dp frame =
  let sigName = deltaPredicateSignal dp
      currVal = getSignalValue sigName dbc cache frame
      prevVal = Data.Maybe.map CachedSignal.value (lookupCache sigName cache)
  in case currVal of λ where
    nothing   → Unknown
    (just cv) → case prevVal of λ where
      nothing   → True  -- First observation: vacuously satisfied
      (just pv) → fromBool (evalDeltaPredicate dp pv cv)

-- Evaluate any signal predicate with cache
evalPredicateTV : DBC → SignalCache → SignalPredicate → CANFrame → ThreeVal
evalPredicateTV dbc cache (ValueP vp) frame = evalValuePredicateTV dbc cache vp frame
evalPredicateTV dbc cache (DeltaP dp) frame = evalDeltaPredicateTV dbc cache dp frame

