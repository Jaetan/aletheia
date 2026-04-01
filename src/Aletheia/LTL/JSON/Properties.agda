{-# OPTIONS --safe --without-K #-}

-- Correctness properties for the LTL JSON parser and formatter.
--
-- Purpose: Prove roundtrip, soundness, and completeness for LTL formula serialization.
-- Properties:
--   Roundtrip: parseLTL (formatLTL φ) ≡ just (resetStart φ)
--   Soundness: parseLTL json ≡ just φ → json is a JObject
--   Completeness: Corollary of roundtrip
-- Role: Phase 3 verification of LTL DSL translation correctness.
--
-- Note: resetStart zeros out the startTime parameter in metric operators.
-- formatLTL ignores startTime; the parser always produces startTime=0.
-- For user-facing formulas (always startTime=0), resetStart f ≡ f.
module Aletheia.LTL.JSON.Properties where

open import Data.Maybe using (just)
open import Data.Product using (_,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Aletheia.Protocol.JSON using (JSON; JNull; JBool; JNumber; JString; JArray; JObject; getNat; ℕtoℚ)
open import Aletheia.Protocol.JSON.Properties using (getNat-ℕtoℚ)
open import Aletheia.LTL.Syntax using (LTL)
open import Aletheia.LTL.SignalPredicate using (SignalPredicate; ValueP; DeltaP; Equals; LessThan; GreaterThan; LessThanOrEqual; GreaterThanOrEqual; Between; ChangedBy)
open import Aletheia.LTL.JSON using (parseLTL; parseSignalPredicate)
open import Aletheia.LTL.JSON.Format using (formatLTL; formatSignalPredicateFields)

-- ============================================================================
-- RESET START TIME (normalize for roundtrip)
-- ============================================================================

-- formatLTL ignores the startTime parameter in metric operators, and the parser
-- always produces startTime=0. resetStart zeros out startTime so the roundtrip
-- holds for all formulas. For user-facing formulas (startTime=0), resetStart f ≡ f.
resetStart : LTL SignalPredicate → LTL SignalPredicate
resetStart (LTL.Atomic a) = LTL.Atomic a
resetStart (LTL.Not f) = LTL.Not (resetStart f)
resetStart (LTL.And f g) = LTL.And (resetStart f) (resetStart g)
resetStart (LTL.Or f g) = LTL.Or (resetStart f) (resetStart g)
resetStart (LTL.Next f) = LTL.Next (resetStart f)
resetStart (LTL.Always f) = LTL.Always (resetStart f)
resetStart (LTL.Eventually f) = LTL.Eventually (resetStart f)
resetStart (LTL.Until f g) = LTL.Until (resetStart f) (resetStart g)
resetStart (LTL.Release f g) = LTL.Release (resetStart f) (resetStart g)
resetStart (LTL.MetricEventually n _ f) = LTL.MetricEventually n 0 (resetStart f)
resetStart (LTL.MetricAlways n _ f) = LTL.MetricAlways n 0 (resetStart f)
resetStart (LTL.MetricUntil n _ f g) = LTL.MetricUntil n 0 (resetStart f) (resetStart g)
resetStart (LTL.MetricRelease n _ f g) = LTL.MetricRelease n 0 (resetStart f) (resetStart g)

-- ============================================================================
-- SIGNAL PREDICATE ROUNDTRIP
-- ============================================================================

predicate-roundtrip : (p : SignalPredicate)
  → parseSignalPredicate (formatSignalPredicateFields p) ≡ just p
predicate-roundtrip (ValueP (Equals s v)) = refl
predicate-roundtrip (ValueP (LessThan s v)) = refl
predicate-roundtrip (ValueP (GreaterThan s v)) = refl
predicate-roundtrip (ValueP (LessThanOrEqual s v)) = refl
predicate-roundtrip (ValueP (GreaterThanOrEqual s v)) = refl
predicate-roundtrip (ValueP (Between s min max)) = refl
predicate-roundtrip (DeltaP (ChangedBy s d)) = refl

-- ============================================================================
-- LTL ROUNDTRIP
-- ============================================================================

-- No depth parameter needed: parseLTL is structurally recursive on JSON input.
-- Each case reduces by computation (string comparisons on concrete operator names)
-- plus the induction hypothesis on sub-formulas.
roundtrip : (f : LTL SignalPredicate)
  → parseLTL (formatLTL f) ≡ just (resetStart f)

-- Atomic: predicate roundtrip
roundtrip (LTL.Atomic p)
  rewrite predicate-roundtrip p = refl

-- Unary operators
roundtrip (LTL.Not f)
  rewrite roundtrip f = refl

roundtrip (LTL.Next f)
  rewrite roundtrip f = refl

roundtrip (LTL.Always f)
  rewrite roundtrip f = refl

roundtrip (LTL.Eventually f)
  rewrite roundtrip f = refl

-- Binary operators
roundtrip (LTL.And f g)
  rewrite roundtrip f | roundtrip g = refl

roundtrip (LTL.Or f g)
  rewrite roundtrip f | roundtrip g = refl

roundtrip (LTL.Until f g)
  rewrite roundtrip f | roundtrip g = refl

roundtrip (LTL.Release f g)
  rewrite roundtrip f | roundtrip g = refl

-- Metric unary operators: getNat abstraction needed for ℕtoℚ roundtrip
roundtrip (LTL.MetricEventually n _ f)
  with getNat (JNumber (ℕtoℚ n)) | getNat-ℕtoℚ n
... | .(just n) | refl rewrite roundtrip f = refl

roundtrip (LTL.MetricAlways n _ f)
  with getNat (JNumber (ℕtoℚ n)) | getNat-ℕtoℚ n
... | .(just n) | refl rewrite roundtrip f = refl

-- Metric binary operators
roundtrip (LTL.MetricUntil n _ f g)
  with getNat (JNumber (ℕtoℚ n)) | getNat-ℕtoℚ n
... | .(just n) | refl
  rewrite roundtrip f | roundtrip g = refl

roundtrip (LTL.MetricRelease n _ f g)
  with getNat (JNumber (ℕtoℚ n)) | getNat-ℕtoℚ n
... | .(just n) | refl
  rewrite roundtrip f | roundtrip g = refl

-- ============================================================================
-- COMPLETENESS (corollary of roundtrip)
-- ============================================================================

-- If a formula was successfully parsed, it can be re-serialized and re-parsed.
-- Note: parsed formulas always have startTime=0, so resetStart f ≡ f for them.
completeness : (json : JSON) (f : LTL SignalPredicate)
  → parseLTL json ≡ just f
  → parseLTL (formatLTL f) ≡ just (resetStart f)
completeness json f _ = roundtrip f

-- ============================================================================
-- SOUNDNESS (structural property)
-- ============================================================================

-- Minimal soundness: successful parse implies JSON is an object.
-- parseLTL only succeeds on JObject values (all other constructors return nothing).
parseLTL-isObject : ∀ json f → parseLTL json ≡ just f
  → ∃[ fields ] (json ≡ JObject fields)
parseLTL-isObject JNull f ()
parseLTL-isObject (JBool _) f ()
parseLTL-isObject (JNumber _) f ()
parseLTL-isObject (JString _) f ()
parseLTL-isObject (JArray _) f ()
parseLTL-isObject (JObject fields) f _ = fields , refl
