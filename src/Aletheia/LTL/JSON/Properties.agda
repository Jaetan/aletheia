{-# OPTIONS --safe --without-K #-}

-- Correctness properties for the LTL JSON parser and formatter.
--
-- Purpose: Prove roundtrip and soundness for LTL formula serialization.
-- Properties:
--   Roundtrip: parseLTL (formatLTL φ) ≡ inj₂ (resetStart φ)
--   Soundness: parseLTL json ≡ inj₂ φ → json is a JObject
--   Completeness: Corollary of roundtrip
-- Role: Phase 3 verification of LTL DSL translation correctness.
--
-- Note: resetStart zeros out the startTime parameter in metric operators.
-- formatLTL ignores startTime; the parser always produces startTime=0.
-- For user-facing formulas (always startTime=0), resetStart f ≡ f.
module Aletheia.LTL.JSON.Properties where

open import Data.Maybe using (just)
open import Data.Sum using (inj₂)
open import Data.Product using (_,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Aletheia.JSON using (JNull; JBool; JNumber; JString; JArray; JObject; getNat)
open import Aletheia.Prelude using (ℕtoℚ)
open import Aletheia.Trace.Time using (tsValue)
open import Aletheia.JSON.Properties using (getNat-ℕtoℚ)
open import Aletheia.LTL.Syntax using (LTL)
open import Aletheia.LTL.SignalPredicate using (SignalPredicate; ValueP; DeltaP; Equals; LessThan; GreaterThan; LessThanOrEqual; GreaterThanOrEqual; Between; ChangedBy; StableWithin)
open import Aletheia.LTL.JSON using (parseLTL; parseSignalPredicate)
open import Aletheia.LTL.JSON.Format using (formatLTL; formatSignalPredicateFields)
open import Aletheia.DBC.Identifier using (parseIdentifierField-on-valid)

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
resetStart (LTL.WNext f) = LTL.WNext (resetStart f)
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
  → parseSignalPredicate (formatSignalPredicateFields p) ≡ inj₂ p
predicate-roundtrip (ValueP (Equals s v)) rewrite parseIdentifierField-on-valid s = refl
predicate-roundtrip (ValueP (LessThan s v)) rewrite parseIdentifierField-on-valid s = refl
predicate-roundtrip (ValueP (GreaterThan s v)) rewrite parseIdentifierField-on-valid s = refl
predicate-roundtrip (ValueP (LessThanOrEqual s v)) rewrite parseIdentifierField-on-valid s = refl
predicate-roundtrip (ValueP (GreaterThanOrEqual s v)) rewrite parseIdentifierField-on-valid s = refl
predicate-roundtrip (ValueP (Between s min max)) rewrite parseIdentifierField-on-valid s = refl
predicate-roundtrip (DeltaP (ChangedBy s d)) rewrite parseIdentifierField-on-valid s = refl
predicate-roundtrip (DeltaP (StableWithin s t)) rewrite parseIdentifierField-on-valid s = refl

-- ============================================================================
-- LTL ROUNDTRIP
-- ============================================================================

-- No depth parameter needed: parseLTL is structurally recursive on JSON input.
-- Each case reduces by computation (string comparisons on concrete operator names)
-- plus the induction hypothesis on sub-formulas.
roundtrip : (f : LTL SignalPredicate)
  → parseLTL (formatLTL f) ≡ inj₂ (resetStart f)

-- Atomic: predicate roundtrip
roundtrip (LTL.Atomic p)
  rewrite predicate-roundtrip p = refl

-- Unary operators
roundtrip (LTL.Not f)
  rewrite roundtrip f = refl

roundtrip (LTL.Next f)
  rewrite roundtrip f = refl

roundtrip (LTL.WNext f)
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

-- Metric unary operators: getNat abstraction needed for ℕtoℚ roundtrip.
-- Window is unwrapped via tsValue at the formatter; parser re-wraps via mkTs,
-- and `mkTs (tsValue n) ≡ n` by Timestamp record η-conversion.
-- INVARIANT: do not change `Timestamp` to a `data` declaration or break record
-- η (e.g. via private constructor / erasure boundary) — this roundtrip would
-- silently stop reducing.  See Aletheia.Trace.Time.
roundtrip (LTL.MetricEventually n _ f)
  with getNat (JNumber (ℕtoℚ (tsValue n))) | getNat-ℕtoℚ (tsValue n)
... | .(just (tsValue n)) | refl rewrite roundtrip f = refl

roundtrip (LTL.MetricAlways n _ f)
  with getNat (JNumber (ℕtoℚ (tsValue n))) | getNat-ℕtoℚ (tsValue n)
... | .(just (tsValue n)) | refl rewrite roundtrip f = refl

-- Metric binary operators
roundtrip (LTL.MetricUntil n _ f g)
  with getNat (JNumber (ℕtoℚ (tsValue n))) | getNat-ℕtoℚ (tsValue n)
... | .(just (tsValue n)) | refl
  rewrite roundtrip f | roundtrip g = refl

roundtrip (LTL.MetricRelease n _ f g)
  with getNat (JNumber (ℕtoℚ (tsValue n))) | getNat-ℕtoℚ (tsValue n)
... | .(just (tsValue n)) | refl
  rewrite roundtrip f | roundtrip g = refl

-- ============================================================================
-- SOUNDNESS (structural property)
-- ============================================================================

-- Minimal soundness: successful parse implies JSON is an object.
-- parseLTL only succeeds on JObject values (all other constructors return nothing).
parseLTL-isObject : ∀ json f → parseLTL json ≡ inj₂ f
  → ∃[ fields ] (json ≡ JObject fields)
parseLTL-isObject JNull f ()
parseLTL-isObject (JBool _) f ()
parseLTL-isObject (JNumber _) f ()
parseLTL-isObject (JString _) f ()
parseLTL-isObject (JArray _) f ()
parseLTL-isObject (JObject fields) f _ = fields , refl
