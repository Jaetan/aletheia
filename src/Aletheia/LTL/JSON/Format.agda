{-# OPTIONS --safe --without-K #-}

-- Formatter and depth function for LTL formulas with signal predicates.
--
-- Purpose: Convert LTL formulas back to JSON for roundtrip proofs.
-- Produces canonical JSON that the parser in Aletheia.LTL.JSON can parse back.
-- Role: Foundation for roundtrip correctness proofs in LTL.JSON.Properties.
module Aletheia.LTL.JSON.Format where

open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Aletheia.Protocol.JSON using (JSON; JNumber; JString; JObject; ℕtoℚ)
open import Aletheia.LTL.Syntax using (LTL)
open import Aletheia.LTL.SignalPredicate using (SignalPredicate; ValueP; DeltaP; ValuePredicate; DeltaPredicate; Equals; LessThan; GreaterThan; LessThanOrEqual; GreaterThanOrEqual; Between; ChangedBy; StableWithin)

-- ============================================================================
-- VALUE PREDICATE FORMATTER
-- ============================================================================

-- Format a ValuePredicate as a list of JSON fields (canonical order).
formatValuePredicateFields : ValuePredicate → List (String × JSON)
formatValuePredicateFields (Equals s v) =
  ("predicate" , JString "equals") ∷ ("signal" , JString s) ∷ ("value" , JNumber v) ∷ []
formatValuePredicateFields (LessThan s v) =
  ("predicate" , JString "lessThan") ∷ ("signal" , JString s) ∷ ("value" , JNumber v) ∷ []
formatValuePredicateFields (GreaterThan s v) =
  ("predicate" , JString "greaterThan") ∷ ("signal" , JString s) ∷ ("value" , JNumber v) ∷ []
formatValuePredicateFields (LessThanOrEqual s v) =
  ("predicate" , JString "lessThanOrEqual") ∷ ("signal" , JString s) ∷ ("value" , JNumber v) ∷ []
formatValuePredicateFields (GreaterThanOrEqual s v) =
  ("predicate" , JString "greaterThanOrEqual") ∷ ("signal" , JString s) ∷ ("value" , JNumber v) ∷ []
formatValuePredicateFields (Between s min max) =
  ("predicate" , JString "between") ∷ ("signal" , JString s) ∷ ("min" , JNumber min) ∷ ("max" , JNumber max) ∷ []

-- ============================================================================
-- DELTA PREDICATE FORMATTER
-- ============================================================================

-- Format a DeltaPredicate as a list of JSON fields (canonical order).
formatDeltaPredicateFields : DeltaPredicate → List (String × JSON)
formatDeltaPredicateFields (ChangedBy s d) =
  ("predicate" , JString "changedBy") ∷ ("signal" , JString s) ∷ ("delta" , JNumber d) ∷ []
formatDeltaPredicateFields (StableWithin s t) =
  ("predicate" , JString "stableWithin") ∷ ("signal" , JString s) ∷ ("tolerance" , JNumber t) ∷ []

-- ============================================================================
-- SIGNAL PREDICATE FORMATTER
-- ============================================================================

-- Format a SignalPredicate as a list of JSON fields (canonical order).
-- Field order matches what the parser expects: "predicate" first, then signal/value fields.
formatSignalPredicateFields : SignalPredicate → List (String × JSON)
formatSignalPredicateFields (ValueP vp) = formatValuePredicateFields vp
formatSignalPredicateFields (DeltaP dp) = formatDeltaPredicateFields dp

-- ============================================================================
-- LTL FORMULA FORMATTER
-- ============================================================================

-- Format an LTL formula as a JSON object (canonical field order).
-- The formatter never produces "never" or "implies" operators (those are derived forms).
formatLTL : LTL SignalPredicate → JSON
formatLTL (LTL.Atomic p) =
  JObject (("operator" , JString "atomic") ∷
           ("predicate" , JObject (formatSignalPredicateFields p)) ∷ [])
formatLTL (LTL.Not f) =
  JObject (("operator" , JString "not") ∷
           ("formula" , formatLTL f) ∷ [])
formatLTL (LTL.And f g) =
  JObject (("operator" , JString "and") ∷
           ("left" , formatLTL f) ∷ ("right" , formatLTL g) ∷ [])
formatLTL (LTL.Or f g) =
  JObject (("operator" , JString "or") ∷
           ("left" , formatLTL f) ∷ ("right" , formatLTL g) ∷ [])
formatLTL (LTL.Next f) =
  JObject (("operator" , JString "next") ∷
           ("formula" , formatLTL f) ∷ [])
formatLTL (LTL.Always f) =
  JObject (("operator" , JString "always") ∷
           ("formula" , formatLTL f) ∷ [])
formatLTL (LTL.Eventually f) =
  JObject (("operator" , JString "eventually") ∷
           ("formula" , formatLTL f) ∷ [])
formatLTL (LTL.Until f g) =
  JObject (("operator" , JString "until") ∷
           ("left" , formatLTL f) ∷ ("right" , formatLTL g) ∷ [])
formatLTL (LTL.Release f g) =
  JObject (("operator" , JString "release") ∷
           ("left" , formatLTL f) ∷ ("right" , formatLTL g) ∷ [])
formatLTL (LTL.MetricEventually n _ f) =
  JObject (("operator" , JString "metricEventually") ∷
           ("timebound" , JNumber (ℕtoℚ n)) ∷
           ("formula" , formatLTL f) ∷ [])
formatLTL (LTL.MetricAlways n _ f) =
  JObject (("operator" , JString "metricAlways") ∷
           ("timebound" , JNumber (ℕtoℚ n)) ∷
           ("formula" , formatLTL f) ∷ [])
formatLTL (LTL.MetricUntil n _ f g) =
  JObject (("operator" , JString "metricUntil") ∷
           ("timebound" , JNumber (ℕtoℚ n)) ∷
           ("left" , formatLTL f) ∷ ("right" , formatLTL g) ∷ [])
formatLTL (LTL.MetricRelease n _ f g) =
  JObject (("operator" , JString "metricRelease") ∷
           ("timebound" , JNumber (ℕtoℚ n)) ∷
           ("left" , formatLTL f) ∷ ("right" , formatLTL g) ∷ [])

