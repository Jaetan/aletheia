{-# OPTIONS --safe --without-K #-}

-- Formatter and depth function for LTL formulas with signal predicates.
--
-- Purpose: Convert LTL formulas back to JSON for roundtrip proofs.
-- Produces canonical JSON that the parser in Aletheia.LTL.JSON can parse back.
-- Role: Foundation for roundtrip correctness proofs in LTL.JSON.Properties.
module Aletheia.LTL.JSON.Format where

open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; suc; zero; _⊔_)
open import Data.Integer using (+_)
open import Data.Rational using (ℚ; mkℚ)
open import Data.Nat.Coprimality using (sym; 1-coprimeTo)
open import Data.Product using (_×_; _,_)
open import Aletheia.Protocol.JSON using (JSON; JNull; JBool; JNumber; JString; JArray; JObject)
open import Aletheia.LTL.Syntax using (LTL)
open import Aletheia.LTL.SignalPredicate using (SignalPredicate)

-- ============================================================================
-- NATURAL TO RATIONAL (proof-friendly)
-- ============================================================================

-- Convert ℕ to ℚ using mkℚ directly (bypasses GCD normalization in _/_).
-- This allows toℚᵘ to reduce by definition: toℚᵘ (mkℚ (+ n) 0 _) = mkℚᵘ (+ n) 0
-- Critical for the roundtrip proofs of metric operators.
ℕtoℚ : ℕ → ℚ
ℕtoℚ n = mkℚ (+ n) 0 (sym (1-coprimeTo n))

-- ============================================================================
-- SIGNAL PREDICATE FORMATTER
-- ============================================================================

-- Format a SignalPredicate as a list of JSON fields (canonical order).
-- Field order matches what the parser expects: "predicate" first, then signal/value fields.
formatSignalPredicateFields : SignalPredicate → List (String × JSON)
formatSignalPredicateFields (SignalPredicate.Equals s v) =
  ("predicate" , JString "equals") ∷ ("signal" , JString s) ∷ ("value" , JNumber v) ∷ []
formatSignalPredicateFields (SignalPredicate.LessThan s v) =
  ("predicate" , JString "lessThan") ∷ ("signal" , JString s) ∷ ("value" , JNumber v) ∷ []
formatSignalPredicateFields (SignalPredicate.GreaterThan s v) =
  ("predicate" , JString "greaterThan") ∷ ("signal" , JString s) ∷ ("value" , JNumber v) ∷ []
formatSignalPredicateFields (SignalPredicate.LessThanOrEqual s v) =
  ("predicate" , JString "lessThanOrEqual") ∷ ("signal" , JString s) ∷ ("value" , JNumber v) ∷ []
formatSignalPredicateFields (SignalPredicate.GreaterThanOrEqual s v) =
  ("predicate" , JString "greaterThanOrEqual") ∷ ("signal" , JString s) ∷ ("value" , JNumber v) ∷ []
formatSignalPredicateFields (SignalPredicate.Between s min max) =
  ("predicate" , JString "between") ∷ ("signal" , JString s) ∷ ("min" , JNumber min) ∷ ("max" , JNumber max) ∷ []
formatSignalPredicateFields (SignalPredicate.ChangedBy s d) =
  ("predicate" , JString "changedBy") ∷ ("signal" , JString s) ∷ ("delta" , JNumber d) ∷ []

-- Format a SignalPredicate as a JSON object
formatSignalPredicate : SignalPredicate → JSON
formatSignalPredicate p = JObject (formatSignalPredicateFields p)

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
formatLTL (LTL.MetricEventually n f) =
  JObject (("operator" , JString "metricEventually") ∷
           ("timebound" , JNumber (ℕtoℚ n)) ∷
           ("formula" , formatLTL f) ∷ [])
formatLTL (LTL.MetricAlways n f) =
  JObject (("operator" , JString "metricAlways") ∷
           ("timebound" , JNumber (ℕtoℚ n)) ∷
           ("formula" , formatLTL f) ∷ [])
formatLTL (LTL.MetricUntil n f g) =
  JObject (("operator" , JString "metricUntil") ∷
           ("timebound" , JNumber (ℕtoℚ n)) ∷
           ("left" , formatLTL f) ∷ ("right" , formatLTL g) ∷ [])
formatLTL (LTL.MetricRelease n f g) =
  JObject (("operator" , JString "metricRelease") ∷
           ("timebound" , JNumber (ℕtoℚ n)) ∷
           ("left" , formatLTL f) ∷ ("right" , formatLTL g) ∷ [])

-- ============================================================================
-- DEPTH FUNCTION
-- ============================================================================

-- Compute the minimum depth required to parse a formatted LTL formula.
-- The parser consumes depth at three points per nesting level:
--   parseLTL (1 suc), parseLTLObject (1 suc), parseUnary/parseBinary (1 suc)
-- Atomic formulas need only 2 (parseAtomic doesn't consume depth).
ltlDepth : LTL SignalPredicate → ℕ
ltlDepth (LTL.Atomic _)              = 2
ltlDepth (LTL.Not f)                 = suc (suc (suc (ltlDepth f)))
ltlDepth (LTL.And f g)               = suc (suc (suc (ltlDepth f ⊔ ltlDepth g)))
ltlDepth (LTL.Or f g)                = suc (suc (suc (ltlDepth f ⊔ ltlDepth g)))
ltlDepth (LTL.Next f)                = suc (suc (suc (ltlDepth f)))
ltlDepth (LTL.Always f)              = suc (suc (suc (ltlDepth f)))
ltlDepth (LTL.Eventually f)          = suc (suc (suc (ltlDepth f)))
ltlDepth (LTL.Until f g)             = suc (suc (suc (ltlDepth f ⊔ ltlDepth g)))
ltlDepth (LTL.Release f g)           = suc (suc (suc (ltlDepth f ⊔ ltlDepth g)))
ltlDepth (LTL.MetricEventually _ f)  = suc (suc (suc (ltlDepth f)))
ltlDepth (LTL.MetricAlways _ f)      = suc (suc (suc (ltlDepth f)))
ltlDepth (LTL.MetricUntil _ f g)     = suc (suc (suc (ltlDepth f ⊔ ltlDepth g)))
ltlDepth (LTL.MetricRelease _ f g)   = suc (suc (suc (ltlDepth f ⊔ ltlDepth g)))
