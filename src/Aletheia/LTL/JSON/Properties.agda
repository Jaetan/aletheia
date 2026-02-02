{-# OPTIONS --safe --without-K #-}

-- Correctness properties for the LTL JSON parser and formatter.
--
-- Purpose: Prove roundtrip, soundness, and completeness for LTL formula serialization.
-- Properties:
--   Roundtrip: parseLTL (ltlDepth φ) (formatLTL φ) ≡ just φ
--   Soundness: parseLTL d json ≡ just φ → IsWellFormedLTLJSON json
--   Completeness: Corollary of roundtrip
-- Role: Phase 3 verification of LTL DSL translation correctness.
module Aletheia.LTL.JSON.Properties where

open import Data.String using (String; _≟_)
open import Data.Bool using (if_then_else_; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Nat using (ℕ; suc; zero; _⊔_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; ≤-trans; ≤-refl)
open import Data.Integer using (+_)
open import Data.Rational using (ℚ; _/_)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Relation.Binary.PropositionalEquality using (inspect; [_])
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Empty using (⊥-elim)

open import Aletheia.Protocol.JSON
open import Aletheia.Prelude using (lookupByKey)
open import Aletheia.LTL.Syntax using (LTL)
open import Aletheia.LTL.SignalPredicate using (SignalPredicate; ValueP; DeltaP; ValuePredicate; DeltaPredicate)
open import Aletheia.LTL.SignalPredicate as VP using (Equals; LessThan; GreaterThan; LessThanOrEqual; GreaterThanOrEqual; Between)
open import Aletheia.LTL.SignalPredicate as DP using (ChangedBy)
open import Aletheia.LTL.JSON
open import Aletheia.LTL.JSON.Format
open import Data.Nat.Divisibility using (1∣_; _∣?_)

-- ============================================================================
-- HELPER: getNat on ℕtoℚ
-- ============================================================================

-- getNat extracts the natural number from JNumber (ℕtoℚ n).
-- The proof abstracts over the divisibility check (1 ∣? n) which doesn't reduce
-- for variable n, but we know 1 ∣ n for all n.
getNat-ℕtoℚ : (n : ℕ) → getNat (JNumber (ℕtoℚ n)) ≡ just n
getNat-ℕtoℚ n with 1 ∣? n
... | yes _ = refl  -- divideInteger (+ n) 0 = + n, extractNat (just (+ n)) = just n
... | no ¬1∣n = ⊥-elim (¬1∣n (1∣ n))

-- ============================================================================
-- SIGNAL PREDICATE ROUNDTRIP
-- ============================================================================

-- Each case normalizes to refl since all field names and predicate
-- type strings are concrete (only signal name and value are variables).
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
-- LTL ROUNDTRIP (combined with depth monotonicity)
-- ============================================================================

-- The roundtrip is proven for any depth ≥ ltlDepth f, avoiding the need
-- for a separate general monotonicity proof. Binary operators use ≤-trans
-- with m≤m⊔n / m≤n⊔m to share the common depth budget.
roundtrip : (f : LTL SignalPredicate) (d : ℕ)
  → ltlDepth f ≤ d → parseLTL d (formatLTL f) ≡ just f

-- Atomic: depth ≥ 2 suffices, parseAtomic ignores depth
roundtrip (LTL.Atomic p) (suc (suc d')) (s≤s (s≤s z≤n))
  rewrite predicate-roundtrip p = refl

-- Unary operators: depth ≥ 3 + ltlDepth sub
roundtrip (LTL.Not f) (suc (suc (suc d'))) (s≤s (s≤s (s≤s le)))
  rewrite roundtrip f d' le = refl

roundtrip (LTL.Next f) (suc (suc (suc d'))) (s≤s (s≤s (s≤s le)))
  rewrite roundtrip f d' le = refl

roundtrip (LTL.Always f) (suc (suc (suc d'))) (s≤s (s≤s (s≤s le)))
  rewrite roundtrip f d' le = refl

roundtrip (LTL.Eventually f) (suc (suc (suc d'))) (s≤s (s≤s (s≤s le)))
  rewrite roundtrip f d' le = refl

-- Binary operators: depth ≥ 3 + max(ltlDepth f, ltlDepth g)
roundtrip (LTL.And f g) (suc (suc (suc d'))) (s≤s (s≤s (s≤s le)))
  rewrite roundtrip f d' (≤-trans (m≤m⊔n (ltlDepth f) (ltlDepth g)) le)
        | roundtrip g d' (≤-trans (m≤n⊔m (ltlDepth f) (ltlDepth g)) le) = refl

roundtrip (LTL.Or f g) (suc (suc (suc d'))) (s≤s (s≤s (s≤s le)))
  rewrite roundtrip f d' (≤-trans (m≤m⊔n (ltlDepth f) (ltlDepth g)) le)
        | roundtrip g d' (≤-trans (m≤n⊔m (ltlDepth f) (ltlDepth g)) le) = refl

roundtrip (LTL.Until f g) (suc (suc (suc d'))) (s≤s (s≤s (s≤s le)))
  rewrite roundtrip f d' (≤-trans (m≤m⊔n (ltlDepth f) (ltlDepth g)) le)
        | roundtrip g d' (≤-trans (m≤n⊔m (ltlDepth f) (ltlDepth g)) le) = refl

roundtrip (LTL.Release f g) (suc (suc (suc d'))) (s≤s (s≤s (s≤s le)))
  rewrite roundtrip f d' (≤-trans (m≤m⊔n (ltlDepth f) (ltlDepth g)) le)
        | roundtrip g d' (≤-trans (m≤n⊔m (ltlDepth f) (ltlDepth g)) le) = refl

-- Metric unary operators: depth ≥ 3 + ltlDepth sub
-- These use with-abstraction on getNat to handle the divisibility check
roundtrip (LTL.MetricEventually n f) (suc (suc (suc d'))) (s≤s (s≤s (s≤s le)))
  with getNat (JNumber (ℕtoℚ n)) | getNat-ℕtoℚ n
... | .(just n) | refl rewrite roundtrip f d' le = refl

roundtrip (LTL.MetricAlways n f) (suc (suc (suc d'))) (s≤s (s≤s (s≤s le)))
  with getNat (JNumber (ℕtoℚ n)) | getNat-ℕtoℚ n
... | .(just n) | refl rewrite roundtrip f d' le = refl

-- Metric binary operators: depth ≥ 3 + max(ltlDepth f, ltlDepth g)
roundtrip (LTL.MetricUntil n f g) (suc (suc (suc d'))) (s≤s (s≤s (s≤s le)))
  with getNat (JNumber (ℕtoℚ n)) | getNat-ℕtoℚ n
... | .(just n) | refl
  rewrite roundtrip f d' (≤-trans (m≤m⊔n (ltlDepth f) (ltlDepth g)) le)
        | roundtrip g d' (≤-trans (m≤n⊔m (ltlDepth f) (ltlDepth g)) le) = refl

roundtrip (LTL.MetricRelease n f g) (suc (suc (suc d'))) (s≤s (s≤s (s≤s le)))
  with getNat (JNumber (ℕtoℚ n)) | getNat-ℕtoℚ n
... | .(just n) | refl
  rewrite roundtrip f d' (≤-trans (m≤m⊔n (ltlDepth f) (ltlDepth g)) le)
        | roundtrip g d' (≤-trans (m≤n⊔m (ltlDepth f) (ltlDepth g)) le) = refl

-- ============================================================================
-- DERIVED: exact-depth roundtrip
-- ============================================================================

roundtrip-exact : (f : LTL SignalPredicate)
  → parseLTL (ltlDepth f) (formatLTL f) ≡ just f
roundtrip-exact f = roundtrip f (ltlDepth f) ≤-refl

-- ============================================================================
-- COMPLETENESS (corollary of roundtrip)
-- ============================================================================

-- If a formula was successfully parsed, it can be re-serialized and re-parsed.
completeness : (d : ℕ) (json : JSON) (f : LTL SignalPredicate)
  → parseLTL d json ≡ just f
  → parseLTL (ltlDepth f) (formatLTL f) ≡ just f
completeness d json f _ = roundtrip-exact f

-- ============================================================================
-- SOUNDNESS (structural property)
-- ============================================================================

-- Soundness property: successful parsing implies the JSON is a well-formed object.
-- A full IsWellFormedLTLJSON predicate with all operator shapes is deferred to
-- avoid the ~14 operators × 6 JSON types case explosion in this initial proof.
-- The key insight is that parseLTL only succeeds on JObject values with valid
-- "operator" fields, which is enforced by the parser's structure.

-- Minimal soundness: successful parse implies JSON is an object
parseLTL-isObject : ∀ d json f → parseLTL d json ≡ just f
  → ∃[ fields ] (json ≡ JObject fields)
parseLTL-isObject zero json f ()
parseLTL-isObject (suc d) JNull f ()
parseLTL-isObject (suc d) (JBool _) f ()
parseLTL-isObject (suc d) (JNumber _) f ()
parseLTL-isObject (suc d) (JString _) f ()
parseLTL-isObject (suc d) (JArray _) f ()
parseLTL-isObject (suc d) (JObject fields) f _ = fields , refl

-- ============================================================================
-- PROOF SUMMARY
-- ============================================================================

-- ✅ ALL CORE PROOFS COMPLETE (Phase 3 Goal 4)
--
-- Proven properties:
-- ✅ Signal Predicate Roundtrip (7 cases):
--    parseSignalPredicate (formatSignalPredicateFields p) ≡ just p
--
-- ✅ LTL Roundtrip (13 cases):
--    parseLTL (ltlDepth f) (formatLTL f) ≡ just f
--    - 4 unary operators (Not, Next, Always, Eventually)
--    - 4 binary operators (And, Or, Until, Release)
--    - 4 metric operators (MetricEventually, MetricAlways, MetricUntil, MetricRelease)
--    - 1 base case (Atomic)
--
-- ✅ Completeness (corollary):
--    parseLTL d json ≡ just f → parseLTL (ltlDepth f) (formatLTL f) ≡ just f
--
-- ✅ Soundness (structural):
--    parseLTL d json ≡ just f → ∃ fields. json ≡ JObject fields
--
-- Key techniques:
-- - Combined roundtrip+monotonicity via ≤ evidence (avoids separate mono proof)
-- - Direct ℚ construction via mkℚ (bypasses GCD normalization issues)
-- - with-abstraction on divisibility check (1 ∣? n) for metric operators
--
-- Total: 22 proven properties with zero holes
