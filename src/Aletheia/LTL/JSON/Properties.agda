-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Correctness properties for the LTL JSON parser and formatter.
--
-- The parser reads signal names against `known`, the loaded DBC's signals,
-- and decides every time bound against `max-time-bound`, so the round trip
-- holds for a formula whose every signal is known and every time bound within
-- its limit:
--   Roundtrip: Readable known φ → parseLTL known (formatLTL φ) ≡ inj₂ (resetStart φ)
--   Soundness: parseLTL known json ≡ inj₂ φ → json is a JObject
--
-- Note: resetStart zeros out the startTime parameter in metric operators.
-- formatLTL ignores startTime; the parser always produces startTime=0.
-- For user-facing formulas (always startTime=0), resetStart f ≡ f.
module Aletheia.LTL.JSON.Properties where

open import Data.Bool using (Bool; true; T; T?)
open import Data.Bool.Properties using (T-irrelevant)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (_≤_) renaming (_≤ᵇ_ to _≤ᵇℕ_)
open import Data.Nat.Properties using (≤⇒≤ᵇ)
open import Data.Rational using (0ℚ; _≤ᵇ_)
open import Relation.Nullary using (yes; no)
open import Aletheia.Limits using (max-time-bound)
open import Data.Char using (Char)
open import Data.List using (List)
open import Data.Maybe using (just)
open import Data.Sum using (inj₂)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Aletheia.JSON using (JNull; JBool; JNumber; JString; JArray; JObject; getNat)
open import Aletheia.Prelude using (ℕtoℚ)
open import Aletheia.Trace.Time using (tsValue)
open import Aletheia.JSON.Properties using (getNat-ℕtoℚ)
open import Aletheia.LTL.Syntax using (LTL)
open import Aletheia.LTL.SignalPredicate using (SignalPredicate; ValueP; DeltaP; Equals; LessThan; GreaterThan; LessThanOrEqual; GreaterThanOrEqual; Between; ChangedBy; StableWithin; signalOf)
open import Aletheia.LTL.JSON using (parseLTL; parseSub; parseSignalPredicate; ordered; tolerant; timeBound)
open import Aletheia.LTL.JSON.Format using (formatLTL; formatSignalPredicateFields)
open import Aletheia.DBC.JSONParser using (validateIdent-on-valid)

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

-- The signals `setProperties` admits: each is a signal of the loaded DBC.
-- The length and the keyword are inside every `Identifier` already.
KnownPredicate : (List Char → Bool) → SignalPredicate → Set
KnownPredicate known p = known (signalOf p) ≡ true

-- What the parser reads back: every signal known, every time bound within
-- its limit.
Readable : (List Char → Bool) → LTL SignalPredicate → Set
Readable known (LTL.Atomic p) = KnownPredicate known p
Readable known (LTL.Not f) = Readable known f
Readable known (LTL.And f g) = Readable known f × Readable known g
Readable known (LTL.Or f g) = Readable known f × Readable known g
Readable known (LTL.Next f) = Readable known f
Readable known (LTL.WNext f) = Readable known f
Readable known (LTL.Always f) = Readable known f
Readable known (LTL.Eventually f) = Readable known f
Readable known (LTL.Until f g) = Readable known f × Readable known g
Readable known (LTL.Release f g) = Readable known f × Readable known g
Readable known (LTL.MetricEventually n _ f) = tsValue n ≤ max-time-bound × Readable known f
Readable known (LTL.MetricAlways n _ f) = tsValue n ≤ max-time-bound × Readable known f
Readable known (LTL.MetricUntil n _ f g) = tsValue n ≤ max-time-bound × Readable known f × Readable known g
Readable known (LTL.MetricRelease n _ f g) = tsValue n ≤ max-time-bound × Readable known f × Readable known g

-- ============================================================================
-- VALUE DECISIONS ON A FORMATTED VALUE
-- ============================================================================

-- A range the predicate carries in order is read back in order, its
-- decision the one it carried.
ordered-yes : ∀ s lo hi (w : T (lo ≤ᵇ hi)) → ordered s lo hi ≡ inj₂ (ValueP (Between s lo hi w))
ordered-yes s lo hi w with T? (lo ≤ᵇ hi)
... | yes w′ = cong (λ v → inj₂ (ValueP (Between s lo hi v))) (T-irrelevant w′ w)
... | no ¬w  = ⊥-elim (¬w w)

tolerant-yes : ∀ s tol (w : T (0ℚ ≤ᵇ tol)) → tolerant s tol ≡ inj₂ (DeltaP (StableWithin s tol w))
tolerant-yes s tol w with T? (0ℚ ≤ᵇ tol)
... | yes w′ = cong (λ v → inj₂ (DeltaP (StableWithin s tol v))) (T-irrelevant w′ w)
... | no ¬w  = ⊥-elim (¬w w)

-- A whole time bound within its limit is read back as itself.
timeBound-ℕ : ∀ n → n ≤ max-time-bound → timeBound (ℕtoℚ n) ≡ inj₂ n
timeBound-ℕ n n≤ with getNat (JNumber (ℕtoℚ n)) | getNat-ℕtoℚ n
... | .(just n) | refl with T? (n ≤ᵇℕ max-time-bound)
...   | yes _ = refl
...   | no ¬w = ⊥-elim (¬w (≤⇒≤ᵇ n≤))

predicate-roundtrip : ∀ (known : List Char → Bool) (p : SignalPredicate)
  → KnownPredicate known p
  → parseSignalPredicate known (formatSignalPredicateFields p) ≡ inj₂ p
predicate-roundtrip known (ValueP (Equals s v)) has rewrite validateIdent-on-valid s | has = refl
predicate-roundtrip known (ValueP (LessThan s v)) has rewrite validateIdent-on-valid s | has = refl
predicate-roundtrip known (ValueP (GreaterThan s v)) has rewrite validateIdent-on-valid s | has = refl
predicate-roundtrip known (ValueP (LessThanOrEqual s v)) has rewrite validateIdent-on-valid s | has = refl
predicate-roundtrip known (ValueP (GreaterThanOrEqual s v)) has rewrite validateIdent-on-valid s | has = refl
predicate-roundtrip known (ValueP (Between s min max w)) has
  rewrite validateIdent-on-valid s | has | ordered-yes s min max w = refl
predicate-roundtrip known (DeltaP (ChangedBy s d)) has rewrite validateIdent-on-valid s | has = refl
predicate-roundtrip known (DeltaP (StableWithin s t w)) has
  rewrite validateIdent-on-valid s | has | tolerant-yes s t w = refl

-- A formatted formula is an object, so a sub-formula reads as a property does.
parseSub-formatLTL : ∀ known key f → parseSub known key (formatLTL f) ≡ parseLTL known (formatLTL f)
parseSub-formatLTL _ _ (LTL.Atomic _) = refl
parseSub-formatLTL _ _ (LTL.Not _) = refl
parseSub-formatLTL _ _ (LTL.And _ _) = refl
parseSub-formatLTL _ _ (LTL.Or _ _) = refl
parseSub-formatLTL _ _ (LTL.Next _) = refl
parseSub-formatLTL _ _ (LTL.WNext _) = refl
parseSub-formatLTL _ _ (LTL.Always _) = refl
parseSub-formatLTL _ _ (LTL.Eventually _) = refl
parseSub-formatLTL _ _ (LTL.Until _ _) = refl
parseSub-formatLTL _ _ (LTL.Release _ _) = refl
parseSub-formatLTL _ _ (LTL.MetricEventually _ _ _) = refl
parseSub-formatLTL _ _ (LTL.MetricAlways _ _ _) = refl
parseSub-formatLTL _ _ (LTL.MetricUntil _ _ _ _) = refl
parseSub-formatLTL _ _ (LTL.MetricRelease _ _ _ _) = refl

-- ============================================================================
-- LTL ROUNDTRIP
-- ============================================================================

-- No depth parameter needed: parseLTL is structurally recursive on JSON input.
-- Each case reduces by computation (string comparisons on concrete operator names)
-- plus the induction hypothesis on sub-formulas.
roundtrip : ∀ (known : List Char → Bool) (f : LTL SignalPredicate)
  → Readable known f
  → parseLTL known (formatLTL f) ≡ inj₂ (resetStart f)

roundtrip known (LTL.Atomic p) k
  rewrite predicate-roundtrip known p k = refl

roundtrip known (LTL.Not f) k
  rewrite parseSub-formatLTL known "formula" f | roundtrip known f k = refl

roundtrip known (LTL.Next f) k
  rewrite parseSub-formatLTL known "formula" f | roundtrip known f k = refl

roundtrip known (LTL.WNext f) k
  rewrite parseSub-formatLTL known "formula" f | roundtrip known f k = refl

roundtrip known (LTL.Always f) k
  rewrite parseSub-formatLTL known "formula" f | roundtrip known f k = refl

roundtrip known (LTL.Eventually f) k
  rewrite parseSub-formatLTL known "formula" f | roundtrip known f k = refl

roundtrip known (LTL.And f g) (kf , kg)
  rewrite parseSub-formatLTL known "left" f | parseSub-formatLTL known "right" g
        | roundtrip known f kf | roundtrip known g kg = refl

roundtrip known (LTL.Or f g) (kf , kg)
  rewrite parseSub-formatLTL known "left" f | parseSub-formatLTL known "right" g
        | roundtrip known f kf | roundtrip known g kg = refl

roundtrip known (LTL.Until f g) (kf , kg)
  rewrite parseSub-formatLTL known "left" f | parseSub-formatLTL known "right" g
        | roundtrip known f kf | roundtrip known g kg = refl

roundtrip known (LTL.Release f g) (kf , kg)
  rewrite parseSub-formatLTL known "left" f | parseSub-formatLTL known "right" g
        | roundtrip known f kf | roundtrip known g kg = refl

-- Metric operators: the time bound is read back by `timeBound-ℕ` within its
-- limit.  The window is unwrapped via `tsValue` at the formatter and
-- re-wrapped via `mkTs` by the parser; `mkTs (tsValue n) ≡ n` by `Timestamp`
-- record η.
-- INVARIANT: `Timestamp` stays a record with η (no `data`, no private
-- constructor, no erasure boundary), or this roundtrip stops reducing.
roundtrip known (LTL.MetricEventually n _ f) (n≤ , k)
  rewrite timeBound-ℕ (tsValue n) n≤ | parseSub-formatLTL known "formula" f
        | roundtrip known f k = refl

roundtrip known (LTL.MetricAlways n _ f) (n≤ , k)
  rewrite timeBound-ℕ (tsValue n) n≤ | parseSub-formatLTL known "formula" f
        | roundtrip known f k = refl

roundtrip known (LTL.MetricUntil n _ f g) (n≤ , kf , kg)
  rewrite timeBound-ℕ (tsValue n) n≤
        | parseSub-formatLTL known "left" f | parseSub-formatLTL known "right" g
        | roundtrip known f kf | roundtrip known g kg = refl

roundtrip known (LTL.MetricRelease n _ f g) (n≤ , kf , kg)
  rewrite timeBound-ℕ (tsValue n) n≤
        | parseSub-formatLTL known "left" f | parseSub-formatLTL known "right" g
        | roundtrip known f kf | roundtrip known g kg = refl

-- ============================================================================
-- SOUNDNESS (structural property)
-- ============================================================================

-- A successful parse implies the JSON is an object: `parseLTL` succeeds on
-- `JObject` values only.
parseLTL-isObject : ∀ (known : List Char → Bool) json f → parseLTL known json ≡ inj₂ f
  → ∃[ fields ] (json ≡ JObject fields)
parseLTL-isObject _ JNull f ()
parseLTL-isObject _ (JBool _) f ()
parseLTL-isObject _ (JNumber _) f ()
parseLTL-isObject _ (JString _) f ()
parseLTL-isObject _ (JArray _) f ()
parseLTL-isObject _ (JObject fields) f _ = fields , refl
