-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Correctness properties for the LTL JSON parser and formatter.
--
-- The parser reads signal names against `known`, the loaded DBC's signals,
-- so the round trip holds for a formula whose every signal is known:
--   Roundtrip: KnownSignals known φ → parseLTL known (formatLTL φ) ≡ inj₂ (resetStart φ)
--   Soundness: parseLTL known json ≡ inj₂ φ → json is a JObject
--
-- Note: resetStart zeros out the startTime parameter in metric operators.
-- formatLTL ignores startTime; the parser always produces startTime=0.
-- For user-facing formulas (always startTime=0), resetStart f ≡ f.
module Aletheia.LTL.JSON.Properties where

open import Data.Bool using (Bool; true)
open import Data.Char using (Char)
open import Data.List using (List)
open import Data.Maybe using (just)
open import Data.Sum using (inj₂)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Aletheia.JSON using (JNull; JBool; JNumber; JString; JArray; JObject; getNat)
open import Aletheia.Prelude using (ℕtoℚ)
open import Aletheia.Trace.Time using (tsValue)
open import Aletheia.JSON.Properties using (getNat-ℕtoℚ)
open import Aletheia.LTL.Syntax using (LTL)
open import Aletheia.LTL.SignalPredicate using (SignalPredicate; ValueP; DeltaP; Equals; LessThan; GreaterThan; LessThanOrEqual; GreaterThanOrEqual; Between; ChangedBy; StableWithin; signalOf)
open import Aletheia.LTL.JSON using (parseLTL; parseSignalPredicate)
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

KnownSignals : (List Char → Bool) → LTL SignalPredicate → Set
KnownSignals known (LTL.Atomic p) = KnownPredicate known p
KnownSignals known (LTL.Not f) = KnownSignals known f
KnownSignals known (LTL.And f g) = KnownSignals known f × KnownSignals known g
KnownSignals known (LTL.Or f g) = KnownSignals known f × KnownSignals known g
KnownSignals known (LTL.Next f) = KnownSignals known f
KnownSignals known (LTL.WNext f) = KnownSignals known f
KnownSignals known (LTL.Always f) = KnownSignals known f
KnownSignals known (LTL.Eventually f) = KnownSignals known f
KnownSignals known (LTL.Until f g) = KnownSignals known f × KnownSignals known g
KnownSignals known (LTL.Release f g) = KnownSignals known f × KnownSignals known g
KnownSignals known (LTL.MetricEventually _ _ f) = KnownSignals known f
KnownSignals known (LTL.MetricAlways _ _ f) = KnownSignals known f
KnownSignals known (LTL.MetricUntil _ _ f g) = KnownSignals known f × KnownSignals known g
KnownSignals known (LTL.MetricRelease _ _ f g) = KnownSignals known f × KnownSignals known g

predicate-roundtrip : ∀ (known : List Char → Bool) (p : SignalPredicate)
  → KnownPredicate known p
  → parseSignalPredicate known (formatSignalPredicateFields p) ≡ inj₂ p
predicate-roundtrip known (ValueP (Equals s v)) has rewrite validateIdent-on-valid s | has = refl
predicate-roundtrip known (ValueP (LessThan s v)) has rewrite validateIdent-on-valid s | has = refl
predicate-roundtrip known (ValueP (GreaterThan s v)) has rewrite validateIdent-on-valid s | has = refl
predicate-roundtrip known (ValueP (LessThanOrEqual s v)) has rewrite validateIdent-on-valid s | has = refl
predicate-roundtrip known (ValueP (GreaterThanOrEqual s v)) has rewrite validateIdent-on-valid s | has = refl
predicate-roundtrip known (ValueP (Between s min max)) has rewrite validateIdent-on-valid s | has = refl
predicate-roundtrip known (DeltaP (ChangedBy s d)) has rewrite validateIdent-on-valid s | has = refl
predicate-roundtrip known (DeltaP (StableWithin s t)) has rewrite validateIdent-on-valid s | has = refl

-- ============================================================================
-- LTL ROUNDTRIP
-- ============================================================================

-- No depth parameter needed: parseLTL is structurally recursive on JSON input.
-- Each case reduces by computation (string comparisons on concrete operator names)
-- plus the induction hypothesis on sub-formulas.
roundtrip : ∀ (known : List Char → Bool) (f : LTL SignalPredicate)
  → KnownSignals known f
  → parseLTL known (formatLTL f) ≡ inj₂ (resetStart f)

roundtrip known (LTL.Atomic p) k
  rewrite predicate-roundtrip known p k = refl

roundtrip known (LTL.Not f) k
  rewrite roundtrip known f k = refl

roundtrip known (LTL.Next f) k
  rewrite roundtrip known f k = refl

roundtrip known (LTL.WNext f) k
  rewrite roundtrip known f k = refl

roundtrip known (LTL.Always f) k
  rewrite roundtrip known f k = refl

roundtrip known (LTL.Eventually f) k
  rewrite roundtrip known f k = refl

roundtrip known (LTL.And f g) (kf , kg)
  rewrite roundtrip known f kf | roundtrip known g kg = refl

roundtrip known (LTL.Or f g) (kf , kg)
  rewrite roundtrip known f kf | roundtrip known g kg = refl

roundtrip known (LTL.Until f g) (kf , kg)
  rewrite roundtrip known f kf | roundtrip known g kg = refl

roundtrip known (LTL.Release f g) (kf , kg)
  rewrite roundtrip known f kf | roundtrip known g kg = refl

-- Metric operators: `getNat` abstraction needed for the ℕtoℚ roundtrip.  The
-- window is unwrapped via `tsValue` at the formatter and re-wrapped via
-- `mkTs` by the parser; `mkTs (tsValue n) ≡ n` by `Timestamp` record η.
-- INVARIANT: `Timestamp` stays a record with η (no `data`, no private
-- constructor, no erasure boundary), or this roundtrip stops reducing.
roundtrip known (LTL.MetricEventually n _ f) k
  with getNat (JNumber (ℕtoℚ (tsValue n))) | getNat-ℕtoℚ (tsValue n)
... | .(just (tsValue n)) | refl rewrite roundtrip known f k = refl

roundtrip known (LTL.MetricAlways n _ f) k
  with getNat (JNumber (ℕtoℚ (tsValue n))) | getNat-ℕtoℚ (tsValue n)
... | .(just (tsValue n)) | refl rewrite roundtrip known f k = refl

roundtrip known (LTL.MetricUntil n _ f g) (kf , kg)
  with getNat (JNumber (ℕtoℚ (tsValue n))) | getNat-ℕtoℚ (tsValue n)
... | .(just (tsValue n)) | refl
  rewrite roundtrip known f kf | roundtrip known g kg = refl

roundtrip known (LTL.MetricRelease n _ f g) (kf , kg)
  with getNat (JNumber (ℕtoℚ (tsValue n))) | getNat-ℕtoℚ (tsValue n)
... | .(just (tsValue n)) | refl
  rewrite roundtrip known f kf | roundtrip known g kg = refl

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
