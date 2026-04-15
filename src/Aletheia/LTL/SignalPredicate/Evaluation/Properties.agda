{-# OPTIONS --safe --without-K #-}

-- Cache → predicate-definiteness bridge.
--
-- Purpose: Prove that when a signal predicate's target signal already has a
-- cache entry, `evalPredicateTV` yields a definite (True/False) verdict —
-- never `Unknown` or `Pending`. This is the "warm cache" guarantee that
-- bridges runtime signal cache state to the two-valued precondition of the
-- `agreement` theorem in `Adequacy.Agreement`.
--
-- Exports:
--   * signalOf — associate a SignalPredicate with its target signal name.
--   * fromBool-definite — every `fromBool b` result is True or False.
--   * getTruthValue-cache-just — cache hit ⇒ getTruthValue yields `just _`.
--   * evalValue-cache-definite — cache hit ⇒ value predicate is definite.
--   * evalDelta-cache-definite — cache hit ⇒ delta predicate is definite.
--   * evalPredicate-cache-definite — cache hit ⇒ any predicate is definite.
--
-- Proof strategy: the direct `with`/`rewrite` approach runs into Agda's
-- syntactic-matching limitations — `evalValuePredicateTV` and `getTruthValue`
-- unfold to nested `case_of_` lambdas where the abstraction finds fewer
-- occurrences than it should (and the `hit` equation's `lookupCache` form
-- doesn't line up with the `lookupEntries …` form the normalizer produces).
-- Instead, we introduce pattern-matching helpers (`valueAt`, `deltaAt`) that
-- mirror the bodies of the `TV` functions but take already-resolved `Maybe ℚ`
-- arguments. A pointwise unfolding lemma (`evalValuePredicateTV-unfold`,
-- `evalDeltaPredicateTV-unfold`) bridges between the two forms via `with` +
-- `refl`. The main lemmas then compose `cong`/`cong₂` + `trans` on the
-- unfolding lemma and the cache-hit equation entirely at the term level —
-- no `with` or `rewrite` touches the headline goal.
--
-- Role: Closes review finding C3. Once every atomic predicate's signal has
-- been observed (cached) at least once, the four-valued monitor operates in
-- the two-valued regime where `agreement : runL ≡ ⟦_⟧` holds (provided the
-- table is assembled from `evalPredicateTV` rather than raw `Unknown`).
module Aletheia.LTL.SignalPredicate.Evaluation.Properties where

open import Aletheia.Prelude
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (∃-syntax; _,_)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong; cong₂)

open import Aletheia.CAN.Frame using (CANFrame)
open import Aletheia.DBC.Types using (DBC)

open import Aletheia.LTL.SignalPredicate.Types
open import Aletheia.LTL.SignalPredicate.Cache
open import Aletheia.LTL.SignalPredicate.Evaluation

-- ============================================================================
-- HELPERS
-- ============================================================================

-- Associate a SignalPredicate with its target signal name.
signalOf : SignalPredicate → String
signalOf (ValueP vp) = valuePredicateSignal vp
signalOf (DeltaP dp) = deltaPredicateSignal dp

-- `fromBool b` is definite for any `b`: it's either True or False.
fromBool-definite : ∀ b → (fromBool b ≡ True) ⊎ (fromBool b ≡ False)
fromBool-definite true  = inj₁ refl
fromBool-definite false = inj₂ refl

-- Pattern-matching helpers that mirror evalValuePredicateTV /
-- evalDeltaPredicateTV but take already-resolved `Maybe ℚ` arguments directly.
-- Bridging through these avoids Agda's syntactic-matching issues with
-- `case_of_` lambdas in `with`/`rewrite`.
private
  valueAt : ValuePredicate → Maybe ℚ → TruthVal
  valueAt vp (just v) = fromBool (evalValuePredicate vp v)
  valueAt _  nothing  = Unknown

  deltaAt : DeltaPredicate → Maybe ℚ → Maybe ℚ → TruthVal
  deltaAt _  nothing    _          = Unknown
  deltaAt _  (just _)   nothing    = Pending
  deltaAt dp (just cv)  (just pv)  = fromBool (evalDeltaPredicate dp pv cv)

  -- Pointwise unfolding: evalValuePredicateTV ≡ valueAt ∘ getTruthValue.
  -- Provable by `with` on `getTruthValue` + `refl` in each branch, because
  -- once the argument is a concrete constructor both sides reduce alike.
  evalValuePredicateTV-unfold :
    ∀ {n} dbc cache vp (frame : CANFrame n)
    → evalValuePredicateTV dbc cache vp frame
      ≡ valueAt vp (getTruthValue (valuePredicateSignal vp) dbc cache frame)
  evalValuePredicateTV-unfold dbc cache vp frame
    with getTruthValue (valuePredicateSignal vp) dbc cache frame
  ... | just _  = refl
  ... | nothing = refl

  -- Pointwise unfolding for the delta case: currVal comes from getTruthValue,
  -- prevVal from `lookupCacheValue`, which unfolds to `cachedSignalValue ∘
  -- lookupCache` (see Evaluation.agda). We nest the two `with` clauses —
  -- outer on `getTruthValue`, inner on `lookupCache` — because Agda's
  -- abstraction doesn't descend into the body of a non-applied case lambda.
  -- The outer `with` commits the outer `case currVal of …` to its
  -- `(just cv)` branch, which fully applies the outer lambda; only then is
  -- the inner `lookupCache …` reachable by the inner `with` abstraction.
  -- (A flat `with … | …` fails here because the inner occurrence stays
  -- hidden inside the unapplied outer lambda.) The inner `with lookupCache`
  -- works because `lookupCacheValue sig cache` reduces to `cachedSignalValue
  -- (lookupCache sig cache)`, exposing `lookupCache` syntactically on the
  -- equation's RHS too.
  evalDeltaPredicateTV-unfold :
    ∀ {n} dbc cache dp (frame : CANFrame n)
    → evalDeltaPredicateTV dbc cache dp frame
      ≡ deltaAt dp
          (getTruthValue (deltaPredicateSignal dp) dbc cache frame)
          (lookupCacheValue (deltaPredicateSignal dp) cache)
  evalDeltaPredicateTV-unfold dbc cache dp frame
    with getTruthValue (deltaPredicateSignal dp) dbc cache frame
  ... | nothing = refl
  ... | just _
        with lookupCache (deltaPredicateSignal dp) cache
  ...      | nothing = refl
  ...      | just _  = refl

  -- Transport a binary disjunction of equalities along a preceding equality:
  -- given `lhs ≡ rhs` and `(rhs ≡ t) ⊎ (rhs ≡ f)`, conclude `(lhs ≡ t) ⊎
  -- (lhs ≡ f)`. Shared by both evalValue-cache-definite and
  -- evalDelta-cache-definite, which previously inlined identical copies.
  lift-def : ∀ {A : Set} {lhs rhs t f : A}
           → lhs ≡ rhs
           → (rhs ≡ t) ⊎ (rhs ≡ f)
           → (lhs ≡ t) ⊎ (lhs ≡ f)
  lift-def eq (inj₁ p) = inj₁ (trans eq p)
  lift-def eq (inj₂ p) = inj₂ (trans eq p)

-- ============================================================================
-- CACHE-DEFINITENESS BRIDGE
-- ============================================================================

-- Cache hit ⇒ getTruthValue yields `just _`. The frame-hit path returns the
-- fresh value directly; the cache-fallback path transports `hit` via `cong`.
getTruthValue-cache-just : ∀ {n} sigName dbc cache (frame : CANFrame n) cs
  → lookupCache sigName cache ≡ just cs
  → ∃[ v ] (getTruthValue sigName dbc cache frame ≡ just v)
getTruthValue-cache-just sigName dbc cache frame cs hit
  with extractTruthValue sigName dbc frame
... | just v  = v , refl
... | nothing = CachedSignal.value cs , cong cachedSignalValue hit

-- If the value predicate's signal is cached, evaluation yields a definite
-- verdict (never `Unknown`). We compose the unfolding lemma with a
-- `cong (valueAt vp)` transport on the cache-hit equation — no `with` or
-- `rewrite` touches the headline goal.
evalValue-cache-definite : ∀ {n} dbc cache vp (frame : CANFrame n) cs
  → lookupCache (valuePredicateSignal vp) cache ≡ just cs
  → (evalValuePredicateTV dbc cache vp frame ≡ True)
  ⊎ (evalValuePredicateTV dbc cache vp frame ≡ False)
evalValue-cache-definite dbc cache vp frame cs hit
  with getTruthValue-cache-just (valuePredicateSignal vp) dbc cache frame cs hit
... | v , gtv≡jv =
  lift-def combined (fromBool-definite (evalValuePredicate vp v))
  where
    combined :
      evalValuePredicateTV dbc cache vp frame
      ≡ fromBool (evalValuePredicate vp v)
    combined =
      trans (evalValuePredicateTV-unfold dbc cache vp frame)
            (cong (valueAt vp) gtv≡jv)

-- If the delta predicate's signal is cached, evaluation yields a definite
-- verdict (never `Unknown` or `Pending`). Same technique as the value case,
-- but with `cong₂ (deltaAt dp)` transporting both `currVal` (via `gtv≡jv`)
-- and `prevVal` (via `cong cachedSignalValue hit`).
evalDelta-cache-definite : ∀ {n} dbc cache dp (frame : CANFrame n) cs
  → lookupCache (deltaPredicateSignal dp) cache ≡ just cs
  → (evalDeltaPredicateTV dbc cache dp frame ≡ True)
  ⊎ (evalDeltaPredicateTV dbc cache dp frame ≡ False)
evalDelta-cache-definite dbc cache dp frame cs hit
  with getTruthValue-cache-just (deltaPredicateSignal dp) dbc cache frame cs hit
... | v , gtv≡jv =
  lift-def combined
    (fromBool-definite (evalDeltaPredicate dp (CachedSignal.value cs) v))
  where
    prev-eq :
      lookupCacheValue (deltaPredicateSignal dp) cache
      ≡ just (CachedSignal.value cs)
    prev-eq = cong cachedSignalValue hit

    combined :
      evalDeltaPredicateTV dbc cache dp frame
      ≡ fromBool (evalDeltaPredicate dp (CachedSignal.value cs) v)
    combined =
      trans (evalDeltaPredicateTV-unfold dbc cache dp frame)
            (cong₂ (deltaAt dp) gtv≡jv prev-eq)

-- Lifts the value/delta lemmas to the `SignalPredicate` sum. This is the
-- headline lemma of C3: cache warmness implies definiteness for any atomic
-- predicate, closing the gap between the runtime cache and the two-valued
-- regime where `agreement : runL ≡ ⟦_⟧` holds.
evalPredicate-cache-definite : ∀ {n} dbc cache p (frame : CANFrame n) cs
  → lookupCache (signalOf p) cache ≡ just cs
  → (evalPredicateTV dbc cache p frame ≡ True)
  ⊎ (evalPredicateTV dbc cache p frame ≡ False)
evalPredicate-cache-definite dbc cache (ValueP vp) frame cs hit =
  evalValue-cache-definite dbc cache vp frame cs hit
evalPredicate-cache-definite dbc cache (DeltaP dp) frame cs hit =
  evalDelta-cache-definite dbc cache dp frame cs hit
