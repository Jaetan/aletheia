-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Verdict preservation for the extract-once streaming step.
--
-- The runtime evaluates predicates against the shared per-frame extraction table
-- (`mkPredTableT` / `evalPredicateTVT`), while the adequacy/soundness chain
-- reasons about the frame-extracting spec (`mkPredTable` / `evalPredicateTV`).
-- This module closes that eval-side gap end-to-end and UNCONDITIONALLY: on any
-- accepted (monotone) frame the runtime `handleDataFrame` produces the SAME
-- `StreamState × Response` as the spec that evaluates predicates through
-- `mkPredTable` directly.  The per-property step is preserved whenever the table
-- covers that property's atoms (`stepProperty-preserves`); the top theorem
-- discharges that coverage internally, because `handleDataFrame` builds the
-- table over `readableSignals props` — the union of every active property's atom
-- signals — so no readable-coverage hypothesis remains.  Nothing in `stepL` or
-- the adequacy theorems is changed — this is a strictly additive congruence
-- bridge that makes the optimization proof-carrying, and it is the first
-- consumer of `extractTable-faithful`.  The outgoing cache term is identical on
-- both sides (`dispatchIterResult` stores it in the state but never consults it
-- for the verdict), so the identity is precisely the eval-side one.
--
-- Chain: `extractTable-faithful` (table lookup = frame extraction for a readable
-- name) → `evalPredicateTVT-faithful` (per-predicate) → `mkPredTableT-pointwise`
-- (table agrees with spec at every index) → `stepL-cong` (pointwise-equal tables
-- give equal `stepL`) → `stepProperty-preserves` (runtime step ≡ spec step, given
-- coverage) → `readableSignals-covers` (the built table covers every property) +
-- `iterate-cong` (pointwise-equal steps give equal iteration) →
-- `handleDataFrame-verdict-preserved` (runtime frame result ≡ spec, no premise).
module Aletheia.Protocol.FrameProcessor.Properties.VerdictPreserved where

open import Data.Char using (Char)
open import Data.Bool using (true; false)
open import Data.Nat using (ℕ; zero; suc; _≤ᵇ_)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; map) renaming (_++_ to _++ₗ_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (just; nothing; _<∣>_)
open import Data.Maybe.Properties using (just-injective)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)

open import Aletheia.DBC.Types using (DBC)
open import Aletheia.DBC.Identifier using (_≡csᵇ_; ≡csᵇ-refl-eq)
open import Aletheia.CAN.Frame using (CANFrame)
open import Aletheia.Trace.CANTrace using (TimedFrame; tsValue; timestamp)
open import Aletheia.LTL.Incremental using (Counterexample)
open import Aletheia.LTL.Syntax using
  (Atomic; Not; And; Or; Next; WNext; Always; Eventually; Until; Release;
   MetricEventually; MetricAlways; MetricUntil; MetricRelease)
open import Aletheia.LTL.Coalgebra using (LTLProc; PredTable; stepL; metricElapsed)
open import Aletheia.LTL.SignalPredicate using
  (SignalPredicate; ValueP; DeltaP;
   signalOf; valuePredicateSignal; deltaPredicateSignal;
   extractTruthValue; lookupCacheValue; lookupET;
   evalValuePredicateTVT; evalDeltaPredicateTVT; evalPredicateTVT;
   evalValuePredicateTV; evalDeltaPredicateTV; evalPredicateTV)
open import Aletheia.Protocol.Iteration using
  (StepOutcome; advance; halt; complete;
   iterate; iterate-correct; specResult; specHalt; specCompletions)
open import Aletheia.Protocol.StreamState using
  (PropertyState; Streaming; stepFrameShared; handleDataFrame; checkMonotonic)
open import Aletheia.Protocol.StreamState.Internals using
  (extractTable; mkPredTable; mkPredTableT; stepProperty; classifyStepResult;
   lookupAtom; _∈ᵇ_; readableSignals; cacheFromTable; dispatchIterResult)
open import Aletheia.LTL.SignalPredicate.Evaluation using (withForcedTable-id)
open import Aletheia.LTL.SignalPredicate.Cache using (SignalCache; withForcedCache; withForcedCache-id)
open import Aletheia.Protocol.FrameProcessor.Properties.Cache using (extractTable-faithful)

-- ============================================================================
-- stepL congruence: pointwise-equal tables (at the current frame) agree
-- ============================================================================
--
-- `stepL` reads the table only in the `Atomic` case, always at the top-level
-- frame `curr`; every other case recurses structurally and combines the
-- sub-results.  So pointwise table equality at `curr` propagates through the
-- whole step.  This is additive: `stepL` itself is untouched.
stepL-cong : ∀ (t1 t2 : PredTable) (proc : LTLProc) (curr : TimedFrame)
  → (∀ n → t1 n curr ≡ t2 n curr)
  → stepL t1 proc curr ≡ stepL t2 proc curr
stepL-cong t1 t2 (Atomic n) curr h rewrite h n = refl
stepL-cong t1 t2 (Not φ) curr h rewrite stepL-cong t1 t2 φ curr h = refl
stepL-cong t1 t2 (And φ ψ) curr h
  rewrite stepL-cong t1 t2 φ curr h | stepL-cong t1 t2 ψ curr h = refl
stepL-cong t1 t2 (Or φ ψ) curr h
  rewrite stepL-cong t1 t2 φ curr h | stepL-cong t1 t2 ψ curr h = refl
stepL-cong t1 t2 (Next φ) curr h = refl
stepL-cong t1 t2 (WNext φ) curr h = refl
stepL-cong t1 t2 (Always φ) curr h rewrite stepL-cong t1 t2 φ curr h = refl
stepL-cong t1 t2 (Eventually φ) curr h rewrite stepL-cong t1 t2 φ curr h = refl
stepL-cong t1 t2 (Until φ ψ) curr h
  rewrite stepL-cong t1 t2 φ curr h | stepL-cong t1 t2 ψ curr h = refl
stepL-cong t1 t2 (Release φ ψ) curr h
  rewrite stepL-cong t1 t2 φ curr h | stepL-cong t1 t2 ψ curr h = refl
stepL-cong t1 t2 (MetricEventually w s φ) curr h
  with metricElapsed s curr ≤ᵇ tsValue w
... | false = refl
... | true  rewrite stepL-cong t1 t2 φ curr h = refl
stepL-cong t1 t2 (MetricAlways w s φ) curr h
  with metricElapsed s curr ≤ᵇ tsValue w
... | false = refl
... | true  rewrite stepL-cong t1 t2 φ curr h = refl
stepL-cong t1 t2 (MetricUntil w s φ ψ) curr h
  with metricElapsed s curr ≤ᵇ tsValue w
... | false = refl
... | true  rewrite stepL-cong t1 t2 φ curr h | stepL-cong t1 t2 ψ curr h = refl
stepL-cong t1 t2 (MetricRelease w s φ ψ) curr h
  with metricElapsed s curr ≤ᵇ tsValue w
... | false = refl
... | true  rewrite stepL-cong t1 t2 φ curr h | stepL-cong t1 t2 ψ curr h = refl

-- ============================================================================
-- Eval-side faithfulness: table reader ≡ frame-extracting spec for a readable name
-- ============================================================================

-- `getTruthValueT`/`getTruthValue` unfold to `<extraction> <∣> lookupCacheValue …`
-- with an identical cache fallback, so the value read from the shared table
-- equals the value read from the frame (`extractTable-faithful`).  We abstract
-- the WHOLE `_<∣>_` scrutinee via `with` (rather than `rewrite`-ing the table
-- lookup into `extractTruthValue`), which would re-abstract the inner `with`s of
-- `extractSignalWithContext` and produce a different normal form — the same
-- reason the cache decomposition proofs avoid `rewrite findEq`.  With the two
-- scrutinees tied equal, both `case`s reduce identically.
evalValuePredicateTVT-faithful : ∀ {n} dbc (frame : CANFrame n) readable cache vp →
  (valuePredicateSignal vp ∈ᵇ readable) ≡ true →
  evalValuePredicateTVT (extractTable dbc frame readable) cache vp
    ≡ evalValuePredicateTV dbc cache vp frame
evalValuePredicateTVT-faithful dbc frame readable cache vp h
  with lookupET (valuePredicateSignal vp) (extractTable dbc frame readable)
         <∣> lookupCacheValue (valuePredicateSignal vp) cache
     | extractTruthValue (valuePredicateSignal vp) dbc frame
         <∣> lookupCacheValue (valuePredicateSignal vp) cache
     | cong (_<∣> lookupCacheValue (valuePredicateSignal vp) cache)
            (extractTable-faithful dbc frame readable (valuePredicateSignal vp) h)
... | just _  | .(just _)  | refl = refl
... | nothing | .nothing   | refl = refl

evalDeltaPredicateTVT-faithful : ∀ {n} dbc (frame : CANFrame n) readable cache dp →
  (deltaPredicateSignal dp ∈ᵇ readable) ≡ true →
  evalDeltaPredicateTVT (extractTable dbc frame readable) cache dp
    ≡ evalDeltaPredicateTV dbc cache dp frame
-- The delta case needs the shared `prevVal` (the OLD-cache lookup, identical on
-- both sides) split too: the inner `case prevVal` leaves two DISTINCT extended
-- lambdas (Agda treats each `λ where` as opaque by its definition site), which
-- only reduce once `prevVal` is a constructor.
evalDeltaPredicateTVT-faithful dbc frame readable cache dp h
  with lookupET (deltaPredicateSignal dp) (extractTable dbc frame readable)
         <∣> lookupCacheValue (deltaPredicateSignal dp) cache
     | extractTruthValue (deltaPredicateSignal dp) dbc frame
         <∣> lookupCacheValue (deltaPredicateSignal dp) cache
     | cong (_<∣> lookupCacheValue (deltaPredicateSignal dp) cache)
            (extractTable-faithful dbc frame readable (deltaPredicateSignal dp) h)
... | nothing | .nothing    | refl = refl
... | just cv | .(just cv)  | refl with lookupCacheValue (deltaPredicateSignal dp) cache
...   | nothing = refl
...   | just pv = refl

evalPredicateTVT-faithful : ∀ {n} dbc (frame : CANFrame n) readable cache pred →
  (signalOf pred ∈ᵇ readable) ≡ true →
  evalPredicateTVT (extractTable dbc frame readable) cache pred
    ≡ evalPredicateTV dbc cache pred frame
evalPredicateTVT-faithful dbc frame readable cache (ValueP vp) h =
  evalValuePredicateTVT-faithful dbc frame readable cache vp h
evalPredicateTVT-faithful dbc frame readable cache (DeltaP dp) h =
  evalDeltaPredicateTVT-faithful dbc frame readable cache dp h

-- ============================================================================
-- Table coverage: every active atom's signal is readable
-- ============================================================================

-- Every atom in the list targets a signal in the readable set.  Mirrors the
-- readable-coverage `handleDataFrame` establishes by building the table over
-- `readableSignals props` (the union of the active atoms' signals).
AllReadable : List SignalPredicate → List (List Char) → Set
AllReadable []       readable = ⊤
AllReadable (p ∷ ps) readable = ((signalOf p ∈ᵇ readable) ≡ true) × AllReadable ps readable

-- Index into a covered atom list: the atom found at any index is readable.
lookupAtom-readable : ∀ atoms readable n pred →
  AllReadable atoms readable →
  lookupAtom atoms n ≡ just pred →
  (signalOf pred ∈ᵇ readable) ≡ true
lookupAtom-readable []       readable n       pred allR         ()
lookupAtom-readable (a ∷ as) readable zero    pred (h0 , _)     eq =
  subst (λ x → (signalOf x ∈ᵇ readable) ≡ true) (just-injective eq) h0
lookupAtom-readable (a ∷ as) readable (suc m) pred (_  , hrest) eq =
  lookupAtom-readable as readable m pred hrest eq

-- ============================================================================
-- mkPredTableT ≡ mkPredTable pointwise (given coverage), then verdict preserved
-- ============================================================================

-- On a covered atom list the runtime table agrees with the spec table at every
-- index (and at the frame the table was built from).  Out-of-range indices are
-- `Unknown` on both sides.
mkPredTableT-pointwise : ∀ dbc (tf : TimedFrame) readable cache atoms →
  AllReadable atoms readable →
  ∀ n → mkPredTableT (extractTable dbc (TimedFrame.frame tf) readable) dbc cache atoms n tf
       ≡ mkPredTable dbc cache atoms n tf
mkPredTableT-pointwise dbc tf readable cache atoms allR n
  with lookupAtom atoms n in eqLA
... | nothing   = refl
... | just pred =
      evalPredicateTVT-faithful dbc (TimedFrame.frame tf) readable cache pred
        (lookupAtom-readable atoms readable n pred allR eqLA)

-- Verdict preservation (per property): when the shared table covers the
-- property's atoms, the runtime `stepProperty` (driven by `mkPredTableT`)
-- produces the SAME `StepOutcome` as the spec (driven by `mkPredTable`).  The
-- `AllReadable` hypothesis is exactly what `handleDataFrame` establishes by
-- building the table over `readableSignals props`.
stepProperty-preserves : ∀ {m} dbc (tf : TimedFrame) readable cache (prop : PropertyState m) →
  AllReadable (PropertyState.atoms prop) readable →
  stepProperty dbc (extractTable dbc (TimedFrame.frame tf) readable) cache tf prop
    ≡ classifyStepResult
        (stepL (mkPredTable dbc cache (PropertyState.atoms prop)) (PropertyState.proc prop) tf)
        prop
stepProperty-preserves dbc tf readable cache prop allR =
  cong (λ r → classifyStepResult r prop)
       (stepL-cong
         (mkPredTableT (extractTable dbc (TimedFrame.frame tf) readable) dbc cache (PropertyState.atoms prop))
         (mkPredTable dbc cache (PropertyState.atoms prop))
         (PropertyState.proc prop) tf
         (mkPredTableT-pointwise dbc tf readable cache (PropertyState.atoms prop) allR))

-- ============================================================================
-- Readable-set membership is monotone under list append
-- ============================================================================
--
-- `readableSignals (p ∷ ps)` is the union `map signalOf (atoms p) ++ₗ
-- readableSignals ps`.  Coverage of one property's atoms survives extending the
-- readable set on either side of an append, so a per-property `AllReadable`
-- witness lifts to the whole-union readable set the streaming step builds.

∈ᵇ-++ʳ : ∀ name xs ys → (name ∈ᵇ xs) ≡ true → (name ∈ᵇ (xs ++ₗ ys)) ≡ true
∈ᵇ-++ʳ name []       ys ()
∈ᵇ-++ʳ name (x ∷ xs) ys h with name ≡csᵇ x | h
... | true  | _  = refl
... | false | h' = ∈ᵇ-++ʳ name xs ys h'

∈ᵇ-++ˡ : ∀ name ys zs → (name ∈ᵇ zs) ≡ true → (name ∈ᵇ (ys ++ₗ zs)) ≡ true
∈ᵇ-++ˡ name []       zs h = h
∈ᵇ-++ˡ name (y ∷ ys) zs h with name ≡csᵇ y
... | true  = refl
... | false = ∈ᵇ-++ˡ name ys zs h

AllReadable-++ʳ : ∀ (as : List SignalPredicate) xs ys →
  AllReadable as xs → AllReadable as (xs ++ₗ ys)
AllReadable-++ʳ []       xs ys _        = tt
AllReadable-++ʳ (a ∷ as) xs ys (h , hs) =
  ∈ᵇ-++ʳ (signalOf a) xs ys h , AllReadable-++ʳ as xs ys hs

AllReadable-++ˡ : ∀ (as : List SignalPredicate) ys zs →
  AllReadable as zs → AllReadable as (ys ++ₗ zs)
AllReadable-++ˡ []       ys zs _        = tt
AllReadable-++ˡ (a ∷ as) ys zs (h , hs) =
  ∈ᵇ-++ˡ (signalOf a) ys zs h , AllReadable-++ˡ as ys zs hs

-- Every atom in a list is readable against that list's own signal-name set
-- (`map signalOf`).  Mirrors `all-atoms-readable` in `Adequacy.StreamingWarm`,
-- re-proven here against this module's `AllReadable` (the two definitions are
-- structurally identical but distinct Agda names).
self-map-∈ : ∀ (as : List SignalPredicate) → AllReadable as (map signalOf as)
self-map-∈ []       = tt
self-map-∈ (a ∷ as) =
  head∈ , AllReadable-++ˡ as (signalOf a ∷ []) (map signalOf as) (self-map-∈ as)
  where
    head∈ : (signalOf a ∈ᵇ (signalOf a ∷ map signalOf as)) ≡ true
    head∈ rewrite ≡csᵇ-refl-eq (signalOf a) = refl

-- ============================================================================
-- readableSignals covers every property's atoms
-- ============================================================================

-- Every active property's atoms are readable against `readable`.  The whole-list
-- analogue of `AllReadable`, ranging over the property list.
AtomsCovered : ∀ {n} → List (PropertyState n) → List (List Char) → Set
AtomsCovered []       readable = ⊤
AtomsCovered (p ∷ ps) readable =
  AllReadable (PropertyState.atoms p) readable × AtomsCovered ps readable

AtomsCovered-++ˡ : ∀ {n} (props : List (PropertyState n)) ys zs →
  AtomsCovered props zs → AtomsCovered props (ys ++ₗ zs)
AtomsCovered-++ˡ []       ys zs _        = tt
AtomsCovered-++ˡ (p ∷ ps) ys zs (h , hs) =
  AllReadable-++ˡ (PropertyState.atoms p) ys zs h , AtomsCovered-++ˡ ps ys zs hs

-- The readable set the streaming step derives — the union of every active
-- property's atom signals — covers every property's atoms.  This is the
-- coverage `handleDataFrame` establishes by construction: it discharges the
-- `AllReadable` premise of `stepProperty-preserves` for every property at once.
readableSignals-covers : ∀ {n} (props : List (PropertyState n)) →
  AtomsCovered props (readableSignals props)
readableSignals-covers []       = tt
readableSignals-covers (p ∷ ps) =
    AllReadable-++ʳ (PropertyState.atoms p)
      (map signalOf (PropertyState.atoms p)) (readableSignals ps)
      (self-map-∈ (PropertyState.atoms p))
  , AtomsCovered-++ˡ ps
      (map signalOf (PropertyState.atoms p)) (readableSignals ps)
      (readableSignals-covers ps)

-- ============================================================================
-- iterate congruence: pointwise-equal step functions give equal iteration
-- ============================================================================
--
-- `iterate` applies its step function only to the elements of the input list
-- (survivors go to an accumulator and are never re-stepped), so two step
-- functions that agree on those elements produce the same `iterate` result.
-- The accumulator machinery (`iterateImpl`) is private, so this routes through
-- the public `iterate-correct` to reduce `iterate` to the three forward specs
-- (`specResult`/`specHalt`/`specCompletions`), each of which is congruent under
-- pointwise step equality.  Additive: `iterate` itself is untouched.

-- Pointwise step equality along a fixed list (the only place the two step
-- functions are ever compared).
Pointwise-eq : ∀ {S E C : Set} → (S → StepOutcome S E C) → (S → StepOutcome S E C)
             → List S → Set
Pointwise-eq f g []       = ⊤
Pointwise-eq f g (x ∷ xs) = (f x ≡ g x) × Pointwise-eq f g xs

specResult-cong : ∀ {S E C : Set} (f g : S → StepOutcome S E C) xs →
  Pointwise-eq f g xs → specResult f xs ≡ specResult g xs
specResult-cong f g []       _        = refl
specResult-cong f g (x ∷ xs) (h , hs) with f x | g x | h
... | advance a  | advance .a  | refl = cong (a ∷_) (specResult-cong f g xs hs)
... | halt e     | halt .e     | refl = refl
... | complete c | complete .c | refl = specResult-cong f g xs hs

specHalt-cong : ∀ {S E C : Set} (f g : S → StepOutcome S E C) xs →
  Pointwise-eq f g xs → specHalt f xs ≡ specHalt g xs
specHalt-cong f g []       _        = refl
specHalt-cong f g (x ∷ xs) (h , hs) with f x | g x | h
... | advance a  | advance .a  | refl = specHalt-cong f g xs hs
... | halt e     | halt .e     | refl = refl
... | complete c | complete .c | refl = specHalt-cong f g xs hs

specCompletions-cong : ∀ {S E C : Set} (f g : S → StepOutcome S E C) xs →
  Pointwise-eq f g xs → specCompletions f xs ≡ specCompletions g xs
specCompletions-cong f g []       _        = refl
specCompletions-cong f g (x ∷ xs) (h , hs) with f x | g x | h
... | advance a  | advance .a  | refl = specCompletions-cong f g xs hs
... | halt e     | halt .e     | refl = refl
... | complete c | complete .c | refl = cong (c ∷_) (specCompletions-cong f g xs hs)

-- Local cong₂ (kept inside ≡-without-K reasoning; mirrors `Iteration.cong₂'`).
cong₂ᵥ : ∀ {A B Z : Set} (f : A → B → Z) {a a' : A} {b b' : B}
       → a ≡ a' → b ≡ b' → f a b ≡ f a' b'
cong₂ᵥ f refl refl = refl

iterate-cong : ∀ {S E C : Set} (f g : S → StepOutcome S E C) xs →
  Pointwise-eq f g xs → iterate f xs ≡ iterate g xs
iterate-cong f g xs pw =
  trans (iterate-correct f xs)
    (trans (cong₂ᵥ (λ r h → (r , h))
              (specResult-cong f g xs pw)
              (cong₂ᵥ (λ hlt cs → (hlt , cs))
                (specHalt-cong f g xs pw)
                (specCompletions-cong f g xs pw)))
      (sym (iterate-correct g xs)))

-- ============================================================================
-- End-to-end verdict preservation (unconditional)
-- ============================================================================
--
-- The spec step: classify `stepL` over the frame-extracting `mkPredTable`
-- (re-extracting each atom's signal from the frame per predicate) — the
-- adequacy/soundness chain reasons about this.  The runtime `stepProperty`
-- drives `stepL` over the shared-table `mkPredTableT` instead.
specStep : ∀ {n} → DBC → SignalCache → TimedFrame → PropertyState n →
  StepOutcome (PropertyState n) (Fin n × Counterexample) (Fin n)
specStep dbc cache tf prop =
  classifyStepResult
    (stepL (mkPredTable dbc cache (PropertyState.atoms prop)) (PropertyState.proc prop) tf)
    prop

-- Coverage lifts to pointwise step equality: on a covered property list the
-- runtime per-property step agrees with the spec step at every element.
covered→pointwise : ∀ {n} dbc (tf : TimedFrame) cache readable (props : List (PropertyState n)) →
  AtomsCovered props readable →
  Pointwise-eq (stepProperty dbc (extractTable dbc (TimedFrame.frame tf) readable) cache tf)
               (specStep dbc cache tf) props
covered→pointwise dbc tf cache readable []       _        = tt
covered→pointwise dbc tf cache readable (p ∷ ps) (h , hs) =
    stepProperty-preserves dbc tf readable cache p h
  , covered→pointwise dbc tf cache readable ps hs

-- The per-frame iteration core: iterating the runtime step over the shared table
-- built from `readableSignals props` equals iterating the spec step — the
-- `AllReadable` premise discharged internally by `readableSignals-covers`, with
-- no residual hypothesis.
stepFrame-core-preserved : ∀ {n} dbc (props : List (PropertyState n)) (tf : TimedFrame) cache →
  iterate (stepProperty dbc (extractTable dbc (TimedFrame.frame tf) (readableSignals props)) cache tf) props
    ≡ iterate (specStep dbc cache tf) props
stepFrame-core-preserved dbc props tf cache =
  iterate-cong _ _ props
    (covered→pointwise dbc tf cache (readableSignals props) props (readableSignals-covers props))

-- The whole shared-table streaming step (transparency wrappers included)
-- produces the SAME `StreamState × Response` as the spec that uses `mkPredTable`
-- directly.  The outgoing cache term is identical on both sides —
-- `dispatchIterResult` stores it in the result state but never consults it for
-- the verdict — so this is exactly the eval-side identity.
stepFrameShared-verdict-preserved : ∀ {n} dbc (props : List (PropertyState n)) (tf : TimedFrame) cache →
  stepFrameShared dbc props tf cache (extractTable dbc (TimedFrame.frame tf) (readableSignals props))
    ≡ dispatchIterResult dbc (iterate (specStep dbc cache tf) props) tf
        (cacheFromTable (timestamp tf) (extractTable dbc (TimedFrame.frame tf) (readableSignals props)) cache)
stepFrameShared-verdict-preserved dbc props tf cache =
  trans (withForcedTable-id table (withForcedCache cache′ body))
    (trans (withForcedCache-id cache′ body)
      (cong (λ ir → dispatchIterResult dbc ir tf cache′)
            (stepFrame-core-preserved dbc props tf cache)))
  where
    table  = extractTable dbc (TimedFrame.frame tf) (readableSignals props)
    cache′ = cacheFromTable (timestamp tf) table cache
    body   = dispatchIterResult dbc (iterate (stepProperty dbc table cache tf) props) tf

-- Top-level, unconditional: on an accepted (monotone) frame the runtime
-- `handleDataFrame` produces the SAME result as the spec streaming step.  The
-- readable-coverage premise is gone — it is discharged internally because the
-- table is built over `readableSignals props`, the union of every property's
-- atom signals.
handleDataFrame-verdict-preserved : ∀ {n} dbc (props : List (PropertyState n)) prev cache (tf : TimedFrame) →
  checkMonotonic prev tf ≡ nothing →
  handleDataFrame (Streaming n dbc props prev cache) tf
    ≡ dispatchIterResult dbc (iterate (specStep dbc cache tf) props) tf
        (cacheFromTable (timestamp tf) (extractTable dbc (TimedFrame.frame tf) (readableSignals props)) cache)
handleDataFrame-verdict-preserved dbc props prev cache tf mono
  with checkMonotonic prev tf | mono
... | nothing | refl = stepFrameShared-verdict-preserved dbc props tf cache
