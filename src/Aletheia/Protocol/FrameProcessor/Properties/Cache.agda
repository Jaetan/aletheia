{-# OPTIONS --safe --without-K #-}

-- Signal cache update properties.
--
-- Decomposition lemmas (P10–P13) showing that `updateCache`,
-- `updateSignals`, and `updateCacheFromFrame` step in lock-step with
-- `lookupCache` and `findMessageById`, plus the monotonicity / timestamp
-- bound preservation properties (P23–P26) used by the cache-warmness
-- adequacy chain in `Protocol.Adequacy.WarmCache`.
--
-- All lemmas in this module are about the `SignalCache` data structure
-- and its update functions in
-- `Aletheia.Protocol.StreamState.Internals` — they do NOT touch
-- `handleDataFrame` or `stepL`.
module Aletheia.Protocol.FrameProcessor.Properties.Cache where
open import Aletheia.DBC.Types using (signalNameStr)

open import Aletheia.Protocol.StreamState.Internals
    using (updateCacheFromFrame; updateSignals)
open import Aletheia.LTL.SignalPredicate
    using (SignalCache; mkSignalCache; CacheEntries;
           CachedSignal; mkCachedSignal; lookupCache; updateCache;
           lookupEntries; updateEntries; extractTruthValue)
open import Aletheia.LTL.SignalPredicate.Cache.Properties
    using (AllTimestamps≤; updateCache-monotone; updateCache-timestamps≤)
open import Aletheia.DBC.Types using (DBCSignal; DBCMessage)
open import Aletheia.CAN.Frame using (CANFrame)
open import Aletheia.CAN.DBCHelpers using (findMessageById)
open import Data.String using (String)
open import Data.String.Properties using () renaming (_≟_ to _≟ₛ_)
open import Data.Product using (_,_; ∃-syntax)
open import Data.Maybe using (just; nothing)
open import Data.List using (List; []; _∷_) renaming (_++_ to _++ₗ_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)

-- ============================================================================
-- PROPERTY 10: Signal cache update — same name lookup
-- ============================================================================

private
  -- Helper: looking up name in (name , v) ∷ rest returns just v.
  -- Uses Dec-based `with` so ⌊ name ≟ₛ name ⌋ reduces inside lookupEntries.
  lookupEntries-head : ∀ name v rest →
    lookupEntries name ((name , v) ∷ rest) ≡ just v
  lookupEntries-head name v rest with name ≟ₛ name
  ... | yes _ = refl
  ... | no ¬p = ⊥-elim (¬p refl)

  -- Helper: looking up name' ≢ name skips the head entry.
  lookupEntries-skip : ∀ name' name v rest →
    name' ≢ name →
    lookupEntries name' ((name , v) ∷ rest) ≡ lookupEntries name' rest
  lookupEntries-skip name' name v rest neq with name' ≟ₛ name
  ... | yes p = ⊥-elim (neq p)
  ... | no  _ = refl

  -- List-level: after updateEntries, looking up the updated name returns the new value.
  lookupEntries-updateEntries-hit : ∀ name val ts (es : CacheEntries) →
    lookupEntries name (updateEntries name val ts es) ≡ just (mkCachedSignal val ts)
  lookupEntries-updateEntries-hit name val ts [] =
    lookupEntries-head name (mkCachedSignal val ts) []
  lookupEntries-updateEntries-hit name val ts ((n , cached) ∷ rest)
    with name ≟ₛ n
  ... | yes _ = lookupEntries-head name (mkCachedSignal val ts) rest
  ... | no ¬a = trans (lookupEntries-skip name n cached (updateEntries name val ts rest) ¬a)
                      (lookupEntries-updateEntries-hit name val ts rest)

  -- List-level: after updateEntries, looking up a different name is unchanged.
  lookupEntries-updateEntries-miss : ∀ name name' val ts (es : CacheEntries) →
    name ≢ name' →
    lookupEntries name' (updateEntries name val ts es) ≡ lookupEntries name' es
  lookupEntries-updateEntries-miss name name' val ts [] name≢name' =
    lookupEntries-skip name' name (mkCachedSignal val ts) [] (λ p → name≢name' (sym p))
  lookupEntries-updateEntries-miss name name' val ts ((n , cached) ∷ rest) name≢name'
    with name ≟ₛ n | name' ≟ₛ n
  ... | yes p | yes q = ⊥-elim (name≢name' (trans p (sym q)))
  ... | yes _ | no  _ =
    lookupEntries-skip name' name (mkCachedSignal val ts) rest (λ p → name≢name' (sym p))
  ... | no  _ | yes refl =
    lookupEntries-head name' cached (updateEntries name val ts rest)
  ... | no  _ | no ¬b =
    trans (lookupEntries-skip name' n cached (updateEntries name val ts rest) ¬b)
          (lookupEntries-updateEntries-miss name name' val ts rest name≢name')

-- After updateCache, looking up the updated name returns the new value.
-- Delegates to list-level proof via record decomposition.
lookupCache-updateCache-hit : ∀ name val ts cache →
  lookupCache name (updateCache name val ts cache) ≡ just (mkCachedSignal val ts)
lookupCache-updateCache-hit name val ts (mkSignalCache es _) =
  lookupEntries-updateEntries-hit name val ts es

-- ============================================================================
-- PROPERTY 11: Signal cache update — different name lookup unchanged
-- ============================================================================

-- After updateCache, looking up a different name returns the original value.
-- Combined with Property 10, this proves updateCache is a correct map-update.
lookupCache-updateCache-miss : ∀ name name' val ts cache →
  name ≢ name' →
  lookupCache name' (updateCache name val ts cache) ≡ lookupCache name' cache
lookupCache-updateCache-miss name name' val ts (mkSignalCache es _) name≢name' =
  lookupEntries-updateEntries-miss name name' val ts es name≢name'

-- ============================================================================
-- PROPERTY 12: updateSignals step decomposition
-- ============================================================================

-- When extraction succeeds, updateSignals steps to updateCache + recurse.
updateSignals-step-hit : ∀ {n} dbc (frame : CANFrame n) ts sig sigs cache v →
  extractTruthValue (signalNameStr sig) dbc frame ≡ just v →
  updateSignals dbc frame ts (sig ∷ sigs) cache
    ≡ updateSignals dbc frame ts sigs (updateCache (signalNameStr sig) v ts cache)
updateSignals-step-hit dbc frame ts sig sigs cache v eq rewrite eq = refl

-- When extraction fails, updateSignals skips the signal.
updateSignals-step-miss : ∀ {n} dbc (frame : CANFrame n) ts sig sigs cache →
  extractTruthValue (signalNameStr sig) dbc frame ≡ nothing →
  updateSignals dbc frame ts (sig ∷ sigs) cache
    ≡ updateSignals dbc frame ts sigs cache
updateSignals-step-miss dbc frame ts sig sigs cache eq rewrite eq = refl

-- ============================================================================
-- PROPERTY 13: updateCacheFromFrame decomposition
-- ============================================================================

-- When no message matches the frame, cache is unchanged.
updateCacheFromFrame-no-match : ∀ {n} dbc cache ts (frame : CANFrame n) →
  findMessageById (CANFrame.id frame) dbc ≡ nothing →
  updateCacheFromFrame dbc cache ts frame ≡ cache
updateCacheFromFrame-no-match dbc cache ts frame eq rewrite eq = refl

-- When a message matches, updateCacheFromFrame delegates to updateSignals.
updateCacheFromFrame-match : ∀ {n} dbc cache ts (frame : CANFrame n) msg →
  findMessageById (CANFrame.id frame) dbc ≡ just msg →
  updateCacheFromFrame dbc cache ts frame
    ≡ updateSignals dbc frame ts (DBCMessage.signals msg) cache
updateCacheFromFrame-match dbc cache ts frame msg eq rewrite eq = refl

-- ============================================================================
-- PROPERTY 23: updateSignals monotonicity — cache entries survive signal list
-- ============================================================================

-- If a key was in the cache before updateSignals, it is still in the cache after.
updateSignals-monotone : ∀ {m} dbc (frame : CANFrame m) ts sigs cache name cached →
  lookupCache name cache ≡ just cached →
  ∃[ cached' ] lookupCache name (updateSignals dbc frame ts sigs cache) ≡ just cached'
updateSignals-monotone dbc frame ts [] cache name cached eq = cached , eq
updateSignals-monotone dbc frame ts (sig ∷ sigs) cache name cached eq
  with extractTruthValue (signalNameStr sig) dbc frame
... | nothing = updateSignals-monotone dbc frame ts sigs cache name cached eq
... | just v  =
  let (cached₁ , eq₁) = updateCache-monotone (signalNameStr sig) v ts cache name cached eq
  in updateSignals-monotone dbc frame ts sigs (updateCache (signalNameStr sig) v ts cache)
       name cached₁ eq₁

-- ============================================================================
-- PROPERTY 24: updateSignals timestamp bound — AllTimestamps≤ preserved
-- ============================================================================

-- If all cache entries had timestamps ≤ ts, they still do after updateSignals.
updateSignals-timestamps≤ : ∀ {m} dbc (frame : CANFrame m) ts sigs cache →
  AllTimestamps≤ ts (SignalCache.entries cache) →
  AllTimestamps≤ ts (SignalCache.entries (updateSignals dbc frame ts sigs cache))
updateSignals-timestamps≤ dbc frame ts [] cache h = h
updateSignals-timestamps≤ dbc frame ts (sig ∷ sigs) cache h
  with extractTruthValue (signalNameStr sig) dbc frame
... | nothing = updateSignals-timestamps≤ dbc frame ts sigs cache h
... | just v  = updateSignals-timestamps≤ dbc frame ts sigs
                  (updateCache (signalNameStr sig) v ts cache)
                  (updateCache-timestamps≤ (signalNameStr sig) v ts cache h)

-- ============================================================================
-- PROPERTY 25: updateCacheFromFrame monotonicity — entries survive frame processing
-- ============================================================================

-- If a key was in the cache, it is still present after processing any frame.
updateCacheFromFrame-monotone : ∀ {m} dbc cache ts (frame : CANFrame m) name cached →
  lookupCache name cache ≡ just cached →
  ∃[ cached' ] lookupCache name (updateCacheFromFrame dbc cache ts frame) ≡ just cached'
updateCacheFromFrame-monotone dbc cache ts frame name cached eq
  with findMessageById (CANFrame.id frame) dbc
... | nothing  = cached , eq
... | just msg = updateSignals-monotone dbc frame ts (DBCMessage.signals msg)
                   cache name cached eq

-- ============================================================================
-- PROPERTY 26: updateCacheFromFrame timestamp bound — AllTimestamps≤ preserved
-- ============================================================================

-- If all cache entries had timestamps ≤ ts, they still do after processing a frame.
updateCacheFromFrame-timestamps≤ : ∀ {m} dbc cache ts (frame : CANFrame m) →
  AllTimestamps≤ ts (SignalCache.entries cache) →
  AllTimestamps≤ ts (SignalCache.entries (updateCacheFromFrame dbc cache ts frame))
updateCacheFromFrame-timestamps≤ dbc cache ts frame h
  with findMessageById (CANFrame.id frame) dbc
... | nothing  = h
... | just msg = updateSignals-timestamps≤ dbc frame ts (DBCMessage.signals msg) cache h

-- ============================================================================
-- PROPERTY 30: Signal cache coherence with frame extraction (Gap 12.3)
-- ============================================================================
--
-- Closes deferred non-blocker 12.3 from project_system_review_deferred.md:
-- after `updateCacheFromFrame`, the cache value for a signal name agrees
-- with what would be extracted by `extractTruthValue` on the same frame.
-- This is the "no staleness" property — combined with the existing
-- monotonicity / timestamp-bound properties (P23–P26), it shows that the
-- streaming cache is a faithful reflection of the latest frame's signals,
-- not just a witness of definiteness.
--
-- The proof is parameterised over a `prefix ++ₗ sig ∷ suffix` split of the
-- matching message's signal list, with `NotInSignals (signalNameStr sig) suffix`
-- ensuring last-writer-wins semantics: any later signal sharing the same
-- name would overwrite the cache entry, so we require none. For valid DBCs
-- (passing `Validator/Checks.checkAllDuplicateSignalName`), this condition
-- holds vacuously, but the proof does not depend on validator state.

-- Auxiliary predicate: a name does not appear as the name of any signal in
-- the list. Used to express "this signal is the last with its name".
data NotInSignals : String → List DBCSignal → Set where
  []ₙ : ∀ {name} → NotInSignals name []
  _∷ₙ_ : ∀ {name sig sigs} →
        signalNameStr sig ≢ name →
        NotInSignals name sigs →
        NotInSignals name (sig ∷ sigs)

-- Helper: if a name's value is correct in the cache and the upcoming signals
-- don't contain that name, then `updateSignals` preserves the value.
-- Each step either skips (extraction failed → cache unchanged) or writes a
-- different name (cache entry for our `name` survives via the miss lemma).
updateSignals-preserves-hit :
  ∀ {n} dbc (frame : CANFrame n) ts sigs cache name v →
  lookupCache name cache ≡ just (mkCachedSignal v ts) →
  NotInSignals name sigs →
  lookupCache name (updateSignals dbc frame ts sigs cache)
    ≡ just (mkCachedSignal v ts)
updateSignals-preserves-hit dbc frame ts [] cache name v eq notIn = eq
updateSignals-preserves-hit dbc frame ts (sig ∷ sigs) cache name v eq (neq ∷ₙ notIn)
  with extractTruthValue (signalNameStr sig) dbc frame
... | nothing = updateSignals-preserves-hit dbc frame ts sigs cache name v eq notIn
... | just v' = updateSignals-preserves-hit dbc frame ts sigs
                  (updateCache (signalNameStr sig) v' ts cache) name v
                  (trans (lookupCache-updateCache-miss
                            (signalNameStr sig) name v' ts cache neq) eq)
                  notIn

-- Head case: a signal at the head of the list with successful extraction
-- writes its value into the cache, and `updateSignals-preserves-hit`
-- ensures it survives the rest of the list (since the tail doesn't
-- contain its name).
updateSignals-coherent-head :
  ∀ {n} dbc (frame : CANFrame n) ts sig sigs cache v →
  extractTruthValue (signalNameStr sig) dbc frame ≡ just v →
  NotInSignals (signalNameStr sig) sigs →
  lookupCache (signalNameStr sig)
    (updateSignals dbc frame ts (sig ∷ sigs) cache)
    ≡ just (mkCachedSignal v ts)
updateSignals-coherent-head dbc frame ts sig sigs cache v eq notIn rewrite eq =
  updateSignals-preserves-hit dbc frame ts sigs
    (updateCache (signalNameStr sig) v ts cache)
    (signalNameStr sig) v
    (lookupCache-updateCache-hit (signalNameStr sig) v ts cache)
    notIn

-- General position: a signal at any position in the list, given as a
-- `prefix ++ₗ sig ∷ suffix` split, lands its extracted value in the cache
-- as long as the suffix contains no duplicate of its name. Each prefix
-- step is irrelevant — the extraction call's outcome only changes which
-- cache the IH starts from, but the IH conclusion does not depend on the
-- starting cache.
updateSignals-coherent-split :
  ∀ {n} dbc (frame : CANFrame n) ts prefix sig suffix cache v →
  extractTruthValue (signalNameStr sig) dbc frame ≡ just v →
  NotInSignals (signalNameStr sig) suffix →
  lookupCache (signalNameStr sig)
    (updateSignals dbc frame ts (prefix ++ₗ sig ∷ suffix) cache)
    ≡ just (mkCachedSignal v ts)
updateSignals-coherent-split dbc frame ts [] sig suffix cache v eq notIn =
  updateSignals-coherent-head dbc frame ts sig suffix cache v eq notIn
updateSignals-coherent-split dbc frame ts (p ∷ prefix) sig suffix cache v eq notIn
  with extractTruthValue (signalNameStr p) dbc frame
... | nothing = updateSignals-coherent-split dbc frame ts prefix sig suffix cache v eq notIn
... | just v' = updateSignals-coherent-split dbc frame ts prefix sig suffix
                  (updateCache (signalNameStr p) v' ts cache) v eq notIn

-- Top-level cache coherence: for any signal in the matching message of
-- a frame whose extraction succeeds, looking up its name in the post-update
-- cache returns exactly that value with the update timestamp. The signal
-- is identified by a `prefix ++ₗ sig ∷ suffix` decomposition of the message's
-- signal list together with `NotInSignals (signalNameStr sig) suffix`.
--
-- The proof composes the existing decomposition lemma `updateCacheFromFrame-match`
-- with `cong` (for the `splitEq` substitution) via `trans`, then transports the
-- result via `cong (lookupCache ...)`. We avoid `rewrite findEq` here because
-- `findMessageById` reduces to `findByPredicate matchesId (DBC.messages dbc)`
-- which also appears inside the unfolding of `extractTruthValue`'s
-- `extractSignalWithContext`; rewriting would force Agda to re-abstract the
-- inner `with`-blocks of `extractSignalWithContext` and produce a different
-- normal form for the type of `extractEq` than the lemma expects.
updateCacheFromFrame-coherent :
  ∀ {n} dbc cache ts (frame : CANFrame n) msg prefix sig suffix v →
  findMessageById (CANFrame.id frame) dbc ≡ just msg →
  DBCMessage.signals msg ≡ prefix ++ₗ sig ∷ suffix →
  extractTruthValue (signalNameStr sig) dbc frame ≡ just v →
  NotInSignals (signalNameStr sig) suffix →
  lookupCache (signalNameStr sig)
    (updateCacheFromFrame dbc cache ts frame)
    ≡ just (mkCachedSignal v ts)
updateCacheFromFrame-coherent dbc cache ts frame msg prefix sig suffix v
                              findEq splitEq extractEq notIn =
  let step1 : updateCacheFromFrame dbc cache ts frame
            ≡ updateSignals dbc frame ts (DBCMessage.signals msg) cache
      step1 = updateCacheFromFrame-match dbc cache ts frame msg findEq
      step2 : updateSignals dbc frame ts (DBCMessage.signals msg) cache
            ≡ updateSignals dbc frame ts (prefix ++ₗ sig ∷ suffix) cache
      step2 = cong (λ s → updateSignals dbc frame ts s cache) splitEq
      lhs-eq : updateCacheFromFrame dbc cache ts frame
             ≡ updateSignals dbc frame ts (prefix ++ₗ sig ∷ suffix) cache
      lhs-eq = trans step1 step2
  in trans (cong (lookupCache (signalNameStr sig)) lhs-eq)
           (updateSignals-coherent-split dbc frame ts prefix sig suffix cache v
              extractEq notIn)
