{-# OPTIONS --safe --without-K #-}

-- Step-level properties of the LTL frame processor.
--
-- Combines:
--   PROPERTY 1  — handleDataFrame state-machine guards (non-Streaming → no-op)
--   PROPERTY 2  — byte modulus identity (boundary justification for the FFI shim)
--   PROPERTY 3  — classifyStepResult faithfulness wrt StepResult constructors
--   PROPERTY 4  — stepProperty halts iff stepL returns Violated
--   PROPERTY 5  — dispatchIterResult response characterization
--   PROPERTY 6  — handleDataFrame Streaming decomposition (monotonic frames)
--   PROPERTY 7  — Ack soundness (Ack ⇒ no violation)
--   PROPERTY 8  — Violation soundness (PropertyResponse ⇒ some violation)
--   PROPERTY 14 — Ack completeness (no violation ⇒ Ack)
--   PROPERTY 15 — Violation completeness (some violation ⇒ PropertyResponse)
--
-- All proofs in this module take a `checkMonotonic prev tf ≡ nothing`
-- precondition where required, ruling out the rejection branch added
-- when monotonicity enforcement was lifted into Agda. The Monotonic
-- side of that contract is proven separately in
-- `FrameProcessor.Properties.Monotonic`.
module Aletheia.Protocol.FrameProcessor.Properties.Step where

open import Aletheia.Protocol.StreamState
    using (WaitingForDBC; ReadyToStream; Streaming;
           handleDataFrame; checkMonotonic;
           PropertyState; mkPropertyState)
open import Aletheia.Protocol.StreamState.Internals
    using (classifyStepResult; stepProperty; dispatchIterResult;
           mkPredTable; updateCacheFromFrame)
open import Aletheia.Protocol.Message using (Response)
open import Aletheia.Protocol.Response as PR using (mkCounterexampleData)
open import Aletheia.Protocol.Iteration using (advance; halt; complete; iterate; iterate-correct; specResult; specHalt; specCompletions)
open import Aletheia.Trace.CANTrace using (TimedFrame; timestamp)
open import Aletheia.LTL.Incremental using (Continue; Violated; Satisfied; Counterexample)
open import Aletheia.LTL.Coalgebra using (stepL)
open import Aletheia.LTL.Simplify using (simplify)
open import Data.List using (List; []; _∷_; map) renaming (_++_ to _++ₗ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; _<_; _%_)
open import Data.Nat.DivMod using (m<n⇒m%n≡m)
open import Data.Fin using (Fin; toℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

-- ============================================================================
-- PROPERTY 1: State machine guards
-- ============================================================================

-- When not in Streaming phase, handleDataFrame returns the state unchanged.
-- With the sum type, these are trivially refl — no precondition needed.

handleDataFrame-guard-waitingForDBC : ∀ (tf : TimedFrame)
    → proj₁ (handleDataFrame WaitingForDBC tf) ≡ WaitingForDBC
handleDataFrame-guard-waitingForDBC tf = refl

handleDataFrame-guard-readyToStream : ∀ n dbc props cache (tf : TimedFrame)
    → proj₁ (handleDataFrame (ReadyToStream n dbc props cache) tf) ≡ ReadyToStream n dbc props cache
handleDataFrame-guard-readyToStream n dbc props cache tf = refl

-- ============================================================================
-- PROPERTY 2: Byte modulus identity (boundary justification)
-- ============================================================================

-- When n < 256, n % 256 ≡ n.
-- This justifies the Haskell shim's bytesToAgdaVec skipping % 256:
-- Agda's listToVec applies (x % 256), but the Haskell shim constructs
-- Vec entries directly from Word8 values (which are already in [0,255]).
-- Since Word8 ∈ [0,255] implies n < 256, the modulo is a no-op.
-- Direct re-export of stdlib `m<n⇒m%n≡m` (R19 cluster 15 — AGDA-C-27.5);
-- kept exported under the documented name because the Haskell shim cites
-- it in `haskell-shim/src/AletheiaFFI/Marshal.hs`'s rationale comment.
mod-identity-byte : ∀ (n : ℕ) → n < 256 → n % 256 ≡ n
mod-identity-byte _ = m<n⇒m%n≡m

-- ============================================================================
-- PROPERTY 3: classifyStepResult faithfully reflects StepResult constructors
-- ============================================================================

-- Violated → halt (property index + counterexample)
classifyStepResult-violated : ∀ {n} ce (prop : PropertyState n)
  → classifyStepResult (Violated ce) prop ≡ halt (PropertyState.index prop , ce)
classifyStepResult-violated ce prop = refl

-- Continue → advance (simplified successor state)
classifyStepResult-continue : ∀ {n} k newProc (prop : PropertyState n)
  → classifyStepResult (Continue k newProc) prop
    ≡ advance (mkPropertyState (PropertyState.index prop)
                                (PropertyState.formula prop)
                                (PropertyState.atoms prop)
                                (simplify newProc))
classifyStepResult-continue k newProc prop = refl

-- Satisfied → complete (property dropped from active set; AGDA-B-9.2
-- closure).  R23 — AGDA-D-12.1: `complete` now carries the property
-- index so dispatchIterResult can emit a `PropertyResult.Satisfaction`
-- at the frame where the property completed.
classifyStepResult-satisfied : ∀ {n} (prop : PropertyState n)
  → classifyStepResult Satisfied prop ≡ complete (PropertyState.index prop)
classifyStepResult-satisfied prop = refl

-- ============================================================================
-- PROPERTY 4: stepProperty — halt iff stepL returns Violated
-- ============================================================================

-- Forward: If stepL returns Violated, stepProperty halts with matching evidence.
stepProperty-violated : ∀ {n} dbc cache tf (prop : PropertyState n) ce
  → stepL (mkPredTable dbc cache (PropertyState.atoms prop)) (PropertyState.proc prop) tf ≡ Violated ce
  → stepProperty dbc cache tf prop ≡ halt (PropertyState.index prop , ce)
stepProperty-violated dbc cache tf prop ce steq rewrite steq = refl

-- Backward: If stepProperty halts, stepL returned Violated.
-- Returns: proof that idx matches the property index, and the stepL equality.
stepProperty-halt-implies-violated : ∀ {n} dbc cache tf (prop : PropertyState n) (idx : Fin n) ce
  → stepProperty dbc cache tf prop ≡ halt (idx , ce)
  → idx ≡ PropertyState.index prop
    × stepL (mkPredTable dbc cache (PropertyState.atoms prop)) (PropertyState.proc prop) tf ≡ Violated ce
stepProperty-halt-implies-violated dbc cache tf prop idx ce eq
  with stepL (mkPredTable dbc cache (PropertyState.atoms prop)) (PropertyState.proc prop) tf | eq
... | Continue _ _  | ()
... | Violated .ce  | refl = refl , refl
... | Satisfied     | ()

-- ============================================================================
-- PROPERTY 5: dispatchIterResult response characterization
-- ============================================================================

-- When iterate finds no violation AND no completions, response is Ack.
-- R23 — AGDA-D-12.1: the empty-completion-list precondition is the new
-- constraint; pre-R23 there was no completion list and a no-violation
-- frame unconditionally returned Ack.  After the change, a frame with
-- one-or-more completions returns PropertyResponse (carrying the
-- satisfaction list) rather than Ack — see dispatchIterResult-completions
-- below for that case.
dispatchIterResult-ack : ∀ {n} dbc (ps : List (PropertyState n)) tf cache
  → proj₂ (dispatchIterResult dbc (ps , nothing , []) tf cache) ≡ Response.Ack
dispatchIterResult-ack dbc ps tf cache = refl

-- R23 — AGDA-D-12.1: when iterate finds no violation but one-or-more
-- completions, response is PropertyResponse carrying the satisfaction
-- list (no violation appended).  This is the mid-stream-Satisfaction
-- emission path that did not exist pre-R23.
dispatchIterResult-completions : ∀ {n} dbc (ps : List (PropertyState n)) (c : Fin n) cs tf cache
  → proj₂ (dispatchIterResult dbc (ps , nothing , c ∷ cs) tf cache)
    ≡ Response.PropertyResponse
        (map (λ i → PR.PropertyResult.Satisfaction (toℕ i)) (c ∷ cs))
dispatchIterResult-completions dbc ps c cs tf cache = refl

-- When iterate finds a violation (just), response is PropertyResponse
-- carrying any preceding completions followed by the violation, in
-- source-order.  `toℕ idx` reflects the `Fin n → ℕ` wire-boundary
-- conversion done by `dispatchIterResult` (R20 cluster R6-B7.4); the
-- internal pipeline carries `Fin n` until this emission point.
dispatchIterResult-violation : ∀ {n} dbc (ps : List (PropertyState n)) (idx : Fin n) ce completions tf cache
  → proj₂ (dispatchIterResult dbc (ps , just (idx , ce) , completions) tf cache)
    ≡ Response.PropertyResponse
        (map (λ i → PR.PropertyResult.Satisfaction (toℕ i)) completions
         ++ₗ (PR.PropertyResult.Violation (toℕ idx)
                (mkCounterexampleData (TimedFrame.timestamp (Counterexample.violatingFrame ce))
                                      (Counterexample.reason ce))
              ∷ []))
dispatchIterResult-violation dbc ps idx ce completions tf cache = refl

-- ============================================================================
-- PROPERTY 6: handleDataFrame Streaming decomposition
-- ============================================================================

-- In Streaming phase with a monotonic timestamp, handleDataFrame decomposes into:
--   dispatchIterResult ∘ iterate ∘ stepProperty
-- The precondition `checkMonotonic prev tf ≡ nothing` rules out the rejection
-- branch added when monotonicity enforcement was lifted into Agda.
handleDataFrame-streaming : ∀ {n} dbc (props : List (PropertyState n)) prev cache tf
  → checkMonotonic prev tf ≡ nothing
  → handleDataFrame (Streaming n dbc props prev cache) tf
    ≡ let updatedCache = updateCacheFromFrame dbc cache
                           (timestamp tf) (TimedFrame.frame tf)
      in dispatchIterResult dbc
           (iterate (stepProperty dbc cache tf) props)
           tf updatedCache
handleDataFrame-streaming dbc props prev cache tf mono
  rewrite mono = refl

-- ============================================================================
-- PROPERTY 7: Ack soundness — Ack means no halt AND no completion
-- ============================================================================

-- If handleDataFrame returns Ack, then the frame was monotonic, iterate
-- found no halt evidence, AND no property completed (no completion
-- payloads).  R23 — AGDA-D-12.1: pre-R23 only the no-halt conclusion
-- existed; mid-stream completions are now lifted to the wire, so Ack
-- additionally implies the completion list is empty.  The monotonicity
-- precondition rules out the NonMonotonicTimestamp branch (which never
-- returns Ack).
handleDataFrame-ack-sound : ∀ {n} dbc (props : List (PropertyState n)) prev cache tf
  → checkMonotonic prev tf ≡ nothing
  → proj₂ (handleDataFrame (Streaming n dbc props prev cache) tf) ≡ Response.Ack
  → proj₁ (proj₂ (iterate (stepProperty dbc cache tf) props)) ≡ nothing
  × proj₂ (proj₂ (iterate (stepProperty dbc cache tf) props)) ≡ []
handleDataFrame-ack-sound dbc props prev cache tf mono resp-eq
  rewrite mono
  with iterate (stepProperty dbc cache tf) props | resp-eq
... | (ps , nothing , [])         | _  = refl , refl
... | (ps , nothing , _ ∷ _)      | ()
... | (ps , just (idx , ce) , _)  | ()

-- ============================================================================
-- PROPERTY 8: Batch soundness — PropertyResponse means some event fired
-- ============================================================================

-- If handleDataFrame returns PropertyResponse, then the frame was
-- monotonic and iterate produced at least one property event (either a
-- halt evidence, one or more completion payloads, or both).  R23 —
-- AGDA-D-12.1: pre-R23 PropertyResponse meant "violation"; after the
-- mid-stream-Satisfaction lift, PropertyResponse means "non-empty
-- batch" which covers completions-only frames in addition to violations.
handleDataFrame-events-sound : ∀ {n} dbc (props : List (PropertyState n)) prev cache tf pr
  → checkMonotonic prev tf ≡ nothing
  → proj₂ (handleDataFrame (Streaming n dbc props prev cache) tf) ≡ Response.PropertyResponse pr
  → (∃[ e ] proj₁ (proj₂ (iterate (stepProperty dbc cache tf) props)) ≡ just e)
    ⊎ (∃[ c ] ∃[ cs ] proj₂ (proj₂ (iterate (stepProperty dbc cache tf) props)) ≡ c ∷ cs)
handleDataFrame-events-sound dbc props prev cache tf pr mono resp-eq
  rewrite mono
  with iterate (stepProperty dbc cache tf) props | resp-eq
... | (ps , nothing , [])         | ()
... | (ps , nothing , c ∷ cs)     | _ = inj₂ (c , cs , refl)
... | (ps , just e , _)           | _ = inj₁ (e , refl)

-- ============================================================================
-- PROPERTY 14: Ack completeness — no halt AND no completion ⇒ Ack
-- ============================================================================

-- If the frame is monotonic, no property's stepProperty halts, AND no
-- property completes, handleDataFrame returns Ack.  Without the
-- monotonicity precondition the result would be a NonMonotonicTimestamp
-- Error instead; without the empty-completion-list premise the response
-- would be a PropertyResponse carrying the satisfaction list.
handleDataFrame-ack-complete : ∀ {n} dbc (props : List (PropertyState n)) prev cache tf
  → checkMonotonic prev tf ≡ nothing
  → specHalt (stepProperty dbc cache tf) props ≡ nothing
  → specCompletions (stepProperty dbc cache tf) props ≡ []
  → proj₂ (handleDataFrame (Streaming n dbc props prev cache) tf) ≡ Response.Ack
handleDataFrame-ack-complete dbc props prev cache tf mono spec-halt spec-comp
  rewrite mono =
    cong (λ p → proj₂ (dispatchIterResult dbc p tf updatedCache)) iter-eq
  where
    step = stepProperty dbc cache tf
    updatedCache = updateCacheFromFrame dbc cache (timestamp tf) (TimedFrame.frame tf)
    iter-eq : iterate step props ≡ (specResult step props , nothing , [])
    iter-eq = trans (iterate-correct step props)
                    (cong₂ (λ h c → (specResult step props , h , c)) spec-halt spec-comp)
      where
        cong₂ : ∀ {A B Z : Set} (f : A → B → Z) {a a' : A} {b b' : B}
              → a ≡ a' → b ≡ b' → f a b ≡ f a' b'
        cong₂ f refl refl = refl

-- ============================================================================
-- PROPERTY 15: Violation completeness — halt ⇒ PropertyResponse (sats ++ violation)
-- ============================================================================

-- If the frame is monotonic and some property's stepProperty halts,
-- handleDataFrame returns PropertyResponse carrying the preceding
-- satisfactions followed by the violation in source-order.  R23 —
-- AGDA-D-12.1: pre-R23 the conclusion was a singleton-Violation
-- PropertyResponse; after the mid-stream-Satisfaction lift the
-- violation arrives at the tail of a (possibly empty) satisfaction list.
handleDataFrame-violation-complete : ∀ {n} dbc (props : List (PropertyState n)) prev cache tf (idx : Fin n) ce
  → checkMonotonic prev tf ≡ nothing
  → specHalt (stepProperty dbc cache tf) props ≡ just (idx , ce)
  → proj₂ (handleDataFrame (Streaming n dbc props prev cache) tf)
    ≡ Response.PropertyResponse
        (map (λ i → PR.PropertyResult.Satisfaction (toℕ i))
             (specCompletions (stepProperty dbc cache tf) props)
         ++ₗ (PR.PropertyResult.Violation (toℕ idx)
                (mkCounterexampleData (TimedFrame.timestamp (Counterexample.violatingFrame ce))
                                      (Counterexample.reason ce))
              ∷ []))
handleDataFrame-violation-complete dbc props prev cache tf idx ce mono spec-eq
  rewrite mono =
    cong (λ p → proj₂ (dispatchIterResult dbc p tf updatedCache)) iter-eq
  where
    step = stepProperty dbc cache tf
    updatedCache = updateCacheFromFrame dbc cache (timestamp tf) (TimedFrame.frame tf)
    iter-eq : iterate step props ≡
                (specResult step props , just (idx , ce) , specCompletions step props)
    iter-eq = trans (iterate-correct step props)
                    (cong (λ h → (specResult step props , h , specCompletions step props)) spec-eq)
