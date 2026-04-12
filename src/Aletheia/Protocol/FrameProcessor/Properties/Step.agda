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
    using (StreamState; WaitingForDBC; ReadyToStream; Streaming;
           handleDataFrame; checkMonotonic;
           PropertyState; mkPropertyState)
open import Aletheia.Protocol.StreamState.Internals
    using (classifyStepResult; stepProperty; dispatchIterResult;
           mkPredTable; updateCacheFromFrame)
open import Aletheia.Protocol.Message using (Response; Ack; Error; PropertyResponse)
open import Aletheia.Protocol.Response as PR using (mkCounterexampleData; PropertyResult)
open import Aletheia.Protocol.Iteration using (StepOutcome; advance; halt; iterate; iterate-correct; specHalt)
open import Aletheia.Trace.CANTrace using (TimedFrame; timestamp; timestampℕ)
open import Aletheia.LTL.Incremental using (StepResult; Continue; Violated; Satisfied; Counterexample)
open import Aletheia.LTL.Coalgebra using (stepL)
open import Aletheia.LTL.Simplify using (simplify)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _<_; _%_)
open import Data.Nat.DivMod using (m<n⇒m%n≡m)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- ============================================================================
-- PROPERTY 1: State machine guards
-- ============================================================================

-- When not in Streaming phase, handleDataFrame returns the state unchanged.
-- With the sum type, these are trivially refl — no precondition needed.

handleDataFrame-guard-waitingForDBC : ∀ (tf : TimedFrame)
    → proj₁ (handleDataFrame WaitingForDBC tf) ≡ WaitingForDBC
handleDataFrame-guard-waitingForDBC tf = refl

handleDataFrame-guard-readyToStream : ∀ dbc props cache (tf : TimedFrame)
    → proj₁ (handleDataFrame (ReadyToStream dbc props cache) tf) ≡ ReadyToStream dbc props cache
handleDataFrame-guard-readyToStream dbc props cache tf = refl

-- ============================================================================
-- PROPERTY 2: Byte modulus identity (boundary justification)
-- ============================================================================

-- When n < 256, n % 256 ≡ n.
-- This justifies the Haskell shim's bytesToAgdaVec skipping % 256:
-- Agda's listToVec applies (x % 256), but the Haskell shim constructs
-- Vec entries directly from Word8 values (which are already in [0,255]).
-- Since Word8 ∈ [0,255] implies n < 256, the modulo is a no-op.
mod-identity-byte : ∀ (n : ℕ) → n < 256 → n % 256 ≡ n
mod-identity-byte n n<256 = m<n⇒m%n≡m n<256

-- ============================================================================
-- PROPERTY 3: classifyStepResult faithfully reflects StepResult constructors
-- ============================================================================

-- Violated → halt (property index + counterexample)
classifyStepResult-violated : ∀ ce prop
  → classifyStepResult (Violated ce) prop ≡ halt (PropertyState.index prop , ce)
classifyStepResult-violated ce prop = refl

-- Continue → advance (simplified successor state)
classifyStepResult-continue : ∀ n newProc prop
  → classifyStepResult (Continue n newProc) prop
    ≡ advance (mkPropertyState (PropertyState.index prop)
                                (PropertyState.formula prop)
                                (PropertyState.atoms prop)
                                (simplify newProc))
classifyStepResult-continue n newProc prop = refl

-- Satisfied → advance (property state unchanged)
classifyStepResult-satisfied : ∀ prop
  → classifyStepResult Satisfied prop ≡ advance prop
classifyStepResult-satisfied prop = refl

-- ============================================================================
-- PROPERTY 4: stepProperty — halt iff stepL returns Violated
-- ============================================================================

-- Forward: If stepL returns Violated, stepProperty halts with matching evidence.
stepProperty-violated : ∀ dbc cache tf prop ce
  → stepL (mkPredTable dbc cache (PropertyState.atoms prop)) (PropertyState.proc prop) tf ≡ Violated ce
  → stepProperty dbc cache tf prop ≡ halt (PropertyState.index prop , ce)
stepProperty-violated dbc cache tf prop ce steq rewrite steq = refl

-- Backward: If stepProperty halts, stepL returned Violated.
-- Returns: proof that idx matches the property index, and the stepL equality.
stepProperty-halt-implies-violated : ∀ dbc cache tf prop idx ce
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

-- When iterate finds no violation (nothing), response is Ack.
dispatchIterResult-ack : ∀ dbc ps tf cache
  → proj₂ (dispatchIterResult dbc (ps , nothing) tf cache) ≡ Response.Ack
dispatchIterResult-ack dbc ps tf cache = refl

-- When iterate finds a violation (just), response is PropertyResponse.
dispatchIterResult-violation : ∀ dbc ps idx ce tf cache
  → proj₂ (dispatchIterResult dbc (ps , just (idx , ce)) tf cache)
    ≡ Response.PropertyResponse
        (PR.PropertyResult.Violation idx
          (mkCounterexampleData (TimedFrame.timestamp (Counterexample.violatingFrame ce))
                                (Counterexample.reason ce)))
dispatchIterResult-violation dbc ps idx ce tf cache = refl

-- ============================================================================
-- PROPERTY 6: handleDataFrame Streaming decomposition
-- ============================================================================

-- In Streaming phase with a monotonic timestamp, handleDataFrame decomposes into:
--   dispatchIterResult ∘ iterate ∘ stepProperty
-- The precondition `checkMonotonic prev tf ≡ nothing` rules out the rejection
-- branch added when monotonicity enforcement was lifted into Agda.
handleDataFrame-streaming : ∀ dbc props prev cache tf
  → checkMonotonic prev tf ≡ nothing
  → handleDataFrame (Streaming dbc props prev cache) tf
    ≡ let updatedCache = updateCacheFromFrame dbc cache
                           (timestampℕ tf) (TimedFrame.frame tf)
      in dispatchIterResult dbc
           (iterate (stepProperty dbc cache tf) props)
           tf updatedCache
handleDataFrame-streaming dbc props prev cache tf mono
  rewrite mono = refl

-- ============================================================================
-- PROPERTY 7: Ack soundness — Ack means no property violated
-- ============================================================================

-- If handleDataFrame returns Ack, then the frame was monotonic and iterate
-- found no halt evidence. The monotonicity precondition rules out the
-- NonMonotonicTimestamp branch (which never returns Ack).
handleDataFrame-ack-sound : ∀ dbc props prev cache tf
  → checkMonotonic prev tf ≡ nothing
  → proj₂ (handleDataFrame (Streaming dbc props prev cache) tf) ≡ Response.Ack
  → proj₂ (iterate (stepProperty dbc cache tf) props) ≡ nothing
handleDataFrame-ack-sound dbc props prev cache tf mono resp-eq
  rewrite mono
  with iterate (stepProperty dbc cache tf) props | resp-eq
... | (ps , nothing)         | _ = refl
... | (ps , just (idx , ce)) | ()

-- ============================================================================
-- PROPERTY 8: Violation soundness — PropertyResponse means some property violated
-- ============================================================================

-- If handleDataFrame returns PropertyResponse, then the frame was monotonic
-- and iterate found halt evidence. The monotonicity precondition rules out the
-- NonMonotonicTimestamp branch (which returns Error, not PropertyResponse).
handleDataFrame-violation-sound : ∀ dbc props prev cache tf pr
  → checkMonotonic prev tf ≡ nothing
  → proj₂ (handleDataFrame (Streaming dbc props prev cache) tf) ≡ Response.PropertyResponse pr
  → ∃[ e ] proj₂ (iterate (stepProperty dbc cache tf) props) ≡ just e
handleDataFrame-violation-sound dbc props prev cache tf pr mono resp-eq
  rewrite mono
  with iterate (stepProperty dbc cache tf) props | resp-eq
... | (ps , nothing)    | ()
... | (ps , just e)     | _ = e , refl

-- ============================================================================
-- PROPERTY 14: Ack completeness — no violation ⇒ Ack
-- ============================================================================

-- If the frame is monotonic and no property's stepProperty halts, handleDataFrame
-- returns Ack. Without the monotonicity precondition the result would be a
-- NonMonotonicTimestamp Error instead.
handleDataFrame-ack-complete : ∀ dbc props prev cache tf
  → checkMonotonic prev tf ≡ nothing
  → specHalt (stepProperty dbc cache tf) props ≡ nothing
  → proj₂ (handleDataFrame (Streaming dbc props prev cache) tf) ≡ Response.Ack
handleDataFrame-ack-complete dbc props prev cache tf mono spec-eq
  rewrite mono
  rewrite iterate-correct (stepProperty dbc cache tf) props
  rewrite spec-eq
  = refl

-- ============================================================================
-- PROPERTY 15: Violation completeness — some violation ⇒ PropertyResponse
-- ============================================================================

-- If the frame is monotonic and some property's stepProperty halts,
-- handleDataFrame returns PropertyResponse.
handleDataFrame-violation-complete : ∀ dbc props prev cache tf idx ce
  → checkMonotonic prev tf ≡ nothing
  → specHalt (stepProperty dbc cache tf) props ≡ just (idx , ce)
  → proj₂ (handleDataFrame (Streaming dbc props prev cache) tf)
    ≡ Response.PropertyResponse
        (PR.PropertyResult.Violation idx
          (mkCounterexampleData (TimedFrame.timestamp (Counterexample.violatingFrame ce))
                                (Counterexample.reason ce)))
handleDataFrame-violation-complete dbc props prev cache tf idx ce mono spec-eq
  rewrite mono
  rewrite iterate-correct (stepProperty dbc cache tf) props
  rewrite spec-eq
  = refl
