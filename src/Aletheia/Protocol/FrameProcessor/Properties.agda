{-# OPTIONS --safe --without-K #-}

-- Correctness properties for the frame processing path.
--
-- Purpose: Prove properties of handleDataFrame — the core function called by
--          both the JSON path (processJSONLine) and the binary FFI entry point
--          (processFrameDirect in Main.agda).
-- These proofs are about the code that actually runs in production.
--
-- Properties:
--   (1) handleDataFrame-guards: non-Streaming state → state unchanged
--   (2) mod-identity-byte: justifies the Haskell shim's bytesToAgdaVec
--       skipping % 256 for Word8 inputs
--   (3) classifyStepResult/stepProperty: classify result faithfully reflects stepL
--   (4) dispatchIterResult: nothing → Ack, just → PropertyResponse
--   (5) handleDataFrame-streaming: decomposition into dispatchIterResult ∘ iterate ∘ stepProperty
--   (6) handleDataFrame-ack-sound: Ack response ⇒ no property violated
--   (7) handleDataFrame-violation-sound: PropertyResponse ⇒ some property violated
module Aletheia.Protocol.FrameProcessor.Properties where

open import Aletheia.Protocol.StreamState
    using (StreamState; StreamPhase; WaitingForDBC; ReadyToStream; Streaming;
           handleDataFrame; PropertyState; mkPropertyState;
           classifyStepResult; stepProperty; dispatchIterResult;
           mkPredTable; updateCacheFromFrame)
open import Aletheia.Protocol.Message using (Response)
open import Aletheia.Protocol.Response as PR using (mkCounterexampleData; PropertyResult)
open import Aletheia.Protocol.Iteration using (StepOutcome; advance; halt; iterate)
open import Aletheia.Trace.CANTrace using (TimedFrame)
open import Aletheia.LTL.Incremental using (StepResult; Continue; Violated; Satisfied; Counterexample)
open import Aletheia.LTL.Coalgebra using (LTLProc; stepL; simplify)
open import Aletheia.LTL.SignalPredicate using (SignalCache)
open import Aletheia.DBC.Types using (DBC)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List)
open import Data.Nat using (ℕ; _<_; _%_)
open import Data.Nat.DivMod using (m<n⇒m%n≡m)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- ============================================================================
-- PROPERTY 1: State machine guards
-- ============================================================================

-- When not in Streaming phase, handleDataFrame returns the state unchanged.
-- This is a direct case split — handleDataFrame pattern-matches on phase first.

handleDataFrame-guard-waitingForDBC : ∀ (state : StreamState) (tf : TimedFrame)
    → StreamState.phase state ≡ WaitingForDBC
    → proj₁ (handleDataFrame state tf) ≡ state
handleDataFrame-guard-waitingForDBC state tf refl = refl

handleDataFrame-guard-readyToStream : ∀ (state : StreamState) (tf : TimedFrame)
    → StreamState.phase state ≡ ReadyToStream
    → proj₁ (handleDataFrame state tf) ≡ state
handleDataFrame-guard-readyToStream state tf refl = refl

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

-- In Streaming phase with loaded DBC, handleDataFrame decomposes into:
--   dispatchIterResult ∘ iterate ∘ stepProperty
-- This is the bridge between handleDataFrame and the factored helpers.
handleDataFrame-streaming : ∀ state tf dbc
  → StreamState.phase state ≡ Streaming
  → StreamState.dbc state ≡ just dbc
  → handleDataFrame state tf
    ≡ let cache = StreamState.signalCache state
          updatedCache = updateCacheFromFrame dbc cache
                           (TimedFrame.timestamp tf) (TimedFrame.frame tf)
      in dispatchIterResult dbc
           (iterate (stepProperty dbc cache tf) (StreamState.properties state))
           tf updatedCache
handleDataFrame-streaming state tf dbc phase-eq dbc-eq
  with StreamState.phase state | phase-eq
... | .Streaming | refl with StreamState.dbc state | dbc-eq
... | .(just dbc) | refl = refl

-- ============================================================================
-- PROPERTY 7: Ack soundness — Ack means no property violated
-- ============================================================================

-- If handleDataFrame returns Ack, then iterate found no halt evidence.
-- Combined with iterate-correct and specHalt, this means:
-- no property's stepL returned Violated.
handleDataFrame-ack-sound : ∀ state tf dbc
  → StreamState.phase state ≡ Streaming
  → StreamState.dbc state ≡ just dbc
  → proj₂ (handleDataFrame state tf) ≡ Response.Ack
  → proj₂ (iterate (stepProperty dbc (StreamState.signalCache state) tf)
                    (StreamState.properties state)) ≡ nothing
handleDataFrame-ack-sound state tf dbc phase-eq dbc-eq resp-eq
  with StreamState.phase state | phase-eq
... | .Streaming | refl with StreamState.dbc state | dbc-eq
... | .(just dbc) | refl
  with iterate (stepProperty dbc (StreamState.signalCache state) tf)
               (StreamState.properties state) | resp-eq
... | (ps , nothing)         | _ = refl
... | (ps , just (idx , ce)) | ()

-- ============================================================================
-- PROPERTY 8: Violation soundness — PropertyResponse means some property violated
-- ============================================================================

-- If handleDataFrame returns PropertyResponse, then iterate found halt evidence:
-- some property's stepProperty halted (which, by stepProperty-halt-implies-violated,
-- means some stepL returned Violated).
handleDataFrame-violation-sound : ∀ state tf dbc pr
  → StreamState.phase state ≡ Streaming
  → StreamState.dbc state ≡ just dbc
  → proj₂ (handleDataFrame state tf) ≡ Response.PropertyResponse pr
  → ∃[ e ] proj₂ (iterate (stepProperty dbc (StreamState.signalCache state) tf)
                           (StreamState.properties state)) ≡ just e
handleDataFrame-violation-sound state tf dbc pr phase-eq dbc-eq resp-eq
  with StreamState.phase state | phase-eq
... | .Streaming | refl with StreamState.dbc state | dbc-eq
... | .(just dbc) | refl
  with iterate (stepProperty dbc (StreamState.signalCache state) tf)
               (StreamState.properties state) | resp-eq
... | (ps , nothing)    | ()
... | (ps , just e)     | _ = e , refl
