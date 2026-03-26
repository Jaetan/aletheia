{-# OPTIONS --safe --without-K #-}

-- Correctness properties for the binary frame processing path.
--
-- Purpose: Prove properties of handleDataFrame — the function called by
--          the binary FFI entry point (processFrameDirect in Main.agda).
-- These proofs are about the code that actually runs in production.
--
-- Properties:
--   (1) handleDataFrame-guards: non-Streaming state → state unchanged
--   (2) mod-identity-byte: justifies the Haskell shim's bytesToAgdaVec
--       skipping % 256 for Word8 inputs
module Aletheia.Protocol.FrameProcessor.Properties where

open import Aletheia.Protocol.StreamState
    using (StreamState; StreamPhase; WaitingForDBC; ReadyToStream; Streaming;
           handleDataFrame)
open import Aletheia.Protocol.Message using (Response)
open import Aletheia.Trace.CANTrace using (TimedFrame)
open import Data.Product using (_×_; proj₁; proj₂)
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
