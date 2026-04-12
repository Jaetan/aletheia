{-# OPTIONS --safe --without-K #-}

-- Timestamp monotonicity properties of the LTL frame processor.
--
--   PROPERTY 28 — Step-local timestamp monotonicity:
--     `checkMonotonic` accepts iff `timestampℕ tf ≥ timestampℕ prev`,
--     and `handleDataFrame` rejects backward frames with the
--     `NonMonotonicTimestamp HandlerError`. The state's `prev` field is
--     the monotonicity anchor (proven by `handleDataFrame-rejects-regress`).
--
--   PROPERTY 29 — Trace-level lift:
--     The sequence of frames surviving the running `checkMonotonic`
--     filter is globally `Monotonic` in the sense of
--     `Trace.CANTrace.Monotonic`. This bridges the runtime enforcement
--     in `handleDataFrame` to the `Monotonic σ` precondition of the
--     metric LTL soundness theorems in `Coalgebra.Properties`.
--
-- Composes the `handleDataFrame-streaming` decomposition lemma from
-- `FrameProcessor.Properties.Step` to obtain the
-- `handleDataFrame-accepts-monotonic` and `handleDataFrame-first-frame`
-- corollaries.
module Aletheia.Protocol.FrameProcessor.Properties.Monotonic where

open import Aletheia.Protocol.StreamState
    using (StreamState; Streaming; handleDataFrame; checkMonotonic)
open import Aletheia.Protocol.StreamState.Internals
    using (stepProperty; dispatchIterResult; updateCacheFromFrame)
open import Aletheia.Protocol.Message using (Response; Error)
open import Aletheia.Protocol.Iteration using (iterate)
open import Aletheia.Protocol.FrameProcessor.Properties.Step
    using (handleDataFrame-streaming)
open import Aletheia.Trace.CANTrace using (TimedFrame; timestamp; timestampℕ; Monotonic)
open import Aletheia.Error using (NonMonotonicTimestamp; HandlerErr; WithContext)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; _<_; _≤_)
open import Data.Nat.Properties using (≮⇒≥; <⇒<ᵇ; <ᵇ⇒<)
open import Data.Bool using (T; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

-- ============================================================================
-- PROPERTY 28: Timestamp monotonicity enforcement
-- ============================================================================
--
-- Lifts the Trace.CANTrace.Monotonic predicate from "defined but unused" to
-- a property of the operational streaming pipeline. handleDataFrame now
-- refuses non-monotonic frames in Agda (single source of truth across all
-- bindings), and the proofs below connect that runtime check to the
-- Monotonic predicate used by Coalgebra/Properties metric LTL theorems.

-- The first frame after StartStream (prev = nothing) is always accepted.
checkMonotonic-first : ∀ tf → checkMonotonic nothing tf ≡ nothing
checkMonotonic-first tf = refl

-- checkMonotonic returns nothing iff timestamp tf ≥ timestamp prev.
-- This is the "accept" branch of the runtime check.
checkMonotonic-≥ : ∀ p tf
  → timestampℕ p ≤ timestampℕ tf
  → checkMonotonic (just p) tf ≡ nothing
checkMonotonic-≥ p tf p≤tf with timestampℕ tf Data.Nat.<ᵇ timestampℕ p in eq
  where open import Data.Nat using (_<ᵇ_)
... | false = refl
... | true  = ⊥-elim (<⇒≱ tf<p p≤tf)
  where
    open import Data.Nat.Properties using (<⇒≱)
    tf<p : timestampℕ tf < timestampℕ p
    tf<p = <ᵇ⇒< (timestampℕ tf) (timestampℕ p) (subst T (sym eq) tt)

-- checkMonotonic returns just(NonMonotonicTimestamp) iff timestampℕ tf < timestampℕ prev.
-- This is the "reject" branch of the runtime check.
checkMonotonic-< : ∀ p tf
  → timestampℕ tf < timestampℕ p
  → checkMonotonic (just p) tf ≡ just (NonMonotonicTimestamp (timestampℕ tf) (timestampℕ p))
checkMonotonic-< p tf tf<p with timestampℕ tf Data.Nat.<ᵇ timestampℕ p in eq
  where open import Data.Nat using (_<ᵇ_)
... | true  = refl
... | false = ⊥-elim (subst T eq (<⇒<ᵇ tf<p))

-- Backward timestamps are rejected with NonMonotonicTimestamp HandlerError.
-- The state's `prev` is left unchanged so the next frame is still checked
-- against the same anchor — the rejected frame is never the new anchor.
handleDataFrame-rejects-regress : ∀ dbc props p cache tf
  → timestampℕ tf < timestampℕ p
  → handleDataFrame (Streaming dbc props (just p) cache) tf
    ≡ (Streaming dbc props (just p) cache ,
       Response.Error
         (WithContext "DataFrame"
           (HandlerErr (NonMonotonicTimestamp (timestampℕ tf) (timestampℕ p)))))
handleDataFrame-rejects-regress dbc props p cache tf tf<p
  rewrite checkMonotonic-< p tf tf<p
  = refl

-- A monotonic frame leaves handleDataFrame's behavior unchanged from the
-- pre-enforcement decomposition. The metric LTL completeness theorems in
-- Coalgebra/Properties take Monotonic σ as a hypothesis; this property
-- guarantees that the streaming pipeline only enters its iteration logic on
-- frames that satisfy the monotonicity precondition those theorems require.
handleDataFrame-accepts-monotonic : ∀ dbc props p cache tf
  → timestampℕ p ≤ timestampℕ tf
  → handleDataFrame (Streaming dbc props (just p) cache) tf
    ≡ let updatedCache = updateCacheFromFrame dbc cache
                           (timestampℕ tf) (TimedFrame.frame tf)
      in dispatchIterResult dbc
           (iterate (stepProperty dbc cache tf) props)
           tf updatedCache
handleDataFrame-accepts-monotonic dbc props p cache tf p≤tf =
  handleDataFrame-streaming dbc props (just p) cache tf
    (checkMonotonic-≥ p tf p≤tf)

-- After StartStream (prev = nothing), the first frame is always accepted.
handleDataFrame-first-frame : ∀ dbc props cache tf
  → handleDataFrame (Streaming dbc props nothing cache) tf
    ≡ let updatedCache = updateCacheFromFrame dbc cache
                           (timestampℕ tf) (TimedFrame.frame tf)
      in dispatchIterResult dbc
           (iterate (stepProperty dbc cache tf) props)
           tf updatedCache
handleDataFrame-first-frame dbc props cache tf =
  handleDataFrame-streaming dbc props nothing cache tf refl

-- Inverse of checkMonotonic-≥: if the runtime check accepts a frame against
-- an actual anchor, then the anchor's timestamp is ≤ the new frame's
-- timestamp. This is the key per-step bound propagated by Property 29
-- into a trace-level Monotonic guarantee.
checkMonotonic-≥-inv : ∀ p tf
  → checkMonotonic (just p) tf ≡ nothing
  → timestampℕ p ≤ timestampℕ tf
checkMonotonic-≥-inv p tf eq =
  ≮⇒≥ λ tf<p → nothing≢just (trans (sym eq) (checkMonotonic-< p tf tf<p))
  where
    nothing≢just : ∀ {A : Set} {x : A} → _≡_ {A = Maybe A} nothing (just x) → ⊥
    nothing≢just ()

-- ============================================================================
-- PROPERTY 29: Trace-level monotonicity from runtime enforcement
-- ============================================================================
--
-- Property 28 proved the step-local monotonicity contract of checkMonotonic.
-- This property lifts that contract to the trace level: the sequence of
-- frames surviving the running checkMonotonic filter (starting from any
-- initial anchor) is globally Monotonic in the sense of
-- Trace.CANTrace.Monotonic.
--
-- This closes the formal bridge between the runtime enforcement in
-- handleDataFrame (Protocol.StreamState) and the Monotonic σ precondition
-- of the metric LTL soundness theorems in Coalgebra.Properties: a client
-- that iterates handleDataFrame over an input sequence and feeds its
-- accepted subsequence (as modelled by checkedFrames below) to a metric
-- operator automatically discharges the Monotonic σ hypothesis.

-- Filter a sequence of frames through the running monotonicity check.
-- Mirrors the frame-acceptance behavior of iterating handleDataFrame in the
-- Streaming phase: rejected frames are dropped (anchor unchanged), accepted
-- frames become the new anchor for subsequent checks.
checkedFrames : Maybe TimedFrame → List TimedFrame → List TimedFrame
checkedFrames _    [] = []
checkedFrames prev (tf ∷ rest) with checkMonotonic prev tf
... | nothing = tf ∷ checkedFrames (just tf) rest
... | just _  = checkedFrames prev rest

-- Lower-bounded monotonicity: the trace is Monotonic, and (when non-empty
-- and paired with a concrete anchor) its head's timestamp is ≥ the anchor.
-- This is the inductive invariant used to prove checkedFrames-monotonic;
-- carrying the head bound lets the proof extend the trace by one element
-- without re-analyzing its structure.
HeadBounded : Maybe TimedFrame → List TimedFrame → Set
HeadBounded _        []          = ⊤
HeadBounded nothing  (f ∷ rest)  = Monotonic (f ∷ rest)
HeadBounded (just p) (f ∷ rest)  = timestampℕ p ≤ timestampℕ f × Monotonic (f ∷ rest)

-- Discard the anchor bound: a head-bounded trace is monotonic.
HeadBounded→Monotonic : ∀ prev σ → HeadBounded prev σ → Monotonic σ
HeadBounded→Monotonic _        []        _         = tt
HeadBounded→Monotonic nothing  (_ ∷ _)   mon       = mon
HeadBounded→Monotonic (just _) (_ ∷ _)   (_ , mon) = mon

-- Cons lemma: if σ is head-bounded by f (i.e. σ starts with something ≥ f
-- or is empty), then f ∷ σ is monotonic. Used to build a longer monotonic
-- trace from the current frame and the inductive hypothesis about the rest.
mon-cons : ∀ f σ → HeadBounded (just f) σ → Monotonic (f ∷ σ)
mon-cons f []         _             = tt
mon-cons f (_ ∷ _)    (f≤g , mon)   = f≤g , mon

-- Main theorem (strong form): the filtered trace is head-bounded by the
-- initial anchor. Induction on inputs; case split on the running check.
checkedFrames-headBounded : ∀ prev inputs → HeadBounded prev (checkedFrames prev inputs)
checkedFrames-headBounded _        []        = tt
checkedFrames-headBounded nothing  (tf ∷ rest) =
  mon-cons tf (checkedFrames (just tf) rest)
           (checkedFrames-headBounded (just tf) rest)
checkedFrames-headBounded (just p) (tf ∷ rest) with checkMonotonic (just p) tf in cm-eq
... | nothing =
    checkMonotonic-≥-inv p tf cm-eq ,
    mon-cons tf (checkedFrames (just tf) rest)
             (checkedFrames-headBounded (just tf) rest)
... | just _  = checkedFrames-headBounded (just p) rest

-- Main theorem (weak form): the filtered trace is monotonic. This is the
-- bridge consumed by clients of the streaming pipeline — any σ built from
-- handleDataFrame's accepted frames satisfies Trace.CANTrace.Monotonic,
-- discharging the precondition of metric LTL soundness theorems in
-- Coalgebra.Properties (runL-monotonic-mtl-sound and its dual forms).
checkedFrames-monotonic : ∀ prev inputs → Monotonic (checkedFrames prev inputs)
checkedFrames-monotonic prev inputs =
  HeadBounded→Monotonic prev (checkedFrames prev inputs)
                        (checkedFrames-headBounded prev inputs)
