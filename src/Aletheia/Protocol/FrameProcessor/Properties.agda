-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Correctness properties for the frame processing path (curated facade).
--
-- Purpose: Re-export the step-level, cache-level, handler, atom-bound,
--   and timestamp-monotonicity theorems used by downstream proofs and
--   FFI consumers, grouped by topic.
--
-- The actual proofs live in five sibling submodules so that IDE
-- jump-to-definition stays fast and each layer can be re-checked
-- independently:
--
--   Properties.Step      — Step-level state machine, decomposition, and
--                          Ack/Violation soundness/completeness
--                          (P1-P8, P14-P15).
--   Properties.Cache     — Signal cache update decomposition + monotonicity
--                          / timestamp-bound preservation (P10-P13, P23-P26).
--   Properties.Handlers  — FFI link properties + read-only handler
--                          state preservation (P16-P22).
--   Properties.Bounded   — Atom-index faithfulness (P9) and atom-index
--                          bound through simplify/stepL (P27).
--   Properties.Monotonic — Timestamp monotonicity enforcement at the step
--                          level + trace-level lift to Trace.CANTrace.Monotonic
--                          (P28-P29).
--
-- Public API consumed downstream of this module:
--   - `AllBelow`, `mkPredTable-lookup` — used by `Protocol.Adequacy.WarmCache`.
-- The remaining names are re-exported for completeness so external clients
-- can keep importing `Aletheia.Protocol.FrameProcessor.Properties` directly.
module Aletheia.Protocol.FrameProcessor.Properties where

-- ============================================================================
-- STEP-LEVEL PROPERTIES (P1-P8, P14-P15)
-- ============================================================================
-- State machine guards, byte modulus identity, classifyStepResult /
-- stepProperty / dispatchIterResult characterizations, the Streaming
-- decomposition lemma, and Ack/Violation soundness + completeness.
open import Aletheia.Protocol.FrameProcessor.Properties.Step public
  using ( )

-- ============================================================================
-- CACHE UPDATE PROPERTIES (P10-P13, P23-P26, P30)
-- ============================================================================
-- `updateCache` step lemmas plus properties of the shared per-frame extraction
-- table (`extractTable`/`cacheFromTable`) that `updateCacheFromFrame` folds:
-- table-lookup faithfulness, the monotonicity / timestamp-bound / no-message
-- preservation properties consumed by `Protocol.Adequacy.WarmCache`, and the
-- coherence property (P30) showing that the post-update cache for a frame
-- agrees with the value `extractTruthValue` would compute on the same frame.
open import Aletheia.Protocol.FrameProcessor.Properties.Cache public
  using ( )

-- ============================================================================
-- HANDLER + FFI LINK PROPERTIES (P16-P19, P22)
-- ============================================================================
-- `processFrameDirect` decomposition (state passes through, response is
-- formatJSON ∘ formatResponse), end-to-end Ack soundness at the JSON
-- level, and read-only handler state preservation for the two remaining
-- non-mutating handler entry points (extract and formatDBC).
open import Aletheia.Protocol.FrameProcessor.Properties.Handlers public
  using ( )

-- ============================================================================
-- ATOM-INDEX BOUND PROPERTIES (P9, P27)
-- ============================================================================
-- `mkPredTable` faithfulness (atom indices line up with `lookupAtom`)
-- and the atom-index bound through `simplify` and `stepL`. The bound
-- terminal `mkPredTable-bounded` corollary is what makes the
-- `nothing → Unknown` branch in `mkPredTable` provably dead code on
-- the streaming hot path.
--
-- `AllBelow` and `mkPredTable-lookup` are the names consumed by
-- `Protocol.Adequacy.WarmCache` to discharge the warm-cache agreement chain.
open import Aletheia.Protocol.FrameProcessor.Properties.Bounded public
  using ( mkPredTable-lookup
        ; AllBelow
        )

-- ============================================================================
-- TIMESTAMP MONOTONICITY (P28, P29)
-- ============================================================================
-- Step-level enforcement: `checkMonotonic` accepts iff `timestampℕ tf ≥
-- timestampℕ prev`, and `handleDataFrame` rejects backward frames with
-- `NonMonotonicTimestamp`. Trace-level lift: the sequence of frames
-- surviving the running `checkMonotonic` filter is globally `Monotonic`
-- in the sense of `Trace.CANTrace.Monotonic`, discharging the
-- `Monotonic σ` precondition of the metric LTL soundness theorems in
-- `Coalgebra.Properties`.
open import Aletheia.Protocol.FrameProcessor.Properties.Monotonic public
  using ( )

-- ============================================================================
-- EXTRACT-ONCE VERDICT PRESERVATION
-- ============================================================================
-- The runtime step drives predicate evaluation from the shared per-frame
-- extraction table (`mkPredTableT`), while adequacy reasons about the
-- frame-extracting spec (`mkPredTable`).  This bridge proves the two produce the
-- SAME `StepOutcome` when the table covers the property's atoms — which
-- `handleDataFrame` guarantees by building the table over `readableSignals props`
-- — so the extract-once optimization is proof-carrying on the eval side.  Pulled
-- in as a walk root here (nothing else imports it) and the first consumer of
-- `extractTable-faithful`.
open import Aletheia.Protocol.FrameProcessor.Properties.VerdictPreserved public
  using ( stepL-cong; evalPredicateTVT-faithful; stepProperty-preserves )
