-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K --no-main #-}

-- Main entry point for Aletheia (JSON streaming protocol + binary APIs).
--
-- Purpose: Curated public facade re-exporting the types, state-machine,
--   command dispatch, frame/error types, and FFI entry points that external
--   callers (Haskell REPL, tests, AletheiaFFI.hs) need.
--
-- State Machine: WaitingForDBC → ReadyToStream → Streaming
--
-- Compilation: Compiled to Haskell via MAlonzo; the FFI shim
-- (AletheiaFFI.hs) calls processJSONLine and the processXxxDirect/Bin
-- entries directly from the Main.JSON and Main.Binary sub-modules. This
-- facade does not add FFI symbols of its own — it exists for
-- discoverability. Bindings (Python/C++/Go) load libaletheia-ffi.so via
-- ctypes/dlopen (direct FFI).
--
-- Sub-modules:
--   Main.JSON   — processJSONLine and (private) JSON dispatch helpers
--   Main.Binary — all binary entry points (*Direct for JSON output,
--                 *Bin for binary output)
--
-- Key design: ALL logic lives in Agda (parsing, validation, state, LTL
-- checking). Haskell FFI shim (AletheiaFFI.hs) only handles C-callable
-- exports and state management.
--
-- Name clashes: The constructor `Response.Error` (from
-- `Aletheia.Protocol.Message`) and the constructor `TraceEvent.Error`
-- (from `Aletheia.Trace.CANTrace`) both clash with the `Error` type from
-- `Aletheia.Error`. They are re-exported under renamed names
-- (`ResponseError` and `TraceError`) to keep all three names in scope
-- simultaneously from this facade.
--
-- Adequacy scope: The production pipeline exposed here has
-- a formal soundness proof chain composed of two theorems:
--   * `Aletheia.LTL.Adequacy.Pipeline.pipeline-adequate` — the
--     simplify/stepL loop preserves the adequacy of the coalgebra (the
--     simplify pass between steps does not alter verdicts).
--   * `Aletheia.Protocol.Adequacy.StreamingWarm.streaming-warms-cache` —
--     on a trace that satisfies `AllObserved dbc σ atoms` (every atom's
--     target signal is extracted from at least one frame in σ), the
--     streaming cache-update discharges the `AllCached` premise of
--     `warm-cache-agreement`.
-- Together, these yield unconditional soundness for offline traces that
-- satisfy `AllObserved`. The FFI runtime does NOT check `AllObserved` on
-- the hot path — it is a user obligation on the trace. Traces that omit a
-- property's target signal may silently report the property as `Unsure`
-- rather than `Violated`/`Satisfied` (three-valued Kleene finalization),
-- which remains sound but not complete (see `PROTOCOL.md § Streaming
-- Semantics: Soundness vs. Completeness`).
module Aletheia.Main where

-- ============================================================================
-- FFI ENTRY POINTS
-- ============================================================================
-- Called directly from AletheiaFFI.hs via MAlonzo (the shim imports
-- MAlonzo.Code.Aletheia.Main.JSON and MAlonzo.Code.Aletheia.Main.Binary
-- rather than this facade, so these re-exports are for discoverability).

open import Aletheia.Main.JSON public
  using ()

open import Aletheia.Main.Binary public
  using ( processFrameDirect
        )

-- ============================================================================
-- STATE MACHINE
-- ============================================================================
-- Stream state type, phase constructors, initial state, and the public
-- frame/trace-event handlers. `checkMonotonic` is exported so tests and
-- proof clients can reference the monotonicity predicate directly.

open import Aletheia.Protocol.StreamState public
  using ( )

-- ============================================================================
-- COMMAND DISPATCH
-- ============================================================================
-- High-level streaming protocol: StreamCommand sum, Response sum, and
-- the command dispatcher. Response.Error is renamed to `ResponseError`
-- to avoid clashing with Aletheia.Error.Error.

open import Aletheia.Protocol.Message public
  using ( )
  renaming ()

open import Aletheia.Protocol.Handlers public
  using ()

-- ============================================================================
-- FRAME, TRACE, AND DLC TYPES
-- ============================================================================
-- Types that appear in the signatures of the FFI entry points above.
-- TraceEvent.Error is renamed to `TraceError` to avoid clashing with
-- Aletheia.Error.Error.

open import Aletheia.CAN.Frame public
  using ( )

open import Aletheia.CAN.DLC public
  using ( )

open import Aletheia.Trace.CANTrace public
  using ( )
  renaming ()

open import Aletheia.Trace.Time public
  using ( )

-- ============================================================================
-- ERROR TYPES AND INSPECTION
-- ============================================================================
-- Top-level `Error` sum plus the per-domain error ADTs and the
-- `formatError` / `errorCode` inspection helpers that tests and callers
-- use to classify failures.

open import Aletheia.Error public
  using ( )

-- ============================================================================
-- JSON AND RESPONSE FORMATTING
-- ============================================================================
-- JSON datatype and the formatter that turns a Response into
-- wire-format JSON. Exposed so that callers that build Responses
-- directly (Haskell REPL, tests) can render them the same way the FFI
-- shim does.

open import Aletheia.Protocol.JSON public
  using ( )

open import Aletheia.Protocol.ResponseFormat public
  using ()

-- Cross-binding-identical Rational pretty-printer.
-- Exposed so the FFI shim can call `formatRational` on raw (numerator,
-- denominator) pairs and return the result via CString.  Replaces three
-- per-binding implementations with a single Agda kernel function.
open import Aletheia.DBC.RationalRenderer public
  using ()

-- Decimal-string → exact rational entry point for the FFI shim.
-- Exposed so `aletheia_parse_decimal` can call `parseDecimal` (the kernel's
-- single source of truth for decimal→rational across all bindings).  Opened
-- only to force MAlonzo compilation of the module; nothing is brought into
-- Main's scope (`using ()`).
open import Aletheia.DBC.TextParser.DecimalEntry public
  using ()
