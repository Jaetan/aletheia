-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Protocol message types for the JSON streaming LTL checker.
--
-- Purpose: Define command and response types for the streaming protocol.
-- Types: StreamCommand (the JSON command vocabulary), Response (every reply
--        shape the protocol can emit).
-- Role: The protocol's shared vocabulary — Routing constructs StreamCommands,
--       the Handlers tree produces Responses, ResponseFormat serializes them.
module Aletheia.Protocol.Message where

open import Data.String using (String)
open import Data.List using (List)
open import Data.Rational using (ℚ)
open import Data.Product using (_×_)
open import Aletheia.Protocol.Response using (PropertyResult; Warning)
-- JSON.Types (not the Protocol.JSON umbrella): only the JSON value type
-- is needed here; the umbrella re-exports the parser, which would put
-- the message vocabulary inside every combinator change's recheck closure.
open import Aletheia.Protocol.JSON.Types using (JSON)
open import Aletheia.DBC.Types using (ValidationIssue)
import Aletheia.Error as Err

-- ============================================================================
-- STREAMING PROTOCOL COMMANDS (Phase 2B)
-- ============================================================================

-- DBC / property commands carried over the JSON command path
-- (`aletheia_process` → `processStreamCommand`).  Frame-level streaming —
-- start/end stream, send-frame, extract-signals, format-DBC — is NOT a
-- StreamCommand: production drives it through the binary FFI entry points
-- in `Main/Binary.agda` (`process*Direct`), which call the same handlers
-- directly.  The JSON mirrors of those operations were test-only and have
-- been removed; only the DBC/property commands below have no binary twin.
data StreamCommand : Set where
  -- Parse DBC file and reset all state
  -- Args: DBC JSON structure
  ParseDBC : JSON → StreamCommand

  -- Set LTL properties to check (must be called after ParseDBC, before streaming begins)
  -- Args: List of property JSON objects (parsed by Python DSL)
  SetProperties : List JSON → StreamCommand

  -- Validate DBC structure and return all issues (read-only, does not change state)
  -- Args: DBC JSON structure
  ValidateDBC : JSON → StreamCommand

  -- Parse DBC from raw DBC text using the verified Agda text parser
  -- (exposes parseText + validateDBCFull as one operation).
  -- Args: DBC text image (e.g. the contents of a .dbc file)
  ParseDBCText : String → StreamCommand

  -- Format DBC JSON dict back to .dbc text.
  -- Args: DBC JSON structure (same wire shape ParseDBCText returns).
  --       Always strict: refuses with a typed error rather than emit text that
  --       does not re-parse to the input DBC (the exact round-trip verdict).
  FormatDBCText : JSON → StreamCommand

-- ============================================================================
-- RESPONSE TYPES
-- ============================================================================

-- Response types for the streaming protocol
data Response : Set where
  -- Generic success with message
  Success : String → Response

  -- Error with typed error value
  Error : Err.Error → Response

  -- Extraction results (emitted by the signal-extraction handler, reached
  -- via the binary `processExtractDirect` entry point)
  -- Args: successfully extracted values, errors, absent signals
  ExtractionResultsResponse : List (String × ℚ) → List (String × String) → List String → Response

  -- Per-frame batch of property events emitted during streaming.
  -- Each element is one PropertyResult (Violation / Satisfaction /
  -- Unresolved); the list is in source-order — satisfactions that
  -- completed before a halting violation come first, then the violation.
  -- Empty list is unreachable here — `dispatchIterResult` emits `Ack`
  -- instead when no events fired on the frame (so a single-event frame
  -- is encoded as a one-element list, never as `PropertyResponse []`).
  -- Lifted from `PropertyResult → Response` (singular) to surface
  -- mid-stream Satisfaction events that were previously lost (a Satisfied
  -- property was dropped from the active set without any wire emission,
  -- and finalizeL at EndStream only walks the survivors).
  PropertyResponse : List PropertyResult → Response

  -- Acknowledgment (for data frames that don't trigger property results)
  Ack : Response

  -- Stream complete with finalization results for all properties + any
  -- EndStream warnings (cache-miss diagnostics).  The
  -- warnings list is empty when no atom went uncached; new wire field
  -- `warnings: [...]` on the JSON Complete response (binding parsers see
  -- it as an optional field).
  Complete : List PropertyResult → List Warning → Response

  -- Validation results from validateDBC command (read-only probe)
  ValidationResponse : List ValidationIssue → Response

  -- Formatted DBC as JSON (emitted by the format-DBC handler, reached via
  -- the binary `processFormatDBCDirect` entry point)
  DBCResponse : JSON → Response

  -- Parsed-and-validated DBC: the parsed body plus any non-error issues
  -- (warnings).  Used by ParseDBC and ParseDBCText on the success path
  -- (option 6b: warnings are NOT silently dropped on success).
  ParsedDBCResponse : JSON → List ValidationIssue → Response

  -- DBC text image (for FormatDBCText command): the formatted text plus its
  -- `wfTextIssues` diagnostics (warning-severity only).  Emitted ONLY when the
  -- text provably round-trips (the exact round-trip check said `true`), so these issues
  -- are advisory — the list MAY be non-empty even on a proven round-trip.
  -- Divergence is NEVER reported through this constructor: a DBC whose text does
  -- not round-trip yields the error-severity `TextRoundTripFailed` instead.
  -- Field shape mirrors ParsedDBCResponse (body + issues).
  DBCTextResponse : String → List ValidationIssue → Response
