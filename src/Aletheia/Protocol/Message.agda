-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Protocol message types for the JSON streaming LTL checker.
--
-- Purpose: Define command and response types for the streaming protocol.
-- Types: StreamCommand (parseDBC, setProperties, startStream, endStream),
--        Response (success, error, ack, property).
-- Role: Core types used by Protocol.Routing and Protocol.StreamState.
module Aletheia.Protocol.Message where

open import Data.String using (String)
open import Data.List using (List)
open import Data.Bool using (Bool)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ)
open import Data.Rational using (ℚ)
open import Data.Vec using (Vec)
open import Data.Product using (_×_)
open import Aletheia.CAN.Frame using (Byte; CANId)
open import Aletheia.CAN.DLC using (DLC; dlcBytes)
open import Aletheia.Protocol.Response using (PropertyResult; Warning)
open import Aletheia.Protocol.JSON using (JSON)
open import Aletheia.DBC.Types using (ValidationIssue)
import Aletheia.Error as Err

-- ============================================================================
-- STREAMING PROTOCOL COMMANDS (Phase 2B)
-- ============================================================================

-- Commands for the JSON streaming protocol
data StreamCommand : Set where
  -- Parse DBC file and reset all state
  -- Args: DBC JSON structure
  ParseDBC : JSON → StreamCommand

  -- Set LTL properties to check (must be called after ParseDBC, before StartStream)
  -- Args: List of property JSON objects (parsed by Python DSL)
  SetProperties : List JSON → StreamCommand

  -- Begin streaming data frames
  StartStream : StreamCommand

  -- Submit a CAN data frame to the active monitoring stream — JSON mirror
  -- of the binary FFI `aletheia_send_frame` entry point.  R19 Phase 2
  -- cluster 18 — AGDA-D-10.1 closure: the JSON path now carries CAN-FD
  -- BRS / ESI metadata (ISO 11898-1:2015 §10.4.2 / §10.4.3) end-to-end.
  -- Args: timestamp µs, CAN ID, validated DLC, payload (length =
  --       dlcBytes DLC), optional BRS bit, optional ESI bit.
  -- Returns: Ack on no-property-fired, Violation otherwise (same shape
  --          as the binary FFI response).
  SendFrame : (ts : ℕ) → CANId → (dlc : DLC) → Vec Byte (dlcBytes dlc)
            → (brs : Maybe Bool) → (esi : Maybe Bool) → StreamCommand

  -- Extract all signals from a CAN frame
  -- Args: CAN ID, validated DLC, frame data (length = dlcBytes DLC)
  -- Returns: Extraction results (values/errors/absent)
  ExtractAllSignals : CANId → (dlc : DLC) → Vec Byte (dlcBytes dlc) → StreamCommand

  -- End stream and emit final property results
  EndStream : StreamCommand

  -- Validate DBC structure and return all issues (read-only, does not change state)
  -- Args: DBC JSON structure
  ValidateDBC : JSON → StreamCommand

  -- Format the currently-loaded DBC back to JSON
  FormatDBC : StreamCommand

  -- Parse DBC from raw DBC text using the verified Agda text parser
  -- (Track B.3.e — exposes parseText + validateDBCFull as one operation).
  -- Args: DBC text image (e.g. the contents of a .dbc file)
  ParseDBCText : String → StreamCommand

  -- Format DBC JSON dict back to .dbc text (Track E.10 — closes C3 deferral).
  -- Args: DBC JSON structure (same wire shape ParseDBCText returns)
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

  -- Extraction results (for ExtractAllSignals command)
  -- Args: successfully extracted values, errors, absent signals
  ExtractionResultsResponse : List (String × ℚ) → List (String × String) → List String → Response

  -- Per-frame batch of property events emitted during streaming.
  -- Each element is one PropertyResult (Violation / Satisfaction /
  -- Unresolved); the list is in source-order — satisfactions that
  -- completed before a halting violation come first, then the violation.
  -- Empty list is unreachable here — `dispatchIterResult` emits `Ack`
  -- instead when no events fired on the frame (so a single-event frame
  -- is encoded as a one-element list, never as `PropertyResponse []`).
  -- R23 — AGDA-D-12.1: lifted from `PropertyResult → Response` (singular)
  -- to surface mid-stream Satisfaction events that were previously lost
  -- (a Satisfied property was dropped from the active set without any
  -- wire emission, and finalizeL at EndStream only walks the survivors).
  PropertyResponse : List PropertyResult → Response

  -- Acknowledgment (for data frames that don't trigger property results)
  Ack : Response

  -- Stream complete with finalization results for all properties + any
  -- EndStream warnings (cache-miss diagnostics per AGDA-D-12.1).  The
  -- warnings list is empty when no atom went uncached; new wire field
  -- `warnings: [...]` on the JSON Complete response (binding parsers see
  -- it as an optional field).
  Complete : List PropertyResult → List Warning → Response

  -- Validation results from validateDBC command (read-only probe)
  ValidationResponse : List ValidationIssue → Response

  -- Formatted DBC as JSON (for FormatDBC command)
  DBCResponse : JSON → Response

  -- Parsed-and-validated DBC: the parsed body plus any non-error issues
  -- (warnings).  Used by ParseDBC and ParseDBCText on the success path
  -- (option 6b: warnings are NOT silently dropped on success).
  ParsedDBCResponse : JSON → List ValidationIssue → Response

  -- DBC text image (for FormatDBCText command, Track E.10).
  -- Carries `formatText dbc : String` produced from a JSON DBC input.
  DBCTextResponse : String → Response
