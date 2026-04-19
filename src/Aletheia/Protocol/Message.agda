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
open import Data.Rational using (ℚ)
open import Data.Vec using (Vec)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_)
open import Aletheia.CAN.Frame using (Byte; CANId)
open import Aletheia.CAN.DLC using (DLC; dlcBytes)
open import Aletheia.Protocol.Response using (PropertyResult)
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

  -- Property violation/satisfaction (for streaming data)
  PropertyResponse : PropertyResult → Response

  -- Acknowledgment (for data frames that don't trigger property results)
  Ack : Response

  -- Stream complete with finalization results for all properties
  Complete : List PropertyResult → Response

  -- Validation results from validateDBC command (read-only probe)
  ValidationResponse : List ValidationIssue → Response

  -- Formatted DBC as JSON (for FormatDBC command)
  DBCResponse : JSON → Response
