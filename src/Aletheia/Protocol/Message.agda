{-# OPTIONS --safe --without-K #-}

-- Protocol message types for the JSON streaming LTL checker.
--
-- Purpose: Define command and response types for the streaming protocol.
-- Types: StreamCommand (parseDBC, setProperties, startStream, endStream),
--        Request (command or data frame), Response (success, error, ack, property).
-- Role: Core types used by Protocol.Routing and Protocol.StreamState.
module Aletheia.Protocol.Message where

open import Data.String using (String)
open import Data.List using (List)
open import Data.Rational using (ℚ)
open import Data.Vec using (Vec)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_)
open import Aletheia.CAN.Frame using (Byte; CANId)
open import Aletheia.CAN.DLC using (dlcToBytes)
open import Aletheia.Trace.CANTrace using (TimedFrame)
open import Aletheia.Protocol.Response using (PropertyResult)
open import Aletheia.Protocol.JSON using (JSON)
open import Aletheia.DBC.Types using (ValidationIssue)

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

  -- BATCH SIGNAL OPERATIONS (Phase 2B.1)

  -- Build CAN frame from signal name-value pairs
  -- Args: CAN ID, DLC (must be ≤ 15, validated by Routing.parseCommand),
  --       list of {name: string, value: rational} objects
  -- Returns: frame with all signals encoded (byte count = dlcToBytes DLC)
  BuildFrame : CANId → (dlc : ℕ) → List JSON → StreamCommand

  -- Extract all signals from a CAN frame
  -- Args: CAN ID, DLC (must be ≤ 15, validated by Routing.parseCommand),
  --       frame data (length = dlcToBytes DLC)
  -- Returns: Extraction results (values/errors/absent)
  ExtractAllSignals : CANId → (dlc : ℕ) → Vec Byte (dlcToBytes dlc) → StreamCommand

  -- Update specific signals in an existing frame
  -- Args: CAN ID, DLC (must be ≤ 15, validated by Routing.parseCommand),
  --       existing frame bytes, list of {name: string, value: rational} updates
  -- Returns: Updated frame
  UpdateFrame : CANId → (dlc : ℕ) → Vec Byte (dlcToBytes dlc) → List JSON → StreamCommand

  -- End stream and emit final property results
  EndStream : StreamCommand

  -- Validate DBC structure and return all issues (read-only, does not change state)
  -- Args: DBC JSON structure
  ValidateDBC : JSON → StreamCommand

  -- Format the currently-loaded DBC back to JSON
  FormatDBC : StreamCommand

-- ============================================================================
-- REQUEST TYPES
-- ============================================================================

-- Request types: either a command or a data frame
data Request : Set where
  CommandRequest : StreamCommand → Request
  DataFrame : TimedFrame → Request

-- ============================================================================
-- RESPONSE TYPES
-- ============================================================================

-- Response types for the streaming protocol
data Response : Set where
  -- Generic success with message
  Success : String → Response

  -- Error with reason
  Error : String → Response

  -- Byte array response (for BuildFrame and UpdateFrame commands)
  ByteArray : ∀ {n} → Vec Byte n → Response

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
