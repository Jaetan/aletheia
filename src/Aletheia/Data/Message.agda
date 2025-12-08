{-# OPTIONS --safe --without-K #-}

-- Protocol message types for the JSON streaming LTL checker.
--
-- Purpose: Define command and response types for the streaming protocol.
-- Types: StreamCommand (parseDBC, setProperties, startStream, endStream),
--        Request (command or data frame), Response (success, error, ack, property).
-- Role: Core types used by Protocol.Routing and Protocol.StreamState.
module Aletheia.Data.Message where

open import Data.String using (String)
open import Data.List using (List)
open import Data.Rational using (ℚ)
open import Data.Vec using (Vec)
open import Data.Integer using (ℤ)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_)
open import Aletheia.CAN.Frame using (CANFrame; Byte)
open import Aletheia.Protocol.Response using (PropertyResult)
open import Aletheia.Protocol.JSON using (JSON)

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
  -- Args: CAN ID (as JSON number), list of {name: string, value: rational} objects
  -- Returns: 8-byte frame with all signals encoded
  BuildFrame : JSON → List JSON → StreamCommand

  -- Extract all signals from a CAN frame
  -- Args: CAN ID (as JSON number), 8-byte frame data
  -- Returns: Extraction results (values/errors/absent)
  ExtractAllSignals : JSON → Vec Byte 8 → StreamCommand

  -- Update specific signals in an existing frame
  -- Args: CAN ID, existing frame bytes, list of {name: string, value: rational} updates
  -- Returns: Updated 8-byte frame
  UpdateFrame : JSON → Vec Byte 8 → List JSON → StreamCommand

  -- End stream and emit final property results
  EndStream : StreamCommand

-- ============================================================================
-- REQUEST TYPES
-- ============================================================================

-- Request types: either a command or a data frame
data Request : Set where
  CommandRequest : StreamCommand → Request
  DataFrame : ℕ → CANFrame → Request  -- Timestamp (microseconds) and frame

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
  ByteArray : Vec Byte 8 → Response

  -- Extraction results (for ExtractAllSignals command)
  -- Args: successfully extracted values, errors, absent signals
  ExtractionResultsResponse : List (String × ℚ) → List (String × String) → List String → Response

  -- Property violation/satisfaction/pending (for streaming data)
  PropertyResponse : PropertyResult → Response

  -- Acknowledgment (for data frames that don't trigger property results)
  Ack : Response

  -- Stream complete (all properties decided, sent after EndStream)
  Complete : Response
