{-# OPTIONS --safe --without-K #-}

module Aletheia.Data.Message where

open import Data.String using (String)
open import Data.List using (List)
open import Data.Rational using (ℚ)
open import Data.Vec using (Vec)
open import Data.Integer using (ℤ)
open import Data.Nat using (ℕ)
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

  -- Encode a signal value into frame bytes (service command, independent of stream)
  -- Args: message name, signal name, signal value
  -- Returns: 8-byte frame with signal encoded
  Encode : String → String → ℤ → StreamCommand

  -- Decode a signal value from frame bytes (service command, independent of stream)
  -- Args: message name, signal name, frame bytes
  -- Returns: rational signal value
  Decode : String → String → Vec Byte 8 → StreamCommand

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

  -- Byte array response (for Encode command)
  ByteArray : Vec Byte 8 → Response

  -- Signal value response (for Decode command)
  SignalValue : ℚ → Response

  -- Property violation/satisfaction/pending (for streaming data)
  PropertyResponse : PropertyResult → Response

  -- Acknowledgment (for data frames that don't trigger property results)
  Ack : Response

  -- Stream complete (all properties decided, sent after EndStream)
  Complete : Response
