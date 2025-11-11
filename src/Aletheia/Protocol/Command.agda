{-# OPTIONS --safe #-}

module Aletheia.Protocol.Command where

open import Data.String using (String)
open import Data.Nat using (ℕ)
open import Data.Rational using (ℚ)
open import Data.Vec using (Vec)
open import Data.Fin using (Fin)
open import Aletheia.CAN.Frame using (CANFrame; Byte)

-- Commands supported by the Aletheia binary
data Command : Set where
  -- Echo command for testing
  Echo : String → Command

  -- Parse a DBC YAML file
  ParseDBC : String → Command

  -- Extract a signal value from a CAN frame
  -- Args: DBC YAML, message name, signal name, frame bytes
  ExtractSignal : String → String → String → Vec Byte 8 → Command

  -- Inject a signal value into a CAN frame
  -- Args: DBC YAML, message name, signal name, signal value, frame bytes
  InjectSignal : String → String → String → ℚ → Vec Byte 8 → Command
