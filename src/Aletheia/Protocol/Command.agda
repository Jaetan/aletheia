{-# OPTIONS --safe --without-K #-}

module Aletheia.Protocol.Command where

open import Data.String using (String)
open import Data.Nat using (ℕ)
open import Data.Rational using (ℚ)
open import Data.Vec using (Vec)
open import Data.List using (List)
open import Data.Fin using (Fin)
open import Aletheia.CAN.Frame using (CANFrame; Byte)

-- Commands supported by the Aletheia binary
data Command : Set where
  -- Parse a DBC YAML file
  ParseDBC : String → Command

  -- Extract a signal value from a CAN frame
  -- Args: DBC YAML, message name, signal name, frame bytes
  ExtractSignal : String → String → String → Vec Byte 8 → Command

  -- Inject a signal value into a CAN frame
  -- Args: DBC YAML, message name, signal name, signal value, frame bytes
  InjectSignal : String → String → String → ℚ → Vec Byte 8 → Command

  -- Check an LTL property on a CAN trace
  -- Args: DBC YAML, Trace YAML, Property YAML (PythonLTL format)
  CheckLTL : String → String → String → Command

  -- Check multiple LTL properties on a streaming trace
  -- Args: DBC YAML, List of Property YAMLs
  -- Note: Trace comes from remaining stdin (not a parameter)
  CheckStreamingLTL : String → List String → Command
