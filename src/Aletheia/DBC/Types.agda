{-# OPTIONS --safe --without-K #-}

-- DBC (Database CAN) file structure types.
--
-- Purpose: Define types representing DBC file contents (messages, signals, metadata).
-- Types: DBC (top-level), Message (CAN message definition), Signal (signal within message).
-- Role: Core data structure used throughout CAN processing and verification.
--
-- Design: Matches DBC file format with type-safe representations.
-- All numeric fields use ℕ for O(1) MAlonzo allocation.
module Aletheia.DBC.Types where

open import Aletheia.CAN.Frame
open import Aletheia.CAN.Signal
open import Aletheia.CAN.Endianness
open import Data.String using (String)
open import Data.List using (List)
open import Data.Nat using (ℕ)

-- Signal presence model for multiplexing
-- A signal is either always present or conditionally present based on a multiplexor
data SignalPresence : Set where
  Always : SignalPresence
  When : (multiplexor : String) → (value : ℕ) → SignalPresence

record DBCSignal : Set where
  field
    name : String
    signalDef : SignalDef
    byteOrder : ByteOrder
    unit : String
    presence : SignalPresence  -- NEW: Conditional presence for multiplexing

record DBCMessage : Set where
  field
    id : CANId
    name : String
    dlc : ℕ
    sender : String
    signals : List DBCSignal

record DBC : Set where
  field
    version : String
    messages : List DBCMessage
