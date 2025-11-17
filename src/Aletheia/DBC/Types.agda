{-# OPTIONS --safe --without-K #-}

module Aletheia.DBC.Types where

open import Aletheia.CAN.Frame
open import Aletheia.CAN.Signal
open import Aletheia.CAN.Endianness
open import Data.String using (String)
open import Data.List using (List)
open import Data.Fin using (Fin)
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
    dlc : Fin 9
    sender : String
    signals : List DBCSignal

record DBC : Set where
  field
    version : String
    messages : List DBCMessage
