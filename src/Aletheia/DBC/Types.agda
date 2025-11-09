{-# OPTIONS --safe --without-K #-}

module Aletheia.DBC.Types where

open import Aletheia.CAN.Frame
open import Aletheia.CAN.Signal
open import Aletheia.CAN.Endianness
open import Data.String using (String)
open import Data.List using (List)
open import Data.Fin using (Fin)

record DBCSignal : Set where
  field
    name : String
    signalDef : SignalDef
    byteOrder : ByteOrder
    unit : String

record DBCMessage : Set where
  field
    id : Fin 2048
    name : String
    dlc : Fin 9
    sender : String
    signals : List DBCSignal

record DBC : Set where
  field
    version : String
    messages : List DBCMessage
