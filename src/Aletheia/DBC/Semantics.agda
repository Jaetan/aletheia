{-# OPTIONS --safe --without-K #-}

module Aletheia.DBC.Semantics where

open import Aletheia.DBC.Types
open import Aletheia.CAN.Frame
open import Aletheia.CAN.Signal
open import Data.String using (String)
open import Data.Maybe using (Maybe)
open import Data.List using (List)

decodeFrame : DBC → CANFrame → Maybe (List (String × SignalValue))
decodeFrame = {!!}
