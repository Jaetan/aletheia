{-# OPTIONS --safe --without-K #-}

module Aletheia.CAN.Frame where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Vec using (Vec)

Byte : Set
Byte = Fin 256

record CANFrame : Set where
  field
    id : Fin 2048
    dlc : Fin 9
    payload : Vec Byte 8

BitPosition : Set
BitPosition = Fin 64
