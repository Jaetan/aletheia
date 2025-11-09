{-# OPTIONS --safe --without-K #-}

module Aletheia.CAN.Endianness where

open import Aletheia.CAN.Frame
open import Data.Vec using (Vec)

data ByteOrder : Set where
  LittleEndian BigEndian : ByteOrder

-- TODO: Add byte swapping functions
-- TODO: Prove swap ∘ swap ≡ id
