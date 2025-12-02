{-# OPTIONS --safe --without-K #-}

-- CAN frame types with bounded IDs and data length codes.
--
-- Purpose: Define type-safe CAN frames with compile-time bounds checking.
-- Types: CANId (Fin 2048 for standard 11-bit IDs), DLC (Fin 9 for 0-8 bytes),
--        Frame (ID + 8-byte payload), TimedFrame (Frame + timestamp).
-- Role: Core types used throughout CAN processing and signal extraction.
--
-- Current constraints: Standard CAN only (11-bit IDs, 8-byte frames).
-- Future: Extended IDs (29-bit) deferred to later phase.
module Aletheia.CAN.Frame where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Vec using (Vec)

Byte : Set
Byte = Fin 256

-- CAN ID type supporting both standard (11-bit) and extended (29-bit) IDs
data CANId : Set where
  Standard : Fin 2048 → CANId          -- 11-bit standard IDs (0x000-0x7FF)
  Extended : Fin 536870912 → CANId     -- 29-bit extended IDs (0x00000000-0x1FFFFFFF)

record CANFrame : Set where
  field
    id : CANId
    dlc : Fin 9
    payload : Vec Byte 8

BitPosition : Set
BitPosition = Fin 64
