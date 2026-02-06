{-# OPTIONS --safe --without-K #-}

-- CAN frame types with bounded IDs and data length codes.
--
-- Purpose: Define type-safe CAN frames with runtime bounds enforcement.
-- Types: CANId (Standard 11-bit | Extended 29-bit), DLC (ℕ for 0-8 bytes),
--        Frame (ID + 8-byte payload), TimedFrame (Frame + timestamp).
-- Role: Core types used throughout CAN processing and signal extraction.
--
-- All numeric fields use ℕ at runtime for O(1) MAlonzo allocation.
-- Bounds enforcement is at construction sites (% n / input validation).
-- Supported: Both standard (11-bit) and extended (29-bit) CAN IDs via sum type.
-- Current constraint: Fixed 8-byte payload (CAN 2.0B, no CAN-FD support yet).
module Aletheia.CAN.Frame where

open import Data.Nat using (ℕ)
open import Data.Vec using (Vec)

-- Byte is ℕ at runtime for O(1) allocation.
-- MAlonzo compiles ℕ to Integer via BUILTIN NATURAL (machine word for <2^63).
-- Fin 256 would create O(n) nested suc constructors (~3.2 KB per byte value).
-- Bounds enforcement is at construction sites (% 256 / input validation).
Byte : Set
Byte = ℕ

-- CAN ID type supporting both standard (11-bit) and extended (29-bit) IDs.
-- Fields use ℕ for O(1) MAlonzo allocation; bounds enforced at construction.
data CANId : Set where
  Standard : ℕ → CANId          -- 11-bit standard IDs (0x000-0x7FF)
  Extended : ℕ → CANId          -- 29-bit extended IDs (0x00000000-0x1FFFFFFF)

record CANFrame : Set where
  field
    id : CANId
    dlc : ℕ
    payload : Vec Byte 8

BitPosition : Set
BitPosition = ℕ
