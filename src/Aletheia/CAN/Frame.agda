{-# OPTIONS --safe --without-K #-}

-- CAN frame types with bounded IDs and data length codes.
--
-- Purpose: Define type-safe CAN frames with runtime bounds enforcement.
-- Types: CANId (Standard 11-bit | Extended 29-bit), DLC (ℕ for 0-15),
--        CANFrame n (ID + DLC + n-byte payload), Byte (ℕ alias), BitPosition (ℕ alias).
-- Role: Core types used throughout CAN processing and signal extraction.
--
-- All numeric fields use ℕ at runtime for O(1) MAlonzo allocation.
-- Bounds enforcement is at construction sites (% n / input validation).
-- Supported: Both standard (11-bit) and extended (29-bit) CAN IDs via sum type.
-- Payload size is parameterized: CAN 2.0B uses n=8, CAN-FD uses n=12..64.
module Aletheia.CAN.Frame where

open import Data.Bool using (T)
open import Data.Nat using (ℕ; _<ᵇ_)
open import Data.Vec using (Vec)

open import Aletheia.Prelude using (standard-can-id-max; extended-can-id-max)

-- Byte is ℕ at runtime for O(1) allocation.
-- MAlonzo compiles ℕ to Integer via BUILTIN NATURAL (machine word for <2^63).
-- Fin 256 would create O(n) nested suc constructors (~3.2 KB per byte value).
-- Bounds enforcement is at construction sites (% 256 / input validation).
Byte : Set
Byte = ℕ

-- CAN ID type supporting both standard (11-bit) and extended (29-bit) IDs.
-- Bounds are embedded via T (n <ᵇ max): O(1) proof (just tt) at runtime,
-- but statically enforced at every construction site inside Agda.
-- At the FFI boundary (Haskell shim), bounds are checked at runtime.
data CANId : Set where
  Standard : (n : ℕ) → T (n <ᵇ standard-can-id-max) → CANId
  Extended : (n : ℕ) → T (n <ᵇ extended-can-id-max) → CANId

-- CAN frame parameterized by payload size n.
-- CAN 2.0B: n = 8 (fixed). CAN-FD: n ∈ {0..8, 12, 16, 20, 24, 32, 48, 64}.
-- MAlonzo compiles Vec Byte n to n nested constructors — O(n) per frame.
-- CAN 2.0B users pay no overhead (n=8 unchanged).
record CANFrame (n : ℕ) : Set where
  field
    id      : CANId
    dlc     : ℕ
    payload : Vec Byte n

BitPosition : Set
BitPosition = ℕ
