{-# OPTIONS --safe --without-K #-}

-- Correctness properties for CAN endianness operations.
--
-- Purpose: Facade re-exporting all proof lemmas about ByteOrder, extractBits,
--   injectBits, swapBytes, payloadIso, physicalBitPos, and startBit conversion
--   from per-topic submodules.
-- Submodules: Roundtrip, WriteSet, StartBit, CrossOrder.
module Aletheia.CAN.Endianness.Properties where

-- Byte/bitvec roundtrips and extract-inject roundtrip
open import Aletheia.CAN.Endianness.Properties.Roundtrip public using
  ( swapBytes-involutive
  ; byteToBitVec-roundtrip
  ; bitVecToByte-roundtrip
  ; extractBits-injectBits-roundtrip
  ; injectBits-preserves-disjoint
  )

-- Write-set algebra and injection commutativity
open import Aletheia.CAN.Endianness.Properties.WriteSet public using
  ( applyWrites-push
  ; applyWrites-comm
  ; injectBits≡applyWrites
  ; writesOf-distinct
  ; disjoint-ranges→AllDiffPos
  ; injectBits-commute
  ; payloadIso-involutive
  ; injectPayload-commute
  ; injectPayload-preserves-disjoint-same
  )

-- PhysicalBitPos properties and startBit conversion roundtrips
open import Aletheia.CAN.Endianness.Properties.StartBit public using
  ( lookupSafe-swapBytes
  ; physicalBitPos-BE-bounded
  ; physicalBitPos-BE-bounded-any
  ; convertStartBit-wf-bound
  ; physicalBitPos-BE-involutive
  ; convertStartBit-roundtrip
  ; unconvertStartBit-roundtrip
  )

-- Cross-byte-order bit preservation and mixed-order commutativity
open import Aletheia.CAN.Endianness.Properties.CrossOrder public using
  ( injectBits-preserves-outside
  ; extractBits-swap-inject-preserves
  ; physicalWrites
  ; swap-applyWrites-swap
  ; injectPayload-commute-mixed
  )
