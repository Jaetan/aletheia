{-# OPTIONS --safe --without-K #-}

-- Byte order handling for CAN signal extraction (little/big endian).
--
-- Purpose: Convert between little-endian and big-endian byte representations.
-- Operations: byteSwap (reverse bytes), proven involutive (swap ∘ swap ≡ id).
-- Role: Used by CAN.Encoding to handle different signal byte orders in DBC.
--
-- Architecture: Uses BitVec for structural bit operations, not arithmetic.
-- Proof: byteSwap is its own inverse (Phase 1 proof, verified).
--
-- Proofs live in Aletheia.CAN.Endianness.Properties (separate module).
module Aletheia.CAN.Endianness where

open import Aletheia.CAN.Frame using (Byte)
open import Aletheia.Data.BitVec using (BitVec; testBit; setBit)
open import Aletheia.Data.BitVec.Conversion using (ℕToBitVec; bitVecToℕ)
open import Data.Vec using (Vec; []; _∷_; reverse)
open import Data.Fin using (Fin; fromℕ<)
open import Data.Nat as Nat using (ℕ; zero; suc; _+_; _∸_; _*_; _<_; _≤_; z≤n; s≤s; _/_; _%_)
open import Data.Nat.DivMod using (m%n<n)
open import Data.Nat.Properties using (_≟_; _<?_; +-suc; +-identityʳ; ≤-antisym; ≮⇒≥)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; _≢_)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Empty using (⊥-elim)

data ByteOrder : Set where
  LittleEndian BigEndian : ByteOrder

-- ============================================================================
-- BYTE <-> BITVEC CONVERSION
-- ============================================================================

-- Convert a byte (ℕ) to an 8-bit bitvector (uses mod 256 for bounds)
byteToBitVec : Byte → BitVec 8
byteToBitVec b = ℕToBitVec (b Nat.% 256) (m%n<n b 256)

-- Convert an 8-bit bitvector to a byte (ℕ)
bitVecToByte : BitVec 8 → Byte
bitVecToByte bits = bitVecToℕ bits

-- ============================================================================
-- BIT EXTRACTION AND INJECTION (STRUCTURAL)
-- ============================================================================

-- Safe lookup (returns 0 if out of bounds)
lookupSafe : (n : ℕ) → ℕ → Vec Byte n → Byte
lookupSafe zero _ _ = 0
lookupSafe (suc n) zero (b ∷ _) = b
lookupSafe (suc n) (suc m) (_ ∷ bs) = lookupSafe n m bs

updateSafe : (n : ℕ) → ℕ → (Byte → Byte) → Vec Byte n → Vec Byte n
updateSafe zero _ _ bs = bs
updateSafe (suc n) zero f (b ∷ bs) = f b ∷ bs
updateSafe (suc n) (suc m) f (b ∷ bs) = b ∷ updateSafe n m f bs

-- Extract bits from a byte vector starting at a given bit position
-- Returns a BitVec (structural, not arithmetic)
-- Parameterized by payload size n (supports any CAN/CAN-FD byte count).
-- {length} is first implicit for backward compatibility with existing proof code.
extractBits : ∀ {length} {n} → Vec Byte n → ℕ → BitVec length
extractBits {zero} bytes startBit = []
extractBits {suc length} {n} bytes startBit = bitValue ∷ restBits
  where
    byteIdx : ℕ
    byteIdx = startBit Nat./ 8

    bitInBytePos : Fin 8
    bitInBytePos = fromℕ< (m%n<n startBit 8)

    byte : Byte
    byte = lookupSafe n byteIdx bytes

    byteBits : BitVec 8
    byteBits = byteToBitVec byte

    bitValue : Bool
    bitValue = testBit byteBits bitInBytePos

    restBits : BitVec length
    restBits = extractBits bytes (suc startBit)

-- Inject bits into a byte vector at a given position
-- Takes a BitVec (structural, not arithmetic)
-- Parameterized by payload size n (supports any CAN/CAN-FD byte count).
-- {length} is first implicit for backward compatibility with existing proof code.
injectBits : ∀ {length} {n} → Vec Byte n → ℕ → BitVec length → Vec Byte n
injectBits bytes startBit [] = bytes
injectBits {_} {n} bytes startBit (bitValue ∷ restBits) = injectBits updatedBytes (suc startBit) restBits
  where
    byteIdx : ℕ
    byteIdx = startBit Nat./ 8

    bitInBytePos : Fin 8
    bitInBytePos = fromℕ< (m%n<n startBit 8)

    updateByte : Byte → Byte
    updateByte b =
      let byteBits = byteToBitVec b
          updatedBits = setBit byteBits bitInBytePos bitValue
      in bitVecToByte updatedBits

    updatedBytes : Vec Byte n
    updatedBytes = updateSafe n byteIdx updateByte bytes

-- ============================================================================
-- BYTE ORDER CONVERSION
-- ============================================================================

-- Check if byte order is big-endian
isBigEndian : ByteOrder → Bool
isBigEndian LittleEndian = false
isBigEndian BigEndian = true

-- Byte order conversion for multi-byte sequences
-- Parameterized by payload size n
swapBytes : ∀ {n} → Vec Byte n → Vec Byte n
swapBytes = reverse

-- ============================================================================
-- PAYLOAD ISOMORPHISM (factors out byte order handling)
-- ============================================================================

-- The byte order isomorphism: id for LittleEndian, swapBytes for BigEndian
-- Defined using if to match injectSignal's implementation definitionally
-- Parameterized by payload size n
payloadIso : ∀ {n} → ByteOrder → Vec Byte n → Vec Byte n
payloadIso bo bytes = if isBigEndian bo then swapBytes bytes else bytes

-- Inject bits with byte order handling factored out
-- injectPayload = payloadIso ∘ injectBits ∘ payloadIso
-- Parameterized by payload size n
injectPayload : ∀ {len} {n} → ℕ → BitVec len → ByteOrder → Vec Byte n → Vec Byte n
injectPayload s bits bo payload =
  payloadIso bo (injectBits (payloadIso bo payload) s bits)

-- ============================================================================
-- BYTE ORDER DECIDABLE EQUALITY
-- ============================================================================

_≟-ByteOrder_ : (bo₁ bo₂ : ByteOrder) → Dec (bo₁ ≡ bo₂)
LittleEndian ≟-ByteOrder LittleEndian = yes refl
LittleEndian ≟-ByteOrder BigEndian    = no (λ ())
BigEndian    ≟-ByteOrder LittleEndian = no (λ ())
BigEndian    ≟-ByteOrder BigEndian    = yes refl

-- ============================================================================
-- PHYSICAL BIT POSITION (for mixed byte order support)
-- ============================================================================

-- Maps a logical bit position to the physical bit position it occupies
-- in the original (non-swapped) payload.
-- LE: identity (logical = physical)
-- BE: byte-swapped (byte index reversed, bit-within-byte preserved)
physicalBitPos : ℕ → ByteOrder → ℕ → ℕ
physicalBitPos _ LittleEndian b = b
physicalBitPos frameBytes BigEndian b = ((frameBytes ∸ 1) ∸ (b / 8)) * 8 + (b % 8)

-- ============================================================================
-- MOTOROLA STARTBIT CONVERSION
-- ============================================================================

-- Convert a Motorola (DBC) startBit to the internal startBit used by
-- the swap model.  For LE: identity.  For BE: physicalBitPos s ∸ (l ∸ 1).
--
-- The swap model reverses the 8-byte payload then extracts at a linear
-- position.  The Motorola convention specifies the MSB position; this
-- conversion computes the linear position in the reversed frame whose
-- ascending extraction matches Motorola MSB-first semantics.
convertStartBit : ℕ → ByteOrder → ℕ → ℕ → ℕ
convertStartBit _ LittleEndian s _ = s
convertStartBit frameBytes BigEndian s l = physicalBitPos frameBytes BigEndian s ∸ (l ∸ 1)

-- Reverse conversion: internal startBit back to Motorola (DBC) startBit.
unconvertStartBit : ℕ → ByteOrder → ℕ → ℕ → ℕ
unconvertStartBit _ LittleEndian s _ = s
unconvertStartBit frameBytes BigEndian s l = physicalBitPos frameBytes BigEndian (s + l ∸ 1)

-- ============================================================================
-- NOT-IN-INTERVAL HELPER (runtime function used by Encoding)
-- ============================================================================

-- If p ≢ a+k for all k < m, then p < a or a+m ≤ p
not-in-interval : ∀ a m p → (∀ k → k < m → p ≢ a + k) → p < a ⊎ a + m ≤ p
not-in-interval a m p noHit = go a m p noHit
  where
    go : ∀ a m p → (∀ k → k < m → p ≢ a + k) → p < a ⊎ a + m ≤ p
    go a zero p _ with p <? a
    ... | yes p<a = inj₁ p<a
    ... | no ¬p<a = inj₂ (subst (_≤ p) (sym (+-identityʳ a)) (≮⇒≥ ¬p<a))
    go a (suc m) p noHit with p <? a
    ... | yes p<a = inj₁ p<a
    ... | no ¬p<a with p ≟ a
    ...   | yes refl = ⊥-elim (noHit 0 (s≤s z≤n) (sym (+-identityʳ a)))
    ...   | no p≢a with go (suc a) m p noHit'
      where
        noHit' : ∀ k → k < m → p ≢ suc a + k
        noHit' k k<m = subst (p ≢_) (+-suc a k) (noHit (suc k) (s≤s k<m))
    ...     | inj₁ p<sa = ⊥-elim (p≢a (≤-antisym (Data.Nat.Properties.≤-pred p<sa) (≮⇒≥ ¬p<a)))
              where open import Data.Nat.Properties using (≤-pred)
    ...     | inj₂ sa+m≤p = inj₂ (subst (_≤ p) (sym (+-suc a m)) sa+m≤p)
