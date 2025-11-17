{-# OPTIONS --safe --without-K #-}

module Aletheia.CAN.Endianness where

open import Aletheia.CAN.Frame
open import Data.Vec using (Vec; []; _∷_; lookup; updateAt; reverse; map)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin using (toℕ; fromℕ; inject≤)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _<_; _≤_; _^_; _≡ᵇ_; z≤n; s≤s)
open import Data.Nat.DivMod using (_div_; _mod_)
open import Data.Bool using (Bool; true; false; if_then_else_; not; _∧_; _∨_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (Dec; yes; no)
open import Function using (_∘_; id)

data ByteOrder : Set where
  LittleEndian BigEndian : ByteOrder

-- Simple bit manipulation on natural numbers
private
  -- Shift right by n positions (divide by 2^n)
  shiftR : ℕ → ℕ → ℕ
  shiftR value 0 = value
  shiftR value (suc n) = shiftR (value div 2) n

  -- Test if bit n is set in a natural number
  testBitℕ : ℕ → ℕ → Bool
  testBitℕ value bitPos = (toℕ ((shiftR value bitPos) mod 2)) ≡ᵇ 1

  -- Set bit n in a natural number
  setBitℕ : ℕ → ℕ → Bool → ℕ
  setBitℕ value bitPos true = value + (2 ^ bitPos)
  setBitℕ value bitPos false =
    if testBitℕ value bitPos
    then value ∸ (2 ^ bitPos)
    else value

-- Extract a byte from a Fin 256 (Byte)
byteToℕ : Byte → ℕ
byteToℕ = toℕ

-- Convert natural number to Byte (modulo 256)
ℕtoByte : ℕ → Byte
ℕtoByte n = n mod 256

-- Test if specific bit is set in a byte
testBit : Byte → ℕ → Bool
testBit b bitPos = testBitℕ (byteToℕ b) bitPos

-- Set a specific bit in a byte
setBit : Byte → ℕ → Bool → Byte
setBit b bitPos val = ℕtoByte (setBitℕ (byteToℕ b) bitPos val)

-- Extract bits from a byte vector starting at a given bit position
-- Returns the extracted value as a natural number
extractBits : Vec Byte 8 → ℕ → ℕ → ℕ
extractBits bytes startBit 0 = 0
extractBits bytes startBit (suc length) =
  let byteIdx : ℕ
      byteIdx = startBit div 8
      bitInBytePos : ℕ
      bitInBytePos = toℕ (startBit mod 8)
      byte : Byte
      byte = lookupSafe 8 byteIdx bytes
      bitValue : ℕ
      bitValue = if testBit byte bitInBytePos then 1 else 0
      restValue : ℕ
      restValue = extractBits bytes (suc startBit) length
  in bitValue + 2 * restValue
  where
    -- Safe lookup that returns 0 if out of bounds (parameterized over size)
    lookupSafe : (n : ℕ) → ℕ → Vec Byte n → Byte
    lookupSafe zero _ _ = fzero
    lookupSafe (suc n) zero (b ∷ _) = b
    lookupSafe (suc n) (suc m) (_ ∷ bs) = lookupSafe n m bs

-- Inject bits into a byte vector at a given position
-- Updates the byte vector with the given value
injectBits : Vec Byte 8 → ℕ → ℕ → ℕ → Vec Byte 8
injectBits bytes startBit value 0 = bytes
injectBits bytes startBit value (suc length) =
  let byteIdx : ℕ
      byteIdx = startBit div 8
      bitInBytePos : ℕ
      bitInBytePos = toℕ (startBit mod 8)
      bitValue : Bool
      bitValue = (toℕ (value mod 2)) ≡ᵇ 1
      updatedBytes : Vec Byte 8
      updatedBytes = updateSafe 8 byteIdx (λ b → setBit b bitInBytePos bitValue) bytes
      nextValue : ℕ
      nextValue = value div 2
  in injectBits updatedBytes (suc startBit) nextValue length
  where
    -- Safe update that does nothing if out of bounds (parameterized over size)
    updateSafe : (n : ℕ) → ℕ → (Byte → Byte) → Vec Byte n → Vec Byte n
    updateSafe zero _ _ bs = bs
    updateSafe (suc n) zero f (b ∷ bs) = f b ∷ bs
    updateSafe (suc n) (suc m) f (b ∷ bs) = b ∷ updateSafe n m f bs

-- Byte order conversion for multi-byte sequences
swapBytes : Vec Byte 8 → Vec Byte 8
swapBytes = reverse

-- Proof that swapping twice is identity
swapBytes-involutive : ∀ (bytes : Vec Byte 8) → swapBytes (swapBytes bytes) ≡ bytes
swapBytes-involutive bytes = reverse-involutive bytes
  where
    open import Data.Vec.Properties using (reverse-involutive)
