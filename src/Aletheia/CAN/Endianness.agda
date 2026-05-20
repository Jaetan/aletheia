{-# OPTIONS --safe --without-K #-}

-- Byte order handling for CAN signal extraction (little/big endian).
--
-- Purpose: Convert between little-endian and big-endian byte representations.
-- Operations: swapBytes (reverse bytes), proven involutive (swap ∘ swap ≡ id).
-- Role: Used by CAN.Encoding to handle different signal byte orders in DBC.
--
-- Architecture: Uses BitVec for structural bit operations, not arithmetic.
-- Proofs live in Aletheia.CAN.Endianness.Properties (separate module).
--
-- Public API (all used by at least one downstream module):
--   Types:       ByteOrder, LittleEndian, BigEndian, _≟-ByteOrder_
--   Bit I/O:     extractBits, extractRaw, extractRaw-extractBits, injectBits,
--                lookupSafe, updateSafe
--   Byte conv:   byteToBitVec, bitVecToByte
--   Byte order:  isBigEndian, swapBytes, payloadIso, injectPayload
--   Geometry:    physicalBitPos, convertStartBit, unconvertStartBit
--   Proof util:  not-in-interval
--
-- All internal helpers (shiftR, dropVec, extractCore, shiftR-≡, bit-equiv,
-- extractCore-extractBits, lookupSafe-dropVec, extractCore-dropVec) are in
-- a private block and not exported. All downstream open-import statements
-- use explicit `using` lists.
--
-- DEFER-stdlib-mandate (Cat 29): this module transitively relies on
-- `shiftR-mod-pow2` from `Aletheia.Data.BitVec.Conversion`, whose signature
-- carries a `.{{_ : NonZero (2 ^ n)}}` instance argument mandated by the
-- stdlib `_%_` on ℕ. The witness is supplied explicitly at every call site
-- (`{{m^n≢0 2 8}}` at line 154), so instance resolution is trivial. This is
-- the DEFER recorded against Cat 29 per the universal rules' in-source
-- exception path.
module Aletheia.CAN.Endianness where

open import Aletheia.CAN.Frame using (Byte)
open import Aletheia.Data.BitVec using (BitVec; testBit; setBit)
open import Aletheia.Data.BitVec.Conversion using (ℕToBitVec; bitVecToℕ; shiftR-conv; boolToℕ; ℕToBitVec-lookup; shiftR-mod-pow2)
open import Data.Vec using (Vec; []; _∷_; reverse; lookup)
open import Data.Fin using (Fin; fromℕ<; toℕ)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.Nat as Nat using (ℕ; zero; suc; _+_; _∸_; _*_; _<_; _≤_; z≤n; s≤s; _/_; _%_; NonZero)
open import Data.Nat.DivMod using (m%n<n; m≡m%n+[m/n]*n; [m+kn]%n≡m%n; +-distrib-/-∣ʳ; m*n/n≡m)
open import Data.Nat.Divisibility using (divides-refl)
open import Data.Nat.Properties using (_≟_; _<?_; +-suc; +-identityʳ; ≤-antisym; ≮⇒≥; m^n≢0)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; _≢_)
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

-- Safe lookup: returns 0 for out-of-bounds indices.
--
-- Dead default branch: the `zero _ _ = 0` clause (and the `suc n (suc m) (_ ∷ bs)`
-- tail recursion that eventually lands on it) is only reached when the index
-- exceeds the vector length. `Aletheia.DBC.Validator.Checks.checkSignalExceedsDLC`
-- (DBC validation check 6) rejects DBCs where `startBit + bitLength > dlc * 8`,
-- so by the time `extractRaw` / `extractCore` compute `byteIdx = startBit / 8`
-- on a validator-accepted DBC the index is always in bounds. Returning 0 is
-- a safe operational fallback for tests/synthetic inputs that bypass the
-- validator — no client-facing code path exercises the dead default.
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

-- Raw value extraction using ℕ arithmetic (no BitVec allocation).
-- Pre-slices the Vec to skip irrelevant leading bytes, reducing per-bit
-- lookupSafe cost from O(byteIndex) to O(0..bitLength/8).
-- For CAN-FD signal at byte 50: O(50) once instead of O(50) × bitLength.
private
  -- Right-shift: x / 2^k via k divisions by 2 (avoids _^_ which is O(k) in MAlonzo)
  shiftR : ℕ → ℕ → ℕ
  shiftR x zero = x
  shiftR x (suc k) = shiftR (x Nat./ 2) k

  -- Drop first k bytes from a Vec
  dropVec : ∀ n k → Vec Byte n → Vec Byte (n ∸ k)
  dropVec n zero bs = bs
  dropVec zero (suc k) [] = []
  dropVec (suc n) (suc k) (_ ∷ bs) = dropVec n k bs

  -- Core bit-at-a-time extraction (structurally recursive on bitLength)
  extractCore : (n : ℕ) → Vec Byte n → ℕ → (bitLength : ℕ) → ℕ
  extractCore n bytes sb zero = 0
  extractCore n bytes sb (suc bl) =
    let byte = lookupSafe n (sb Nat./ 8) bytes
        bitVal = shiftR byte (sb Nat.% 8) Nat.% 2
    in bitVal + 2 * extractCore n bytes (suc sb) bl

  -- ====================================================================
  -- PROOF: extractCore ≡ bitVecToℕ ∘ extractBits
  -- ====================================================================

  -- Bridge: shiftR (Endianness) ≡ shiftR-conv (Conversion)
  -- Both defined as iterated /2, so proof is by induction on k.
  shiftR-≡ : ∀ x k → shiftR x k ≡ shiftR-conv x k
  shiftR-≡ x zero = refl
  shiftR-≡ x (suc k) = shiftR-≡ (x Nat./ 2) k

  -- Per-bit equivalence: extractCore's bit read ≡ extractBits' bit read.
  -- shiftR byte (sb%8) % 2 ≡ boolToℕ (testBit (byteToBitVec byte) (fromℕ< (m%n<n sb 8)))
  bit-equiv : ∀ (byte : Byte) (sb : ℕ)
    → shiftR byte (sb Nat.% 8) Nat.% 2
      ≡ boolToℕ (testBit (byteToBitVec byte) (fromℕ< (m%n<n sb 8)))
  bit-equiv byte sb =
    let sb%8 = sb Nat.% 8
        -- Step 1: shiftR ≡ shiftR-conv
        step1 : shiftR byte sb%8 Nat.% 2 ≡ shiftR-conv byte sb%8 Nat.% 2
        step1 = cong (Nat._% 2) (shiftR-≡ byte sb%8)
        -- Step 2: shiftR-conv byte k % 2 ≡ shiftR-conv (byte%256) k % 2  (k < 8)
        step2 : shiftR-conv byte sb%8 Nat.% 2 ≡ shiftR-conv (byte Nat.% 256) sb%8 Nat.% 2
        step2 = shiftR-mod-pow2 byte 8 sb%8 {{m^n≢0 2 8}} (m%n<n sb 8)
        -- Step 3: ℕToBitVec-lookup relates lookup to shiftR-conv
        step3 : boolToℕ (lookup (ℕToBitVec (byte Nat.% 256) (m%n<n byte 256)) (fromℕ< (m%n<n sb 8)))
                ≡ shiftR-conv (byte Nat.% 256) (toℕ (fromℕ< (m%n<n sb 8))) Nat.% 2
        step3 = ℕToBitVec-lookup 8 (byte Nat.% 256) (m%n<n byte 256) (fromℕ< (m%n<n sb 8))
        -- Step 4: toℕ (fromℕ< (m%n<n sb 8)) ≡ sb%8
        step4 : toℕ (fromℕ< (m%n<n sb 8)) ≡ sb%8
        step4 = toℕ-fromℕ< (m%n<n sb 8)
    in trans step1 (trans step2 (sym (trans step3 (cong (λ k → shiftR-conv (byte Nat.% 256) k Nat.% 2) step4))))

  -- Main structural lemma: extractCore agrees with bitVecToℕ ∘ extractBits
  -- for any Vec Byte n and start bit position.
  extractCore-extractBits : ∀ (bl n : ℕ) (bytes : Vec Byte n) (sb : ℕ)
    → extractCore n bytes sb bl ≡ bitVecToℕ (extractBits {bl} {n} bytes sb)
  extractCore-extractBits zero n bytes sb = refl
  extractCore-extractBits (suc bl) n bytes sb
    with testBit (byteToBitVec byte) (fromℕ< (m%n<n sb 8))
       | bit-equiv byte sb
    where byte = lookupSafe n (sb Nat./ 8) bytes
  ... | false | beq =
    -- bitVal ≡ 0 (from beq), RHS reduces to 2 * bitVecToℕ (extractBits bytes (suc sb))
    cong₂ Nat._+_ beq (cong (2 Nat.*_) (extractCore-extractBits bl n bytes (suc sb)))
  ... | true | beq =
    -- bitVal ≡ 1 (from beq), RHS = 1 + 2 * bitVecToℕ (extractBits bytes (suc sb))
    cong₂ Nat._+_ beq (cong (2 Nat.*_) (extractCore-extractBits bl n bytes (suc sb)))

  -- lookupSafe commutes with dropVec: looking up j in dropped vec ≡ looking up j+k in original
  lookupSafe-dropVec : ∀ n k j (bytes : Vec Byte n)
    → lookupSafe (n ∸ k) j (dropVec n k bytes) ≡ lookupSafe n (j Nat.+ k) bytes
  lookupSafe-dropVec n zero j bytes = cong (λ x → lookupSafe n x bytes) (sym (+-identityʳ j))
  lookupSafe-dropVec zero (suc k) j [] = refl
  lookupSafe-dropVec (suc n) (suc k) j (b ∷ bs) =
    trans (lookupSafe-dropVec n k j bs) (cong (λ x → lookupSafe (suc n) x (b ∷ bs)) (sym (+-suc j k)))

  -- extractCore on a dropped vec agrees with extractCore on the original
  -- with an adjusted start bit (sb + skip * 8).
  -- Key insight: instead of proving extractBits-shift (which crosses byte
  -- boundaries when sb%8=7), work at the extractCore level where byte
  -- lookups are explicit and can be rewritten via lookupSafe-dropVec.
  extractCore-dropVec : ∀ (bl m : ℕ) (bytes : Vec Byte m) (skip sb : ℕ)
    → extractCore (m ∸ skip) (dropVec m skip bytes) sb bl
      ≡ extractCore m bytes (sb Nat.+ skip Nat.* 8) bl
  extractCore-dropVec zero m bytes skip sb = refl
  extractCore-dropVec (suc bl) m bytes skip sb =
    let n' = m ∸ skip
        bytes' = dropVec m skip bytes
        sb' = sb Nat.+ skip Nat.* 8
        -- Byte lookup: lookupSafe n' (sb/8) bytes' ≡ lookupSafe m (sb'/8) bytes
        byte-step₁ : lookupSafe n' (sb Nat./ 8) bytes' ≡ lookupSafe m (sb Nat./ 8 Nat.+ skip) bytes
        byte-step₁ = lookupSafe-dropVec m skip (sb Nat./ 8) bytes
        div-id : (sb Nat.+ skip Nat.* 8) Nat./ 8 ≡ sb Nat./ 8 Nat.+ (skip Nat.* 8) Nat./ 8
        div-id = +-distrib-/-∣ʳ sb (divides-refl skip)
        kn-simp : (skip Nat.* 8) Nat./ 8 ≡ skip
        kn-simp = m*n/n≡m skip 8
        byte-eq : lookupSafe n' (sb Nat./ 8) bytes' ≡ lookupSafe m (sb' Nat./ 8) bytes
        byte-eq = trans byte-step₁ (cong (λ x → lookupSafe m x bytes)
                    (sym (trans div-id (cong (sb Nat./ 8 Nat.+_) kn-simp))))
        -- Bit position: sb%8 ≡ sb'%8
        bit-eq : sb Nat.% 8 ≡ sb' Nat.% 8
        bit-eq = sym ([m+kn]%n≡m%n sb skip 8)
        -- Bit value equality
        bitVal-eq : shiftR (lookupSafe n' (sb Nat./ 8) bytes') (sb Nat.% 8) Nat.% 2
                    ≡ shiftR (lookupSafe m (sb' Nat./ 8) bytes) (sb' Nat.% 8) Nat.% 2
        bitVal-eq = cong (Nat._% 2) (cong₂ shiftR byte-eq bit-eq)
        -- Recursive call (suc sb + skip*8 = suc (sb + skip*8) definitionally)
        rec-eq : extractCore n' bytes' (suc sb) bl
                 ≡ extractCore m bytes (suc sb Nat.+ skip Nat.* 8) bl
        rec-eq = extractCore-dropVec bl m bytes skip (suc sb)
    in cong₂ Nat._+_ bitVal-eq (cong (2 Nat.*_) rec-eq)

extractRaw : (n : ℕ) → Vec Byte n → ℕ → (bitLength : ℕ) → ℕ
extractRaw n bytes startBit bitLength =
  let skip = startBit Nat./ 8
  in extractCore (n ∸ skip) (dropVec n skip bytes) (startBit Nat.% 8) bitLength

-- ============================================================================
-- PROOF: extractRaw ≡ bitVecToℕ ∘ extractBits
-- ============================================================================

-- extractRaw agrees with extractBits on identical inputs.
-- Bridges the dropVec optimization with the direct per-bit lookup.
--
-- Proof strategy: compose three steps:
--   1. extractCore-dropVec: extractCore on dropped vec ≡ extractCore on original (with sb%8 + skip*8)
--   2. Arithmetic: sb%8 + (sb/8)*8 ≡ sb (division algorithm identity)
--   3. extractCore-extractBits: extractCore ≡ bitVecToℕ ∘ extractBits
extractRaw-extractBits : ∀ (m : ℕ) (bytes : Vec Byte m) (sb bl : ℕ)
  → extractRaw m bytes sb bl ≡ bitVecToℕ (extractBits {bl} {m} bytes sb)
extractRaw-extractBits m bytes sb bl =
  let skip = sb Nat./ 8
      rem = sb Nat.% 8
      -- Step 1: extractCore on dropped vec ≡ extractCore on original with (rem + skip*8)
      step₁ : extractCore (m ∸ skip) (dropVec m skip bytes) rem bl
              ≡ extractCore m bytes (rem Nat.+ skip Nat.* 8) bl
      step₁ = extractCore-dropVec bl m bytes skip rem
      -- Step 2: rem + skip*8 ≡ sb (division algorithm: m ≡ m%n + m/n * n)
      step₂ : extractCore m bytes (rem Nat.+ skip Nat.* 8) bl
              ≡ extractCore m bytes sb bl
      step₂ = cong (λ x → extractCore m bytes x bl)
                    (sym (m≡m%n+[m/n]*n sb 8))
      -- Step 3: extractCore ≡ bitVecToℕ ∘ extractBits
      step₃ : extractCore m bytes sb bl
              ≡ bitVecToℕ (extractBits {bl} {m} bytes sb)
      step₃ = extractCore-extractBits bl m bytes sb
  in trans step₁ (trans step₂ step₃)

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
