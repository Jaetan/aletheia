{-# OPTIONS --safe --without-K #-}

-- All proofs complete! Frame bounds derived from explicit preconditions.

-- Byte order handling for CAN signal extraction (little/big endian).
--
-- Purpose: Convert between little-endian and big-endian byte representations.
-- Operations: byteSwap (reverse bytes), proven involutive (swap ∘ swap ≡ id).
-- Role: Used by CAN.Encoding to handle different signal byte orders in DBC.
--
-- Architecture: Uses BitVec for structural bit operations, not arithmetic.
-- Proof: byteSwap is its own inverse (Phase 1 proof, verified).
module Aletheia.CAN.Endianness where

open import Aletheia.CAN.Frame
open import Aletheia.Data.BitVec
open import Aletheia.Data.BitVec.Conversion
open import Data.Vec using (Vec; []; _∷_; lookup; updateAt; reverse; replicate)
open import Data.Fin using (Fin; toℕ; fromℕ<) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _<_; _≤_; _>_; _^_; _≡ᵇ_; z≤n; s≤s)
open import Data.Nat as Nat using (_/_; _%_)
open import Data.Nat.DivMod using (m%n<n)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; cong₂; _≢_; inspect; [_])
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (_∘_; id)

data ByteOrder : Set where
  LittleEndian BigEndian : ByteOrder

-- ============================================================================
-- BYTE <-> BITVEC CONVERSION
-- ============================================================================

-- Extract a byte to a natural number (for compatibility)
byteToℕ : Byte → ℕ
byteToℕ = toℕ

-- Convert a byte (Fin 256) to an 8-bit bitvector
byteToBitVec : Byte → BitVec 8
byteToBitVec b = ℕToBitVec (toℕ b) (byte-bounded b)
  where
    open import Data.Nat.Properties using (≤⇒≤″; ≤″⇒≤)
    open import Data.Fin.Properties using (toℕ<n)

    -- Byte values are < 256 = 2^8
    byte-bounded : ∀ (b : Byte) → toℕ b < 2 ^ 8
    byte-bounded b = subst (toℕ b <_) (sym 2^8≡256) (toℕ<n b)
      where
        2^8≡256 : 2 ^ 8 ≡ 256
        2^8≡256 = refl

-- Convert an 8-bit bitvector to a byte (Fin 256)
bitVecToByte : BitVec 8 → Byte
bitVecToByte bits = fromℕ< {bitVecToℕ bits} (bitVec-to-byte-bounded bits)
  where
    open import Data.Nat.Properties using (≤⇒≤″; ≤″⇒≤)

    -- BitVec 8 converts to ℕ < 256
    bitVec-to-byte-bounded : ∀ (bits : BitVec 8) → bitVecToℕ bits < 256
    bitVec-to-byte-bounded bits = subst (bitVecToℕ bits <_) 2^8≡256 (bitVecToℕ-bounded bits)
      where
        2^8≡256 : 2 ^ 8 ≡ 256
        2^8≡256 = refl

-- ============================================================================
-- BIT EXTRACTION AND INJECTION (STRUCTURAL)
-- ============================================================================

-- Helper: Safe lookup (returns 0 if out of bounds)
private
  lookupSafe : (n : ℕ) → ℕ → Vec Byte n → Byte
  lookupSafe zero _ _ = fzero
  lookupSafe (suc n) zero (b ∷ _) = b
  lookupSafe (suc n) (suc m) (_ ∷ bs) = lookupSafe n m bs

  updateSafe : (n : ℕ) → ℕ → (Byte → Byte) → Vec Byte n → Vec Byte n
  updateSafe zero _ _ bs = bs
  updateSafe (suc n) zero f (b ∷ bs) = f b ∷ bs
  updateSafe (suc n) (suc m) f (b ∷ bs) = b ∷ updateSafe n m f bs

-- Extract bits from a byte vector starting at a given bit position
-- Returns a BitVec (structural, not arithmetic)
extractBits : ∀ {length} → Vec Byte 8 → ℕ → BitVec length
extractBits {zero} bytes startBit = []
extractBits {suc length} bytes startBit = bitValue ∷ restBits
  where
    open import Data.Nat.DivMod using (m%n<n)
    open import Data.Nat as Nat using (_/_)

    byteIdx : ℕ
    byteIdx = startBit Nat./ 8

    bitInBytePos : Fin 8
    bitInBytePos = fromℕ< (m%n<n startBit 8)

    byte : Byte
    byte = lookupSafe 8 byteIdx bytes

    byteBits : BitVec 8
    byteBits = byteToBitVec byte

    bitValue : Bool
    bitValue = testBit byteBits bitInBytePos

    restBits : BitVec length
    restBits = extractBits bytes (suc startBit)

-- Inject bits into a byte vector at a given position
-- Takes a BitVec (structural, not arithmetic)
injectBits : ∀ {length} → Vec Byte 8 → ℕ → BitVec length → Vec Byte 8
injectBits bytes startBit [] = bytes
injectBits bytes startBit (bitValue ∷ restBits) = injectBits updatedBytes (suc startBit) restBits
  where
    open import Data.Nat.DivMod using (m%n<n)
    open import Data.Nat as Nat using (_/_)

    byteIdx : ℕ
    byteIdx = startBit Nat./ 8

    bitInBytePos : Fin 8
    bitInBytePos = fromℕ< (m%n<n startBit 8)

    updateByte : Byte → Byte
    updateByte b =
      let byteBits = byteToBitVec b
          updatedBits = setBit byteBits bitInBytePos bitValue
      in bitVecToByte updatedBits

    updatedBytes : Vec Byte 8
    updatedBytes = updateSafe 8 byteIdx updateByte bytes

-- ============================================================================
-- BYTE ORDER CONVERSION
-- ============================================================================

-- Byte order conversion for multi-byte sequences
swapBytes : Vec Byte 8 → Vec Byte 8
swapBytes = reverse

-- Proof that swapping twice is identity
swapBytes-involutive : ∀ (bytes : Vec Byte 8) → swapBytes (swapBytes bytes) ≡ bytes
swapBytes-involutive bytes = reverse-involutive bytes
  where
    open import Data.Vec.Properties using (reverse-involutive)

-- ============================================================================
-- BYTE ↔ BITVEC ROUNDTRIP PROOFS
-- ============================================================================

-- Proof: Byte → BitVec → Byte roundtrip
byteToBitVec-roundtrip : ∀ (b : Byte) → bitVecToByte (byteToBitVec b) ≡ b
byteToBitVec-roundtrip b = toℕ-injective (trans (toℕ-fromℕ< _) (bitVec-roundtrip 8 (toℕ b) (byte-bounded b)))
  where
    open import Data.Fin.Properties using (toℕ-injective; toℕ-fromℕ<)
    open import Data.Nat.Properties using (≤⇒≤″; ≤″⇒≤)

    byte-bounded : ∀ (b : Byte) → toℕ b < 2 ^ 8
    byte-bounded b = subst (toℕ b <_) (sym 2^8≡256) (toℕ<n b)
      where
        open import Data.Fin.Properties using (toℕ<n)
        2^8≡256 : 2 ^ 8 ≡ 256
        2^8≡256 = refl

-- Proof: BitVec → Byte → BitVec roundtrip
-- Custom congruence for ℕToBitVec that handles dependent bound proof
private
  ℕToBitVec-cong : ∀ {n m} {pn : n < 2 ^ 8} {pm : m < 2 ^ 8} →
    n ≡ m → ℕToBitVec {8} n pn ≡ ℕToBitVec {8} m pm
  ℕToBitVec-cong {n} {.n} refl = refl

bitVecToByte-roundtrip : ∀ (bits : BitVec 8) → byteToBitVec (bitVecToByte bits) ≡ bits
bitVecToByte-roundtrip bits =
  trans (ℕToBitVec-cong {n = toℕ (bitVecToByte bits)} {m = bitVecToℕ bits}
                         {pn = byte-bounded (bitVecToByte bits)}
                         {pm = bitVecToℕ-bounded bits}
                         (toℕ-fromℕ< (bitVecToℕ-bounded bits)))
    (bitVec-roundtrip-reverse 8 bits (bitVecToℕ-bounded bits))
  where
    open import Data.Fin.Properties using (toℕ<n)
    byte-bounded : ∀ (b : Byte) → toℕ b < 2 ^ 8
    byte-bounded b = subst (toℕ b <_) (sym refl) (toℕ<n b)

-- ============================================================================
-- EXTRACTBITS-INJECTBITS ROUNDTRIP PROOF
-- ============================================================================

-- Helper lemmas: lookupSafe and updateSafe non-interference
private
  -- Looking up the same index after update gives the updated value (requires idx < n)
  lookupSafe-updateSafe-same : ∀ {n idx : ℕ} (f : Byte → Byte) (bytes : Vec Byte n)
    → idx < n
    → lookupSafe n idx (updateSafe n idx f bytes) ≡ f (lookupSafe n idx bytes)
  lookupSafe-updateSafe-same {zero} f [] ()
  lookupSafe-updateSafe-same {suc n} {zero} f (b ∷ bytes) (s≤s z≤n) = refl
  lookupSafe-updateSafe-same {suc n} {suc idx} f (b ∷ bytes) (s≤s prf) = lookupSafe-updateSafe-same f bytes prf

  -- Looking up a different index after update gives the original value
  lookupSafe-updateSafe-diff : ∀ (n idx₁ idx₂ : ℕ) (f : Byte → Byte) (bytes : Vec Byte n)
    → idx₁ ≢ idx₂
    → lookupSafe n idx₁ (updateSafe n idx₂ f bytes) ≡ lookupSafe n idx₁ bytes
  lookupSafe-updateSafe-diff zero idx₁ idx₂ f bytes neq = refl
  lookupSafe-updateSafe-diff (suc n) zero zero f (b ∷ bytes) neq = ⊥-elim (neq refl)
  lookupSafe-updateSafe-diff (suc n) zero (suc idx₂) f (b ∷ bytes) neq = refl
  lookupSafe-updateSafe-diff (suc n) (suc idx₁) zero f (b ∷ bytes) neq = refl
  lookupSafe-updateSafe-diff (suc n) (suc idx₁) (suc idx₂) f (b ∷ bytes) neq =
    lookupSafe-updateSafe-diff n idx₁ idx₂ f bytes (λ eq → neq (cong suc eq))

  -- Key preservation lemma: injecting at positions ≥ laterPos doesn't affect bit at earlierPos
  -- Explicit non-interference condition: laterPos > earlierPos
  -- Frame bound: laterPos + length ≤ 64 (to derive laterByteIdx < 8)
  injectBits-preserves-earlier-bit :
    ∀ {length} (bytes : Vec Byte 8) (earlierPos laterPos : ℕ) (bits : BitVec length)
    → laterPos > earlierPos
    → laterPos + length ≤ 64
    → let earlierByteIdx = earlierPos Nat./ 8
          earlierBitPos = fromℕ< (m%n<n earlierPos 8)
      in testBit (byteToBitVec (lookupSafe 8 earlierByteIdx (injectBits bytes laterPos bits))) earlierBitPos
       ≡ testBit (byteToBitVec (lookupSafe 8 earlierByteIdx bytes)) earlierBitPos
  injectBits-preserves-earlier-bit bytes earlierPos laterPos [] later>earlier frameBound = refl
  injectBits-preserves-earlier-bit {suc len} bytes earlierPos laterPos (b ∷ bs) later>earlier frameBound =
    trans recursive-preservation first-step-preservation
    where
      open import Data.Nat.Properties using (_≟_)

      open import Data.Nat.DivMod using (m%n<n)
      open import Data.Nat as Nat using (_/_; _%_)

      earlierByteIdx : ℕ
      earlierByteIdx = earlierPos Nat./ 8

      earlierBitPos : Fin 8
      earlierBitPos = fromℕ< (m%n<n earlierPos 8)

      laterByteIdx : ℕ
      laterByteIdx = laterPos Nat./ 8

      laterBitPos : Fin 8
      laterBitPos = fromℕ< (m%n<n laterPos 8)

      -- First step: update byte at laterPos with b
      updatedBytes : Vec Byte 8
      updatedBytes = updateSafe 8 laterByteIdx (λ byte → bitVecToByte (setBit (byteToBitVec byte) laterBitPos b)) bytes

      -- Recursive step: inject bs at suc laterPos (preserves earlierPos since suc laterPos > earlierPos)
      recursive-preservation : testBit (byteToBitVec (lookupSafe 8 earlierByteIdx (injectBits updatedBytes (suc laterPos) bs))) earlierBitPos
                             ≡ testBit (byteToBitVec (lookupSafe 8 earlierByteIdx updatedBytes)) earlierBitPos
      recursive-preservation = injectBits-preserves-earlier-bit updatedBytes earlierPos (suc laterPos) bs (s≤s (<⇒≤ later>earlier)) restFrameBound
        where
          open import Data.Nat.Properties using (<⇒≤; +-suc)

          -- frameBound : laterPos + suc len ≤ 64
          -- want : suc laterPos + len ≤ 64
          -- Note: suc laterPos + len = suc (laterPos + len) by definition of +
          --       laterPos + suc len = suc (laterPos + len) by +-suc
          -- So they're equal!
          restFrameBound : suc laterPos + len ≤ 64
          restFrameBound = subst (_≤ 64) (+-suc laterPos len) frameBound

      -- First step: updating byte at laterPos preserves bit at earlierPos
      -- Case split: different byte indices OR same byte but different bit positions
      first-step-preservation : testBit (byteToBitVec (lookupSafe 8 earlierByteIdx updatedBytes)) earlierBitPos
                              ≡ testBit (byteToBitVec (lookupSafe 8 earlierByteIdx bytes)) earlierBitPos
      first-step-preservation with earlierByteIdx ≟ laterByteIdx
      ... | yes byteIdx-eq =
        -- Same byte: substitute to work with laterByteIdx, then use bit-level reasoning
        subst (λ idx → testBit (byteToBitVec (lookupSafe 8 idx updatedBytes)) earlierBitPos
                      ≡ testBit (byteToBitVec (lookupSafe 8 idx bytes)) earlierBitPos)
              (sym byteIdx-eq)
              (trans (cong (λ byte → testBit (byteToBitVec byte) earlierBitPos)
                           (lookupSafe-updateSafe-same (λ byte → bitVecToByte (setBit (byteToBitVec byte) laterBitPos b)) bytes laterByteIdx<8))
                (trans (cong (λ bv → testBit bv earlierBitPos) (bitVecToByte-roundtrip (setBit (byteToBitVec (lookupSafe 8 laterByteIdx bytes)) laterBitPos b)))
                  (testBit-setBit-diff (byteToBitVec (lookupSafe 8 laterByteIdx bytes)) laterBitPos earlierBitPos b laterBitPos≢earlierBitPos)))
        where
          open import Data.Fin.Properties using (toℕ-injective)
          open import Data.Nat.DivMod using (m≡m%n+[m/n]*n; m<n*o⇒m/o<n)
          open import Data.Nat.Properties using (<⇒≢; ≤-trans; m<n+m; <-≤-trans; +-comm)
          open import Data.Nat.Instances using () -- For NonZero instance

          -- Derive laterByteIdx < 8 from frame bound
          -- frameBound: laterPos + suc len ≤ 64 ⟹ laterPos < suc len + laterPos = laterPos + suc len ≤ 64 ⟹ laterPos < 64 = 8 * 8 ⟹ laterPos / 8 < 8
          laterByteIdx<8 : laterByteIdx < 8
          laterByteIdx<8 = m<n*o⇒m/o<n {laterPos} {8} {8} (subst (laterPos <_) (sym 8*8≡64) laterPos<64)
            where
              laterPos<64 : laterPos < 64
              laterPos<64 = <-≤-trans (subst (laterPos <_) (+-comm (suc len) laterPos) (m<n+m laterPos (s≤s z≤n))) frameBound

              8*8≡64 : 8 * 8 ≡ 64
              8*8≡64 = refl

          -- From laterPos > earlierPos and same byte, derive different bit positions
          -- Proof by contradiction: if laterBitPos ≡ earlierBitPos, then laterPos ≡ earlierPos (absurd)
          laterBitPos≢earlierBitPos : laterBitPos ≢ earlierBitPos
          laterBitPos≢earlierBitPos eq =
            <⇒≢ later>earlier pos-eq
            where
              open import Data.Fin.Properties using (toℕ-fromℕ<; toℕ-injective)
              open import Data.Nat as Nat using (_/_; _%_)

              -- earlierBitPos and laterBitPos are Fin 8, defined as:
              -- earlierBitPos = fromℕ< (m%n<n earlierPos 8)
              -- laterBitPos = fromℕ< (m%n<n laterPos 8)

              -- So: toℕ earlierBitPos ≡ earlierPos % 8 (by toℕ-fromℕ<)
              -- And: toℕ laterBitPos ≡ laterPos % 8 (by toℕ-fromℕ<)

              -- From eq : laterBitPos ≡ earlierBitPos, we derive:
              mod-eq : earlierPos Nat.% 8 ≡ laterPos Nat.% 8
              mod-eq = trans (sym earlier-eq) (trans (cong toℕ (sym eq)) later-eq)
                where
                  -- toℕ-fromℕ< eliminates the fromℕ< directly
                  earlier-eq : toℕ earlierBitPos ≡ earlierPos Nat.% 8
                  earlier-eq = toℕ-fromℕ< (m%n<n earlierPos 8)

                  later-eq : toℕ laterBitPos ≡ laterPos Nat.% 8
                  later-eq = toℕ-fromℕ< (m%n<n laterPos 8)

              -- From byteIdx-eq : earlierByteIdx ≡ laterByteIdx (i.e., earlierPos / 8 ≡ laterPos / 8)
              div-eq : earlierPos Nat./ 8 ≡ laterPos Nat./ 8
              div-eq = byteIdx-eq

              -- Reconstruct using m≡m%n+[m/n]*n
              pos-eq : earlierPos ≡ laterPos
              pos-eq =
                trans (m≡m%n+[m/n]*n earlierPos 8)
                  (trans (cong₂ _+_ mod-eq (cong (_* 8) div-eq))
                    (sym (m≡m%n+[m/n]*n laterPos 8)))
      ... | no neq = cong (λ x → testBit (byteToBitVec x) earlierBitPos) (lookupSafe-updateSafe-diff 8 earlierByteIdx laterByteIdx _ bytes neq)

  -- Symmetric case: injecting at earlier positions doesn't affect later bits
  -- Precondition: earlierPos + length ≤ laterPos (injection range ends before the checked bit)
  injectBits-preserves-later-bit :
    ∀ {length} (bytes : Vec Byte 8) (earlierPos laterPos : ℕ) (bits : BitVec length)
    → earlierPos + length ≤ laterPos
    → laterPos < 64
    → let laterByteIdx = laterPos Nat./ 8
          laterBitPos = fromℕ< (m%n<n laterPos 8)
      in testBit (byteToBitVec (lookupSafe 8 laterByteIdx (injectBits bytes earlierPos bits))) laterBitPos
       ≡ testBit (byteToBitVec (lookupSafe 8 laterByteIdx bytes)) laterBitPos
  injectBits-preserves-later-bit bytes earlierPos laterPos [] disjoint laterPos<64 = refl
  injectBits-preserves-later-bit {suc len} bytes earlierPos laterPos (b ∷ bs) disjoint laterPos<64 =
    trans recursive-preservation first-step-preservation
    where
      open import Data.Nat.Properties using (_≟_; ≤-trans; +-suc)
      open import Data.Nat.DivMod using (m%n<n; m<n*o⇒m/o<n)
      open import Data.Nat as Nat using (_/_; _%_)

      earlierByteIdx : ℕ
      earlierByteIdx = earlierPos Nat./ 8

      earlierBitPos : Fin 8
      earlierBitPos = fromℕ< (m%n<n earlierPos 8)

      laterByteIdx : ℕ
      laterByteIdx = laterPos Nat./ 8

      laterBitPos : Fin 8
      laterBitPos = fromℕ< (m%n<n laterPos 8)

      -- First step: update byte at earlierPos with b
      updatedBytes : Vec Byte 8
      updatedBytes = updateSafe 8 earlierByteIdx (λ byte → bitVecToByte (setBit (byteToBitVec byte) earlierBitPos b)) bytes

      -- Recursive: suc earlierPos + len ≤ laterPos (from earlierPos + suc len ≤ laterPos via +-suc)
      rest-disjoint : suc earlierPos + len ≤ laterPos
      rest-disjoint = subst (_≤ laterPos) (+-suc earlierPos len) disjoint

      -- Recursive step: inject bs at suc earlierPos preserves laterPos
      recursive-preservation : testBit (byteToBitVec (lookupSafe 8 laterByteIdx (injectBits updatedBytes (suc earlierPos) bs))) laterBitPos
                             ≡ testBit (byteToBitVec (lookupSafe 8 laterByteIdx updatedBytes)) laterBitPos
      recursive-preservation = injectBits-preserves-later-bit updatedBytes (suc earlierPos) laterPos bs rest-disjoint laterPos<64

      -- First step: updating byte at earlierPos preserves bit at laterPos
      -- Key: earlierPos < laterPos (since earlierPos + suc len ≤ laterPos implies earlierPos < laterPos)
      first-step-preservation : testBit (byteToBitVec (lookupSafe 8 laterByteIdx updatedBytes)) laterBitPos
                              ≡ testBit (byteToBitVec (lookupSafe 8 laterByteIdx bytes)) laterBitPos
      first-step-preservation with laterByteIdx ≟ earlierByteIdx
      ... | yes byteIdx-eq =
        -- Same byte: chain through earlierByteIdx where the update happened
        -- LHS: lookupSafe 8 laterByteIdx updatedBytes
        -- via byteIdx-eq: lookupSafe 8 earlierByteIdx updatedBytes
        -- via lookupSafe-updateSafe-same: f (lookupSafe 8 earlierByteIdx bytes)
        -- via byteIdx-eq: f (lookupSafe 8 laterByteIdx bytes)
        -- Then bit-level reasoning
        trans (cong (λ idx → testBit (byteToBitVec (lookupSafe 8 idx updatedBytes)) laterBitPos) byteIdx-eq)
          (trans (cong (λ byte → testBit (byteToBitVec byte) laterBitPos)
                       (lookupSafe-updateSafe-same (λ byte → bitVecToByte (setBit (byteToBitVec byte) earlierBitPos b)) bytes earlierByteIdx<8))
            (trans (cong (λ bv → testBit bv laterBitPos) (bitVecToByte-roundtrip (setBit (byteToBitVec (lookupSafe 8 earlierByteIdx bytes)) earlierBitPos b)))
              (trans (testBit-setBit-diff (byteToBitVec (lookupSafe 8 earlierByteIdx bytes)) earlierBitPos laterBitPos b earlierBitPos≢laterBitPos)
                (cong (λ idx → testBit (byteToBitVec (lookupSafe 8 idx bytes)) laterBitPos) (sym byteIdx-eq)))))
        where
          open import Data.Fin.Properties using (toℕ-injective; toℕ-fromℕ<)
          open import Data.Nat.DivMod using (m≡m%n+[m/n]*n)
          open import Data.Nat.Properties using (<⇒≢; ≤-trans; m≤m+n; <-≤-trans)

          -- earlierPos < laterPos from disjoint: earlierPos + suc len ≤ laterPos
          -- suc earlierPos ≤ suc (earlierPos + len) = earlierPos + suc len ≤ laterPos
          earlierPos<laterPos : earlierPos < laterPos
          earlierPos<laterPos = ≤-trans (m≤m+n (suc earlierPos) len) (subst (_≤ laterPos) (+-suc earlierPos len) disjoint)

          -- Derive earlierByteIdx < 8 from earlierPos < laterPos < 64
          earlierByteIdx<8 : earlierByteIdx < 8
          earlierByteIdx<8 = m<n*o⇒m/o<n {earlierPos} {8} {8} (<-≤-trans earlierPos<laterPos (<⇒≤ laterPos<64))
            where open import Data.Nat.Properties using (<⇒≤)

          -- Different bit positions (since earlierPos < laterPos but same byte)
          earlierBitPos≢laterBitPos : earlierBitPos ≢ laterBitPos
          earlierBitPos≢laterBitPos eq = <⇒≢ earlierPos<laterPos pos-eq
            where
              mod-eq : earlierPos Nat.% 8 ≡ laterPos Nat.% 8
              mod-eq = trans (sym (toℕ-fromℕ< (m%n<n earlierPos 8)))
                         (trans (cong toℕ eq) (toℕ-fromℕ< (m%n<n laterPos 8)))

              div-eq : earlierPos Nat./ 8 ≡ laterPos Nat./ 8
              div-eq = sym byteIdx-eq

              pos-eq : earlierPos ≡ laterPos
              pos-eq = trans (m≡m%n+[m/n]*n earlierPos 8)
                         (trans (cong₂ _+_ mod-eq (cong (_* 8) div-eq))
                           (sym (m≡m%n+[m/n]*n laterPos 8)))
      ... | no neq = cong (λ x → testBit (byteToBitVec x) laterBitPos) (lookupSafe-updateSafe-diff 8 laterByteIdx earlierByteIdx _ bytes neq)

-- Proof: Injecting bits at a disjoint range preserves extraction at another range
-- Two cases: injection before extraction, or extraction before injection
injectBits-preserves-disjoint :
  ∀ {len₁ len₂} (bytes : Vec Byte 8) (start₁ start₂ : ℕ) (bits : BitVec len₁)
  → start₁ + len₁ ≤ start₂ ⊎ start₂ + len₂ ≤ start₁  -- disjoint ranges
  → start₁ + len₁ ≤ 64
  → start₂ + len₂ ≤ 64
  → extractBits {len₂} (injectBits bytes start₁ bits) start₂ ≡ extractBits {len₂} bytes start₂
injectBits-preserves-disjoint {len₁} {zero} bytes start₁ start₂ bits disj bound₁ bound₂ = refl
-- Case: injection ends before extraction starts
injectBits-preserves-disjoint {len₁} {suc len₂} bytes start₁ start₂ bits (inj₁ inj-before-ext) bound₁ bound₂ =
  cong₂ _∷_ first-bit rest-bits
  where
    open import Data.Nat.DivMod using (m%n<n)
    open import Data.Nat as Nat using (_/_)
    open import Data.Nat.Properties using (+-suc; <-≤-trans; m<m+n; ≤-trans; n≤1+n)

    byteIdx = start₂ Nat./ 8
    bitPos = fromℕ< (m%n<n start₂ 8)
    start₂<64 = <-≤-trans (m<m+n start₂ {suc len₂} (s≤s z≤n)) bound₂

    first-bit = injectBits-preserves-later-bit bytes start₁ start₂ bits inj-before-ext start₂<64

    rest-bound₂ = subst (_≤ 64) (+-suc start₂ len₂) bound₂
    rest-disj = inj₁ (≤-trans inj-before-ext (n≤1+n start₂))
    rest-bits = injectBits-preserves-disjoint bytes start₁ (suc start₂) bits rest-disj bound₁ rest-bound₂

-- Case: extraction ends before injection starts
injectBits-preserves-disjoint {len₁} {suc len₂} bytes start₁ start₂ bits (inj₂ ext-before-inj) bound₁ bound₂ =
  cong₂ _∷_ first-bit rest-bits
  where
    open import Data.Nat.DivMod using (m%n<n)
    open import Data.Nat as Nat using (_/_)
    open import Data.Nat.Properties using (+-suc; <-≤-trans; m<m+n; m+n≤o⇒n≤o)

    byteIdx = start₂ Nat./ 8
    bitPos = fromℕ< (m%n<n start₂ 8)
    start₂<64 = <-≤-trans (m<m+n start₂ {suc len₂} (s≤s z≤n)) bound₂

    -- start₂ + suc len₂ ≤ start₁ ⟹ start₂ < start₂ + suc len₂ ≤ start₁ ⟹ start₂ < start₁
    start₂<start₁ : start₂ < start₁
    start₂<start₁ = <-≤-trans (m<m+n start₂ {suc len₂} (s≤s z≤n)) ext-before-inj
    first-bit = injectBits-preserves-earlier-bit bytes start₂ start₁ bits start₂<start₁ bound₁

    rest-bound₂ = subst (_≤ 64) (+-suc start₂ len₂) bound₂
    rest-disj = inj₂ (subst (_≤ start₁) (+-suc start₂ len₂) ext-before-inj)
    rest-bits = injectBits-preserves-disjoint bytes start₁ (suc start₂) bits rest-disj bound₁ rest-bound₂

-- Proof: Extracting after injecting returns the original bitvector
-- Statement strengthened: ∀ startBit → (polymorphic IH for recursion at suc startBit)
-- Precondition: startBit + length ≤ 64 (fits within CAN frame)
extractBits-injectBits-roundtrip :
  ∀ {length} →
  (bytes : Vec Byte 8) →
  ∀ startBit →
  (bits : BitVec length) →
  startBit + length ≤ 64 →
  extractBits (injectBits bytes startBit bits) startBit ≡ bits
extractBits-injectBits-roundtrip bytes startBit [] bound = refl
extractBits-injectBits-roundtrip {suc len} bytes startBit (b ∷ bs) bound =
  cong₂ _∷_ first-bit rest-bits
  where
    open import Data.Nat.DivMod using (m%n<n)
    open import Data.Nat as Nat using (_/_)

    byteIdx : ℕ
    byteIdx = startBit Nat./ 8

    bitPos : Fin 8
    bitPos = fromℕ< (m%n<n startBit 8)

    updateByteFn : Byte → Byte
    updateByteFn byte = bitVecToByte (setBit (byteToBitVec byte) bitPos b)

    -- After injecting b at startBit, the bytes are updated
    updatedBytes : Vec Byte 8
    updatedBytes = updateSafe 8 byteIdx updateByteFn bytes

    -- Bound for recursive call: (suc startBit) + len ≤ 64
    -- bound : startBit + suc len ≤ 64
    -- +-suc : startBit + suc len ≡ suc (startBit + len) = suc startBit + len
    rest-bound : suc startBit + len ≤ 64
    rest-bound = subst (_≤ 64) (+-suc startBit len) bound
      where open import Data.Nat.Properties using (+-suc)

    -- First bit: the bit at startBit equals b after injecting (b ∷ bs)
    -- Strategy: unfold injectBits one step, use preservation lemma, then byteToBitVec-roundtrip + testBit-setBit-same
    first-bit : testBit (byteToBitVec (lookupSafe 8 byteIdx (injectBits bytes startBit (b ∷ bs)))) bitPos ≡ b
    first-bit =
      trans (injectBits-preserves-earlier-bit updatedBytes startBit (suc startBit) bs (s≤s ≤-refl) rest-bound)
        (trans (cong (λ byte → testBit (byteToBitVec byte) bitPos) (lookupSafe-updateSafe-same updateByteFn bytes byteIdx<8))
          (trans (cong (λ bv → testBit bv bitPos) (bitVecToByte-roundtrip (setBit (byteToBitVec (lookupSafe 8 byteIdx bytes)) bitPos b)))
            (testBit-setBit-same (byteToBitVec (lookupSafe 8 byteIdx bytes)) bitPos b)))
      where
        open import Data.Nat.Properties using (≤-refl; +-suc; ≤-trans; m<n+m; <-≤-trans; +-comm)
        open import Data.Nat.DivMod using (m<n*o⇒m/o<n)
        open import Data.Nat.Instances using () -- For NonZero instance

        -- Derive byteIdx < 8 from frame bound
        -- startBit + suc len ≤ 64 ⟹ startBit < suc len + startBit = startBit + suc len ≤ 64 ⟹ startBit < 64 = 8 * 8 ⟹ startBit / 8 < 8
        byteIdx<8 : byteIdx < 8
        byteIdx<8 = m<n*o⇒m/o<n {startBit} {8} {8} (subst (startBit <_) (sym 8*8≡64) startBit<64)
          where
            startBit<64 : startBit < 64
            startBit<64 = <-≤-trans (subst (startBit <_) (+-comm (suc len) startBit) (m<n+m startBit (s≤s z≤n))) bound

            8*8≡64 : 8 * 8 ≡ 64
            8*8≡64 = refl

    -- Rest bits: by IH at suc startBit (definitional with strengthened statement!)
    rest-bits : extractBits (injectBits bytes startBit (b ∷ bs)) (suc startBit) ≡ bs
    rest-bits = extractBits-injectBits-roundtrip updatedBytes (suc startBit) bs rest-bound

-- ============================================================================
-- IMPLEMENTATION NOTES
-- ============================================================================
{-
Key architectural change:

OLD (arithmetic-based):
  extractBits : Vec Byte 8 → ℕ → ℕ → ℕ
  injectBits : Vec Byte 8 → ℕ → ℕ → ℕ → Vec Byte 8

  Proofs required arithmetic reasoning about:
  - Power-of-2 independence
  - Carry propagation
  - Modular arithmetic

NEW (structure-based):
  extractBits : Vec Byte 8 → ℕ → BitVec length
  injectBits : Vec Byte 8 → ℕ → BitVec length → Vec Byte 8

  Proofs use structural properties from BitVec module:
  - testBit-setBit-same (1 line)
  - testBit-setBit-diff (1 line)
  - No arithmetic!

The conversion Byte ↔ BitVec happens at the boundary and uses the
Conversion module's roundtrip proof (proven once).

This is the correct abstraction level for reasoning about CAN frames.
-}
