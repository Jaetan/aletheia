{-# OPTIONS --safe --without-K #-}

-- Byte order handling for CAN signal extraction (little/big endian).
--
-- Purpose: Convert between little-endian and big-endian byte representations.
-- Operations: byteSwap (reverse bytes), proven involutive (swap ∘ swap ≡ id).
-- Role: Used by CAN.Encoding to handle different signal byte orders in DBC.
--
-- Architecture: Uses BitVec for structural bit operations, not arithmetic.
-- Proof: byteSwap is its own inverse (Phase 1 proof, verified).
module Aletheia.CAN.Endianness where

open import Aletheia.CAN.Frame using (Byte)
open import Aletheia.Data.BitVec using (BitVec; testBit; setBit; testBit-setBit-same; testBit-setBit-diff; setBit-setBit-comm)
open import Aletheia.Data.BitVec.Conversion using (ℕToBitVec; bitVecToℕ; bitVec-roundtrip; bitVec-roundtrip-reverse; bitVecToℕ-bounded)
open import Data.Vec using (Vec; []; _∷_; reverse)
open import Data.Vec.Properties using (reverse-involutive)
open import Data.Fin using (Fin; toℕ; fromℕ<) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (toℕ-fromℕ<; toℕ-injective)
open import Data.Nat as Nat using (ℕ; zero; suc; _+_; _∸_; _*_; _<_; _≤_; _>_; _^_; z≤n; s≤s; _/_; _%_)
open import Data.Nat.DivMod using (m%n<n; m<n⇒m%n≡m; m≡m%n+[m/n]*n; m<n*o⇒m/o<n; [m+n]%n≡m%n)
open import Data.Nat.Properties using (_≟_; <⇒≤; <⇒≢; +-suc; +-comm; +-assoc; +-identityʳ; ≤-refl; ≤-trans; n≤1+n; m≤m+n; m<n+m; m<m+n; <-≤-trans; m+n≤o⇒n≤o; m≤n⇒m≤1+n; +-cancelʳ-≡; *-cancelʳ-≡; +-monoˡ-≤; +-monoʳ-<; *-monoˡ-≤; m∸n≤m)
-- Instance-only import: brings NonZero into scope for m<n*o⇒m/o<n
import Data.Nat.Instances
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂; cong₂; _≢_)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Function using (_∘_)

private
  8*8≡64 : 8 * 8 ≡ 64
  8*8≡64 = refl

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

-- Helper: Safe lookup (returns 0 if out of bounds)
private
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
extractBits : ∀ {length} → Vec Byte 8 → ℕ → BitVec length
extractBits {zero} bytes startBit = []
extractBits {suc length} bytes startBit = bitValue ∷ restBits
  where
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

-- Check if byte order is big-endian
isBigEndian : ByteOrder → Bool
isBigEndian LittleEndian = false
isBigEndian BigEndian = true

-- Byte order conversion for multi-byte sequences
swapBytes : Vec Byte 8 → Vec Byte 8
swapBytes = reverse

-- Proof that swapping twice is identity
swapBytes-involutive : ∀ (bytes : Vec Byte 8) → swapBytes (swapBytes bytes) ≡ bytes
swapBytes-involutive bytes = reverse-involutive bytes

-- ============================================================================
-- BYTE ↔ BITVEC ROUNDTRIP PROOFS
-- ============================================================================

-- Proof: Byte → BitVec → Byte roundtrip (modular: result is b % 256)
byteToBitVec-roundtrip : ∀ (b : Byte) → bitVecToByte (byteToBitVec b) ≡ b Nat.% 256
byteToBitVec-roundtrip b = bitVec-roundtrip 8 (b Nat.% 256) (m%n<n b 256)

-- Proof: BitVec → Byte → BitVec roundtrip
-- Custom congruence for ℕToBitVec that handles dependent bound proof
private
  ℕToBitVec-cong : ∀ {n m} {pn : n < 2 ^ 8} {pm : m < 2 ^ 8} →
    n ≡ m → ℕToBitVec {8} n pn ≡ ℕToBitVec {8} m pm
  ℕToBitVec-cong {n} {.n} refl = refl

bitVecToByte-roundtrip : ∀ (bits : BitVec 8) → byteToBitVec (bitVecToByte bits) ≡ bits
bitVecToByte-roundtrip bits =
  trans (ℕToBitVec-cong {pn = m%n<n (bitVecToℕ bits) 256}
                        {pm = bitVecToℕ-bounded bits}
                        (m<n⇒m%n≡m (bitVecToℕ-bounded bits)))
    (bitVec-roundtrip-reverse 8 bits (bitVecToℕ-bounded bits))

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
          -- Derive laterByteIdx < 8 from frame bound
          laterByteIdx<8 : laterByteIdx < 8
          laterByteIdx<8 = m<n*o⇒m/o<n {laterPos} {8} {8} (subst (laterPos <_) (sym 8*8≡64) laterPos<64)
            where
              laterPos<64 : laterPos < 64
              laterPos<64 = <-≤-trans (subst (laterPos <_) (+-comm (suc len) laterPos) (m<n+m laterPos (s≤s z≤n))) frameBound

          -- From laterPos > earlierPos and same byte, derive different bit positions
          laterBitPos≢earlierBitPos : laterBitPos ≢ earlierBitPos
          laterBitPos≢earlierBitPos eq =
            <⇒≢ later>earlier pos-eq
            where
              mod-eq : earlierPos Nat.% 8 ≡ laterPos Nat.% 8
              mod-eq = trans (sym (toℕ-fromℕ< (m%n<n earlierPos 8)))
                         (trans (cong toℕ (sym eq)) (toℕ-fromℕ< (m%n<n laterPos 8)))

              pos-eq : earlierPos ≡ laterPos
              pos-eq =
                trans (m≡m%n+[m/n]*n earlierPos 8)
                  (trans (cong₂ _+_ mod-eq (cong (_* 8) byteIdx-eq))
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
          earlierPos<laterPos : earlierPos < laterPos
          earlierPos<laterPos = ≤-trans (m≤m+n (suc earlierPos) len) (subst (_≤ laterPos) (+-suc earlierPos len) disjoint)

          earlierByteIdx<8 : earlierByteIdx < 8
          earlierByteIdx<8 = m<n*o⇒m/o<n {earlierPos} {8} {8} (<-≤-trans earlierPos<laterPos (<⇒≤ laterPos<64))

          earlierBitPos≢laterBitPos : earlierBitPos ≢ laterBitPos
          earlierBitPos≢laterBitPos eq = <⇒≢ earlierPos<laterPos pos-eq
            where
              mod-eq : earlierPos Nat.% 8 ≡ laterPos Nat.% 8
              mod-eq = trans (sym (toℕ-fromℕ< (m%n<n earlierPos 8)))
                         (trans (cong toℕ eq) (toℕ-fromℕ< (m%n<n laterPos 8)))

              pos-eq : earlierPos ≡ laterPos
              pos-eq = trans (m≡m%n+[m/n]*n earlierPos 8)
                         (trans (cong₂ _+_ mod-eq (cong (_* 8) (sym byteIdx-eq)))
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
    start₂<64 = <-≤-trans (m<m+n start₂ {suc len₂} (s≤s z≤n)) bound₂

    first-bit = injectBits-preserves-later-bit bytes start₁ start₂ bits inj-before-ext start₂<64

    rest-bound₂ = subst (_≤ 64) (+-suc start₂ len₂) bound₂
    rest-disj = inj₁ (≤-trans inj-before-ext (n≤1+n start₂))
    rest-bits = injectBits-preserves-disjoint bytes start₁ (suc start₂) bits rest-disj bound₁ rest-bound₂

-- Case: extraction ends before injection starts
injectBits-preserves-disjoint {len₁} {suc len₂} bytes start₁ start₂ bits (inj₂ ext-before-inj) bound₁ bound₂ =
  cong₂ _∷_ first-bit rest-bits
  where
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

    -- First bit: the bit at startBit equals b after injecting (b ∷ bs)
    first-bit : testBit (byteToBitVec (lookupSafe 8 byteIdx (injectBits bytes startBit (b ∷ bs)))) bitPos ≡ b
    first-bit =
      trans (injectBits-preserves-earlier-bit updatedBytes startBit (suc startBit) bs (s≤s ≤-refl) rest-bound)
        (trans (cong (λ byte → testBit (byteToBitVec byte) bitPos) (lookupSafe-updateSafe-same updateByteFn bytes byteIdx<8))
          (trans (cong (λ bv → testBit bv bitPos) (bitVecToByte-roundtrip (setBit (byteToBitVec (lookupSafe 8 byteIdx bytes)) bitPos b)))
            (testBit-setBit-same (byteToBitVec (lookupSafe 8 byteIdx bytes)) bitPos b)))
      where
        byteIdx<8 : byteIdx < 8
        byteIdx<8 = m<n*o⇒m/o<n {startBit} {8} {8} (subst (startBit <_) (sym 8*8≡64) startBit<64)
          where
            startBit<64 : startBit < 64
            startBit<64 = <-≤-trans (subst (startBit <_) (+-comm (suc len) startBit) (m<n+m startBit (s≤s z≤n))) bound

    -- Rest bits: by IH at suc startBit (definitional with strengthened statement!)
    rest-bits : extractBits (injectBits bytes startBit (b ∷ bs)) (suc startBit) ≡ bs
    rest-bits = extractBits-injectBits-roundtrip updatedBytes (suc startBit) bs rest-bound

-- ============================================================================
-- COMMUTATIVITY: Disjoint injections commute
-- ============================================================================
-- Key insight: injectBits is semantically "apply a finite map of bit writes".
-- Disjoint write sets commute trivially once lifted to this abstraction.

private
  -- A single bit write: (absolute position, value)
  BitWrite : Set
  BitWrite = ℕ × Bool

  -- Apply a single bit write to the frame
  applyWrite : Vec Byte 8 → BitWrite → Vec Byte 8
  applyWrite bytes (pos , val) = updateSafe 8 byteIdx updateFn bytes
    where
      byteIdx = pos Nat./ 8
      bitPos = fromℕ< (m%n<n pos 8)
      updateFn = λ byte → bitVecToByte (setBit (byteToBitVec byte) bitPos val)

  -- Apply a list of writes (fold left = first write applied first, matching injectBits)
  applyWrites : Vec Byte 8 → List BitWrite → Vec Byte 8
  applyWrites bytes [] = bytes
  applyWrites bytes (w ∷ ws) = applyWrites (applyWrite bytes w) ws

  -- Convert BitVec to a list of writes starting at position s
  writesOf : ∀ {len} → ℕ → BitVec len → List BitWrite
  writesOf s [] = []
  writesOf s (b ∷ bs) = (s , b) ∷ writesOf (suc s) bs

  -- Two writes are at different positions
  DiffPos : BitWrite → BitWrite → Set
  DiffPos (p₁ , _) (p₂ , _) = p₁ ≢ p₂

  -- All pairs from two lists have different positions
  AllDiffPos : List BitWrite → List BitWrite → Set
  AllDiffPos [] _ = ⊤
  AllDiffPos (w ∷ ws) ws₂ = All (DiffPos w) ws₂ × AllDiffPos ws ws₂

  -- All writes within a single list are at distinct positions
  AllDistinct : List BitWrite → Set
  AllDistinct [] = ⊤
  AllDistinct (w ∷ ws) = All (DiffPos w) ws × AllDistinct ws

-- ============================================================================
-- WRITE-SET LEMMAS (the semantic layer)
-- ============================================================================

-- Two single writes at different positions commute
private
  applyWrite-comm : ∀ bytes w₁ w₂ → DiffPos w₁ w₂
    → applyWrite (applyWrite bytes w₂) w₁ ≡ applyWrite (applyWrite bytes w₁) w₂
  applyWrite-comm bytes (p₁ , v₁) (p₂ , v₂) p₁≢p₂ = case-split
    where
      idx₁ = p₁ Nat./ 8
      idx₂ = p₂ Nat./ 8
      bitPos₁ = fromℕ< (m%n<n p₁ 8)
      bitPos₂ = fromℕ< (m%n<n p₂ 8)
      f₁ = λ byte → bitVecToByte (setBit (byteToBitVec byte) bitPos₁ v₁)
      f₂ = λ byte → bitVecToByte (setBit (byteToBitVec byte) bitPos₂ v₂)

      -- Different byte indices: use updateSafe commutativity
      diff-byte : idx₁ ≢ idx₂ → applyWrite (applyWrite bytes (p₂ , v₂)) (p₁ , v₁)
                              ≡ applyWrite (applyWrite bytes (p₁ , v₁)) (p₂ , v₂)
      diff-byte neq = updateSafe-comm-diff-lemma idx₁ idx₂ f₁ f₂ bytes neq
        where
          updateSafe-comm-diff-lemma : ∀ {n} (i₁ i₂ : ℕ) (g₁ g₂ : Byte → Byte) (bs : Vec Byte n)
            → i₁ ≢ i₂
            → updateSafe n i₁ g₁ (updateSafe n i₂ g₂ bs) ≡ updateSafe n i₂ g₂ (updateSafe n i₁ g₁ bs)
          updateSafe-comm-diff-lemma {zero} _ _ _ _ [] _ = refl
          updateSafe-comm-diff-lemma {suc n} zero zero _ _ _ neq = ⊥-elim (neq refl)
          updateSafe-comm-diff-lemma {suc n} zero (suc _) _ _ (b ∷ bs) _ = refl
          updateSafe-comm-diff-lemma {suc n} (suc _) zero _ _ (b ∷ bs) _ = refl
          updateSafe-comm-diff-lemma {suc n} (suc i₁) (suc i₂) g₁ g₂ (x ∷ xs) neq =
            cong (x ∷_) (updateSafe-comm-diff-lemma i₁ i₂ g₁ g₂ xs (λ eq → neq (cong suc eq)))

      -- Same byte index but different bit positions: use setBit commutativity
      same-byte : idx₁ ≡ idx₂ → applyWrite (applyWrite bytes (p₂ , v₂)) (p₁ , v₁)
                              ≡ applyWrite (applyWrite bytes (p₁ , v₁)) (p₂ , v₂)
      same-byte idx-eq = updateSafe-same-compose idx-eq bitPos₁≢bitPos₂
        where
          -- p₁ ≢ p₂ and p₁/8 = p₂/8 implies p₁%8 ≢ p₂%8
          bitPos₁≢bitPos₂ : bitPos₁ ≢ bitPos₂
          bitPos₁≢bitPos₂ eq = p₁≢p₂ (trans (m≡m%n+[m/n]*n p₁ 8)
            (trans (cong₂ _+_ (trans (sym (toℕ-fromℕ< (m%n<n p₁ 8)))
                               (trans (cong toℕ eq) (toℕ-fromℕ< (m%n<n p₂ 8))))
                             (cong (_* 8) idx-eq))
              (sym (m≡m%n+[m/n]*n p₂ 8))))

          -- When indices are equal, use function composition and setBit commutativity
          updateSafe-same-compose : idx₁ ≡ idx₂ → bitPos₁ ≢ bitPos₂
            → updateSafe 8 idx₁ f₁ (updateSafe 8 idx₂ f₂ bytes)
            ≡ updateSafe 8 idx₂ f₂ (updateSafe 8 idx₁ f₁ bytes)
          updateSafe-same-compose idx-eq bp-neq =
            subst₂ (λ i j → updateSafe 8 i f₁ (updateSafe 8 j f₂ bytes) ≡ updateSafe 8 j f₂ (updateSafe 8 i f₁ bytes))
                   (sym idx-eq) refl same-idx-proof
            where
              updateSafe-same-lemma : ∀ {n} (i : ℕ) (h₁ h₂ : Byte → Byte) (xs : Vec Byte n)
                → updateSafe n i h₁ (updateSafe n i h₂ xs) ≡ updateSafe n i (h₁ ∘ h₂) xs
              updateSafe-same-lemma {zero} _ _ _ [] = refl
              updateSafe-same-lemma {suc _} zero _ _ (x ∷ xs) = refl
              updateSafe-same-lemma {suc n} (suc i) h₁ h₂ (x ∷ xs) =
                cong (x ∷_) (updateSafe-same-lemma i h₁ h₂ xs)

              updateSafe-cong-fn-lemma : ∀ {n} (i : ℕ) (h₁ h₂ : Byte → Byte) (xs : Vec Byte n)
                → (∀ b → h₁ b ≡ h₂ b) → updateSafe n i h₁ xs ≡ updateSafe n i h₂ xs
              updateSafe-cong-fn-lemma {zero} _ _ _ [] _ = refl
              updateSafe-cong-fn-lemma {suc _} zero h₁ h₂ (x ∷ xs) eq = cong (_∷ xs) (eq x)
              updateSafe-cong-fn-lemma {suc n} (suc i) h₁ h₂ (x ∷ xs) eq =
                cong (x ∷_) (updateSafe-cong-fn-lemma i h₁ h₂ xs eq)

              -- (f₁ ∘ f₂) ≡ (f₂ ∘ f₁) pointwise via setBit commutativity
              fns-commute : ∀ b → (f₁ ∘ f₂) b ≡ (f₂ ∘ f₁) b
              fns-commute b =
                trans (cong (λ bv → bitVecToByte (setBit bv bitPos₁ v₁))
                            (bitVecToByte-roundtrip (setBit (byteToBitVec b) bitPos₂ v₂)))
                  (trans (cong bitVecToByte (setBit-setBit-comm (byteToBitVec b) bitPos₂ bitPos₁ v₂ v₁ (bp-neq ∘ sym)))
                    (sym (cong (λ bv → bitVecToByte (setBit bv bitPos₂ v₂))
                               (bitVecToByte-roundtrip (setBit (byteToBitVec b) bitPos₁ v₁)))))

              -- Proof when both indices are idx₂
              same-idx-proof : updateSafe 8 idx₂ f₁ (updateSafe 8 idx₂ f₂ bytes)
                             ≡ updateSafe 8 idx₂ f₂ (updateSafe 8 idx₂ f₁ bytes)
              same-idx-proof = trans (updateSafe-same-lemma idx₂ f₁ f₂ bytes)
                (trans (updateSafe-cong-fn-lemma idx₂ (f₁ ∘ f₂) (f₂ ∘ f₁) bytes fns-commute)
                  (sym (updateSafe-same-lemma idx₂ f₂ f₁ bytes)))

      case-split : applyWrite (applyWrite bytes (p₂ , v₂)) (p₁ , v₁)
                 ≡ applyWrite (applyWrite bytes (p₁ , v₁)) (p₂ , v₂)
      case-split with idx₁ ≟ idx₂
      ... | yes eq = same-byte eq
      ... | no neq = diff-byte neq

-- Helper: push a write through a list of disjoint writes
-- applyWrites (applyWrite bytes w) ws ≡ applyWrite (applyWrites bytes ws) w
applyWrites-push : ∀ bytes w ws
  → All (DiffPos w) ws
  → applyWrites (applyWrite bytes w) ws ≡ applyWrite (applyWrites bytes ws) w
applyWrites-push bytes w [] [] = refl
applyWrites-push bytes w (w' ∷ ws) (diff ∷ diffs) =
  trans (cong (λ frame → applyWrites frame ws) (sym (applyWrite-comm bytes w w' diff)))
    (applyWrites-push (applyWrite bytes w') w ws diffs)

-- Two disjoint write lists commute (requires both lists are internally distinct)
applyWrites-comm : ∀ bytes ws₁ ws₂
  → AllDistinct ws₁
  → AllDiffPos ws₁ ws₂
  → applyWrites (applyWrites bytes ws₁) ws₂ ≡ applyWrites (applyWrites bytes ws₂) ws₁
applyWrites-comm bytes [] ws₂ _ _ = refl
applyWrites-comm bytes (w ∷ ws₁) ws₂ (w-diff-ws₁ , ws₁-distinct) (w-diff-ws₂ , rest-diff) =
  trans (applyWrites-comm (applyWrite bytes w) ws₁ ws₂ ws₁-distinct rest-diff)
    (cong (λ frame → applyWrites frame ws₁) (applyWrites-push bytes w ws₂ w-diff-ws₂))

-- ============================================================================
-- CONNECTING injectBits TO applyWrites
-- ============================================================================

-- injectBits is exactly applyWrites with writesOf
-- This is now trivial since both use left-fold semantics
injectBits≡applyWrites : ∀ {len} bytes s (bits : BitVec len)
  → injectBits bytes s bits ≡ applyWrites bytes (writesOf s bits)
injectBits≡applyWrites bytes s [] = refl
injectBits≡applyWrites bytes s (b ∷ bs) = injectBits≡applyWrites (applyWrite bytes (s , b)) (suc s) bs

-- writesOf produces internally distinct write lists (consecutive positions)
writesOf-distinct : ∀ {len} s (bits : BitVec len) → AllDistinct (writesOf s bits)
writesOf-distinct s [] = tt
writesOf-distinct s (b ∷ bs) = (all-later-diff s (suc s) bs ≤-refl , writesOf-distinct (suc s) bs)
  where
    -- All positions in writesOf start bs are ≥ start, hence ≠ pos when pos < start
    all-later-diff : ∀ {len} pos start (bits : BitVec len)
      → pos < start  -- pos < start means suc pos ≤ start
      → All (DiffPos (pos , b)) (writesOf start bits)
    all-later-diff pos start [] _ = []
    all-later-diff {suc len} pos start (b' ∷ bs') pos<start =
      (<⇒≢ pos<start) ∷ all-later-diff pos (suc start) bs' (m≤n⇒m≤1+n pos<start)

-- Disjoint ranges produce disjoint write lists
disjoint-ranges→AllDiffPos : ∀ {len₁ len₂} s₁ s₂ (bits₁ : BitVec len₁) (bits₂ : BitVec len₂)
  → s₁ + len₁ ≤ s₂ ⊎ s₂ + len₂ ≤ s₁
  → AllDiffPos (writesOf s₁ bits₁) (writesOf s₂ bits₂)
disjoint-ranges→AllDiffPos s₁ s₂ [] bits₂ disj = tt
disjoint-ranges→AllDiffPos {suc len₁} s₁ s₂ (b₁ ∷ bs₁) bits₂ disj = (all-diff , rest)
  where
    -- s₁ is not equal to any position in range [s₂, s₂+len₂)
    s₁-diff-from-range : ∀ {len} s (bits : BitVec len) → s₁ + suc len₁ ≤ s ⊎ s + len ≤ s₁
      → All (DiffPos (s₁ , b₁)) (writesOf s bits)
    s₁-diff-from-range s [] _ = []
    s₁-diff-from-range {suc len} s (b ∷ bs) disj' = neq ∷ s₁-diff-from-range (suc s) bs rest-disj
      where
        neq : s₁ ≢ s
        neq = case-disj disj'
          where
            case-disj : s₁ + suc len₁ ≤ s ⊎ s + suc len ≤ s₁ → s₁ ≢ s
            case-disj (inj₁ p) = <⇒≢ (<-≤-trans (m<m+n s₁ {suc len₁} (s≤s z≤n)) p)
            case-disj (inj₂ p) = λ eq → <⇒≢ (<-≤-trans (m<m+n s {suc len} (s≤s z≤n)) p) (sym eq)

        rest-disj : s₁ + suc len₁ ≤ suc s ⊎ suc s + len ≤ s₁
        rest-disj = case-disj disj'
          where
            case-disj : s₁ + suc len₁ ≤ s ⊎ s + suc len ≤ s₁ → s₁ + suc len₁ ≤ suc s ⊎ suc s + len ≤ s₁
            case-disj (inj₁ p) = inj₁ (≤-trans p (n≤1+n s))
            case-disj (inj₂ p) = inj₂ (subst (_≤ s₁) (+-suc s len) p)

    all-diff : All (DiffPos (s₁ , b₁)) (writesOf s₂ bits₂)
    all-diff = s₁-diff-from-range s₂ bits₂ disj

    rest : AllDiffPos (writesOf (suc s₁) bs₁) (writesOf s₂ bits₂)
    rest = disjoint-ranges→AllDiffPos (suc s₁) s₂ bs₁ bits₂ rest-disj
      where
        rest-disj : suc s₁ + len₁ ≤ s₂ ⊎ s₂ + _ ≤ suc s₁
        rest-disj = case-disj disj
          where
            case-disj : s₁ + suc len₁ ≤ s₂ ⊎ s₂ + _ ≤ s₁ → suc s₁ + len₁ ≤ s₂ ⊎ s₂ + _ ≤ suc s₁
            case-disj (inj₁ p) = inj₁ (subst (_≤ s₂) (+-suc s₁ len₁) p)
            case-disj (inj₂ p) = inj₂ (≤-trans p (n≤1+n s₁))

-- ============================================================================
-- MAIN THEOREM (now almost trivial!)
-- ============================================================================

-- Disjoint bit injections commute
-- Proof: lift to write-set semantics where commutativity is immediate
injectBits-commute :
  ∀ {len₁ len₂} (bytes : Vec Byte 8) (s₁ s₂ : ℕ)
    (bits₁ : BitVec len₁) (bits₂ : BitVec len₂)
  → s₁ + len₁ ≤ s₂ ⊎ s₂ + len₂ ≤ s₁  -- disjoint ranges
  → s₁ + len₁ ≤ 64
  → s₂ + len₂ ≤ 64
  → injectBits (injectBits bytes s₁ bits₁) s₂ bits₂
    ≡ injectBits (injectBits bytes s₂ bits₂) s₁ bits₁
injectBits-commute bytes s₁ s₂ bits₁ bits₂ disj _ _ =
  begin
    injectBits (injectBits bytes s₁ bits₁) s₂ bits₂
  ≡⟨ cong (λ x → injectBits x s₂ bits₂) (injectBits≡applyWrites bytes s₁ bits₁) ⟩
    injectBits (applyWrites bytes ws₁) s₂ bits₂
  ≡⟨ injectBits≡applyWrites (applyWrites bytes ws₁) s₂ bits₂ ⟩
    applyWrites (applyWrites bytes ws₁) ws₂
  ≡⟨ applyWrites-comm bytes ws₁ ws₂ (writesOf-distinct s₁ bits₁) (disjoint-ranges→AllDiffPos s₁ s₂ bits₁ bits₂ disj) ⟩
    applyWrites (applyWrites bytes ws₂) ws₁
  ≡⟨ sym (injectBits≡applyWrites (applyWrites bytes ws₂) s₁ bits₁) ⟩
    injectBits (applyWrites bytes ws₂) s₁ bits₁
  ≡⟨ cong (λ x → injectBits x s₁ bits₁) (sym (injectBits≡applyWrites bytes s₂ bits₂)) ⟩
    injectBits (injectBits bytes s₂ bits₂) s₁ bits₁
  ∎
  where
    open ≡-Reasoning
    ws₁ = writesOf s₁ bits₁
    ws₂ = writesOf s₂ bits₂

-- ============================================================================
-- PAYLOAD ISOMORPHISM (factors out byte order handling)
-- ============================================================================

-- The byte order isomorphism: id for LittleEndian, swapBytes for BigEndian
-- Defined using if to match injectSignal's implementation definitionally
payloadIso : ByteOrder → Vec Byte 8 → Vec Byte 8
payloadIso bo bytes = if isBigEndian bo then swapBytes bytes else bytes

-- payloadIso is an involution for any byte order
payloadIso-involutive : ∀ bo bytes → payloadIso bo (payloadIso bo bytes) ≡ bytes
payloadIso-involutive LittleEndian bytes = refl
payloadIso-involutive BigEndian bytes = swapBytes-involutive bytes

-- Inject bits with byte order handling factored out
-- injectPayload = payloadIso ∘ injectBits ∘ payloadIso
injectPayload : ∀ {len} → ℕ → BitVec len → ByteOrder → Vec Byte 8 → Vec Byte 8
injectPayload s bits bo payload =
  payloadIso bo (injectBits (payloadIso bo payload) s bits)

-- Commutativity of injectPayload: disjoint injections commute uniformly
-- This is the key lemma - byte order is handled once via payloadIso-involutive
injectPayload-commute :
  ∀ {len₁ len₂} s₁ s₂ (bits₁ : BitVec len₁) (bits₂ : BitVec len₂) bo payload
  → s₁ + len₁ ≤ s₂ ⊎ s₂ + len₂ ≤ s₁
  → s₁ + len₁ ≤ 64
  → s₂ + len₂ ≤ 64
  → injectPayload s₂ bits₂ bo (injectPayload s₁ bits₁ bo payload)
    ≡ injectPayload s₁ bits₁ bo (injectPayload s₂ bits₂ bo payload)
injectPayload-commute s₁ s₂ bits₁ bits₂ bo payload disj fits₁ fits₂ =
  begin
    injectPayload s₂ bits₂ bo (injectPayload s₁ bits₁ bo payload)
  ≡⟨⟩  -- expand definitions, use payloadIso-involutive
    payloadIso bo (injectBits (payloadIso bo (payloadIso bo (injectBits (payloadIso bo payload) s₁ bits₁))) s₂ bits₂)
  ≡⟨ cong (λ x → payloadIso bo (injectBits x s₂ bits₂)) (payloadIso-involutive bo _) ⟩
    payloadIso bo (injectBits (injectBits (payloadIso bo payload) s₁ bits₁) s₂ bits₂)
  ≡⟨ cong (payloadIso bo) (injectBits-commute (payloadIso bo payload) s₁ s₂ bits₁ bits₂ disj fits₁ fits₂) ⟩
    payloadIso bo (injectBits (injectBits (payloadIso bo payload) s₂ bits₂) s₁ bits₁)
  ≡⟨ cong (λ x → payloadIso bo (injectBits x s₁ bits₁)) (sym (payloadIso-involutive bo _)) ⟩
    payloadIso bo (injectBits (payloadIso bo (payloadIso bo (injectBits (payloadIso bo payload) s₂ bits₂))) s₁ bits₁)
  ≡⟨⟩  -- fold definitions
    injectPayload s₁ bits₁ bo (injectPayload s₂ bits₂ bo payload)
  ∎
  where
    open ≡-Reasoning

-- ============================================================================
-- SAME BYTE ORDER: disjoint extraction preserved through injectPayload
-- ============================================================================

-- When both inject and extract use the same byte order, payloadIso cancels
-- and we reduce directly to injectBits-preserves-disjoint.
--
-- This is the common case: CAN messages typically use consistent byte order.

injectPayload-preserves-disjoint-same :
  ∀ {len₁ len₂} s₁ s₂ (bits : BitVec len₁) bo payload
  → s₁ + len₁ ≤ s₂ ⊎ s₂ + len₂ ≤ s₁  -- disjoint ranges
  → s₁ + len₁ ≤ 64
  → s₂ + len₂ ≤ 64
  → extractBits {len₂} (payloadIso bo (injectPayload s₁ bits bo payload)) s₂
    ≡ extractBits {len₂} (payloadIso bo payload) s₂
injectPayload-preserves-disjoint-same {len₁} {len₂} s₁ s₂ bits bo payload disj fits₁ fits₂ =
  begin
    extractBits {len₂} (payloadIso bo (injectPayload s₁ bits bo payload)) s₂
  ≡⟨⟩  -- expand injectPayload
    extractBits {len₂} (payloadIso bo (payloadIso bo (injectBits (payloadIso bo payload) s₁ bits))) s₂
  ≡⟨ cong (λ x → extractBits {len₂} x s₂) (payloadIso-involutive bo _) ⟩
    extractBits {len₂} (injectBits (payloadIso bo payload) s₁ bits) s₂
  ≡⟨ injectBits-preserves-disjoint (payloadIso bo payload) s₁ s₂ bits disj fits₁ fits₂ ⟩
    extractBits {len₂} (payloadIso bo payload) s₂
  ∎
  where
    open ≡-Reasoning

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
physicalBitPos : ByteOrder → ℕ → ℕ
physicalBitPos LittleEndian b = b
physicalBitPos BigEndian b = (7 ∸ (b / 8)) * 8 + (b % 8)

-- ============================================================================
-- CROSS-BYTE-ORDER HELPERS
-- ============================================================================

-- lookupSafe through swapBytes: byte i in reversed = byte (7∸i) in original
-- Proven by concrete case analysis on i ∈ {0..7} with vector pattern matching.
-- reverse normalizes on concrete-length vectors with variable elements.
lookupSafe-swapBytes : ∀ i → i < 8 → ∀ (bytes : Vec Byte 8) →
  lookupSafe 8 i (swapBytes bytes) ≡ lookupSafe 8 (7 ∸ i) bytes
lookupSafe-swapBytes 0 _ (b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ b₅ ∷ b₆ ∷ b₇ ∷ []) = refl
lookupSafe-swapBytes 1 _ (b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ b₅ ∷ b₆ ∷ b₇ ∷ []) = refl
lookupSafe-swapBytes 2 _ (b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ b₅ ∷ b₆ ∷ b₇ ∷ []) = refl
lookupSafe-swapBytes 3 _ (b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ b₅ ∷ b₆ ∷ b₇ ∷ []) = refl
lookupSafe-swapBytes 4 _ (b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ b₅ ∷ b₆ ∷ b₇ ∷ []) = refl
lookupSafe-swapBytes 5 _ (b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ b₅ ∷ b₆ ∷ b₇ ∷ []) = refl
lookupSafe-swapBytes 6 _ (b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ b₅ ∷ b₆ ∷ b₇ ∷ []) = refl
lookupSafe-swapBytes 7 _ (b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ b₅ ∷ b₆ ∷ b₇ ∷ []) = refl
lookupSafe-swapBytes (suc (suc (suc (suc (suc (suc (suc (suc _))))))))
  (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ())))))))) _

-- ============================================================================
-- ARITHMETIC HELPERS for physicalBitPos
-- ============================================================================

private
  -- (m + k * 8) % 8 ≡ m % 8  (repeatedly adding multiples of 8 doesn't change mod)
  [m+kn]%8≡m%8 : ∀ m k → (m + k * 8) % 8 ≡ m % 8
  [m+kn]%8≡m%8 m zero rewrite +-identityʳ m = refl
  [m+kn]%8≡m%8 m (suc k) =
    trans (cong (λ x → (m + x) % 8) (+-comm 8 (k * 8)))
      (trans (cong (_% 8) (sym (+-assoc m (k * 8) 8)))
        (trans ([m+n]%n≡m%n (m + k * 8) 8)
          ([m+kn]%8≡m%8 m k)))

  -- (a * 8 + r) % 8 ≡ r  when r < 8
  mul-add-mod : ∀ a r → r < 8 → (a * 8 + r) % 8 ≡ r
  mul-add-mod a r r<8 =
    trans (cong (_% 8) (+-comm (a * 8) r))
      (trans ([m+kn]%8≡m%8 r a) (m<n⇒m%n≡m r<8))

  -- (a * 8 + r) / 8 ≡ a  when r < 8
  -- Proof: from the division theorem a*8+r = (a*8+r)%8 + ((a*8+r)/8)*8
  --        and mul-add-mod, derive a*8+r = r + ((a*8+r)/8)*8
  --        hence a*8 = ((a*8+r)/8)*8, so a = (a*8+r)/8
  mul-add-div : ∀ a r → r < 8 → (a * 8 + r) / 8 ≡ a
  mul-add-div a r r<8 = *-cancelʳ-≡ ((a * 8 + r) / 8) a 8 step3
    where
      open import Data.Nat.Properties using (*-cancelʳ-≡)

      step1 : a * 8 + r ≡ (a * 8 + r) % 8 + ((a * 8 + r) / 8) * 8
      step1 = m≡m%n+[m/n]*n (a * 8 + r) 8

      step2 : a * 8 + r ≡ r + ((a * 8 + r) / 8) * 8
      step2 = trans step1 (cong (_+ ((a * 8 + r) / 8) * 8) (mul-add-mod a r r<8))

      step3 : ((a * 8 + r) / 8) * 8 ≡ a * 8
      step3 = begin
          ((a * 8 + r) / 8) * 8
        ≡⟨ sym (cancel-right step2) ⟩
          a * 8
        ∎
        where
          open ≡-Reasoning
          -- a*8+r ≡ r + q*8  ⟹  q*8 ≡ a*8
          cancel-right : a * 8 + r ≡ r + ((a * 8 + r) / 8) * 8
                       → a * 8 ≡ ((a * 8 + r) / 8) * 8
          cancel-right eq = Data.Nat.Properties.+-cancelʳ-≡ r (a * 8) _ eq'
            where
              eq' : a * 8 + r ≡ ((a * 8 + r) / 8) * 8 + r
              eq' = trans eq (+-comm r _)

  -- physicalBitPos BE b has the same byte index and bit-in-byte as expected
  physicalBitPos-BE-div8 : ∀ b → b < 64 → physicalBitPos BigEndian b / 8 ≡ 7 ∸ (b / 8)
  physicalBitPos-BE-div8 b b<64 = mul-add-div (7 ∸ (b / 8)) (b % 8) (m%n<n b 8)

  physicalBitPos-BE-mod8 : ∀ b → physicalBitPos BigEndian b % 8 ≡ b % 8
  physicalBitPos-BE-mod8 b = mul-add-mod (7 ∸ (b / 8)) (b % 8) (m%n<n b 8)

-- physicalBitPos BE maps [0,64) → [0,64)
physicalBitPos-BE-bounded : ∀ b → b < 64 → physicalBitPos BigEndian b < 64
physicalBitPos-BE-bounded b b<64 = <-≤-trans step1 step2
  where
    byteIdx = b / 8
    revByte = 7 ∸ byteIdx
    bitIdx = b % 8

    byteIdx<8 : byteIdx < 8
    byteIdx<8 = m<n*o⇒m/o<n {b} {8} {8} (subst (b <_) (sym 8*8≡64) b<64)

    revByte*8≤56 : revByte * 8 ≤ 56
    revByte*8≤56 = *-monoˡ-≤ 8 (m∸n≤m 7 byteIdx)

    step1 : revByte * 8 + bitIdx < revByte * 8 + 8
    step1 = +-monoʳ-< (revByte * 8) (m%n<n b 8)

    step2 : revByte * 8 + 8 ≤ 64
    step2 = +-monoˡ-≤ 8 revByte*8≤56

-- physicalBitPos BE is an involution on [0,64)
physicalBitPos-BE-involutive : ∀ b → b < 64 → physicalBitPos BigEndian (physicalBitPos BigEndian b) ≡ b
physicalBitPos-BE-involutive b b<64 =
  begin
    physicalBitPos BigEndian (physicalBitPos BigEndian b)
  ≡⟨⟩
    (7 ∸ (physBit / 8)) * 8 + (physBit % 8)
  ≡⟨ cong (λ x → (7 ∸ x) * 8 + (physBit % 8)) (physicalBitPos-BE-div8 b b<64) ⟩
    (7 ∸ (7 ∸ (b / 8))) * 8 + (physBit % 8)
  ≡⟨ cong (λ x → (7 ∸ (7 ∸ (b / 8))) * 8 + x) (physicalBitPos-BE-mod8 b) ⟩
    (7 ∸ (7 ∸ (b / 8))) * 8 + (b % 8)
  ≡⟨ cong (λ x → x * 8 + (b % 8)) (m∸[m∸n]≡n byteIdx≤7) ⟩
    (b / 8) * 8 + (b % 8)
  ≡⟨ div-mod-identity b ⟩
    b
  ∎
  where
    open ≡-Reasoning
    open import Data.Nat.Properties using (m∸[m∸n]≡n; n∸n≡0)
    physBit = physicalBitPos BigEndian b

    byteIdx<8 : b / 8 < 8
    byteIdx<8 = m<n*o⇒m/o<n {b} {8} {8} (subst (b <_) (sym 8*8≡64) b<64)

    byteIdx≤7 : b / 8 ≤ 7
    byteIdx≤7 with byteIdx<8
    ... | s≤s p = p

    -- (b / 8) * 8 + (b % 8) ≡ b  (from division theorem + commutativity)
    div-mod-identity : ∀ n → (n / 8) * 8 + (n % 8) ≡ n
    div-mod-identity n = trans (+-comm ((n / 8) * 8) (n % 8)) (sym (m≡m%n+[m/n]*n n 8))

-- If p ≢ a+k for all k < m, then p < a or a+m ≤ p
not-in-interval : ∀ a m p → (∀ k → k < m → p ≢ a + k) → p < a ⊎ a + m ≤ p
not-in-interval a m p noHit = go a m p noHit
  where
    open import Data.Nat.Properties using (_<?_; ≮⇒≥; ≤-antisym)

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

-- ============================================================================
-- UNIFIED BIT PRESERVATION LEMMA
-- ============================================================================

-- If physical bit position p is outside the injection range [s, s+len),
-- then the bit at p is unchanged after injectBits.
injectBits-preserves-bit :
  ∀ {len} (bytes : Vec Byte 8) (s p : ℕ) (bits : BitVec len)
  → p < s ⊎ s + len ≤ p
  → s + len ≤ 64
  → p < 64
  → testBit (byteToBitVec (lookupSafe 8 (p / 8) (injectBits bytes s bits)))
            (fromℕ< (m%n<n p 8))
    ≡ testBit (byteToBitVec (lookupSafe 8 (p / 8) bytes))
              (fromℕ< (m%n<n p 8))
injectBits-preserves-bit bytes s p bits (inj₁ p<s) bound _ =
  injectBits-preserves-earlier-bit bytes p s bits p<s bound
injectBits-preserves-bit bytes s p bits (inj₂ s+len≤p) _ p<64 =
  injectBits-preserves-later-bit bytes s p bits s+len≤p p<64

-- Per-bit version of injectBits-preserves-disjoint:
-- when every extraction bit is individually outside the injection range,
-- extraction is preserved. Avoids needing interval disjointness
-- (which can't be derived from pointwise disjointness for zero-length intervals).
injectBits-preserves-outside :
  ∀ {len₁ len₂} (bytes : Vec Byte 8) (start₁ start₂ : ℕ) (bits : BitVec len₁)
  → (∀ k → k < len₂ → start₂ + k < start₁ ⊎ start₁ + len₁ ≤ start₂ + k)
  → start₁ + len₁ ≤ 64
  → start₂ + len₂ ≤ 64
  → extractBits {len₂} (injectBits bytes start₁ bits) start₂ ≡ extractBits {len₂} bytes start₂
injectBits-preserves-outside {_} {zero} _ _ _ _ _ _ _ = refl
injectBits-preserves-outside {len₁} {suc len₂} bytes start₁ start₂ bits outside bound₁ bound₂ =
  cong₂ _∷_ head-eq rest-eq
  where
    start₂<64 : start₂ < 64
    start₂<64 = <-≤-trans (m<m+n start₂ {suc len₂} (s≤s z≤n)) bound₂

    head-outside : start₂ < start₁ ⊎ start₁ + len₁ ≤ start₂
    head-outside with outside 0 (s≤s z≤n)
    ... | inj₁ p = inj₁ (subst (_< start₁) (+-identityʳ start₂) p)
    ... | inj₂ q = inj₂ (subst (start₁ + len₁ ≤_) (+-identityʳ start₂) q)

    head-eq = injectBits-preserves-bit bytes start₁ start₂ bits head-outside bound₁ start₂<64

    bound₂' : suc start₂ + len₂ ≤ 64
    bound₂' = subst (_≤ 64) (+-suc start₂ len₂) bound₂

    outside' : ∀ k → k < len₂ → suc start₂ + k < start₁ ⊎ start₁ + len₁ ≤ suc start₂ + k
    outside' k k<len₂ with outside (suc k) (s≤s k<len₂)
    ... | inj₁ p = inj₁ (subst (_< start₁) (+-suc start₂ k) p)
    ... | inj₂ q = inj₂ (subst (start₁ + len₁ ≤_) (+-suc start₂ k) q)

    rest-eq = injectBits-preserves-outside bytes start₁ (suc start₂) bits outside' bound₁ bound₂'

-- ============================================================================
-- CROSS-BYTE-ORDER EXTRACTION PRESERVATION
-- ============================================================================

-- Key lemma: extracting from swapBytes(injectBits bytes s₁ bits) at position s₂
-- is the same as from swapBytes(bytes) at s₂, provided the physical bit
-- positions don't overlap with the injection range.
--
-- Physical non-overlap: for each extraction bit k < l₂, the physical position
-- physicalBitPos BE (s₂+k) is outside [s₁, s₁+l₁).

extractBits-swap-inject-preserves :
  ∀ {l₁ l₂} (bytes : Vec Byte 8) (s₁ s₂ : ℕ) (bits : BitVec l₁)
  → (∀ k → k < l₂ → physicalBitPos BigEndian (s₂ + k) < s₁
                    ⊎ s₁ + l₁ ≤ physicalBitPos BigEndian (s₂ + k))
  → s₁ + l₁ ≤ 64
  → s₂ + l₂ ≤ 64
  → extractBits {l₂} (swapBytes (injectBits bytes s₁ bits)) s₂
    ≡ extractBits {l₂} (swapBytes bytes) s₂
extractBits-swap-inject-preserves {l₁} bytes s₁ s₂ bits noOverlap bound₁ bound₂ = go _ s₂ noOverlap bound₂
  where
    go : ∀ l₂ (pos : ℕ)
      → (∀ k → k < l₂ → physicalBitPos BigEndian (pos + k) < s₁
                        ⊎ s₁ + l₁ ≤ physicalBitPos BigEndian (pos + k))
      → pos + l₂ ≤ 64
      → extractBits {l₂} (swapBytes (injectBits bytes s₁ bits)) pos
        ≡ extractBits {l₂} (swapBytes bytes) pos
    go zero pos noOv bound = refl
    go (suc l₂') pos noOv bound = cong₂ _∷_ head-eq (go l₂' (suc pos) noOv' bound')
      where
        -- Bounds for recursion
        bound' : suc pos + l₂' ≤ 64
        bound' = subst (_≤ 64) (+-suc pos l₂') bound

        noOv' : ∀ k → k < l₂' → physicalBitPos BigEndian (suc pos + k) < s₁
                                ⊎ s₁ + l₁ ≤ physicalBitPos BigEndian (suc pos + k)
        noOv' k k<l₂' = subst (λ x → physicalBitPos BigEndian x < s₁
                                     ⊎ s₁ + l₁ ≤ physicalBitPos BigEndian x)
                               (+-suc pos k)
                               (noOv (suc k) (s≤s k<l₂'))

        -- Head bit: the first extracted bit is the same
        pos<64 : pos < 64
        pos<64 = <-≤-trans (m<m+n pos {suc l₂'} (s≤s z≤n)) bound

        byteIdx : ℕ
        byteIdx = pos / 8

        byteIdx<8 : byteIdx < 8
        byteIdx<8 = m<n*o⇒m/o<n {pos} {8} {8} (subst (pos <_) (sym 8*8≡64) pos<64)

        -- Physical bit position for this extraction bit
        physBit : ℕ
        physBit = physicalBitPos BigEndian pos

        -- Physical bit is within [0,64): (7∸byteIdx)*8 + pos%8 < 64
        -- Since byteIdx < 8: (7∸byteIdx) ≤ 7, so (7∸byteIdx)*8 ≤ 56, and pos%8 < 8
        physBit<64 : physBit < 64
        physBit<64 = physicalBitPos-BE-bounded pos pos<64

        -- The disjointness condition for this bit (k = 0, with pos + 0 = pos)
        physBit-disj : physBit < s₁ ⊎ s₁ + l₁ ≤ physBit
        physBit-disj = subst (λ x → physicalBitPos BigEndian x < s₁
                                   ⊎ s₁ + l₁ ≤ physicalBitPos BigEndian x)
                             (+-comm pos 0 )
                             (noOv 0 (s≤s z≤n))

        -- Step 1: lookupSafe through swapBytes
        -- lookupSafe 8 byteIdx (swapBytes v) ≡ lookupSafe 8 (7 ∸ byteIdx) v
        swap-lhs : lookupSafe 8 byteIdx (swapBytes (injectBits bytes s₁ bits))
                 ≡ lookupSafe 8 (7 ∸ byteIdx) (injectBits bytes s₁ bits)
        swap-lhs = lookupSafe-swapBytes byteIdx byteIdx<8 (injectBits bytes s₁ bits)

        swap-rhs : lookupSafe 8 byteIdx (swapBytes bytes)
                 ≡ lookupSafe 8 (7 ∸ byteIdx) bytes
        swap-rhs = lookupSafe-swapBytes byteIdx byteIdx<8 bytes

        -- Step 2: The injection at [s₁, s₁+l₁) doesn't affect byte (7∸byteIdx) at bit pos%8
        -- This is because the physical bit position physBit is outside [s₁, s₁+l₁)

        -- physBit / 8 ≡ 7 ∸ byteIdx
        physBit-div : physBit / 8 ≡ 7 ∸ byteIdx
        physBit-div = physicalBitPos-BE-div8 pos pos<64

        -- physBit % 8 ≡ pos % 8
        physBit-mod : physBit % 8 ≡ pos % 8
        physBit-mod = physicalBitPos-BE-mod8 pos

        -- The bit at physBit in the injected bytes equals the bit in the original bytes
        bit-preserved : testBit (byteToBitVec (lookupSafe 8 (physBit / 8) (injectBits bytes s₁ bits)))
                                (fromℕ< (m%n<n physBit 8))
                      ≡ testBit (byteToBitVec (lookupSafe 8 (physBit / 8) bytes))
                                (fromℕ< (m%n<n physBit 8))
        bit-preserved = injectBits-preserves-bit bytes s₁ physBit bits physBit-disj bound₁ physBit<64

        -- Step 3: Transport through the div/mod equalities to get the byte/bit indices we need
        -- We need: testBit (byteToBitVec (lookupSafe 8 (7∸byteIdx) (injectBits ...))) (fromℕ< (m%n<n pos 8))
        --        ≡ testBit (byteToBitVec (lookupSafe 8 (7∸byteIdx) bytes)) (fromℕ< (m%n<n pos 8))
        inner-preserved : testBit (byteToBitVec (lookupSafe 8 (7 ∸ byteIdx) (injectBits bytes s₁ bits)))
                                  (fromℕ< (m%n<n pos 8))
                        ≡ testBit (byteToBitVec (lookupSafe 8 (7 ∸ byteIdx) bytes))
                                  (fromℕ< (m%n<n pos 8))
        inner-preserved =
          subst₂ (λ idx bpos →
            testBit (byteToBitVec (lookupSafe 8 idx (injectBits bytes s₁ bits))) bpos
            ≡ testBit (byteToBitVec (lookupSafe 8 idx bytes)) bpos)
            physBit-div
            (toℕ-injective (trans (toℕ-fromℕ< (m%n<n physBit 8))
                             (trans physBit-mod
                               (sym (toℕ-fromℕ< (m%n<n pos 8))))))
            bit-preserved

        -- Final: combine swapBytes steps with the inner preservation
        head-eq : testBit (byteToBitVec (lookupSafe 8 byteIdx (swapBytes (injectBits bytes s₁ bits))))
                          (fromℕ< (m%n<n pos 8))
                ≡ testBit (byteToBitVec (lookupSafe 8 byteIdx (swapBytes bytes)))
                          (fromℕ< (m%n<n pos 8))
        head-eq = trans (cong (λ x → testBit (byteToBitVec x) (fromℕ< (m%n<n pos 8))) swap-lhs)
                   (trans inner-preserved
                     (cong (λ x → testBit (byteToBitVec x) (fromℕ< (m%n<n pos 8))) (sym swap-rhs)))

-- ============================================================================
-- MIXED BYTE-ORDER COMMUTATIVITY (Item B)
-- ============================================================================
-- Extends injectPayload-commute to mixed byte orders (LE signal + BE signal).
-- Strategy: swap-conjugation converts cross-BO operations to applyWrites at
-- physical positions, then applyWrites-comm handles commutativity.

-- Layer 0: Concrete swap-update on Vec Byte 8
-- swapBytes (updateSafe at i in swapped) ≡ updateSafe at (7∸i) in original
private
  swap-updateSafe-swap : ∀ i → i < 8 → ∀ (f : Byte → Byte) (bytes : Vec Byte 8)
    → swapBytes (updateSafe 8 i f (swapBytes bytes)) ≡ updateSafe 8 (7 ∸ i) f bytes
  swap-updateSafe-swap 0 _ f (b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ b₅ ∷ b₆ ∷ b₇ ∷ []) = refl
  swap-updateSafe-swap 1 _ f (b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ b₅ ∷ b₆ ∷ b₇ ∷ []) = refl
  swap-updateSafe-swap 2 _ f (b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ b₅ ∷ b₆ ∷ b₇ ∷ []) = refl
  swap-updateSafe-swap 3 _ f (b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ b₅ ∷ b₆ ∷ b₇ ∷ []) = refl
  swap-updateSafe-swap 4 _ f (b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ b₅ ∷ b₆ ∷ b₇ ∷ []) = refl
  swap-updateSafe-swap 5 _ f (b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ b₅ ∷ b₆ ∷ b₇ ∷ []) = refl
  swap-updateSafe-swap 6 _ f (b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ b₅ ∷ b₆ ∷ b₇ ∷ []) = refl
  swap-updateSafe-swap 7 _ f (b₀ ∷ b₁ ∷ b₂ ∷ b₃ ∷ b₄ ∷ b₅ ∷ b₆ ∷ b₇ ∷ []) = refl
  swap-updateSafe-swap (suc (suc (suc (suc (suc (suc (suc (suc _))))))))
    (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ())))))))) _ _

-- Layer 1: Single-write swap-conjugation
-- Converts applyWrite at logical position in swapped frame to applyWrite at physical position.
private
  -- updateSafe with pointwise-equal functions gives equal results
  updateSafe-cong-fn′ : ∀ {n} (i : ℕ) (h₁ h₂ : Byte → Byte) (xs : Vec Byte n)
    → (∀ b → h₁ b ≡ h₂ b) → updateSafe n i h₁ xs ≡ updateSafe n i h₂ xs
  updateSafe-cong-fn′ {zero} _ _ _ [] _ = refl
  updateSafe-cong-fn′ {suc _} zero h₁ h₂ (x ∷ xs) eq = cong (_∷ xs) (eq x)
  updateSafe-cong-fn′ {suc n} (suc i) h₁ h₂ (x ∷ xs) eq =
    cong (x ∷_) (updateSafe-cong-fn′ i h₁ h₂ xs eq)

  -- Core: swap-conjugation for a single applyWrite
  swap-applyWrite-swap : ∀ bytes pos val → pos < 64
    → swapBytes (applyWrite (swapBytes bytes) (pos , val))
      ≡ applyWrite bytes (physicalBitPos BigEndian pos , val)
  swap-applyWrite-swap bytes pos val pos<64 =
    trans step1 (trans step2 step3)
    where
      physBit = physicalBitPos BigEndian pos
      byteIdx = pos / 8
      bitPos = fromℕ< (m%n<n pos 8)
      fn₁ = λ byte → bitVecToByte (setBit (byteToBitVec byte) bitPos val)

      physByteIdx = physBit / 8
      physBitPos′ = fromℕ< (m%n<n physBit 8)
      fn₂ = λ byte → bitVecToByte (setBit (byteToBitVec byte) physBitPos′ val)

      byteIdx<8 : byteIdx < 8
      byteIdx<8 = m<n*o⇒m/o<n {pos} {8} {8} (subst (pos <_) (sym 8*8≡64) pos<64)

      -- Step 1: swap-updateSafe-swap converts to updateSafe at (7∸byteIdx)
      step1 : swapBytes (applyWrite (swapBytes bytes) (pos , val))
            ≡ updateSafe 8 (7 ∸ byteIdx) fn₁ bytes
      step1 = swap-updateSafe-swap byteIdx byteIdx<8 fn₁ bytes

      -- Step 2: equate update functions (bit positions match via physicalBitPos-BE-mod8)
      fin-eq : physBitPos′ ≡ bitPos
      fin-eq = toℕ-injective (trans (toℕ-fromℕ< (m%n<n physBit 8))
                               (trans (physicalBitPos-BE-mod8 pos)
                                 (sym (toℕ-fromℕ< (m%n<n pos 8)))))

      fns-pw : ∀ b → fn₁ b ≡ fn₂ b
      fns-pw b = cong (λ bp → bitVecToByte (setBit (byteToBitVec b) bp val)) (sym fin-eq)

      step2 : updateSafe 8 (7 ∸ byteIdx) fn₁ bytes
            ≡ updateSafe 8 (7 ∸ byteIdx) fn₂ bytes
      step2 = updateSafe-cong-fn′ (7 ∸ byteIdx) fn₁ fn₂ bytes fns-pw

      -- Step 3: equate byte indices (7∸pos/8 ≡ physBit/8 via physicalBitPos-BE-div8)
      step3 : updateSafe 8 (7 ∸ byteIdx) fn₂ bytes
            ≡ updateSafe 8 physByteIdx fn₂ bytes
      step3 = cong (λ i → updateSafe 8 i fn₂ bytes)
                   (sym (physicalBitPos-BE-div8 pos pos<64))

-- Layer 2: Multi-write swap-conjugation
-- Lifts swap-conjugation from single writes to write lists.

-- Map write positions through physicalBitPos BE
physicalWrites : List BitWrite → List BitWrite
physicalWrites = map (λ { (p , v) → (physicalBitPos BigEndian p , v) })

private
  -- All positions in writesOf s bits are < 64 when s + len ≤ 64
  writesOf-bounded : ∀ {len} s (bits : BitVec len) → s + len ≤ 64
    → All (λ { (pos , _) → pos < 64 }) (writesOf s bits)
  writesOf-bounded s [] _ = []
  writesOf-bounded s (b ∷ bits) bound =
    <-≤-trans (m<m+n s {suc _} (s≤s z≤n)) bound
    ∷ writesOf-bounded (suc s) bits (subst (_≤ 64) (+-suc s _) bound)

-- Swap-conjugation lifts from single writes to write lists
swap-applyWrites-swap : ∀ bytes ws
  → All (λ { (pos , _) → pos < 64 }) ws
  → swapBytes (applyWrites (swapBytes bytes) ws) ≡ applyWrites bytes (physicalWrites ws)
swap-applyWrites-swap bytes [] [] = swapBytes-involutive bytes
swap-applyWrites-swap bytes ((pos , val) ∷ ws) (pos<64 ∷ rest) =
  trans (cong (λ x → swapBytes (applyWrites x ws)) aw-rev)
    (swap-applyWrites-swap (applyWrite bytes (physicalBitPos BigEndian pos , val)) ws rest)
  where
    -- Reversed direction: applyWrite in swapped frame ≡ swapBytes of applyWrite at phys pos
    aw-rev : applyWrite (swapBytes bytes) (pos , val)
           ≡ swapBytes (applyWrite bytes (physicalBitPos BigEndian pos , val))
    aw-rev = trans (sym (swapBytes-involutive (applyWrite (swapBytes bytes) (pos , val))))
                   (cong swapBytes (swap-applyWrite-swap bytes pos val pos<64))

-- Layer 3: AllDiffPos structural conversions
-- Converts pointwise ∀∀ disjointness to structural AllDiffPos on writesOf lists.
private
  -- Inner: single write position differs from all positions in writesOf s₂ bits₂
  all-diff-writesOf : ∀ (p : ℕ) (v : Bool) {len₂} s₂ (bits₂ : BitVec len₂)
    → (∀ k₂ → k₂ < len₂ → p ≢ s₂ + k₂)
    → All (DiffPos (p , v)) (writesOf s₂ bits₂)
  all-diff-writesOf p v s₂ [] _ = []
  all-diff-writesOf p v s₂ (b₂ ∷ bits₂) disj =
    subst (p ≢_) (+-identityʳ s₂) (disj 0 (s≤s z≤n))
    ∷ all-diff-writesOf p v (suc s₂) bits₂
        (λ k₂ k₂< → subst (p ≢_) (+-suc s₂ k₂) (disj (suc k₂) (s≤s k₂<)))

  -- Outer: AllDiffPos between two plain writesOf lists
  writesOf-AllDiffPos : ∀ {len₁ len₂} s₁ (bits₁ : BitVec len₁) s₂ (bits₂ : BitVec len₂)
    → (∀ k₁ → k₁ < len₁ → ∀ k₂ → k₂ < len₂ → s₁ + k₁ ≢ s₂ + k₂)
    → AllDiffPos (writesOf s₁ bits₁) (writesOf s₂ bits₂)
  writesOf-AllDiffPos s₁ [] s₂ bits₂ _ = tt
  writesOf-AllDiffPos s₁ (b₁ ∷ bits₁) s₂ bits₂ disj =
    ( all-diff-writesOf s₁ b₁ s₂ bits₂
        (λ k₂ k₂< → subst (_≢ s₂ + k₂) (+-identityʳ s₁) (disj 0 (s≤s z≤n) k₂ k₂<))
    , writesOf-AllDiffPos (suc s₁) bits₁ s₂ bits₂
        (λ k₁ k₁< k₂ k₂< → subst (_≢ s₂ + k₂) (+-suc s₁ k₁) (disj (suc k₁) (s≤s k₁<) k₂ k₂<))
    )

  -- Inner: single write position differs from all physical positions
  all-diff-physWritesOf : ∀ (p : ℕ) (v : Bool) {len₂} s₂ (bits₂ : BitVec len₂)
    → (∀ k₂ → k₂ < len₂ → p ≢ physicalBitPos BigEndian (s₂ + k₂))
    → All (DiffPos (p , v)) (physicalWrites (writesOf s₂ bits₂))
  all-diff-physWritesOf p v s₂ [] _ = []
  all-diff-physWritesOf p v s₂ (b₂ ∷ bits₂) disj =
    subst (p ≢_) (cong (physicalBitPos BigEndian) (+-identityʳ s₂)) (disj 0 (s≤s z≤n))
    ∷ all-diff-physWritesOf p v (suc s₂) bits₂
        (λ k₂ k₂< → subst (p ≢_) (cong (physicalBitPos BigEndian) (+-suc s₂ k₂))
                       (disj (suc k₂) (s≤s k₂<)))

  -- Outer: AllDiffPos between plain writesOf and physicalWrites
  writesOf-AllDiffPos-phys : ∀ {len₁ len₂} s₁ (bits₁ : BitVec len₁) s₂ (bits₂ : BitVec len₂)
    → (∀ k₁ → k₁ < len₁ → ∀ k₂ → k₂ < len₂
       → s₁ + k₁ ≢ physicalBitPos BigEndian (s₂ + k₂))
    → AllDiffPos (writesOf s₁ bits₁) (physicalWrites (writesOf s₂ bits₂))
  writesOf-AllDiffPos-phys s₁ [] s₂ bits₂ _ = tt
  writesOf-AllDiffPos-phys s₁ (b₁ ∷ bits₁) s₂ bits₂ disj =
    ( all-diff-physWritesOf s₁ b₁ s₂ bits₂
        (λ k₂ k₂< → subst (_≢ physicalBitPos BigEndian (s₂ + k₂))
                       (+-identityʳ s₁) (disj 0 (s≤s z≤n) k₂ k₂<))
    , writesOf-AllDiffPos-phys (suc s₁) bits₁ s₂ bits₂
        (λ k₁ k₁< k₂ k₂< → subst (_≢ physicalBitPos BigEndian (s₂ + k₂))
                               (+-suc s₁ k₁) (disj (suc k₁) (s≤s k₁<) k₂ k₂<))
    )

-- Layer 4: Mixed byte-order commutativity
-- Two disjoint injectPayload calls commute regardless of byte order combination.
injectPayload-commute-mixed :
  ∀ {len₁ len₂} s₁ s₂ (bits₁ : BitVec len₁) (bits₂ : BitVec len₂) bo₁ bo₂ payload
  → (∀ k₁ → k₁ < len₁ → ∀ k₂ → k₂ < len₂
     → physicalBitPos bo₁ (s₁ + k₁) ≢ physicalBitPos bo₂ (s₂ + k₂))
  → s₁ + len₁ ≤ 64
  → s₂ + len₂ ≤ 64
  → injectPayload s₂ bits₂ bo₂ (injectPayload s₁ bits₁ bo₁ payload)
    ≡ injectPayload s₁ bits₁ bo₁ (injectPayload s₂ bits₂ bo₂ payload)
injectPayload-commute-mixed {len₁} {len₂} s₁ s₂ bits₁ bits₂ bo₁ bo₂ payload physDisj fits₁ fits₂ =
  go bo₁ bo₂ refl refl
  where
    open ≡-Reasoning
    ws₁ = writesOf s₁ bits₁
    ws₂ = writesOf s₂ bits₂
    bd₁ = writesOf-bounded s₁ bits₁ fits₁
    bd₂ = writesOf-bounded s₂ bits₂ fits₂

    go : (b₁ b₂ : ByteOrder) → b₁ ≡ bo₁ → b₂ ≡ bo₂
       → injectPayload s₂ bits₂ bo₂ (injectPayload s₁ bits₁ bo₁ payload)
         ≡ injectPayload s₁ bits₁ bo₁ (injectPayload s₂ bits₂ bo₂ payload)

    -- LE/LE: payloadIso = id on both sides; reduce to applyWrites-comm
    go LittleEndian LittleEndian refl refl =
      begin
        injectBits (injectBits payload s₁ bits₁) s₂ bits₂
      ≡⟨ cong (λ x → injectBits x s₂ bits₂) (injectBits≡applyWrites payload s₁ bits₁) ⟩
        injectBits (applyWrites payload ws₁) s₂ bits₂
      ≡⟨ injectBits≡applyWrites (applyWrites payload ws₁) s₂ bits₂ ⟩
        applyWrites (applyWrites payload ws₁) ws₂
      ≡⟨ applyWrites-comm payload ws₁ ws₂ (writesOf-distinct s₁ bits₁)
           (writesOf-AllDiffPos s₁ bits₁ s₂ bits₂ physDisj) ⟩
        applyWrites (applyWrites payload ws₂) ws₁
      ≡⟨ sym (injectBits≡applyWrites (applyWrites payload ws₂) s₁ bits₁) ⟩
        injectBits (applyWrites payload ws₂) s₁ bits₁
      ≡⟨ cong (λ x → injectBits x s₁ bits₁) (sym (injectBits≡applyWrites payload s₂ bits₂)) ⟩
        injectBits (injectBits payload s₂ bits₂) s₁ bits₁
      ∎

    -- BE/BE: payloadIso-involutive cancels; cong swapBytes of applyWrites-comm
    go BigEndian BigEndian refl refl =
      begin
        swapBytes (injectBits (payloadIso BigEndian (swapBytes (injectBits (swapBytes payload) s₁ bits₁))) s₂ bits₂)
      ≡⟨ cong (λ x → swapBytes (injectBits x s₂ bits₂))
              (payloadIso-involutive BigEndian (injectBits (swapBytes payload) s₁ bits₁)) ⟩
        swapBytes (injectBits (injectBits (swapBytes payload) s₁ bits₁) s₂ bits₂)
      ≡⟨ cong (λ x → swapBytes (injectBits x s₂ bits₂))
              (injectBits≡applyWrites (swapBytes payload) s₁ bits₁) ⟩
        swapBytes (injectBits (applyWrites (swapBytes payload) ws₁) s₂ bits₂)
      ≡⟨ cong swapBytes (injectBits≡applyWrites (applyWrites (swapBytes payload) ws₁) s₂ bits₂) ⟩
        swapBytes (applyWrites (applyWrites (swapBytes payload) ws₁) ws₂)
      ≡⟨ cong swapBytes (applyWrites-comm (swapBytes payload) ws₁ ws₂
           (writesOf-distinct s₁ bits₁)
           (writesOf-AllDiffPos s₁ bits₁ s₂ bits₂
             (λ k₁ k₁< k₂ k₂< eq → physDisj k₁ k₁< k₂ k₂< (cong (physicalBitPos BigEndian) eq)))) ⟩
        swapBytes (applyWrites (applyWrites (swapBytes payload) ws₂) ws₁)
      ≡⟨ cong swapBytes (sym (injectBits≡applyWrites (applyWrites (swapBytes payload) ws₂) s₁ bits₁)) ⟩
        swapBytes (injectBits (applyWrites (swapBytes payload) ws₂) s₁ bits₁)
      ≡⟨ cong (λ x → swapBytes (injectBits x s₁ bits₁))
              (sym (injectBits≡applyWrites (swapBytes payload) s₂ bits₂)) ⟩
        swapBytes (injectBits (injectBits (swapBytes payload) s₂ bits₂) s₁ bits₁)
      ≡⟨ cong (λ x → swapBytes (injectBits x s₁ bits₁))
              (sym (payloadIso-involutive BigEndian (injectBits (swapBytes payload) s₂ bits₂))) ⟩
        swapBytes (injectBits (payloadIso BigEndian (swapBytes (injectBits (swapBytes payload) s₂ bits₂))) s₁ bits₁)
      ∎

    -- LE/BE: swap-applyWrites-swap converts BE injection to physical writes
    go LittleEndian BigEndian refl refl =
      begin
        swapBytes (injectBits (swapBytes (injectBits payload s₁ bits₁)) s₂ bits₂)
      ≡⟨ cong (λ x → swapBytes (injectBits (swapBytes x) s₂ bits₂))
              (injectBits≡applyWrites payload s₁ bits₁) ⟩
        swapBytes (injectBits (swapBytes (applyWrites payload ws₁)) s₂ bits₂)
      ≡⟨ cong swapBytes (injectBits≡applyWrites (swapBytes (applyWrites payload ws₁)) s₂ bits₂) ⟩
        swapBytes (applyWrites (swapBytes (applyWrites payload ws₁)) ws₂)
      ≡⟨ swap-applyWrites-swap (applyWrites payload ws₁) ws₂ bd₂ ⟩
        applyWrites (applyWrites payload ws₁) (physicalWrites ws₂)
      ≡⟨ applyWrites-comm payload ws₁ (physicalWrites ws₂)
           (writesOf-distinct s₁ bits₁)
           (writesOf-AllDiffPos-phys s₁ bits₁ s₂ bits₂ physDisj) ⟩
        applyWrites (applyWrites payload (physicalWrites ws₂)) ws₁
      ≡⟨ sym (injectBits≡applyWrites (applyWrites payload (physicalWrites ws₂)) s₁ bits₁) ⟩
        injectBits (applyWrites payload (physicalWrites ws₂)) s₁ bits₁
      ≡⟨ cong (λ x → injectBits x s₁ bits₁)
              (sym (swap-applyWrites-swap payload ws₂ bd₂)) ⟩
        injectBits (swapBytes (applyWrites (swapBytes payload) ws₂)) s₁ bits₁
      ≡⟨ cong (λ x → injectBits (swapBytes x) s₁ bits₁)
              (sym (injectBits≡applyWrites (swapBytes payload) s₂ bits₂)) ⟩
        injectBits (swapBytes (injectBits (swapBytes payload) s₂ bits₂)) s₁ bits₁
      ∎

    -- BE/LE: sym of applyWrites-comm with swapped arguments
    go BigEndian LittleEndian refl refl =
      begin
        injectBits (swapBytes (injectBits (swapBytes payload) s₁ bits₁)) s₂ bits₂
      ≡⟨ cong (λ x → injectBits (swapBytes x) s₂ bits₂)
              (injectBits≡applyWrites (swapBytes payload) s₁ bits₁) ⟩
        injectBits (swapBytes (applyWrites (swapBytes payload) ws₁)) s₂ bits₂
      ≡⟨ cong (λ x → injectBits x s₂ bits₂)
              (swap-applyWrites-swap payload ws₁ bd₁) ⟩
        injectBits (applyWrites payload (physicalWrites ws₁)) s₂ bits₂
      ≡⟨ injectBits≡applyWrites (applyWrites payload (physicalWrites ws₁)) s₂ bits₂ ⟩
        applyWrites (applyWrites payload (physicalWrites ws₁)) ws₂
      ≡⟨ sym (applyWrites-comm payload ws₂ (physicalWrites ws₁)
           (writesOf-distinct s₂ bits₂)
           (writesOf-AllDiffPos-phys s₂ bits₂ s₁ bits₁
             (λ k₂ k₂< k₁ k₁< eq → physDisj k₁ k₁< k₂ k₂< (sym eq)))) ⟩
        applyWrites (applyWrites payload ws₂) (physicalWrites ws₁)
      ≡⟨ cong (λ x → applyWrites x (physicalWrites ws₁))
              (sym (injectBits≡applyWrites payload s₂ bits₂)) ⟩
        applyWrites (injectBits payload s₂ bits₂) (physicalWrites ws₁)
      ≡⟨ sym (swap-applyWrites-swap (injectBits payload s₂ bits₂) ws₁ bd₁) ⟩
        swapBytes (applyWrites (swapBytes (injectBits payload s₂ bits₂)) ws₁)
      ≡⟨ cong swapBytes (sym (injectBits≡applyWrites (swapBytes (injectBits payload s₂ bits₂)) s₁ bits₁)) ⟩
        swapBytes (injectBits (swapBytes (injectBits payload s₂ bits₂)) s₁ bits₁)
      ∎

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
