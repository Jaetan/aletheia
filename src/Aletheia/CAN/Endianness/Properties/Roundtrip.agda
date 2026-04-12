{-# OPTIONS --safe --without-K #-}

-- Byte/bitvec roundtrip proofs and extract-inject roundtrip.
--
-- Purpose: Core roundtrip properties for CAN endianness bit operations.
-- Exports: swapBytes-involutive, byte↔bitvec roundtrips,
--   extractBits-injectBits-roundtrip, injectBits-preserves-disjoint,
--   injectBits-preserves-earlier-bit, injectBits-preserves-later-bit.
module Aletheia.CAN.Endianness.Properties.Roundtrip where

open import Aletheia.CAN.Endianness using
  ( ByteOrder; LittleEndian; BigEndian
  ; lookupSafe; updateSafe
  ; byteToBitVec; bitVecToByte
  ; extractBits; injectBits
  ; swapBytes
  )
open import Aletheia.CAN.Frame using (Byte)
open import Aletheia.Data.BitVec using (BitVec; testBit; setBit; testBit-setBit-same; testBit-setBit-diff)
open import Aletheia.Data.BitVec.Conversion using (ℕToBitVec; bitVecToℕ; bitVec-roundtrip; bitVec-roundtrip-reverse; bitVecToℕ-bounded)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Vec.Properties using (reverse-involutive)
open import Data.Fin using (Fin; toℕ; fromℕ<) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.Nat as Nat using (ℕ; zero; suc; _+_; _*_; _<_; _≤_; _>_; _^_; z≤n; s≤s; _%_)
open import Data.Nat.DivMod using (m%n<n; m<n⇒m%n≡m; m≡m%n+[m/n]*n; m<n*o⇒m/o<n)
open import Data.Nat.Properties using (_≟_; <⇒≤; <⇒≢; +-suc; +-comm; ≤-refl; ≤-trans; n≤1+n; m≤m+n; m<n+m; m<m+n; <-≤-trans)
open import Data.Bool using (Bool)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; cong₂; _≢_)
open import Relation.Nullary using (yes; no)
open import Data.Empty using (⊥-elim)

-- ============================================================================
-- SWAPBYTES INVOLUTIVE
-- ============================================================================

swapBytes-involutive : ∀ {n} (bytes : Vec Byte n) → swapBytes (swapBytes bytes) ≡ bytes
swapBytes-involutive bytes = reverse-involutive bytes

-- ============================================================================
-- BYTE ↔ BITVEC ROUNDTRIP PROOFS
-- ============================================================================

byteToBitVec-roundtrip : ∀ (b : Byte) → bitVecToByte (byteToBitVec b) ≡ b Nat.% 256
byteToBitVec-roundtrip b = bitVec-roundtrip 8 (b Nat.% 256) (m%n<n b 256)

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

private
  lookupSafe-updateSafe-same : ∀ {n idx : ℕ} (f : Byte → Byte) (bytes : Vec Byte n)
    → idx < n
    → lookupSafe n idx (updateSafe n idx f bytes) ≡ f (lookupSafe n idx bytes)
  lookupSafe-updateSafe-same {zero} f [] ()
  lookupSafe-updateSafe-same {suc n} {zero} f (b ∷ bytes) (s≤s z≤n) = refl
  lookupSafe-updateSafe-same {suc n} {suc idx} f (b ∷ bytes) (s≤s prf) = lookupSafe-updateSafe-same f bytes prf

  lookupSafe-updateSafe-diff : ∀ (n idx₁ idx₂ : ℕ) (f : Byte → Byte) (bytes : Vec Byte n)
    → idx₁ ≢ idx₂
    → lookupSafe n idx₁ (updateSafe n idx₂ f bytes) ≡ lookupSafe n idx₁ bytes
  lookupSafe-updateSafe-diff zero idx₁ idx₂ f bytes neq = refl
  lookupSafe-updateSafe-diff (suc n) zero zero f (b ∷ bytes) neq = ⊥-elim (neq refl)
  lookupSafe-updateSafe-diff (suc n) zero (suc idx₂) f (b ∷ bytes) neq = refl
  lookupSafe-updateSafe-diff (suc n) (suc idx₁) zero f (b ∷ bytes) neq = refl
  lookupSafe-updateSafe-diff (suc n) (suc idx₁) (suc idx₂) f (b ∷ bytes) neq =
    lookupSafe-updateSafe-diff n idx₁ idx₂ f bytes (λ eq → neq (cong suc eq))

  readBit : ∀ {n} → Vec Byte n → ℕ → Fin 8 → Bool
  readBit {n} bytes idx pos = testBit (byteToBitVec (lookupSafe n idx bytes)) pos

  readBit-updateSafe-same : ∀ {n} (bytes : Vec Byte n) (idx : ℕ) (pos : Fin 8) (b : Bool)
    → idx < n
    → readBit (updateSafe n idx (λ byte → bitVecToByte (setBit (byteToBitVec byte) pos b)) bytes) idx pos ≡ b
  readBit-updateSafe-same bytes idx pos b idx<n =
    trans (cong (λ byte → testBit (byteToBitVec byte) pos)
                (lookupSafe-updateSafe-same (λ byte → bitVecToByte (setBit (byteToBitVec byte) pos b)) bytes idx<n))
      (trans (cong (λ bv → testBit bv pos) (bitVecToByte-roundtrip (setBit (byteToBitVec (lookupSafe _ idx bytes)) pos b)))
        (testBit-setBit-same (byteToBitVec (lookupSafe _ idx bytes)) pos b))

  readBit-updateSafe-diff : ∀ {n} (bytes : Vec Byte n) (idx : ℕ) (updatePos readPos : Fin 8) (b : Bool)
    → idx < n → updatePos ≢ readPos
    → readBit (updateSafe n idx (λ byte → bitVecToByte (setBit (byteToBitVec byte) updatePos b)) bytes) idx readPos
      ≡ readBit bytes idx readPos
  readBit-updateSafe-diff bytes idx updatePos readPos b idx<n pos≢ =
    trans (cong (λ byte → testBit (byteToBitVec byte) readPos)
                (lookupSafe-updateSafe-same (λ byte → bitVecToByte (setBit (byteToBitVec byte) updatePos b)) bytes idx<n))
      (trans (cong (λ bv → testBit bv readPos) (bitVecToByte-roundtrip (setBit (byteToBitVec (lookupSafe _ idx bytes)) updatePos b)))
        (testBit-setBit-diff (byteToBitVec (lookupSafe _ idx bytes)) updatePos readPos b pos≢))

-- Injection preserves bits BEFORE the injection range.
injectBits-preserves-earlier-bit :
  ∀ {length} {n} (bytes : Vec Byte n) (earlierPos laterPos : ℕ) (bits : BitVec length)
  → laterPos > earlierPos
  → laterPos + length ≤ n * 8
  → let earlierByteIdx = earlierPos Nat./ 8
        earlierBitPos = fromℕ< (m%n<n earlierPos 8)
    in testBit (byteToBitVec (lookupSafe n earlierByteIdx (injectBits bytes laterPos bits))) earlierBitPos
     ≡ testBit (byteToBitVec (lookupSafe n earlierByteIdx bytes)) earlierBitPos
injectBits-preserves-earlier-bit bytes earlierPos laterPos [] later>earlier frameBound = refl
injectBits-preserves-earlier-bit {suc len} {n} bytes earlierPos laterPos (b ∷ bs) later>earlier frameBound =
  trans recursive-preservation first-step-preservation
  where
    earlierByteIdx = earlierPos Nat./ 8
    earlierBitPos = fromℕ< (m%n<n earlierPos 8)
    laterByteIdx = laterPos Nat./ 8
    laterBitPos = fromℕ< (m%n<n laterPos 8)
    updatedBytes = updateSafe n laterByteIdx (λ byte → bitVecToByte (setBit (byteToBitVec byte) laterBitPos b)) bytes

    recursive-preservation : testBit (byteToBitVec (lookupSafe n earlierByteIdx (injectBits updatedBytes (suc laterPos) bs))) earlierBitPos
                           ≡ testBit (byteToBitVec (lookupSafe n earlierByteIdx updatedBytes)) earlierBitPos
    recursive-preservation = injectBits-preserves-earlier-bit updatedBytes earlierPos (suc laterPos) bs (s≤s (<⇒≤ later>earlier)) restFrameBound
      where
        restFrameBound : suc laterPos + len ≤ n * 8
        restFrameBound = subst (_≤ n * 8) (+-suc laterPos len) frameBound

    first-step-preservation : testBit (byteToBitVec (lookupSafe n earlierByteIdx updatedBytes)) earlierBitPos
                            ≡ testBit (byteToBitVec (lookupSafe n earlierByteIdx bytes)) earlierBitPos
    first-step-preservation with earlierByteIdx ≟ laterByteIdx
    ... | yes byteIdx-eq =
      subst (λ idx → testBit (byteToBitVec (lookupSafe n idx updatedBytes)) earlierBitPos
                    ≡ testBit (byteToBitVec (lookupSafe n idx bytes)) earlierBitPos)
            (sym byteIdx-eq)
            (readBit-updateSafe-diff bytes laterByteIdx laterBitPos earlierBitPos b laterByteIdx<n laterBitPos≢earlierBitPos)
      where
        laterByteIdx<n : laterByteIdx < n
        laterByteIdx<n = m<n*o⇒m/o<n {laterPos} {n} {8} laterPos<n*8
          where
            laterPos<n*8 : laterPos < n * 8
            laterPos<n*8 = <-≤-trans (subst (laterPos <_) (+-comm (suc len) laterPos) (m<n+m laterPos (s≤s z≤n))) frameBound

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
    ... | no neq = cong (λ x → testBit (byteToBitVec x) earlierBitPos) (lookupSafe-updateSafe-diff n earlierByteIdx laterByteIdx _ bytes neq)

-- Injection preserves bits AFTER the injection range.
injectBits-preserves-later-bit :
  ∀ {length} {n} (bytes : Vec Byte n) (earlierPos laterPos : ℕ) (bits : BitVec length)
  → earlierPos + length ≤ laterPos
  → laterPos < n * 8
  → let laterByteIdx = laterPos Nat./ 8
        laterBitPos = fromℕ< (m%n<n laterPos 8)
    in testBit (byteToBitVec (lookupSafe n laterByteIdx (injectBits bytes earlierPos bits))) laterBitPos
     ≡ testBit (byteToBitVec (lookupSafe n laterByteIdx bytes)) laterBitPos
injectBits-preserves-later-bit bytes earlierPos laterPos [] disjoint laterPos<n*8 = refl
injectBits-preserves-later-bit {suc len} {n} bytes earlierPos laterPos (b ∷ bs) disjoint laterPos<n*8 =
  trans recursive-preservation first-step-preservation
  where
    earlierByteIdx = earlierPos Nat./ 8
    earlierBitPos = fromℕ< (m%n<n earlierPos 8)
    laterByteIdx = laterPos Nat./ 8
    laterBitPos = fromℕ< (m%n<n laterPos 8)
    updatedBytes = updateSafe n earlierByteIdx (λ byte → bitVecToByte (setBit (byteToBitVec byte) earlierBitPos b)) bytes

    rest-disjoint : suc earlierPos + len ≤ laterPos
    rest-disjoint = subst (_≤ laterPos) (+-suc earlierPos len) disjoint

    recursive-preservation : testBit (byteToBitVec (lookupSafe n laterByteIdx (injectBits updatedBytes (suc earlierPos) bs))) laterBitPos
                           ≡ testBit (byteToBitVec (lookupSafe n laterByteIdx updatedBytes)) laterBitPos
    recursive-preservation = injectBits-preserves-later-bit updatedBytes (suc earlierPos) laterPos bs rest-disjoint laterPos<n*8

    first-step-preservation : testBit (byteToBitVec (lookupSafe n laterByteIdx updatedBytes)) laterBitPos
                            ≡ testBit (byteToBitVec (lookupSafe n laterByteIdx bytes)) laterBitPos
    first-step-preservation with laterByteIdx ≟ earlierByteIdx
    ... | yes byteIdx-eq =
      trans (cong (λ idx → readBit updatedBytes idx laterBitPos) byteIdx-eq)
        (trans (readBit-updateSafe-diff bytes earlierByteIdx earlierBitPos laterBitPos b earlierByteIdx<n earlierBitPos≢laterBitPos)
          (cong (λ idx → readBit bytes idx laterBitPos) (sym byteIdx-eq)))
      where
        earlierPos<laterPos : earlierPos < laterPos
        earlierPos<laterPos = ≤-trans (m≤m+n (suc earlierPos) len) (subst (_≤ laterPos) (+-suc earlierPos len) disjoint)

        earlierByteIdx<n : earlierByteIdx < n
        earlierByteIdx<n = m<n*o⇒m/o<n {earlierPos} {n} {8} (<-≤-trans earlierPos<laterPos (<⇒≤ laterPos<n*8))

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
    ... | no neq = cong (λ x → testBit (byteToBitVec x) laterBitPos) (lookupSafe-updateSafe-diff n laterByteIdx earlierByteIdx _ bytes neq)

injectBits-preserves-disjoint :
  ∀ {len₁ len₂} {n} (bytes : Vec Byte n) (start₁ start₂ : ℕ) (bits : BitVec len₁)
  → start₁ + len₁ ≤ start₂ ⊎ start₂ + len₂ ≤ start₁
  → start₁ + len₁ ≤ n * 8
  → start₂ + len₂ ≤ n * 8
  → extractBits {len₂} (injectBits bytes start₁ bits) start₂ ≡ extractBits {len₂} bytes start₂
injectBits-preserves-disjoint {len₁} {zero} bytes start₁ start₂ bits disj bound₁ bound₂ = refl
injectBits-preserves-disjoint {len₁} {suc len₂} {n} bytes start₁ start₂ bits (inj₁ inj-before-ext) bound₁ bound₂ =
  cong₂ _∷_ first-bit rest-bits
  where
    start₂<n*8 = <-≤-trans (m<m+n start₂ {suc len₂} (s≤s z≤n)) bound₂
    first-bit = injectBits-preserves-later-bit bytes start₁ start₂ bits inj-before-ext start₂<n*8
    rest-bound₂ = subst (_≤ n * 8) (+-suc start₂ len₂) bound₂
    rest-disj = inj₁ (≤-trans inj-before-ext (n≤1+n start₂))
    rest-bits = injectBits-preserves-disjoint bytes start₁ (suc start₂) bits rest-disj bound₁ rest-bound₂
injectBits-preserves-disjoint {len₁} {suc len₂} {n} bytes start₁ start₂ bits (inj₂ ext-before-inj) bound₁ bound₂ =
  cong₂ _∷_ first-bit rest-bits
  where
    start₂<n*8 = <-≤-trans (m<m+n start₂ {suc len₂} (s≤s z≤n)) bound₂
    start₂<start₁ : start₂ < start₁
    start₂<start₁ = <-≤-trans (m<m+n start₂ {suc len₂} (s≤s z≤n)) ext-before-inj
    first-bit = injectBits-preserves-earlier-bit bytes start₂ start₁ bits start₂<start₁ bound₁
    rest-bound₂ = subst (_≤ n * 8) (+-suc start₂ len₂) bound₂
    rest-disj = inj₂ (subst (_≤ start₁) (+-suc start₂ len₂) ext-before-inj)
    rest-bits = injectBits-preserves-disjoint bytes start₁ (suc start₂) bits rest-disj bound₁ rest-bound₂

extractBits-injectBits-roundtrip :
  ∀ {length} {n} →
  (bytes : Vec Byte n) →
  ∀ startBit →
  (bits : BitVec length) →
  startBit + length ≤ n * 8 →
  extractBits (injectBits bytes startBit bits) startBit ≡ bits
extractBits-injectBits-roundtrip bytes startBit [] bound = refl
extractBits-injectBits-roundtrip {suc len} {n} bytes startBit (b ∷ bs) bound =
  cong₂ _∷_ first-bit rest-bits
  where
    byteIdx = startBit Nat./ 8
    bitPos = fromℕ< (m%n<n startBit 8)
    updateByteFn = λ byte → bitVecToByte (setBit (byteToBitVec byte) bitPos b)
    updatedBytes = updateSafe n byteIdx updateByteFn bytes
    rest-bound : suc startBit + len ≤ n * 8
    rest-bound = subst (_≤ n * 8) (+-suc startBit len) bound

    first-bit : testBit (byteToBitVec (lookupSafe n byteIdx (injectBits bytes startBit (b ∷ bs)))) bitPos ≡ b
    first-bit =
      trans (injectBits-preserves-earlier-bit updatedBytes startBit (suc startBit) bs (s≤s ≤-refl) rest-bound)
        (readBit-updateSafe-same bytes byteIdx bitPos b byteIdx<n)
      where
        byteIdx<n : byteIdx < n
        byteIdx<n = m<n*o⇒m/o<n {startBit} {n} {8} startBit<n*8
          where
            startBit<n*8 : startBit < n * 8
            startBit<n*8 = <-≤-trans (subst (startBit <_) (+-comm (suc len) startBit) (m<n+m startBit (s≤s z≤n))) bound

    rest-bits : extractBits (injectBits bytes startBit (b ∷ bs)) (suc startBit) ≡ bs
    rest-bits = extractBits-injectBits-roundtrip updatedBytes (suc startBit) bs rest-bound
