{-# OPTIONS --safe --without-K #-}

-- Correctness properties for CAN endianness operations.
--
-- Purpose: Collect all proof lemmas about ByteOrder, extractBits, injectBits,
-- swapBytes, payloadIso, physicalBitPos, and startBit conversion functions.
-- These are separated from Endianness.agda (which holds the definitions) to
-- keep the definition module focused on runtime-relevant code.
module Aletheia.CAN.Endianness.Properties where

open import Aletheia.CAN.Endianness using
  ( ByteOrder; LittleEndian; BigEndian
  ; lookupSafe; updateSafe
  ; byteToBitVec; bitVecToByte
  ; extractBits; injectBits
  ; swapBytes
  ; payloadIso; injectPayload
  ; physicalBitPos
  ; convertStartBit; unconvertStartBit
  )
open import Aletheia.CAN.Frame using (Byte)
open import Aletheia.Data.BitVec using (BitVec; testBit; setBit; testBit-setBit-same; testBit-setBit-diff; setBit-setBit-comm)
open import Aletheia.Data.BitVec.Conversion using (ℕToBitVec; bitVecToℕ; bitVec-roundtrip; bitVec-roundtrip-reverse; bitVecToℕ-bounded)
open import Data.Vec using (Vec; []; _∷_; _∷ʳ_; reverse)
open import Data.Vec.Properties using (reverse-involutive; reverse-∷)
open import Data.Fin using (Fin; toℕ; fromℕ<) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (toℕ-fromℕ<; toℕ-injective)
open import Data.Nat as Nat using (ℕ; zero; suc; _+_; _∸_; _*_; _<_; _≤_; _>_; _^_; z≤n; s≤s; _/_; _%_)
open import Data.Nat.DivMod using (m%n<n; m<n⇒m%n≡m; m≡m%n+[m/n]*n; m<n*o⇒m/o<n; [m+n]%n≡m%n)
open import Data.Nat.Properties using (_≟_; _≤?_; _<?_; <⇒≤; <⇒≢; +-suc; +-comm; +-assoc; +-identityʳ; ≤-refl; ≤-trans; ≤-<-trans; ≤-antisym; ≮⇒≥; n≤1+n; m≤m+n; m<n+m; m<m+n; <-≤-trans; m+n≤o⇒n≤o; m≤n⇒m≤1+n; +-cancelʳ-≡; *-cancelʳ-≡; +-monoˡ-≤; +-monoʳ-<; *-monoˡ-≤; m∸n≤m; n∸n≡0)
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

-- ============================================================================
-- PRIVATE HELPERS
-- ============================================================================

private
  m∸n≡suc[m∸1+n] : ∀ {m n} → n < m → m ∸ n ≡ suc (m ∸ suc n)
  m∸n≡suc[m∸1+n] {suc _} {zero} _ = refl
  m∸n≡suc[m∸1+n] {suc _} {suc _} (s≤s p) = m∸n≡suc[m∸1+n] p

  m∸1∸i≡m∸suci : ∀ {m i} → i < m → (m ∸ 1) ∸ i ≡ m ∸ suc i
  m∸1∸i≡m∸suci {suc _} _ = refl

  lookupSafe-∷ʳ : ∀ {n} i → i < n → (v : Vec Byte n) (x : Byte) →
    lookupSafe (suc n) i (v ∷ʳ x) ≡ lookupSafe n i v
  lookupSafe-∷ʳ {suc _} zero _ (b ∷ bs) x = refl
  lookupSafe-∷ʳ {suc _} (suc i) (s≤s p) (b ∷ bs) x = lookupSafe-∷ʳ i p bs x

  lookupSafe-∷ʳ-last : ∀ {n} (v : Vec Byte n) (x : Byte) →
    lookupSafe (suc n) n (v ∷ʳ x) ≡ x
  lookupSafe-∷ʳ-last [] x = refl
  lookupSafe-∷ʳ-last (b ∷ bs) x = lookupSafe-∷ʳ-last bs x

  updateSafe-∷ʳ : ∀ {n} i → i < n → (f : Byte → Byte) (v : Vec Byte n) (x : Byte) →
    updateSafe (suc n) i f (v ∷ʳ x) ≡ updateSafe n i f v ∷ʳ x
  updateSafe-∷ʳ {suc _} zero _ f (b ∷ bs) x = refl
  updateSafe-∷ʳ {suc _} (suc i) (s≤s p) f (b ∷ bs) x = cong (b ∷_) (updateSafe-∷ʳ i p f bs x)

  updateSafe-∷ʳ-last : ∀ {n} (f : Byte → Byte) (v : Vec Byte n) (x : Byte) →
    updateSafe (suc n) n f (v ∷ʳ x) ≡ v ∷ʳ f x
  updateSafe-∷ʳ-last f [] x = refl
  updateSafe-∷ʳ-last f (b ∷ bs) x = cong (b ∷_) (updateSafe-∷ʳ-last f bs x)

  reverse-∷ʳ : ∀ {n} (xs : Vec Byte n) (x : Byte) →
    reverse (xs ∷ʳ x) ≡ x ∷ reverse xs
  reverse-∷ʳ xs x =
    trans (cong (λ ys → reverse (ys ∷ʳ x)) (sym (reverse-involutive xs)))
      (trans (cong reverse (sym (reverse-∷ x (reverse xs))))
        (reverse-involutive (x ∷ reverse xs)))

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

  -- Read the bit at (byteIdx, bitPos) in a byte vector
  readBit : ∀ {n} → Vec Byte n → ℕ → Fin 8 → Bool
  readBit {n} bytes idx pos = testBit (byteToBitVec (lookupSafe n idx bytes)) pos

  -- After updateSafe with setBit at the SAME bit position, readBit returns the written value
  readBit-updateSafe-same : ∀ {n} (bytes : Vec Byte n) (idx : ℕ) (pos : Fin 8) (b : Bool)
    → idx < n
    → readBit (updateSafe n idx (λ byte → bitVecToByte (setBit (byteToBitVec byte) pos b)) bytes) idx pos ≡ b
  readBit-updateSafe-same bytes idx pos b idx<n =
    trans (cong (λ byte → testBit (byteToBitVec byte) pos)
                (lookupSafe-updateSafe-same (λ byte → bitVecToByte (setBit (byteToBitVec byte) pos b)) bytes idx<n))
      (trans (cong (λ bv → testBit bv pos) (bitVecToByte-roundtrip (setBit (byteToBitVec (lookupSafe _ idx bytes)) pos b)))
        (testBit-setBit-same (byteToBitVec (lookupSafe _ idx bytes)) pos b))

  -- After updateSafe with setBit at a DIFFERENT bit position, readBit is unchanged
  readBit-updateSafe-diff : ∀ {n} (bytes : Vec Byte n) (idx : ℕ) (updatePos readPos : Fin 8) (b : Bool)
    → idx < n → updatePos ≢ readPos
    → readBit (updateSafe n idx (λ byte → bitVecToByte (setBit (byteToBitVec byte) updatePos b)) bytes) idx readPos
      ≡ readBit bytes idx readPos
  readBit-updateSafe-diff bytes idx updatePos readPos b idx<n pos≢ =
    trans (cong (λ byte → testBit (byteToBitVec byte) readPos)
                (lookupSafe-updateSafe-same (λ byte → bitVecToByte (setBit (byteToBitVec byte) updatePos b)) bytes idx<n))
      (trans (cong (λ bv → testBit bv readPos) (bitVecToByte-roundtrip (setBit (byteToBitVec (lookupSafe _ idx bytes)) updatePos b)))
        (testBit-setBit-diff (byteToBitVec (lookupSafe _ idx bytes)) updatePos readPos b pos≢))

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
      earlierByteIdx : ℕ
      earlierByteIdx = earlierPos Nat./ 8

      earlierBitPos : Fin 8
      earlierBitPos = fromℕ< (m%n<n earlierPos 8)

      laterByteIdx : ℕ
      laterByteIdx = laterPos Nat./ 8

      laterBitPos : Fin 8
      laterBitPos = fromℕ< (m%n<n laterPos 8)

      updatedBytes : Vec Byte n
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
      earlierByteIdx : ℕ
      earlierByteIdx = earlierPos Nat./ 8

      earlierBitPos : Fin 8
      earlierBitPos = fromℕ< (m%n<n earlierPos 8)

      laterByteIdx : ℕ
      laterByteIdx = laterPos Nat./ 8

      laterBitPos : Fin 8
      laterBitPos = fromℕ< (m%n<n laterPos 8)

      updatedBytes : Vec Byte n
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
    byteIdx : ℕ
    byteIdx = startBit Nat./ 8

    bitPos : Fin 8
    bitPos = fromℕ< (m%n<n startBit 8)

    updateByteFn : Byte → Byte
    updateByteFn byte = bitVecToByte (setBit (byteToBitVec byte) bitPos b)

    updatedBytes : Vec Byte n
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

-- ============================================================================
-- COMMUTATIVITY: Disjoint injections commute
-- ============================================================================

private
  BitWrite : Set
  BitWrite = ℕ × Bool

  applyWrite : ∀ {n} → Vec Byte n → BitWrite → Vec Byte n
  applyWrite {n} bytes (pos , val) = updateSafe n byteIdx updateFn bytes
    where
      byteIdx = pos Nat./ 8
      bitPos = fromℕ< (m%n<n pos 8)
      updateFn = λ byte → bitVecToByte (setBit (byteToBitVec byte) bitPos val)

  applyWrites : ∀ {n} → Vec Byte n → List BitWrite → Vec Byte n
  applyWrites bytes [] = bytes
  applyWrites bytes (w ∷ ws) = applyWrites (applyWrite bytes w) ws

  writesOf : ∀ {len} → ℕ → BitVec len → List BitWrite
  writesOf s [] = []
  writesOf s (b ∷ bs) = (s , b) ∷ writesOf (suc s) bs

  DiffPos : BitWrite → BitWrite → Set
  DiffPos (p₁ , _) (p₂ , _) = p₁ ≢ p₂

  AllDiffPos : List BitWrite → List BitWrite → Set
  AllDiffPos [] _ = ⊤
  AllDiffPos (w ∷ ws) ws₂ = All (DiffPos w) ws₂ × AllDiffPos ws ws₂

  AllDistinct : List BitWrite → Set
  AllDistinct [] = ⊤
  AllDistinct (w ∷ ws) = All (DiffPos w) ws × AllDistinct ws

-- ============================================================================
-- WRITE-SET LEMMAS
-- ============================================================================

private
  applyWrite-comm : ∀ {n} (bytes : Vec Byte n) w₁ w₂ → DiffPos w₁ w₂
    → applyWrite (applyWrite bytes w₂) w₁ ≡ applyWrite (applyWrite bytes w₁) w₂
  applyWrite-comm {n} bytes (p₁ , v₁) (p₂ , v₂) p₁≢p₂ = case-split
    where
      idx₁ = p₁ Nat./ 8
      idx₂ = p₂ Nat./ 8
      bitPos₁ = fromℕ< (m%n<n p₁ 8)
      bitPos₂ = fromℕ< (m%n<n p₂ 8)
      f₁ = λ byte → bitVecToByte (setBit (byteToBitVec byte) bitPos₁ v₁)
      f₂ = λ byte → bitVecToByte (setBit (byteToBitVec byte) bitPos₂ v₂)

      diff-byte : idx₁ ≢ idx₂ → applyWrite (applyWrite bytes (p₂ , v₂)) (p₁ , v₁)
                              ≡ applyWrite (applyWrite bytes (p₁ , v₁)) (p₂ , v₂)
      diff-byte neq = updateSafe-comm-diff-lemma idx₁ idx₂ f₁ f₂ bytes neq
        where
          updateSafe-comm-diff-lemma : ∀ {m} (i₁ i₂ : ℕ) (g₁ g₂ : Byte → Byte) (bs : Vec Byte m)
            → i₁ ≢ i₂
            → updateSafe m i₁ g₁ (updateSafe m i₂ g₂ bs) ≡ updateSafe m i₂ g₂ (updateSafe m i₁ g₁ bs)
          updateSafe-comm-diff-lemma {zero} _ _ _ _ [] _ = refl
          updateSafe-comm-diff-lemma {suc m} zero zero _ _ _ neq = ⊥-elim (neq refl)
          updateSafe-comm-diff-lemma {suc m} zero (suc _) _ _ (b ∷ bs) _ = refl
          updateSafe-comm-diff-lemma {suc m} (suc _) zero _ _ (b ∷ bs) _ = refl
          updateSafe-comm-diff-lemma {suc m} (suc i₁) (suc i₂) g₁ g₂ (x ∷ xs) neq =
            cong (x ∷_) (updateSafe-comm-diff-lemma i₁ i₂ g₁ g₂ xs (λ eq → neq (cong suc eq)))

      same-byte : idx₁ ≡ idx₂ → applyWrite (applyWrite bytes (p₂ , v₂)) (p₁ , v₁)
                              ≡ applyWrite (applyWrite bytes (p₁ , v₁)) (p₂ , v₂)
      same-byte idx-eq = updateSafe-same-compose idx-eq bitPos₁≢bitPos₂
        where
          bitPos₁≢bitPos₂ : bitPos₁ ≢ bitPos₂
          bitPos₁≢bitPos₂ eq = p₁≢p₂ (trans (m≡m%n+[m/n]*n p₁ 8)
            (trans (cong₂ _+_ (trans (sym (toℕ-fromℕ< (m%n<n p₁ 8)))
                               (trans (cong toℕ eq) (toℕ-fromℕ< (m%n<n p₂ 8))))
                             (cong (_* 8) idx-eq))
              (sym (m≡m%n+[m/n]*n p₂ 8))))

          updateSafe-same-compose : idx₁ ≡ idx₂ → bitPos₁ ≢ bitPos₂
            → updateSafe n idx₁ f₁ (updateSafe n idx₂ f₂ bytes)
            ≡ updateSafe n idx₂ f₂ (updateSafe n idx₁ f₁ bytes)
          updateSafe-same-compose idx-eq bp-neq =
            subst₂ (λ i j → updateSafe n i f₁ (updateSafe n j f₂ bytes) ≡ updateSafe n j f₂ (updateSafe n i f₁ bytes))
                   (sym idx-eq) refl same-idx-proof
            where
              updateSafe-same-lemma : ∀ {m} (i : ℕ) (h₁ h₂ : Byte → Byte) (xs : Vec Byte m)
                → updateSafe m i h₁ (updateSafe m i h₂ xs) ≡ updateSafe m i (h₁ ∘ h₂) xs
              updateSafe-same-lemma {zero} _ _ _ [] = refl
              updateSafe-same-lemma {suc _} zero _ _ (x ∷ xs) = refl
              updateSafe-same-lemma {suc m} (suc i) h₁ h₂ (x ∷ xs) =
                cong (x ∷_) (updateSafe-same-lemma i h₁ h₂ xs)

              updateSafe-cong-fn-lemma : ∀ {m} (i : ℕ) (h₁ h₂ : Byte → Byte) (xs : Vec Byte m)
                → (∀ b → h₁ b ≡ h₂ b) → updateSafe m i h₁ xs ≡ updateSafe m i h₂ xs
              updateSafe-cong-fn-lemma {zero} _ _ _ [] _ = refl
              updateSafe-cong-fn-lemma {suc _} zero h₁ h₂ (x ∷ xs) eq = cong (_∷ xs) (eq x)
              updateSafe-cong-fn-lemma {suc m} (suc i) h₁ h₂ (x ∷ xs) eq =
                cong (x ∷_) (updateSafe-cong-fn-lemma i h₁ h₂ xs eq)

              fns-commute : ∀ b → (f₁ ∘ f₂) b ≡ (f₂ ∘ f₁) b
              fns-commute b =
                trans (cong (λ bv → bitVecToByte (setBit bv bitPos₁ v₁))
                            (bitVecToByte-roundtrip (setBit (byteToBitVec b) bitPos₂ v₂)))
                  (trans (cong bitVecToByte (setBit-setBit-comm (byteToBitVec b) bitPos₂ bitPos₁ v₂ v₁ (bp-neq ∘ sym)))
                    (sym (cong (λ bv → bitVecToByte (setBit bv bitPos₂ v₂))
                               (bitVecToByte-roundtrip (setBit (byteToBitVec b) bitPos₁ v₁)))))

              same-idx-proof : updateSafe n idx₂ f₁ (updateSafe n idx₂ f₂ bytes)
                             ≡ updateSafe n idx₂ f₂ (updateSafe n idx₂ f₁ bytes)
              same-idx-proof = trans (updateSafe-same-lemma idx₂ f₁ f₂ bytes)
                (trans (updateSafe-cong-fn-lemma idx₂ (f₁ ∘ f₂) (f₂ ∘ f₁) bytes fns-commute)
                  (sym (updateSafe-same-lemma idx₂ f₂ f₁ bytes)))

      case-split : applyWrite (applyWrite bytes (p₂ , v₂)) (p₁ , v₁)
                 ≡ applyWrite (applyWrite bytes (p₁ , v₁)) (p₂ , v₂)
      case-split with idx₁ ≟ idx₂
      ... | yes eq = same-byte eq
      ... | no neq = diff-byte neq

applyWrites-push : ∀ {n} (bytes : Vec Byte n) w ws
  → All (DiffPos w) ws
  → applyWrites (applyWrite bytes w) ws ≡ applyWrite (applyWrites bytes ws) w
applyWrites-push bytes w [] [] = refl
applyWrites-push bytes w (w' ∷ ws) (diff ∷ diffs) =
  trans (cong (λ frame → applyWrites frame ws) (sym (applyWrite-comm bytes w w' diff)))
    (applyWrites-push (applyWrite bytes w') w ws diffs)

applyWrites-comm : ∀ {n} (bytes : Vec Byte n) ws₁ ws₂
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

injectBits≡applyWrites : ∀ {len} {n} (bytes : Vec Byte n) s (bits : BitVec len)
  → injectBits bytes s bits ≡ applyWrites bytes (writesOf s bits)
injectBits≡applyWrites bytes s [] = refl
injectBits≡applyWrites bytes s (b ∷ bs) = injectBits≡applyWrites (applyWrite bytes (s , b)) (suc s) bs

writesOf-distinct : ∀ {len} s (bits : BitVec len) → AllDistinct (writesOf s bits)
writesOf-distinct s [] = tt
writesOf-distinct s (b ∷ bs) = (all-later-diff s (suc s) bs ≤-refl , writesOf-distinct (suc s) bs)
  where
    all-later-diff : ∀ {len} pos start (bits : BitVec len)
      → pos < start
      → All (DiffPos (pos , b)) (writesOf start bits)
    all-later-diff pos start [] _ = []
    all-later-diff {suc len} pos start (b' ∷ bs') pos<start =
      (<⇒≢ pos<start) ∷ all-later-diff pos (suc start) bs' (m≤n⇒m≤1+n pos<start)

disjoint-ranges→AllDiffPos : ∀ {len₁ len₂} s₁ s₂ (bits₁ : BitVec len₁) (bits₂ : BitVec len₂)
  → s₁ + len₁ ≤ s₂ ⊎ s₂ + len₂ ≤ s₁
  → AllDiffPos (writesOf s₁ bits₁) (writesOf s₂ bits₂)
disjoint-ranges→AllDiffPos s₁ s₂ [] bits₂ disj = tt
disjoint-ranges→AllDiffPos {suc len₁} s₁ s₂ (b₁ ∷ bs₁) bits₂ disj = (all-diff , rest)
  where
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
-- MAIN COMMUTATIVITY THEOREM
-- ============================================================================

injectBits-commute :
  ∀ {len₁ len₂} {n} (bytes : Vec Byte n) (s₁ s₂ : ℕ)
    (bits₁ : BitVec len₁) (bits₂ : BitVec len₂)
  → s₁ + len₁ ≤ s₂ ⊎ s₂ + len₂ ≤ s₁
  → s₁ + len₁ ≤ n * 8
  → s₂ + len₂ ≤ n * 8
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
-- PAYLOADISO INVOLUTIVE
-- ============================================================================

payloadIso-involutive : ∀ {n} bo (bytes : Vec Byte n) → payloadIso bo (payloadIso bo bytes) ≡ bytes
payloadIso-involutive LittleEndian bytes = refl
payloadIso-involutive BigEndian bytes = swapBytes-involutive bytes

-- ============================================================================
-- INJECTPAYLOAD COMMUTATIVITY
-- ============================================================================

injectPayload-commute :
  ∀ {len₁ len₂} {n} s₁ s₂ (bits₁ : BitVec len₁) (bits₂ : BitVec len₂) bo (payload : Vec Byte n)
  → s₁ + len₁ ≤ s₂ ⊎ s₂ + len₂ ≤ s₁
  → s₁ + len₁ ≤ n * 8
  → s₂ + len₂ ≤ n * 8
  → injectPayload s₂ bits₂ bo (injectPayload s₁ bits₁ bo payload)
    ≡ injectPayload s₁ bits₁ bo (injectPayload s₂ bits₂ bo payload)
injectPayload-commute s₁ s₂ bits₁ bits₂ bo payload disj fits₁ fits₂ =
  begin
    injectPayload s₂ bits₂ bo (injectPayload s₁ bits₁ bo payload)
  ≡⟨⟩
    payloadIso bo (injectBits (payloadIso bo (payloadIso bo (injectBits (payloadIso bo payload) s₁ bits₁))) s₂ bits₂)
  ≡⟨ cong (λ x → payloadIso bo (injectBits x s₂ bits₂)) (payloadIso-involutive bo _) ⟩
    payloadIso bo (injectBits (injectBits (payloadIso bo payload) s₁ bits₁) s₂ bits₂)
  ≡⟨ cong (payloadIso bo) (injectBits-commute (payloadIso bo payload) s₁ s₂ bits₁ bits₂ disj fits₁ fits₂) ⟩
    payloadIso bo (injectBits (injectBits (payloadIso bo payload) s₂ bits₂) s₁ bits₁)
  ≡⟨ cong (λ x → payloadIso bo (injectBits x s₁ bits₁)) (sym (payloadIso-involutive bo _)) ⟩
    payloadIso bo (injectBits (payloadIso bo (payloadIso bo (injectBits (payloadIso bo payload) s₂ bits₂))) s₁ bits₁)
  ≡⟨⟩
    injectPayload s₁ bits₁ bo (injectPayload s₂ bits₂ bo payload)
  ∎
  where
    open ≡-Reasoning

injectPayload-preserves-disjoint-same :
  ∀ {len₁ len₂} {n} s₁ s₂ (bits : BitVec len₁) bo (payload : Vec Byte n)
  → s₁ + len₁ ≤ s₂ ⊎ s₂ + len₂ ≤ s₁
  → s₁ + len₁ ≤ n * 8
  → s₂ + len₂ ≤ n * 8
  → extractBits {len₂} (payloadIso bo (injectPayload s₁ bits bo payload)) s₂
    ≡ extractBits {len₂} (payloadIso bo payload) s₂
injectPayload-preserves-disjoint-same {len₁} {len₂} s₁ s₂ bits bo payload disj fits₁ fits₂ =
  begin
    extractBits {len₂} (payloadIso bo (injectPayload s₁ bits bo payload)) s₂
  ≡⟨⟩
    extractBits {len₂} (payloadIso bo (payloadIso bo (injectBits (payloadIso bo payload) s₁ bits))) s₂
  ≡⟨ cong (λ x → extractBits {len₂} x s₂) (payloadIso-involutive bo _) ⟩
    extractBits {len₂} (injectBits (payloadIso bo payload) s₁ bits) s₂
  ≡⟨ injectBits-preserves-disjoint (payloadIso bo payload) s₁ s₂ bits disj fits₁ fits₂ ⟩
    extractBits {len₂} (payloadIso bo payload) s₂
  ∎
  where
    open ≡-Reasoning

-- ============================================================================
-- LOOKUPAFE-SWAPBYTES
-- ============================================================================

lookupSafe-swapBytes : ∀ {n} i → i < n → (bytes : Vec Byte n) →
  lookupSafe n i (swapBytes bytes) ≡ lookupSafe n ((n ∸ 1) ∸ i) bytes
lookupSafe-swapBytes {zero} _ () _
lookupSafe-swapBytes {suc m} i (s≤s i≤m) (b ∷ bs) with i <? m
... | yes i<m =
  trans (cong (lookupSafe (suc m) i) (reverse-∷ b bs))
    (trans (lookupSafe-∷ʳ i i<m (reverse bs) b)
      (trans (lookupSafe-swapBytes i i<m bs)
        (trans (cong (λ k → lookupSafe m k bs) (m∸1∸i≡m∸suci i<m))
          (sym (cong (λ k → lookupSafe (suc m) k (b ∷ bs)) (m∸n≡suc[m∸1+n] i<m))))))
... | no ¬i<m with ≤-antisym i≤m (≮⇒≥ ¬i<m)
...   | refl =
  trans (cong (lookupSafe (suc m) m) (reverse-∷ b bs))
    (trans (lookupSafe-∷ʳ-last (reverse bs) b)
      (sym (cong (λ k → lookupSafe (suc m) k (b ∷ bs)) (n∸n≡0 m))))

-- ============================================================================
-- ARITHMETIC HELPERS FOR physicalBitPos
-- ============================================================================

private
  [m+kn]%8≡m%8 : ∀ m k → (m + k * 8) % 8 ≡ m % 8
  [m+kn]%8≡m%8 m zero rewrite +-identityʳ m = refl
  [m+kn]%8≡m%8 m (suc k) =
    trans (cong (λ x → (m + x) % 8) (+-comm 8 (k * 8)))
      (trans (cong (_% 8) (sym (+-assoc m (k * 8) 8)))
        (trans ([m+n]%n≡m%n (m + k * 8) 8)
          ([m+kn]%8≡m%8 m k)))

  mul-add-mod : ∀ a r → r < 8 → (a * 8 + r) % 8 ≡ r
  mul-add-mod a r r<8 =
    trans (cong (_% 8) (+-comm (a * 8) r))
      (trans ([m+kn]%8≡m%8 r a) (m<n⇒m%n≡m r<8))

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
          cancel-right : a * 8 + r ≡ r + ((a * 8 + r) / 8) * 8
                       → a * 8 ≡ ((a * 8 + r) / 8) * 8
          cancel-right eq = Data.Nat.Properties.+-cancelʳ-≡ r (a * 8) _ eq'
            where
              eq' : a * 8 + r ≡ ((a * 8 + r) / 8) * 8 + r
              eq' = trans eq (+-comm r _)

  physicalBitPos-BE-div8 : ∀ n b → b < n * 8 → physicalBitPos n BigEndian b / 8 ≡ (n ∸ 1) ∸ (b / 8)
  physicalBitPos-BE-div8 n b b<n*8 = mul-add-div ((n ∸ 1) ∸ (b / 8)) (b % 8) (m%n<n b 8)

  physicalBitPos-BE-mod8 : ∀ n b → physicalBitPos n BigEndian b % 8 ≡ b % 8
  physicalBitPos-BE-mod8 n b = mul-add-mod ((n ∸ 1) ∸ (b / 8)) (b % 8) (m%n<n b 8)

-- ============================================================================
-- physicalBitPos PROPERTIES
-- ============================================================================

physicalBitPos-BE-bounded : ∀ n b → b < n * 8 → physicalBitPos n BigEndian b < n * 8
physicalBitPos-BE-bounded zero b ()
physicalBitPos-BE-bounded (suc n') b b<n*8 = <-≤-trans step1 step2
  where
    open import Data.Nat.Properties using (suc[pred[n]]≡n; *-monoˡ-≤)
    n = suc n'
    byteIdx = b / 8
    revByte = (n ∸ 1) ∸ byteIdx
    bitIdx = b % 8

    suc-revByte≤n : suc revByte ≤ n
    suc-revByte≤n = s≤s (m∸n≤m n' byteIdx)

    step1 : revByte * 8 + bitIdx < revByte * 8 + 8
    step1 = +-monoʳ-< (revByte * 8) (m%n<n b 8)

    step2 : revByte * 8 + 8 ≤ n * 8
    step2 = subst (_≤ n * 8) (+-comm 8 (revByte * 8)) (*-monoˡ-≤ 8 suc-revByte≤n)

physicalBitPos-BE-bounded-any : ∀ n b → 1 ≤ n → physicalBitPos n BigEndian b < n * 8
physicalBitPos-BE-bounded-any (suc n') b _ = <-≤-trans step1 step2
  where
    open import Data.Nat.Properties using (*-monoˡ-≤)
    n = suc n'
    revByte = (n ∸ 1) ∸ (b / 8)

    suc-revByte≤n : suc revByte ≤ n
    suc-revByte≤n = s≤s (m∸n≤m n' (b / 8))

    step1 : revByte * 8 + (b % 8) < revByte * 8 + 8
    step1 = +-monoʳ-< (revByte * 8) (m%n<n b 8)

    step2 : revByte * 8 + 8 ≤ n * 8
    step2 = subst (_≤ n * 8) (+-comm 8 (revByte * 8)) (*-monoˡ-≤ 8 suc-revByte≤n)

convertStartBit-wf-bound : ∀ n bo s l {bound} → 1 ≤ n → n * 8 ≤ bound → s < bound → convertStartBit n bo s l < bound
convertStartBit-wf-bound n LittleEndian s l _ _ s<bound = s<bound
convertStartBit-wf-bound n BigEndian s l n≥1 n*8≤bound _ =
  ≤-<-trans (m∸n≤m (physicalBitPos n BigEndian s) (l ∸ 1))
            (<-≤-trans (physicalBitPos-BE-bounded-any n s n≥1) n*8≤bound)

physicalBitPos-BE-involutive : ∀ n b → b < n * 8 → physicalBitPos n BigEndian (physicalBitPos n BigEndian b) ≡ b
physicalBitPos-BE-involutive n b b<n*8 =
  begin
    physicalBitPos n BigEndian (physicalBitPos n BigEndian b)
  ≡⟨⟩
    ((n ∸ 1) ∸ (physBit / 8)) * 8 + (physBit % 8)
  ≡⟨ cong (λ x → ((n ∸ 1) ∸ x) * 8 + (physBit % 8)) (physicalBitPos-BE-div8 n b b<n*8) ⟩
    ((n ∸ 1) ∸ ((n ∸ 1) ∸ (b / 8))) * 8 + (physBit % 8)
  ≡⟨ cong (λ x → ((n ∸ 1) ∸ ((n ∸ 1) ∸ (b / 8))) * 8 + x) (physicalBitPos-BE-mod8 n b) ⟩
    ((n ∸ 1) ∸ ((n ∸ 1) ∸ (b / 8))) * 8 + (b % 8)
  ≡⟨ cong (λ x → x * 8 + (b % 8)) (m∸[m∸n]≡n byteIdx≤n∸1) ⟩
    (b / 8) * 8 + (b % 8)
  ≡⟨ div-mod-identity b ⟩
    b
  ∎
  where
    open ≡-Reasoning
    open import Data.Nat.Properties using (m∸[m∸n]≡n)
    physBit = physicalBitPos n BigEndian b

    byteIdx<n : b / 8 < n
    byteIdx<n = m<n*o⇒m/o<n {b} {n} {8} b<n*8

    byteIdx≤n∸1 : b / 8 ≤ n ∸ 1
    byteIdx≤n∸1 with byteIdx<n
    ... | s≤s p = p

    div-mod-identity : ∀ m → (m / 8) * 8 + (m % 8) ≡ m
    div-mod-identity m = trans (+-comm ((m / 8) * 8) (m % 8)) (sym (m≡m%n+[m/n]*n m 8))

-- ============================================================================
-- STARTBIT CONVERSION ROUNDTRIP PROOFS
-- ============================================================================

convertStartBit-roundtrip : ∀ n s l →
  1 ≤ l → s < n * 8 → l ∸ 1 ≤ physicalBitPos n BigEndian s →
  unconvertStartBit n BigEndian (convertStartBit n BigEndian s l) l ≡ s
convertStartBit-roundtrip n s (suc k) _ s<n*8 k≤p =
  begin
    physicalBitPos n BigEndian ((p ∸ k) + suc k ∸ 1)
  ≡⟨ cong (λ x → physicalBitPos n BigEndian (x ∸ 1)) (+-suc (p ∸ k) k) ⟩
    physicalBitPos n BigEndian (suc ((p ∸ k) + k) ∸ 1)
  ≡⟨⟩
    physicalBitPos n BigEndian ((p ∸ k) + k)
  ≡⟨ cong (physicalBitPos n BigEndian) (m∸n+n≡m k≤p) ⟩
    physicalBitPos n BigEndian p
  ≡⟨ physicalBitPos-BE-involutive n s s<n*8 ⟩
    s
  ∎
  where
    open ≡-Reasoning
    open import Data.Nat.Properties using (m∸n+n≡m)
    p = physicalBitPos n BigEndian s

unconvertStartBit-roundtrip : ∀ n s l →
  1 ≤ l → s + l ∸ 1 < n * 8 → l ∸ 1 ≤ s →
  convertStartBit n BigEndian (unconvertStartBit n BigEndian s l) l ≡ s
unconvertStartBit-roundtrip n s (suc k) _ sk<n*8 k≤s =
  begin
    physicalBitPos n BigEndian (physicalBitPos n BigEndian (s + suc k ∸ 1)) ∸ k
  ≡⟨ cong (λ x → physicalBitPos n BigEndian (physicalBitPos n BigEndian x) ∸ k) reduce ⟩
    physicalBitPos n BigEndian (physicalBitPos n BigEndian (s + k)) ∸ k
  ≡⟨ cong (_∸ k) (physicalBitPos-BE-involutive n (s + k) (subst (_< n * 8) reduce sk<n*8)) ⟩
    (s + k) ∸ k
  ≡⟨ m+n∸n≡m s k ⟩
    s
  ∎
  where
    open ≡-Reasoning
    open import Data.Nat.Properties using (m+n∸n≡m)
    reduce : s + suc k ∸ 1 ≡ s + k
    reduce = cong (_∸ 1) (+-suc s k)

-- ============================================================================
-- UNIFIED BIT PRESERVATION LEMMA
-- ============================================================================

private
  injectBits-preserves-bit :
    ∀ {len} {n} (bytes : Vec Byte n) (s p : ℕ) (bits : BitVec len)
    → p < s ⊎ s + len ≤ p
    → s + len ≤ n * 8
    → p < n * 8
    → testBit (byteToBitVec (lookupSafe n (p / 8) (injectBits bytes s bits)))
              (fromℕ< (m%n<n p 8))
      ≡ testBit (byteToBitVec (lookupSafe n (p / 8) bytes))
                (fromℕ< (m%n<n p 8))
  injectBits-preserves-bit bytes s p bits (inj₁ p<s) bound _ =
    injectBits-preserves-earlier-bit bytes p s bits p<s bound
  injectBits-preserves-bit bytes s p bits (inj₂ s+len≤p) _ p<n*8 =
    injectBits-preserves-later-bit bytes s p bits s+len≤p p<n*8

injectBits-preserves-outside :
  ∀ {len₁ len₂} {n} (bytes : Vec Byte n) (start₁ start₂ : ℕ) (bits : BitVec len₁)
  → (∀ k → k < len₂ → start₂ + k < start₁ ⊎ start₁ + len₁ ≤ start₂ + k)
  → start₁ + len₁ ≤ n * 8
  → start₂ + len₂ ≤ n * 8
  → extractBits {len₂} (injectBits bytes start₁ bits) start₂ ≡ extractBits {len₂} bytes start₂
injectBits-preserves-outside {_} {zero} _ _ _ _ _ _ _ = refl
injectBits-preserves-outside {len₁} {suc len₂} {n} bytes start₁ start₂ bits outside bound₁ bound₂ =
  cong₂ _∷_ head-eq rest-eq
  where
    start₂<n*8 : start₂ < n * 8
    start₂<n*8 = <-≤-trans (m<m+n start₂ {suc len₂} (s≤s z≤n)) bound₂

    head-outside : start₂ < start₁ ⊎ start₁ + len₁ ≤ start₂
    head-outside with outside 0 (s≤s z≤n)
    ... | inj₁ p = inj₁ (subst (_< start₁) (+-identityʳ start₂) p)
    ... | inj₂ q = inj₂ (subst (start₁ + len₁ ≤_) (+-identityʳ start₂) q)

    head-eq = injectBits-preserves-bit bytes start₁ start₂ bits head-outside bound₁ start₂<n*8

    bound₂' : suc start₂ + len₂ ≤ n * 8
    bound₂' = subst (_≤ n * 8) (+-suc start₂ len₂) bound₂

    outside' : ∀ k → k < len₂ → suc start₂ + k < start₁ ⊎ start₁ + len₁ ≤ suc start₂ + k
    outside' k k<len₂ with outside (suc k) (s≤s k<len₂)
    ... | inj₁ p = inj₁ (subst (_< start₁) (+-suc start₂ k) p)
    ... | inj₂ q = inj₂ (subst (start₁ + len₁ ≤_) (+-suc start₂ k) q)

    rest-eq = injectBits-preserves-outside bytes start₁ (suc start₂) bits outside' bound₁ bound₂'

-- ============================================================================
-- CROSS-BYTE-ORDER EXTRACTION PRESERVATION
-- ============================================================================

extractBits-swap-inject-preserves :
  ∀ {l₁ l₂} {n} (bytes : Vec Byte n) (s₁ s₂ : ℕ) (bits : BitVec l₁)
  → (∀ k → k < l₂ → physicalBitPos n BigEndian (s₂ + k) < s₁
                    ⊎ s₁ + l₁ ≤ physicalBitPos n BigEndian (s₂ + k))
  → s₁ + l₁ ≤ n * 8
  → s₂ + l₂ ≤ n * 8
  → extractBits {l₂} (swapBytes (injectBits bytes s₁ bits)) s₂
    ≡ extractBits {l₂} (swapBytes bytes) s₂
extractBits-swap-inject-preserves {l₁} {_} {n} bytes s₁ s₂ bits noOverlap bound₁ bound₂ = go _ s₂ noOverlap bound₂
  where
    go : ∀ l₂ (pos : ℕ)
      → (∀ k → k < l₂ → physicalBitPos n BigEndian (pos + k) < s₁
                        ⊎ s₁ + l₁ ≤ physicalBitPos n BigEndian (pos + k))
      → pos + l₂ ≤ n * 8
      → extractBits {l₂} (swapBytes (injectBits bytes s₁ bits)) pos
        ≡ extractBits {l₂} (swapBytes bytes) pos
    go zero pos noOv bound = refl
    go (suc l₂') pos noOv bound = cong₂ _∷_ head-eq (go l₂' (suc pos) noOv' bound')
      where
        bound' : suc pos + l₂' ≤ n * 8
        bound' = subst (_≤ n * 8) (+-suc pos l₂') bound

        noOv' : ∀ k → k < l₂' → physicalBitPos n BigEndian (suc pos + k) < s₁
                                ⊎ s₁ + l₁ ≤ physicalBitPos n BigEndian (suc pos + k)
        noOv' k k<l₂' = subst (λ x → physicalBitPos n BigEndian x < s₁
                                     ⊎ s₁ + l₁ ≤ physicalBitPos n BigEndian x)
                               (+-suc pos k)
                               (noOv (suc k) (s≤s k<l₂'))

        pos<n*8 : pos < n * 8
        pos<n*8 = <-≤-trans (m<m+n pos {suc l₂'} (s≤s z≤n)) bound

        byteIdx : ℕ
        byteIdx = pos / 8

        byteIdx<n : byteIdx < n
        byteIdx<n = m<n*o⇒m/o<n {pos} {n} {8} pos<n*8

        physBit : ℕ
        physBit = physicalBitPos n BigEndian pos

        physBit<n*8 : physBit < n * 8
        physBit<n*8 = physicalBitPos-BE-bounded n pos pos<n*8

        physBit-disj : physBit < s₁ ⊎ s₁ + l₁ ≤ physBit
        physBit-disj = subst (λ x → physicalBitPos n BigEndian x < s₁
                                   ⊎ s₁ + l₁ ≤ physicalBitPos n BigEndian x)
                             (+-comm pos 0)
                             (noOv 0 (s≤s z≤n))

        swap-lhs : lookupSafe n byteIdx (swapBytes (injectBits bytes s₁ bits))
                 ≡ lookupSafe n ((n ∸ 1) ∸ byteIdx) (injectBits bytes s₁ bits)
        swap-lhs = lookupSafe-swapBytes byteIdx byteIdx<n (injectBits bytes s₁ bits)

        swap-rhs : lookupSafe n byteIdx (swapBytes bytes)
                 ≡ lookupSafe n ((n ∸ 1) ∸ byteIdx) bytes
        swap-rhs = lookupSafe-swapBytes byteIdx byteIdx<n bytes

        physBit-div : physBit / 8 ≡ (n ∸ 1) ∸ byteIdx
        physBit-div = physicalBitPos-BE-div8 n pos pos<n*8

        physBit-mod : physBit % 8 ≡ pos % 8
        physBit-mod = physicalBitPos-BE-mod8 n pos

        bit-preserved : testBit (byteToBitVec (lookupSafe n (physBit / 8) (injectBits bytes s₁ bits)))
                                (fromℕ< (m%n<n physBit 8))
                      ≡ testBit (byteToBitVec (lookupSafe n (physBit / 8) bytes))
                                (fromℕ< (m%n<n physBit 8))
        bit-preserved = injectBits-preserves-bit bytes s₁ physBit bits physBit-disj bound₁ physBit<n*8

        inner-preserved : testBit (byteToBitVec (lookupSafe n ((n ∸ 1) ∸ byteIdx) (injectBits bytes s₁ bits)))
                                  (fromℕ< (m%n<n pos 8))
                        ≡ testBit (byteToBitVec (lookupSafe n ((n ∸ 1) ∸ byteIdx) bytes))
                                  (fromℕ< (m%n<n pos 8))
        inner-preserved =
          subst₂ (λ idx bpos →
            testBit (byteToBitVec (lookupSafe n idx (injectBits bytes s₁ bits))) bpos
            ≡ testBit (byteToBitVec (lookupSafe n idx bytes)) bpos)
            physBit-div
            (toℕ-injective (trans (toℕ-fromℕ< (m%n<n physBit 8))
                             (trans physBit-mod
                               (sym (toℕ-fromℕ< (m%n<n pos 8))))))
            bit-preserved

        head-eq : testBit (byteToBitVec (lookupSafe n byteIdx (swapBytes (injectBits bytes s₁ bits))))
                          (fromℕ< (m%n<n pos 8))
                ≡ testBit (byteToBitVec (lookupSafe n byteIdx (swapBytes bytes)))
                          (fromℕ< (m%n<n pos 8))
        head-eq = trans (cong (λ x → testBit (byteToBitVec x) (fromℕ< (m%n<n pos 8))) swap-lhs)
                   (trans inner-preserved
                     (cong (λ x → testBit (byteToBitVec x) (fromℕ< (m%n<n pos 8))) (sym swap-rhs)))

-- ============================================================================
-- MIXED BYTE-ORDER COMMUTATIVITY
-- ============================================================================

private
  swap-updateSafe-swap : ∀ {n} i → i < n → (f : Byte → Byte) (bytes : Vec Byte n)
    → swapBytes (updateSafe n i f (swapBytes bytes)) ≡ updateSafe n ((n ∸ 1) ∸ i) f bytes
  swap-updateSafe-swap {zero} _ () _ _
  swap-updateSafe-swap {suc m} i (s≤s i≤m) f (b ∷ bs) with i <? m
  ... | yes i<m =
    trans (cong (λ v → reverse (updateSafe (suc m) i f v)) (reverse-∷ b bs))
      (trans (cong reverse (updateSafe-∷ʳ i i<m f (reverse bs) b))
        (trans (reverse-∷ʳ (updateSafe m i f (reverse bs)) b)
          (trans (cong (b ∷_) (swap-updateSafe-swap i i<m f bs))
            (trans (cong (λ k → b ∷ updateSafe m k f bs) (m∸1∸i≡m∸suci i<m))
              (sym (cong (λ k → updateSafe (suc m) k f (b ∷ bs)) (m∸n≡suc[m∸1+n] i<m)))))))
  ... | no ¬i<m with ≤-antisym i≤m (≮⇒≥ ¬i<m)
  ...   | refl =
    trans (cong (λ v → reverse (updateSafe (suc m) m f v)) (reverse-∷ b bs))
      (trans (cong reverse (updateSafe-∷ʳ-last f (reverse bs) b))
        (trans (reverse-∷ʳ (reverse bs) (f b))
          (trans (cong (f b ∷_) (reverse-involutive bs))
            (sym (cong (λ k → updateSafe (suc m) k f (b ∷ bs)) (n∸n≡0 m))))))

  updateSafe-cong-fn′ : ∀ {n} (i : ℕ) (h₁ h₂ : Byte → Byte) (xs : Vec Byte n)
    → (∀ b → h₁ b ≡ h₂ b) → updateSafe n i h₁ xs ≡ updateSafe n i h₂ xs
  updateSafe-cong-fn′ {zero} _ _ _ [] _ = refl
  updateSafe-cong-fn′ {suc _} zero h₁ h₂ (x ∷ xs) eq = cong (_∷ xs) (eq x)
  updateSafe-cong-fn′ {suc n} (suc i) h₁ h₂ (x ∷ xs) eq =
    cong (x ∷_) (updateSafe-cong-fn′ i h₁ h₂ xs eq)

  swap-applyWrite-swap : ∀ {n} (bytes : Vec Byte n) pos val → pos < n * 8
    → swapBytes (applyWrite (swapBytes bytes) (pos , val))
      ≡ applyWrite bytes (physicalBitPos n BigEndian pos , val)
  swap-applyWrite-swap {n} bytes pos val pos<n*8 =
    trans step1 (trans step2 step3)
    where
      physBit = physicalBitPos n BigEndian pos
      byteIdx = pos / 8
      bitPos = fromℕ< (m%n<n pos 8)
      fn₁ = λ byte → bitVecToByte (setBit (byteToBitVec byte) bitPos val)

      physByteIdx = physBit / 8
      physBitPos′ = fromℕ< (m%n<n physBit 8)
      fn₂ = λ byte → bitVecToByte (setBit (byteToBitVec byte) physBitPos′ val)

      byteIdx<n : byteIdx < n
      byteIdx<n = m<n*o⇒m/o<n {pos} {n} {8} pos<n*8

      step1 : swapBytes (applyWrite (swapBytes bytes) (pos , val))
            ≡ updateSafe n ((n ∸ 1) ∸ byteIdx) fn₁ bytes
      step1 = swap-updateSafe-swap byteIdx byteIdx<n fn₁ bytes

      fin-eq : physBitPos′ ≡ bitPos
      fin-eq = toℕ-injective (trans (toℕ-fromℕ< (m%n<n physBit 8))
                               (trans (physicalBitPos-BE-mod8 n pos)
                                 (sym (toℕ-fromℕ< (m%n<n pos 8)))))

      fns-pw : ∀ b → fn₁ b ≡ fn₂ b
      fns-pw b = cong (λ bp → bitVecToByte (setBit (byteToBitVec b) bp val)) (sym fin-eq)

      step2 : updateSafe n ((n ∸ 1) ∸ byteIdx) fn₁ bytes
            ≡ updateSafe n ((n ∸ 1) ∸ byteIdx) fn₂ bytes
      step2 = updateSafe-cong-fn′ ((n ∸ 1) ∸ byteIdx) fn₁ fn₂ bytes fns-pw

      step3 : updateSafe n ((n ∸ 1) ∸ byteIdx) fn₂ bytes
            ≡ updateSafe n physByteIdx fn₂ bytes
      step3 = cong (λ i → updateSafe n i fn₂ bytes)
                   (sym (physicalBitPos-BE-div8 n pos pos<n*8))

physicalWrites : ℕ → List BitWrite → List BitWrite
physicalWrites n = map (λ { (p , v) → (physicalBitPos n BigEndian p , v) })

private
  writesOf-bounded : ∀ {len} s (bits : BitVec len) {bound} → s + len ≤ bound
    → All (λ { (pos , _) → pos < bound }) (writesOf s bits)
  writesOf-bounded s [] _ = []
  writesOf-bounded s (b ∷ bits) {bound} bd =
    <-≤-trans (m<m+n s {suc _} (s≤s z≤n)) bd
    ∷ writesOf-bounded (suc s) bits (subst (_≤ bound) (+-suc s _) bd)

swap-applyWrites-swap : ∀ {n} (bytes : Vec Byte n) ws
  → All (λ { (pos , _) → pos < n * 8 }) ws
  → swapBytes (applyWrites (swapBytes bytes) ws) ≡ applyWrites bytes (physicalWrites n ws)
swap-applyWrites-swap bytes [] [] = swapBytes-involutive bytes
swap-applyWrites-swap {n} bytes ((pos , val) ∷ ws) (pos<n*8 ∷ rest) =
  trans (cong (λ x → swapBytes (applyWrites x ws)) aw-rev)
    (swap-applyWrites-swap (applyWrite bytes (physicalBitPos n BigEndian pos , val)) ws rest)
  where
    aw-rev : applyWrite (swapBytes bytes) (pos , val)
           ≡ swapBytes (applyWrite bytes (physicalBitPos n BigEndian pos , val))
    aw-rev = trans (sym (swapBytes-involutive (applyWrite (swapBytes bytes) (pos , val))))
                   (cong swapBytes (swap-applyWrite-swap bytes pos val pos<n*8))

private
  all-diff-writesOf : ∀ (p : ℕ) (v : Bool) {len₂} s₂ (bits₂ : BitVec len₂)
    → (∀ k₂ → k₂ < len₂ → p ≢ s₂ + k₂)
    → All (DiffPos (p , v)) (writesOf s₂ bits₂)
  all-diff-writesOf p v s₂ [] _ = []
  all-diff-writesOf p v s₂ (b₂ ∷ bits₂) disj =
    subst (p ≢_) (+-identityʳ s₂) (disj 0 (s≤s z≤n))
    ∷ all-diff-writesOf p v (suc s₂) bits₂
        (λ k₂ k₂< → subst (p ≢_) (+-suc s₂ k₂) (disj (suc k₂) (s≤s k₂<)))

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

  all-diff-physWritesOf : ∀ n (p : ℕ) (v : Bool) {len₂} s₂ (bits₂ : BitVec len₂)
    → (∀ k₂ → k₂ < len₂ → p ≢ physicalBitPos n BigEndian (s₂ + k₂))
    → All (DiffPos (p , v)) (physicalWrites n (writesOf s₂ bits₂))
  all-diff-physWritesOf _ p v s₂ [] _ = []
  all-diff-physWritesOf n p v s₂ (b₂ ∷ bits₂) disj =
    subst (p ≢_) (cong (physicalBitPos n BigEndian) (+-identityʳ s₂)) (disj 0 (s≤s z≤n))
    ∷ all-diff-physWritesOf n p v (suc s₂) bits₂
        (λ k₂ k₂< → subst (p ≢_) (cong (physicalBitPos n BigEndian) (+-suc s₂ k₂))
                       (disj (suc k₂) (s≤s k₂<)))

  writesOf-AllDiffPos-phys : ∀ n {len₁ len₂} s₁ (bits₁ : BitVec len₁) s₂ (bits₂ : BitVec len₂)
    → (∀ k₁ → k₁ < len₁ → ∀ k₂ → k₂ < len₂
       → s₁ + k₁ ≢ physicalBitPos n BigEndian (s₂ + k₂))
    → AllDiffPos (writesOf s₁ bits₁) (physicalWrites n (writesOf s₂ bits₂))
  writesOf-AllDiffPos-phys _ s₁ [] s₂ bits₂ _ = tt
  writesOf-AllDiffPos-phys n s₁ (b₁ ∷ bits₁) s₂ bits₂ disj =
    ( all-diff-physWritesOf n s₁ b₁ s₂ bits₂
        (λ k₂ k₂< → subst (_≢ physicalBitPos n BigEndian (s₂ + k₂))
                       (+-identityʳ s₁) (disj 0 (s≤s z≤n) k₂ k₂<))
    , writesOf-AllDiffPos-phys n (suc s₁) bits₁ s₂ bits₂
        (λ k₁ k₁< k₂ k₂< → subst (_≢ physicalBitPos n BigEndian (s₂ + k₂))
                               (+-suc s₁ k₁) (disj (suc k₁) (s≤s k₁<) k₂ k₂<))
    )

injectPayload-commute-mixed :
  ∀ {len₁ len₂} {n} s₁ s₂ (bits₁ : BitVec len₁) (bits₂ : BitVec len₂) bo₁ bo₂ (payload : Vec Byte n)
  → (∀ k₁ → k₁ < len₁ → ∀ k₂ → k₂ < len₂
     → physicalBitPos n bo₁ (s₁ + k₁) ≢ physicalBitPos n bo₂ (s₂ + k₂))
  → s₁ + len₁ ≤ n * 8
  → s₂ + len₂ ≤ n * 8
  → injectPayload s₂ bits₂ bo₂ (injectPayload s₁ bits₁ bo₁ payload)
    ≡ injectPayload s₁ bits₁ bo₁ (injectPayload s₂ bits₂ bo₂ payload)
injectPayload-commute-mixed {len₁} {len₂} {n} s₁ s₂ bits₁ bits₂ bo₁ bo₂ payload physDisj fits₁ fits₂ =
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
             (λ k₁ k₁< k₂ k₂< eq → physDisj k₁ k₁< k₂ k₂< (cong (physicalBitPos n BigEndian) eq)))) ⟩
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

    go LittleEndian BigEndian refl refl =
      begin
        swapBytes (injectBits (swapBytes (injectBits payload s₁ bits₁)) s₂ bits₂)
      ≡⟨ cong (λ x → swapBytes (injectBits (swapBytes x) s₂ bits₂))
              (injectBits≡applyWrites payload s₁ bits₁) ⟩
        swapBytes (injectBits (swapBytes (applyWrites payload ws₁)) s₂ bits₂)
      ≡⟨ cong swapBytes (injectBits≡applyWrites (swapBytes (applyWrites payload ws₁)) s₂ bits₂) ⟩
        swapBytes (applyWrites (swapBytes (applyWrites payload ws₁)) ws₂)
      ≡⟨ swap-applyWrites-swap (applyWrites payload ws₁) ws₂ bd₂ ⟩
        applyWrites (applyWrites payload ws₁) (physicalWrites n ws₂)
      ≡⟨ applyWrites-comm payload ws₁ (physicalWrites n ws₂)
           (writesOf-distinct s₁ bits₁)
           (writesOf-AllDiffPos-phys n s₁ bits₁ s₂ bits₂ physDisj) ⟩
        applyWrites (applyWrites payload (physicalWrites n ws₂)) ws₁
      ≡⟨ sym (injectBits≡applyWrites (applyWrites payload (physicalWrites n ws₂)) s₁ bits₁) ⟩
        injectBits (applyWrites payload (physicalWrites n ws₂)) s₁ bits₁
      ≡⟨ cong (λ x → injectBits x s₁ bits₁)
              (sym (swap-applyWrites-swap payload ws₂ bd₂)) ⟩
        injectBits (swapBytes (applyWrites (swapBytes payload) ws₂)) s₁ bits₁
      ≡⟨ cong (λ x → injectBits (swapBytes x) s₁ bits₁)
              (sym (injectBits≡applyWrites (swapBytes payload) s₂ bits₂)) ⟩
        injectBits (swapBytes (injectBits (swapBytes payload) s₂ bits₂)) s₁ bits₁
      ∎

    go BigEndian LittleEndian refl refl =
      begin
        injectBits (swapBytes (injectBits (swapBytes payload) s₁ bits₁)) s₂ bits₂
      ≡⟨ cong (λ x → injectBits (swapBytes x) s₂ bits₂)
              (injectBits≡applyWrites (swapBytes payload) s₁ bits₁) ⟩
        injectBits (swapBytes (applyWrites (swapBytes payload) ws₁)) s₂ bits₂
      ≡⟨ cong (λ x → injectBits x s₂ bits₂)
              (swap-applyWrites-swap payload ws₁ bd₁) ⟩
        injectBits (applyWrites payload (physicalWrites n ws₁)) s₂ bits₂
      ≡⟨ injectBits≡applyWrites (applyWrites payload (physicalWrites n ws₁)) s₂ bits₂ ⟩
        applyWrites (applyWrites payload (physicalWrites n ws₁)) ws₂
      ≡⟨ sym (applyWrites-comm payload ws₂ (physicalWrites n ws₁)
           (writesOf-distinct s₂ bits₂)
           (writesOf-AllDiffPos-phys n s₂ bits₂ s₁ bits₁
             (λ k₂ k₂< k₁ k₁< eq → physDisj k₁ k₁< k₂ k₂< (sym eq)))) ⟩
        applyWrites (applyWrites payload ws₂) (physicalWrites n ws₁)
      ≡⟨ cong (λ x → applyWrites x (physicalWrites n ws₁))
              (sym (injectBits≡applyWrites payload s₂ bits₂)) ⟩
        applyWrites (injectBits payload s₂ bits₂) (physicalWrites n ws₁)
      ≡⟨ sym (swap-applyWrites-swap (injectBits payload s₂ bits₂) ws₁ bd₁) ⟩
        swapBytes (applyWrites (swapBytes (injectBits payload s₂ bits₂)) ws₁)
      ≡⟨ cong swapBytes (sym (injectBits≡applyWrites (swapBytes (injectBits payload s₂ bits₂)) s₁ bits₁)) ⟩
        swapBytes (injectBits (swapBytes (injectBits payload s₂ bits₂)) s₁ bits₁)
      ∎
