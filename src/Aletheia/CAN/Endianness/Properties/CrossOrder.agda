{-# OPTIONS --safe --without-K #-}

-- Cross-byte-order bit preservation and mixed-order commutativity.
--
-- Purpose: Prove that LE/BE injections commute when their physical bit ranges
--   are disjoint, via swapBytes ∘ applyWrites ∘ swapBytes decomposition.
-- Exports: injectBits-preserves-outside, extractBits-swap-inject-preserves,
--   physicalWrites, swap-applyWrites-swap, injectPayload-commute-mixed.
module Aletheia.CAN.Endianness.Properties.CrossOrder where

open import Aletheia.CAN.Endianness using
  ( ByteOrder; LittleEndian; BigEndian
  ; lookupSafe; updateSafe
  ; byteToBitVec; bitVecToByte
  ; extractBits; injectBits
  ; swapBytes
  ; payloadIso; injectPayload
  ; physicalBitPos
  )
open import Aletheia.CAN.Frame using (Byte)
open import Aletheia.Data.BitVec using (BitVec; testBit; setBit)
open import Aletheia.CAN.Endianness.Properties.Roundtrip using
  ( swapBytes-involutive
  ; injectBits-preserves-earlier-bit
  ; injectBits-preserves-later-bit
  )
open import Aletheia.CAN.Endianness.Properties.WriteSet using
  ( BitWrite; applyWrite; applyWrites; writesOf; DiffPos; AllDiffPos; AllDistinct
  ; applyWrites-comm; injectBits≡applyWrites; writesOf-distinct
  ; payloadIso-involutive
  )
open import Aletheia.CAN.Endianness.Properties.StartBit using
  ( m∸n≡suc[m∸1+n]; m∸1∸i≡m∸suci
  ; updateSafe-∷ʳ; updateSafe-∷ʳ-last; reverse-∷ʳ
  ; lookupSafe-swapBytes
  ; physicalBitPos-BE-div8; physicalBitPos-BE-mod8
  ; physicalBitPos-BE-bounded
  )
open import Data.Vec using (Vec; []; _∷_; _∷ʳ_; reverse)
open import Data.Vec.Properties using (reverse-involutive; reverse-∷)
open import Data.Fin using (Fin; fromℕ<; toℕ)
open import Data.Fin.Properties using (toℕ-fromℕ<; toℕ-injective)
open import Data.Nat as Nat using (ℕ; zero; suc; _+_; _∸_; _*_; _<_; _≤_; z≤n; s≤s; _/_; _%_)
open import Data.Nat.DivMod using (m%n<n; m<n*o⇒m/o<n)
open import Data.Nat.Properties using (_<?_; +-suc; +-comm; +-identityʳ; ≤-refl; ≤-trans; ≤-antisym; ≮⇒≥; n≤1+n; m<m+n; <-≤-trans; m∸n≤m; n∸n≡0)
open import Data.Bool using (Bool)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂; _≢_)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Nullary using (yes; no)

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
    cong₂ = Relation.Binary.PropositionalEquality.cong₂

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
        cong₂ = Relation.Binary.PropositionalEquality.cong₂

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
