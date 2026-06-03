-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- PhysicalBitPos properties, startBit conversion roundtrips, and shared vec helpers.
--
-- Purpose: Physical bit position arithmetic, lookupSafe-swapBytes bridge,
--   and startBit / unconvertStartBit roundtrip proofs.
-- Exports: vec/arithmetic helpers (used by CrossOrder), lookupSafe-swapBytes,
--   physicalBitPos-BE-bounded, physicalBitPos-BE-bounded-any, physicalBitPos-BE-involutive,
--   physicalBitPos-BE-div8, physicalBitPos-BE-mod8,
--   convertStartBit-wf-bound, convertStartBit-roundtrip, unconvertStartBit-roundtrip.
module Aletheia.CAN.Endianness.Properties.StartBit where

open import Aletheia.CAN.Endianness using
  ( LittleEndian; BigEndian
  ; lookupSafe; updateSafe
  ; swapBytes
  ; physicalBitPos
  ; convertStartBit; unconvertStartBit
  )
open import Aletheia.CAN.Frame using (Byte)
open import Data.Vec using (Vec; []; _∷_; _∷ʳ_; reverse)
open import Data.Vec.Properties using (reverse-involutive; reverse-∷)
open import Data.Nat as Nat using (zero; suc; _+_; _∸_; _*_; _<_; _≤_; s≤s; _/_; _%_)
open import Data.Nat.DivMod using (m%n<n; m<n⇒m%n≡m; m≡m%n+[m/n]*n; m<n*o⇒m/o<n; [m+n]%n≡m%n)
open import Data.Nat.Properties using (_<?_; +-suc; +-comm; +-assoc; +-identityʳ; ≤-<-trans; ≤-antisym; ≮⇒≥; m∸n≤m; n∸n≡0; <-≤-trans; +-monoʳ-<; *-monoˡ-≤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Nullary using (yes; no)

-- ============================================================================
-- SHARED VEC HELPERS (public, used by CrossOrder)
-- ============================================================================

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
-- LOOKUPSAFE-SWAPBYTES
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

-- ============================================================================
-- physicalBitPos DECOMPOSITION LEMMAS (public, used by CrossOrder)
-- ============================================================================

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
    n = suc n'
    revByte = (n ∸ 1) ∸ (b / 8)

    suc-revByte≤n : suc revByte ≤ n
    suc-revByte≤n = s≤s (m∸n≤m n' (b / 8))

    step1 : revByte * 8 + (b % 8) < revByte * 8 + 8
    step1 = +-monoʳ-< (revByte * 8) (m%n<n b 8)

    step2 : revByte * 8 + 8 ≤ n * 8
    step2 = subst (_≤ n * 8) (+-comm 8 (revByte * 8)) (*-monoˡ-≤ 8 suc-revByte≤n)

physicalBitPos-BE-bounded-any : ∀ n b → 1 ≤ n → physicalBitPos n BigEndian b < n * 8
physicalBitPos-BE-bounded-any (suc n') b _ = <-≤-trans step1 step2
  where
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
