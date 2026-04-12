{-# OPTIONS --safe --without-K #-}

-- Write-set algebra and injection commutativity proofs.
--
-- Purpose: Prove that disjoint bit injections commute via write-set decomposition.
-- Exports: BitWrite, applyWrite, applyWrites, writesOf (write-set types),
--   injectBits-commute, payloadIso-involutive, injectPayload-commute,
--   injectPayload-preserves-disjoint-same.
module Aletheia.CAN.Endianness.Properties.WriteSet where

open import Aletheia.CAN.Endianness using
  ( ByteOrder; LittleEndian; BigEndian
  ; updateSafe
  ; byteToBitVec; bitVecToByte
  ; extractBits; injectBits
  ; swapBytes
  ; payloadIso; injectPayload
  )
open import Aletheia.CAN.Frame using (Byte)
open import Aletheia.Data.BitVec using (BitVec; setBit; setBit-setBit-comm)
open import Aletheia.CAN.Endianness.Properties.Roundtrip using
  ( swapBytes-involutive
  ; bitVecToByte-roundtrip
  ; injectBits-preserves-disjoint
  )
open import Data.Vec using (Vec; []; _∷_)
open import Data.Fin using (Fin; fromℕ<; toℕ)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.Nat as Nat using (ℕ; zero; suc; _+_; _*_; _<_; _≤_; z≤n; s≤s; _%_; _/_)
open import Data.Nat.DivMod using (m%n<n; m≡m%n+[m/n]*n)
open import Data.Nat.Properties using (_≟_; <⇒≢; +-suc; ≤-refl; ≤-trans; n≤1+n; m<m+n; <-≤-trans; m≤n⇒m≤1+n)
open import Data.Bool using (Bool)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂; cong₂; _≢_)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Nullary using (yes; no)
open import Function using (_∘_)

-- ============================================================================
-- WRITE-SET TYPES (public, used by CrossOrder)
-- ============================================================================

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
