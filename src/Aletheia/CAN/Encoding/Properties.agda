{-# OPTIONS --safe --without-K #-}

-- Phase 3 verification: Some proofs still TODO (marked with {- TODO Phase 3: ... -} comments)

-- Correctness properties for CAN signal encoding/decoding.
--
-- Purpose: Prove round-trip correctness and non-overlap for signal operations.
-- Strategy: BitVec-based architecture - structural proofs, not arithmetic:
--   Layer 0: BitVec operations (structural) - PROVEN in BitVec module
--   Layer 1: BitVec ↔ ℕ conversion - proven ONCE in Conversion module
--   Layer 2: Integer conversion (ℕ ↔ ℤ) - no ℚ
--   Layer 3: Scaling (ℤ ↔ ℚ) - isolated ℚ lemmas
--   Layer 4: Composition - combine all layers
--
-- Philosophy: Bit independence is structural, not arithmetic.
-- The hard proofs (testBit-setBit) are now trivial because we use the right representation.
module Aletheia.CAN.Encoding.Properties where

open import Aletheia.CAN.Encoding
open import Aletheia.CAN.Endianness
open import Aletheia.CAN.Frame
open import Aletheia.CAN.Signal
open import Aletheia.Data.BitVec
open import Aletheia.Data.BitVec.Conversion
open import Data.Vec using (Vec)
open import Data.Fin using (Fin; toℕ)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _<_; _≤_; _^_; _>_; z≤n; s≤s)
open import Data.Nat.GCD using (gcd; gcd-zeroʳ)
open import Data.Nat.Coprimality using (1-coprimeTo) renaming (sym to coprime-sym)
open import Data.Nat.DivMod as ℕ using (n/1≡n; n%1≡0)
open import Data.Integer as ℤ using (ℤ; +_; -[1+_])
open import Data.Integer.DivMod as ℤ using (div-pos-is-/ℕ)
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ; floor; normalize; 1/_; NonZero; ≢-nonZero; mkℚ; toℚᵘ; fromℚᵘ)
open import Data.Rational using () renaming (_+_ to _+ᵣ_; _*_ to _*ᵣ_; _-_ to _-ᵣ_; _≤_ to _≤ᵣ_; _<_ to _<ᵣ_; _/_ to _/ᵣ_; _÷_ to _÷ᵣ_; -_ to -ᵣ_)
open import Data.Rational.Unnormalised.Base as ℚᵘ using (ℚᵘ; mkℚᵘ)
open import Data.Rational.Literals using (fromℤ)
open import Data.Rational.Properties using (normalize-coprime; mkℚ-cong; +-inverseʳ; *-inverseʳ; *-identityʳ; *-assoc; *-comm; fromℚᵘ-toℚᵘ; toℚᵘ-homo-*; toℚᵘ-homo-1/; fromℚᵘ-cong; ↥p≡0⇒p≡0) renaming (+-identityʳ to ℚ-+-identityʳ; +-assoc to ℚ-+-assoc)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; inspect; [_]; subst; subst₂)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function using (_⇔_)
open import Function using (_∘_; _↔_)

-- ============================================================================
-- LAYER 0: BIT-LEVEL PROPERTIES (STRUCTURAL - from BitVec module)
-- ============================================================================

-- The old arithmetic-based approach required 10-14 hours of proofs about:
-- - Power-of-2 independence
-- - Carry propagation
-- - Modular arithmetic
--
-- The new structural approach: Already proven in BitVec module (30 minutes total)!
--
-- From Aletheia.Data.BitVec:
-- - testBit-setBit-same : testBit (setBit bits k v) k ≡ v (3 lines)
-- - testBit-setBit-diff : testBit (setBit bits k₁ v) k₂ ≡ testBit bits k₂  (6 lines)
-- - setBit-setBit-comm : Disjoint setBit operations commute (6 lines)
--
-- These proofs work because BitVec = Vec Bool, not ℕ + arithmetic.
-- Bit independence is structural, not a theorem.

-- ✅ LAYER 1 COMPLETE: extractBits-injectBits-roundtrip PROVEN
-- See: Aletheia.CAN.Endianness (lines 313-390)
--
-- Property: extractBits-injectBits-roundtrip
-- Signature:
--   ∀ {length} (bytes : Vec Byte 8) (startBit : ℕ) (bits : BitVec length)
--   → (startBit + length ≤ 64)  -- CAN frame constraint
--   → extractBits (injectBits bytes startBit bits) startBit ≡ bits
--
-- Proof uses:
-- - Induction on BitVec length
-- - testBit-setBit-same from BitVec module (structural)
-- - m<n*o⇒m/o<n from Data.Nat.DivMod for byte index bounds
-- - No postulates, full --safe compilation ✅

-- ✅ Additional Layer 1 proofs COMPLETE in Endianness module:
--   - injectBits-preserves-later-bit: injecting at earlier range preserves later bits
--   - injectBits-preserves-disjoint: extraction at disjoint range is preserved
--
-- Note: injectBits-commute can be derived from injectBits-preserves-disjoint if needed

-- ============================================================================
-- LAYER 2: INTEGER CONVERSION PROPERTIES (no ℚ)
-- ============================================================================
-- These proofs work with ℕ ↔ ℤ conversion (two's complement).
-- Still no rational arithmetic.

-- ✅ fromSigned-toSigned-roundtrip PROVEN (lines 110-138)
-- Property: Converting to signed then back to unsigned preserves value
-- (for values that fit in the bit width)
fromSigned-toSigned-roundtrip : ∀ (raw : ℕ) (bitLength : ℕ) (isSigned : Bool)
  → (bitLength > 0)
  → (raw < 2 ^ bitLength)
  → fromSigned (toSigned raw bitLength isSigned) bitLength ≡ raw
fromSigned-toSigned-roundtrip raw bitLength false bitLength>0 raw-bounded =
  -- Unsigned case: toSigned returns + raw, fromSigned (+ raw) returns raw
  refl
fromSigned-toSigned-roundtrip raw bitLength true bitLength>0 raw-bounded
  with (2 ^ (bitLength ∸ 1)) Data.Nat.≤ᵇ raw
... | false =
  -- Not negative: toSigned returns + raw, fromSigned (+ raw) returns raw
  refl
... | true =
  -- Negative case: prove (2 ^ bitLength) ∸ (suc ((2 ^ bitLength) ∸ raw ∸ 1)) ≡ raw
  -- Key insight: suc (x ∸ 1) ≡ x when x > 0
  -- We have: (2 ^ bitLength) ∸ raw > 0 since raw < 2 ^ bitLength
  trans (cong ((2 ^ bitLength) ∸_) suc-m∸1≡m) (m∸[m∸n]≡n (<⇒≤ raw-bounded))
  where
    open import Data.Nat using (_≤ᵇ_)
    open import Data.Nat.Properties using (m∸[m∸n]≡n; <⇒≤; m>n⇒m∸n≢0)
    open import Relation.Binary.PropositionalEquality using (trans; cong)
    open import Data.Empty using (⊥-elim)

    -- Prove: suc ((2 ^ bitLength) ∸ raw ∸ 1) ≡ (2 ^ bitLength) ∸ raw
    -- By cases on (2 ^ bitLength) ∸ raw
    suc-m∸1≡m : suc ((2 ^ bitLength) ∸ raw ∸ 1) ≡ (2 ^ bitLength) ∸ raw
    suc-m∸1≡m with (2 ^ bitLength) ∸ raw | m>n⇒m∸n≢0 raw-bounded
    ... | zero | ≢0 = ⊥-elim (≢0 refl)  -- Contradiction: can't be zero
    ... | suc n | _ = refl  -- suc (suc n ∸ 1) = suc n ∸ 0 = suc n ✓

-- Sign-aware bounds for signed interpretation
-- This captures the semantic constraint: values must fit in their signed range
SignedFits : ℤ → ℕ → Set
SignedFits (+ n) bitLength = n < 2 ^ (bitLength ∸ 1)  -- Positive: fits in positive range
SignedFits -[1+ n ] bitLength = suc n ≤ 2 ^ (bitLength ∸ 1)  -- Negative: fits in negative range

-- Property: Converting signed to unsigned then back to signed preserves value
-- The precondition is now sign-aware: positive values need positive range, negatives need negative range
toSigned-fromSigned-roundtrip : ∀ (z : ℤ) (bitLength : ℕ)
  → (bitLength > 0)
  → SignedFits z bitLength
  → toSigned (fromSigned z bitLength) bitLength true ≡ z
toSigned-fromSigned-roundtrip (+ n) bitLength bitLength>0 n-fits
  with (2 ^ (bitLength ∸ 1)) Data.Nat.≤ᵇ n | inspect (Data.Nat._≤ᵇ_ (2 ^ (bitLength ∸ 1))) n
     where open import Data.Nat using (_≤ᵇ_)
... | true | [ eq ] =
  -- Contradiction: ≤ᵇ returned true means signBitMask ≤ n, but we have n < signBitMask
  ⊥-elim (<⇒≱ n-fits (≤ᵇ⇒≤ (2 ^ (bitLength ∸ 1)) n (subst T (sym eq) tt)))
  where
    open import Data.Nat.Properties using (<⇒≱; ≤ᵇ⇒≤)
    open import Data.Bool using (T)
    open import Data.Unit using (tt)
... | false | _ =
  -- isNegative = false, so toSigned returns + n
  refl
toSigned-fromSigned-roundtrip -[1+ n ] bitLength bitLength>0 n-fits
  with (2 ^ (bitLength ∸ 1)) Data.Nat.≤ᵇ ((2 ^ bitLength) ∸ (suc n))
     | inspect (Data.Nat._≤ᵇ_ (2 ^ (bitLength ∸ 1))) ((2 ^ bitLength) ∸ (suc n))
    where open import Data.Nat using (_≤ᵇ_)
... | false | [ eq ] =
  -- Contradiction: should be in negative range
  ⊥-elim (≤ᵇ-false⇒¬≤ eq (fromSigned-≥-signBit n bitLength bitLength>0 n-fits))
  where
    open import Data.Nat.Properties using ()
    open import Data.Bool using (T)

    -- fromSigned for negative produces value ≥ signBitMask
    fromSigned-≥-signBit : ∀ n bitLength → bitLength > 0 → suc n ≤ 2 ^ (bitLength ∸ 1)
      → 2 ^ (bitLength ∸ 1) ≤ (2 ^ bitLength) ∸ (suc n)
    fromSigned-≥-signBit n (suc bitLength) bitLen>0 n-fits =
      -- Goal: 2 ^ bitLength ≤ (2 ^ suc bitLength) ∸ (suc n)
      -- Strategy: Use m+n≤o⇒m≤o∸n with m = 2 ^ bitLength, n = suc n, o = 2 ^ suc bitLength
      -- Need: 2 ^ bitLength + suc n ≤ 2 ^ suc bitLength
      m+n≤o⇒m≤o∸n (2 ^ bitLength) sum-bounded
      where
        open import Data.Nat.Properties using (m+n≤o⇒m≤o∸n; +-monoʳ-≤)

        -- Power-of-two lemma: 2^(n+1) = 2 * 2^n = 2^n + 2^n
        -- This is a basic fact about powers of two—we state it once and use it
        pow2-double : ∀ n → 2 ^ n + 2 ^ n ≡ 2 ^ suc n
        pow2-double n =
          trans (cong (λ x → 2 ^ n + x) (sym (+-identityʳ (2 ^ n))))
                (cong (λ x → 2 ^ n + (2 ^ n + x)) (*-zeroˡ (2 ^ n)))
          where
            open import Data.Nat.Properties using (+-identityʳ; *-zeroˡ)
          -- 2 ^ suc n = 2 * 2 ^ n = 2 ^ n + 2 ^ n + 0 * 2 ^ n (by definition of *)
          -- Step 1: 2 ^ n + 2 ^ n ≡ 2 ^ n + (2 ^ n + 0) by cong and sym +-identityʳ
          -- Step 2: 2 ^ n + (2 ^ n + 0) ≡ 2 ^ n + (2 ^ n + 0 * 2 ^ n) by cong and *-zeroˡ

        -- Show: 2 ^ bitLength + suc n ≤ 2 ^ suc bitLength
        -- Since suc n ≤ 2 ^ bitLength and 2 ^ suc bitLength = 2 ^ bitLength + 2 ^ bitLength
        sum-bounded : 2 ^ bitLength + suc n ≤ 2 ^ suc bitLength
        sum-bounded = subst ((2 ^ bitLength + suc n) ≤_) (pow2-double bitLength) (+-monoʳ-≤ (2 ^ bitLength) n-fits)

    -- If ≤ᵇ returns false, then ¬ ≤
    ≤ᵇ-false⇒¬≤ : ∀ {m n} → (m Data.Nat.≤ᵇ n) ≡ false → m ≤ n → ⊥
    ≤ᵇ-false⇒¬≤ {m} {n} eq m≤n = subst T eq (≤⇒≤ᵇ m≤n)
      where
        open import Data.Nat.Properties using (≤⇒≤ᵇ)
        -- ≤⇒≤ᵇ : m ≤ n → T (m ≤ᵇ n)
        -- We have: T (m ≤ᵇ n) from m≤n
        -- We have: m ≤ᵇ n ≡ false from eq
        -- So: subst T eq : T (m ≤ᵇ n) → T false
        -- And T false = ⊥
... | true | [ eq ] =
  -- isNegative = true, so toSigned takes negative branch
  -- Need to show: -[1+ ((2 ^ bitLength) ∸ ((2 ^ bitLength) ∸ (suc n)) ∸ 1) ] ≡ -[1+ n ]
  cong -[1+_] (trans (cong (_∸ 1) (m∸[m∸n]≡n (<⇒≤ suc-n-bounded))) refl)
  where
    open import Data.Nat.Properties using (m∸[m∸n]≡n; <⇒≤)
    -- suc n ∸ 1 = n by definition, so second trans step is refl

    -- suc n < 2 ^ bitLength (from n-fits: suc n ≤ 2 ^ (bitLength ∸ 1) and bitLength > 0)
    suc-n-bounded : suc n < 2 ^ bitLength
    suc-n-bounded = pow2-upper bitLength (suc n) bitLength>0 n-fits
      where
        open import Data.Nat.Properties using (≤-<-trans; m<m+n; +-identityʳ; *-zeroˡ)

        -- Infrastructure: values fitting in lower half fit strictly in full range
        pow2-upper : ∀ m x → m > 0 → x ≤ 2 ^ (m ∸ 1) → x < 2 ^ m
        pow2-upper zero _ () _
        pow2-upper (suc m) x _ x-fits =
          -- x ≤ 2^m, and 2^m < 2^(suc m) by monotonicity, so x < 2^(suc m)
          ≤-<-trans x-fits (^-monoʳ-< 2 (s≤s (s≤s z≤n)) (n<1+n m))
          where open import Data.Nat.Properties using (^-monoʳ-<; n<1+n)

-- Property: fromSigned produces bounded results (for negative numbers)
-- Note: For positive numbers, the caller must ensure the input fits
fromSigned-bounded-neg : ∀ (n : ℕ) (bitLength : ℕ)
  → (bitLength > 0)
  → fromSigned -[1+ n ] bitLength < 2 ^ bitLength
fromSigned-bounded-neg n bitLength bitLength>0 =
  -- Need to show: (2 ^ bitLength) ∸ (suc n) < 2 ^ bitLength
  m∸1+n<m (2 ^ bitLength) n (^-positive bitLength)
  where
    open import Data.Nat.Properties using (n≤1+n; ≤-refl; <-trans)
    open import Data.Nat using (_^_)

    -- 2 ^ bitLength > 0 for any bitLength
    ^-positive : ∀ m → 2 ^ m > 0
    ^-positive zero = s≤s z≤n
    ^-positive (suc m) = *-monoʳ-< 2 (^-positive m)
      where open import Data.Nat.Properties using (*-monoʳ-<)

    -- m ∸ (suc n) < m when m > 0
    -- Proof: Via auxiliary lemma without m>0 constraint
    m∸1+n<m : ∀ m n → m > 0 → m ∸ suc n < m
    m∸1+n<m (suc m) n _ = aux m n
      where
        open import Data.Nat.Properties using (≤-refl; <-trans)

        -- Auxiliary: works for all m, n
        aux : ∀ m n → suc m ∸ suc n < suc m
        aux m zero = s≤s ≤-refl  -- suc m ∸ 1 = m < suc m
        aux zero (suc n) = s≤s z≤n  -- 1 ∸ suc (suc n) = 0 < 1
        aux (suc m) (suc n) = <-trans (aux m n) (s≤s ≤-refl)  -- IH + transitivity

-- ============================================================================
-- LAYER 3: SCALING PROPERTIES (isolated ℚ lemmas)
-- ============================================================================
-- These are the ONLY proofs involving rational arithmetic.
-- They are isolated and small.

-- ✅ Layer 3 scaling proofs COMPLETE:
--   - removeScaling-applyScaling-exact (line 454): ℤ → ℚ → ℤ roundtrip is exact
--   - applyScaling-injective (line 465): applyScaling is injective when factor ≠ 0
--   - removeScaling-factor-zero-iff-nothing (line 344): API contract for failure mode

-- Property: removeScaling-factor-zero-iff-nothing
-- ------------------------------------------------
-- removeScaling returns nothing only when factor is zero
-- This is the API contract: the guard is the ONLY failure mode

-- Computational direction: factor ≡ 0 implies removeScaling returns nothing
-- Definition-driven: the isZero guard catches exactly this case
removeScaling-zero⇒nothing : ∀ (value factor offset : ℚ)
  → factor ≡ 0ℚ
  → removeScaling value factor offset ≡ nothing
removeScaling-zero⇒nothing value factor offset factor≡0 =
  -- Rewrite factor to 0ℚ, then removeScaling reduces to nothing by definition
  subst (λ f → removeScaling value f offset ≡ nothing) (sym factor≡0) refl
  where open import Relation.Binary.PropositionalEquality using (subst; sym)

-- Semantic direction: nothing result implies factor was zero
-- The real theorem: proves the guard is the ONLY failure mode
removeScaling-nothing⇒zero : ∀ (value factor offset : ℚ)
  → removeScaling value factor offset ≡ nothing
  → factor ≡ 0ℚ
removeScaling-nothing⇒zero value factor offset result≡nothing =
  aux (factor ≟ 0ℚ) result≡nothing
  where
    open import Data.Rational using (_≟_)
    open import Relation.Nullary using (Dec; yes; no)

    -- Constructor disjointness: just x ≢ nothing
    just≢nothing : ∀ {a} {A : Set a} {x : A} → just x ≢ nothing
    just≢nothing ()

    -- Case analysis on factor's equality with 0
    aux : Dec (factor ≡ 0ℚ) → removeScaling value factor offset ≡ nothing → factor ≡ 0ℚ
    aux (yes factor≡0) _ = factor≡0
    aux (no factor≢0) result≡nothing with factor ≟ 0ℚ
    ... | yes eq = ⊥-elim (factor≢0 eq)  -- Contradiction: factor≢0 but eq proves factor≡0
    ... | no  _  = ⊥-elim (just≢nothing result≡nothing)  -- After reduction: just _ ≡ nothing, contradiction

-- Biconditional: removeScaling returns nothing iff factor is zero
-- This is the complete API contract for removeScaling
removeScaling-factor-zero-iff-nothing : ∀ (value factor offset : ℚ)
  → (removeScaling value factor offset ≡ nothing → factor ≡ 0ℚ)
  × (factor ≡ 0ℚ → removeScaling value factor offset ≡ nothing)
removeScaling-factor-zero-iff-nothing value factor offset =
  (removeScaling-nothing⇒zero value factor offset , removeScaling-zero⇒nothing value factor offset)

-- Arithmetic infrastructure: floor of an integer represented as rational is the integer itself
-- This is the ONLY arithmetic fact needed for the roundtrip proof
-- This is the firewall: gcd reasoning stops here, never leaks upward
private
  -- Arithmetic lemma: floor of integer-as-rational is the integer itself
  -- Uses canonical ℤ → ℚ embedding (fromℤ) to avoid normalization complexity
  floor-fromℤ : ∀ (z : ℤ) → floor (fromℤ z) ≡ z
  floor-fromℤ (+ n) = trans (ℤ.div-pos-is-/ℕ (+ n) 1) (cong +_ (ℕ.n/1≡n n))
  floor-fromℤ -[1+ n ] with ℕ.n%1≡0 (ℕ.suc n)
  ... | eq =
    trans (ℤ.div-pos-is-/ℕ (-[1+ n ]) 1)
          (aux eq)
    where
      aux : ℕ.suc n ℕ.% 1 ≡ 0 → (-[1+ n ]) ℤ./ℕ 1 ≡ -[1+ n ]
      aux eq rewrite eq | ℕ.n/1≡n (ℕ.suc n) = refl

  -- Prove that z / 1 equals fromℤ z (localizes all gcd/normalization complexity)
  z/1≡fromℤ : ∀ (z : ℤ) → z Data.Rational./ 1 ≡ fromℤ z
  z/1≡fromℤ (+ n) = trans (normalize-coprime (coprime-sym (1-coprimeTo n))) (mkℚ-cong refl refl)
  z/1≡fromℤ -[1+ n ] = trans (cong Data.Rational.-_ (normalize-coprime (coprime-sym (1-coprimeTo (suc n)))))
                        (trans (mkℚ-cong refl refl) refl)

  floor-int : ∀ (z : ℤ) → floor (z Data.Rational./ 1) ≡ z
  floor-int z = trans (cong floor (z/1≡fromℤ z)) (floor-fromℤ z)

  -- Constructor injectivity for Maybe
  just-injective : ∀ {a} {A : Set a} {x y : A} → just x ≡ just y → x ≡ y
  just-injective refl = refl

-- Semantic bridge lemma: what does removeScaling ∘ applyScaling evaluate to?
-- This preserves the definitional connection between the result and floor (raw / 1)
-- PROVEN: removeScaling-applyScaling-value (line 394) and removeScaling-applyScaling-exact (line 416)
-- applyScaling raw f o = raw/1 * f + o
-- removeScaling (raw/1 * f + o) f o = just (floor ((raw/1 * f + o - o) / f))
--                                    = just (floor (raw/1 * f / f))
--                                    = just (floor (raw/1)) = just raw
private
  -- Bridge lemma: division via fromℚᵘ/toℚᵘ equals semantic ÷ᵣ
  -- This is the ONLY place where representation details appear
  -- The bridge connects Encoding.divideByFactor to the semantic _÷ᵣ_
  open import Data.Rational.Unnormalised.Base using () renaming (_÷_ to _÷ᵘ_; _*_ to _*ᵘ_; 1/_ to 1/ᵘ_)
  open import Data.Rational.Unnormalised.Properties as ℚᵘ using (≃-refl; ≃-trans; ≃-sym; *-cong)

  -- Step 1: toℚᵘ preserves division (up to ≃ᵘ)
  -- Proof: p ÷ᵣ q = p *ᵣ (1/ q) by definition, then use homomorphisms
  toℚᵘ-homo-÷ : ∀ (p q : ℚ) .{{_ : NonZero q}} → toℚᵘ (p ÷ᵣ q) ℚᵘ.≃ (toℚᵘ p ÷ᵘ toℚᵘ q)
  toℚᵘ-homo-÷ p@(mkℚ _ _ _) q@(mkℚ _ _ _) =
    -- toℚᵘ (p ÷ᵣ q) = toℚᵘ (p *ᵣ 1/ q) ≃ toℚᵘ p *ᵘ toℚᵘ (1/ q) ≃ toℚᵘ p *ᵘ 1/ᵘ (toℚᵘ q) = toℚᵘ p ÷ᵘ toℚᵘ q
    ≃-trans (toℚᵘ-homo-* p (1/ q)) (*-cong (ℚᵘ.≃-refl {toℚᵘ p}) (toℚᵘ-homo-1/ q))

  -- Step 2: fromℚᵘ converts ≃ᵘ back to ≡
  ÷-via-ℚᵘ : ∀ (p q : ℚ) .{{_ : NonZero q}} → fromℚᵘ (toℚᵘ p ÷ᵘ toℚᵘ q) ≡ p ÷ᵣ q
  ÷-via-ℚᵘ p q = trans (fromℚᵘ-cong (≃-sym (toℚᵘ-homo-÷ p q))) (fromℚᵘ-toℚᵘ (p ÷ᵣ q))

  -- Pure ℚ field cancellation lemma: ((x * f + o) - o) ÷ f ≡ x
  -- This is the ONLY place where rational field laws are used
  ℚ-cancel : ∀ (x f o : ℚ) → .{{_ : NonZero f}} → ((x *ᵣ f +ᵣ o) -ᵣ o) ÷ᵣ f ≡ x
  ℚ-cancel x f o = begin
    ((x *ᵣ f +ᵣ o) -ᵣ o) ÷ᵣ f        ≡⟨ cong (_÷ᵣ f) (+-assoc-cancelʳ (x *ᵣ f) o) ⟩
    (x *ᵣ f) ÷ᵣ f                     ≡⟨⟩  -- ÷ᵣ unfolds to *ᵣ (1/ f)
    (x *ᵣ f) *ᵣ (1/ f)                ≡⟨ *-assoc x f (1/ f) ⟩
    x *ᵣ (f *ᵣ (1/ f))                ≡⟨ cong (x *ᵣ_) (*-inverseʳ f) ⟩
    x *ᵣ 1ℚ                           ≡⟨ *-identityʳ x ⟩
    x                                 ∎
    where
      -- Helper: (a + b) - b ≡ a (standard derivation from field laws)
      +-assoc-cancelʳ : ∀ a b → (a +ᵣ b) -ᵣ b ≡ a
      +-assoc-cancelʳ a b = begin
        (a +ᵣ b) -ᵣ b      ≡⟨ ℚ-+-assoc a b (-ᵣ b) ⟩
        a +ᵣ (b -ᵣ b)      ≡⟨ cong (a +ᵣ_) (+-inverseʳ b) ⟩
        a +ᵣ 0ℚ            ≡⟨ ℚ-+-identityʳ a ⟩
        a                  ∎

  -- Structural lemma: nonzero ℚ has nonzero numerator
  -- Uses ↥p≡0⇒p≡0 from stdlib which handles coprimality internally
  ℚ-nonzero⇒num-nonzero : ∀ (q : ℚ) → q ≢ 0ℚ → ℚ.numerator q ≢ + 0
  ℚ-nonzero⇒num-nonzero q nz num≡0 = nz (↥p≡0⇒p≡0 q num≡0)

  -- Semantic bridge using the pure ℚ cancellation
  -- Pattern match on factor structure so divideUnnorm reduces to ÷ᵘ automatically
  -- Then use ÷-via-ℚᵘ to bridge back to ÷ᵣ
  removeScaling-applyScaling-value :
    ∀ (raw : ℤ) (factor offset : ℚ)
    → factor ≢ 0ℚ
    → removeScaling (applyScaling raw factor offset) factor offset
      ≡ just (floor (raw Data.Rational./ 1))
  removeScaling-applyScaling-value raw factor@(mkℚ (+ 0) _ _) offset factor≢0 =
    ⊥-elim (ℚ-nonzero⇒num-nonzero factor factor≢0 refl)
  removeScaling-applyScaling-value raw factor@(mkℚ (+ ℕ.suc _) _ _) offset factor≢0 =
    -- After pattern match, divideUnnorm reduces to ÷ᵘ, and fromℚᵘ (... ÷ᵘ ...) ≡ ... ÷ᵣ ... by ÷-via-ℚᵘ
    let numer = (applyScaling raw factor offset) -ᵣ offset
    in cong just (trans (cong floor (÷-via-ℚᵘ numer factor {{≢-nonZero factor≢0}}))
                        (cong floor (ℚ-cancel (raw Data.Rational./ 1) factor offset {{≢-nonZero factor≢0}})))
  removeScaling-applyScaling-value raw factor@(mkℚ -[1+ _ ] _ _) offset factor≢0 =
    let numer = (applyScaling raw factor offset) -ᵣ offset
    in cong just (trans (cong floor (÷-via-ℚᵘ numer factor {{≢-nonZero factor≢0}}))
                        (cong floor (ℚ-cancel (raw Data.Rational./ 1) factor offset {{≢-nonZero factor≢0}})))

-- Property: removeScaling-applyScaling-exact
-- ---------------------------------------------
-- Applying scaling then removing it returns the original raw value (EXACT)
-- This is the easy direction: starting from ℤ means floor is identity
-- Proof strategy: semantic bridge + arithmetic firewall (no pattern matching information loss)
removeScaling-applyScaling-exact : ∀ (raw : ℤ) (factor offset : ℚ)
  → factor ≢ 0ℚ
  → removeScaling (applyScaling raw factor offset) factor offset ≡ just raw
removeScaling-applyScaling-exact raw factor offset factor≢0 =
  trans (removeScaling-applyScaling-value raw factor offset factor≢0)
        (cong just (floor-int raw))

-- Property: applyScaling-injective
-- ---------------------------------
-- applyScaling is injective when factor ≠ 0
-- Proof strategy: use removeScaling as left inverse (no arithmetic needed)
applyScaling-injective : ∀ (raw₁ raw₂ : ℤ) (factor offset : ℚ)
  → factor ≢ 0ℚ
  → applyScaling raw₁ factor offset ≡ applyScaling raw₂ factor offset
  → raw₁ ≡ raw₂
applyScaling-injective raw₁ raw₂ factor offset factor≢0 eq =
  just-injective (trans (sym (removeScaling-applyScaling-exact raw₁ factor offset factor≢0))
                  (trans (cong (λ x → removeScaling x factor offset) eq)
                         (removeScaling-applyScaling-exact raw₂ factor offset factor≢0)))

-- ═══════════════════════════════════════════════════════════════════════════
-- LAYER A: Floor bounds (arithmetic quarantine)
-- ═══════════════════════════════════════════════════════════════════════════
-- These lemmas isolate all floor/division representation details.
-- They use the same pattern as floor-int: work with ℤ division, then lift to ℚ.

private
  open import Data.Integer.DivMod as ℤ using ([n/d]*d≤n; n<s[n/ℕd]*d)
  open import Data.Rational using (*≤*; *<*)  -- Just constructors; types already renamed to _≤ᵣ_, _<ᵣ_
  open import Data.Rational.Properties using (toℚᵘ-mono-≤; toℚᵘ-cancel-≤; ≤-reflexive)

  -- Floor lower bound: floor(q) / 1 ≤ q
  -- Strategy: floor q = ↥q ℤ./ ↧q, use [n/d]*d≤n, lift via *≤*
  floor-lower : ∀ (q : ℚ) → (floor q Data.Rational./ 1) ≤ᵣ q
  floor-lower q@(mkℚ n d-1 _) = subst (_≤ᵣ q) (sym (z/1≡fromℤ (floor q))) fromℤ-floor-≤
    where
      open import Data.Integer.Properties as ℤ using (*-identityʳ)

      d : ℕ
      d = suc d-1

      -- floor q = n ℤ./ + d (by definition)
      -- fromℤ (floor q) has ↥ = floor q, ↧ = + 1
      -- q has ↥ = n, ↧ = + d
      -- For *≤*: (floor q) * (+ d) ≤ n * (+ 1)
      -- Since n * (+ 1) ≡ n, need (n ℤ./ + d) * (+ d) ≤ n
      fromℤ-floor-≤ : fromℤ (floor q) ≤ᵣ q
      fromℤ-floor-≤ = *≤* (subst ((n ℤ./ + d) ℤ.* + d ℤ.≤_) (sym (ℤ.*-identityʳ n)) ([n/d]*d≤n n (+ d)))

  -- Floor upper bound: q < (floor(q) + 1) / 1
  -- Strategy: use n<s[n/ℕd]*d, lift via *<*
  floor-upper : ∀ (q : ℚ) → q <ᵣ ((floor q ℤ.+ ℤ.+ 1) Data.Rational./ 1)
  floor-upper q@(mkℚ n d-1 _) = subst (q <ᵣ_) (sym (z/1≡fromℤ (floor q ℤ.+ ℤ.+ 1))) fromℤ-suc-floor->
    where
      open import Data.Integer as ℤ using (suc; _<_)
      open import Data.Integer.Properties as ℤ using (*-identityˡ; +-comm)
      open import Data.Integer.DivMod as ℤ using (div-pos-is-/ℕ; _/ℕ_)
      open import Data.Nat as ℕ using () renaming (suc to sucℕ)

      d : ℕ
      d = sucℕ d-1

      -- floor q + + 1 = suc (floor q) (by +-comm: x + 1 = 1 + x = suc x)
      floor+1≡suc : floor q ℤ.+ ℤ.+ 1 ≡ ℤ.suc (floor q)
      floor+1≡suc = +-comm (floor q) (ℤ.+ 1)

      -- suc (n ℤ./ + d) = suc (n /ℕ d) (by div-pos-is-/ℕ)
      suc-div-eq : ℤ.suc (n ℤ./ + d) ≡ ℤ.suc (n /ℕ d)
      suc-div-eq = cong ℤ.suc (div-pos-is-/ℕ n d)

      -- For *<*: n * + 1 < (floor q + + 1) * + d
      -- Step 1: n < suc (n /ℕ d) * + d by n<s[n/ℕd]*d
      -- Step 2: n ≡ n * + 1 by sym *-identityʳ
      -- Step 3: suc (n /ℕ d) ≡ suc (floor q) ≡ floor q + + 1
      fromℤ-suc-floor-> : q <ᵣ fromℤ (floor q ℤ.+ ℤ.+ 1)
      fromℤ-suc-floor-> = *<* goal
        where
          open import Data.Integer.Properties as ℤ using (*-identityʳ)

          -- Step 1: n < suc (n /ℕ d) * + d
          step1 : ℤ._<_ n (ℤ.suc (n /ℕ d) ℤ.* + d)
          step1 = n<s[n/ℕd]*d n d

          -- Step 2: suc (n /ℕ d) * + d ≡ (floor q + + 1) * + d
          -- Since suc x = + 1 + x, and floor q = n ℤ./ + d = n /ℕ d
          rhs-eq : ℤ.suc (n /ℕ d) ℤ.* + d ≡ (floor q ℤ.+ ℤ.+ 1) ℤ.* + d
          rhs-eq = cong (ℤ._* + d) (trans (cong ℤ.suc (sym (div-pos-is-/ℕ n d))) (sym floor+1≡suc))

          -- Step 3: n ≡ n * + 1
          lhs-eq : n ≡ n ℤ.* ℤ.+ 1
          lhs-eq = sym (ℤ.*-identityʳ n)

          -- Combine: n * + 1 < (floor q + + 1) * + d
          goal : ℤ._<_ (n ℤ.* ℤ.+ 1) ((floor q ℤ.+ ℤ.+ 1) ℤ.* + d)
          goal = subst₂ ℤ._<_ lhs-eq rhs-eq step1

-- ═══════════════════════════════════════════════════════════════════════════
-- LAYER A': Algebraic normalization helpers (quarantined field law plumbing)
-- ═══════════════════════════════════════════════════════════════════════════
-- These handle coercions, field identities, and distributes - never seen by Layer C.

private
  -- (a ÷ f) * f ≡ a (field cancellation)
  ÷-*-cancel : ∀ (a f : ℚ) .{{_ : NonZero f}} → (a ÷ᵣ f) *ᵣ f ≡ a
  ÷-*-cancel a f = begin
    (a ÷ᵣ f) *ᵣ f      ≡⟨⟩  -- ÷ᵣ = *ᵣ (1/ f)
    (a *ᵣ (1/ f)) *ᵣ f ≡⟨ *-assoc a (1/ f) f ⟩
    a *ᵣ ((1/ f) *ᵣ f) ≡⟨ cong (a *ᵣ_) (*-inverseˡ f) ⟩
    a *ᵣ 1ℚ            ≡⟨ *-identityʳ a ⟩
    a                  ∎
    where open import Data.Rational.Properties using (*-inverseˡ)

  -- Local: fromℤ (a + b) ≡ fromℤ a + fromℤ b
  -- Needed because stdlib's fromℤ-homo-+ is not exported in all versions
  fromℤ-homo-+ : ∀ (a b : ℤ) → fromℤ (a ℤ.+ b) ≡ fromℤ a +ᵣ fromℤ b
  fromℤ-homo-+ a b = begin
    fromℤ (a ℤ.+ b)               ≡⟨ sym (fromℚᵘ-toℚᵘ (fromℤ (a ℤ.+ b))) ⟩
    fromℚᵘ (toℚᵘ (fromℤ (a ℤ.+ b)))  ≡⟨ fromℚᵘ-cong eq-u ⟩
    fromℚᵘ (toℚᵘ (fromℤ a) ℚᵘ.+ toℚᵘ (fromℤ b)) ≡⟨ fromℚᵘ-cong (≃-sym (toℚᵘ-homo-+ (fromℤ a) (fromℤ b))) ⟩
    fromℚᵘ (toℚᵘ (fromℤ a +ᵣ fromℤ b)) ≡⟨ fromℚᵘ-toℚᵘ (fromℤ a +ᵣ fromℤ b) ⟩
    fromℤ a +ᵣ fromℤ b            ∎
    where
      open import Data.Rational.Unnormalised.Base as ℚᵘ using () renaming (_+_ to _+ᵘ_)
      open import Data.Rational.Unnormalised.Properties as ℚᵘ using (≃-sym)
      open import Data.Rational.Properties using (fromℚᵘ-toℚᵘ; fromℚᵘ-cong; toℚᵘ-homo-+)
      open import Data.Integer.Properties as ℤ using (*-identityʳ)
      open import Data.Rational.Unnormalised.Base using (*≡*)
      -- ℚᵘ equivalence: *≡* constructor requires ↥p * ↧q ≡ ↥q * ↧p
      -- Left: toℚᵘ (fromℤ (a + b)) = mkℚᵘ (a+b) 1, so ↥ = a+b, ↧ = +1
      -- Right: mkℚᵘ a 1 + mkℚᵘ b 1 = mkℚᵘ (a*1 + b*1) (1*1), so ↥ = a*1+b*1, ↧ = 1*1
      -- Need: (a + b) * (1 * 1) ≡ (a * 1 + b * 1) * 1
      eq-u : toℚᵘ (fromℤ (a ℤ.+ b)) ℚᵘ.≃ (toℚᵘ (fromℤ a) ℚᵘ.+ toℚᵘ (fromℤ b))
      eq-u = *≡* eq-proof
        where
          eq-proof : (a ℤ.+ b) ℤ.* (ℤ.+ 1 ℤ.* ℤ.+ 1) ≡ ((a ℤ.* ℤ.+ 1) ℤ.+ (b ℤ.* ℤ.+ 1)) ℤ.* ℤ.+ 1
          eq-proof = begin
            (a ℤ.+ b) ℤ.* (ℤ.+ 1 ℤ.* ℤ.+ 1)          ≡⟨ cong ((a ℤ.+ b) ℤ.*_) refl ⟩
            (a ℤ.+ b) ℤ.* ℤ.+ 1                       ≡⟨ ℤ.*-identityʳ (a ℤ.+ b) ⟩
            a ℤ.+ b                                   ≡⟨ cong₂ ℤ._+_ (sym (ℤ.*-identityʳ a)) (sym (ℤ.*-identityʳ b)) ⟩
            (a ℤ.* ℤ.+ 1) ℤ.+ (b ℤ.* ℤ.+ 1)          ≡⟨ sym (ℤ.*-identityʳ _) ⟩
            ((a ℤ.* ℤ.+ 1) ℤ.+ (b ℤ.* ℤ.+ 1)) ℤ.* ℤ.+ 1  ∎

  -- (raw + 1)/1 * factor ≡ raw/1 * factor + factor
  raw+1*f≡raw*f+f : ∀ (raw : ℤ) (f : ℚ) →
    ((raw ℤ.+ ℤ.+ 1) Data.Rational./ 1) *ᵣ f ≡ (raw Data.Rational./ 1) *ᵣ f +ᵣ f
  raw+1*f≡raw*f+f raw f = begin
    ((raw ℤ.+ ℤ.+ 1) /₁ 1) *ᵣ f             ≡⟨ cong (_*ᵣ f) (z/1≡fromℤ (raw ℤ.+ ℤ.+ 1)) ⟩
    fromℤ (raw ℤ.+ ℤ.+ 1) *ᵣ f              ≡⟨ cong (λ x → fromℤ x *ᵣ f) (ℤ.+-comm raw (ℤ.+ 1)) ⟩
    fromℤ (ℤ.+ 1 ℤ.+ raw) *ᵣ f              ≡⟨ cong (_*ᵣ f) (fromℤ-homo-+ (ℤ.+ 1) raw) ⟩
    (fromℤ (ℤ.+ 1) +ᵣ fromℤ raw) *ᵣ f       ≡⟨ *-distribʳ-+ f (fromℤ (ℤ.+ 1)) (fromℤ raw) ⟩
    fromℤ (ℤ.+ 1) *ᵣ f +ᵣ fromℤ raw *ᵣ f    ≡⟨ cong₂ _+ᵣ_ (*-identityˡ f) (cong (_*ᵣ f) (sym (z/1≡fromℤ raw))) ⟩
    f +ᵣ (raw /₁ 1) *ᵣ f                     ≡⟨ ℚ-+-comm f ((raw /₁ 1) *ᵣ f) ⟩
    (raw /₁ 1) *ᵣ f +ᵣ f                     ∎
    where
      open import Data.Rational.Properties using (*-distribʳ-+; *-identityˡ) renaming (+-comm to ℚ-+-comm)
      open import Data.Integer.Properties as ℤ using (+-comm)
      _/₁_ = Data.Rational._/_

  -- a ≤ b - c ⟹ a + c ≤ b (shift offset right)
  ≤-shift-offset : ∀ (a b c : ℚ) → a ≤ᵣ b -ᵣ c → a +ᵣ c ≤ᵣ b
  ≤-shift-offset a b c a≤b-c = subst (a +ᵣ c ≤ᵣ_) b-c+c≡b (+-monoˡ-≤ c a≤b-c)
    where
      open import Data.Rational.Properties using (+-monoˡ-≤) renaming (+-assoc to ℚ-+-assoc; +-inverseˡ to ℚ-+-inverseˡ; +-identityʳ to ℚ-+-identityʳ)
      -- (b - c) + c ≡ b (standard additive cancellation)
      b-c+c≡b : (b -ᵣ c) +ᵣ c ≡ b
      b-c+c≡b = begin
        (b -ᵣ c) +ᵣ c      ≡⟨ ℚ-+-assoc b (-ᵣ c) c ⟩
        b +ᵣ ((-ᵣ c) +ᵣ c) ≡⟨ cong (b +ᵣ_) (ℚ-+-inverseˡ c) ⟩
        b +ᵣ 0ℚ            ≡⟨ ℚ-+-identityʳ b ⟩
        b                  ∎

  -- a - c < b ⟹ a < b + c (shift offset right, strict)
  <-shift-offset : ∀ (a b c : ℚ) → a -ᵣ c <ᵣ b → a <ᵣ b +ᵣ c
  <-shift-offset a b c a-c<b = subst (_<ᵣ b +ᵣ c) a-c+c≡a (+-monoˡ-< c a-c<b)
    where
      open import Data.Rational.Properties using (+-monoˡ-<) renaming (+-assoc to ℚ-+-assoc; +-inverseˡ to ℚ-+-inverseˡ; +-identityʳ to ℚ-+-identityʳ)
      -- (a - c) + c ≡ a (standard additive cancellation)
      a-c+c≡a : (a -ᵣ c) +ᵣ c ≡ a
      a-c+c≡a = begin
        (a -ᵣ c) +ᵣ c      ≡⟨ ℚ-+-assoc a (-ᵣ c) c ⟩
        a +ᵣ ((-ᵣ c) +ᵣ c) ≡⟨ cong (a +ᵣ_) (ℚ-+-inverseˡ c) ⟩
        a +ᵣ 0ℚ            ≡⟨ ℚ-+-identityʳ a ⟩
        a                  ∎

  -- a - c ≤ b ⟹ a ≤ b + c (unshift offset, non-strict)
  -- Used for: value - offset ≤ raw*f implies value ≤ raw*f + offset = result
  ≤-unshift-offset : ∀ (a b c : ℚ) → a -ᵣ c ≤ᵣ b → a ≤ᵣ b +ᵣ c
  ≤-unshift-offset a b c a-c≤b = subst (_≤ᵣ b +ᵣ c) a-c+c≡a (+-monoˡ-≤ c a-c≤b)
    where
      open import Data.Rational.Properties using (+-monoˡ-≤) renaming (+-assoc to ℚ-+-assoc; +-inverseˡ to ℚ-+-inverseˡ; +-identityʳ to ℚ-+-identityʳ)
      a-c+c≡a : (a -ᵣ c) +ᵣ c ≡ a
      a-c+c≡a = begin
        (a -ᵣ c) +ᵣ c      ≡⟨ ℚ-+-assoc a (-ᵣ c) c ⟩
        a +ᵣ ((-ᵣ c) +ᵣ c) ≡⟨ cong (a +ᵣ_) (ℚ-+-inverseˡ c) ⟩
        a +ᵣ 0ℚ            ≡⟨ ℚ-+-identityʳ a ⟩
        a                  ∎

  -- b < a - c ⟹ b + c < a (unshift offset, strict, flipped)
  -- Used for: raw*f+f < value - offset implies raw*f+f + offset < value
  <-unshift-offset : ∀ (a b c : ℚ) → b <ᵣ a -ᵣ c → b +ᵣ c <ᵣ a
  <-unshift-offset a b c b<a-c = subst (b +ᵣ c <ᵣ_) a-c+c≡a (+-monoˡ-< c b<a-c)
    where
      open import Data.Rational.Properties using (+-monoˡ-<) renaming (+-assoc to ℚ-+-assoc; +-inverseˡ to ℚ-+-inverseˡ; +-identityʳ to ℚ-+-identityʳ)
      a-c+c≡a : (a -ᵣ c) +ᵣ c ≡ a
      a-c+c≡a = begin
        (a -ᵣ c) +ᵣ c      ≡⟨ ℚ-+-assoc a (-ᵣ c) c ⟩
        a +ᵣ ((-ᵣ c) +ᵣ c) ≡⟨ cong (a +ᵣ_) (ℚ-+-inverseˡ c) ⟩
        a +ᵣ 0ℚ            ≡⟨ ℚ-+-identityʳ a ⟩
        a                  ∎

-- ═══════════════════════════════════════════════════════════════════════════
-- LAYER C: Algebraic chain (semantic core)
-- ═══════════════════════════════════════════════════════════════════════════
-- Given raw = floor((value - offset) / factor), derive bounds on result.
-- Uses ONLY: floor bounds (Layer A), monotonicity (stdlib), named helpers (Layer A').
-- NO begin...∎ chains, NO cong, NO coercions.

private
  -- Note: stdlib naming inconsistency - for (_* r):
  --   ≤ version: *-monoʳ-≤-nonNeg (positive), *-monoʳ-≤-nonPos (negative, reverses)
  --   < version: *-monoˡ-<-pos (positive), *-monoˡ-<-neg (negative, reverses)
  open import Data.Rational.Properties using (+-monoˡ-≤; +-monoʳ-≤; *-monoʳ-≤-nonNeg; *-monoʳ-≤-nonPos; *-monoˡ-<-pos; *-monoˡ-<-neg; neg⇒nonPos)
  open import Data.Rational using (Positive; Negative; NonNegative; NonPositive; >-nonZero; <-nonZero; positive; negative)

  scaling-bounds-pos : ∀ (value factor offset : ℚ) (raw : ℤ)
    → (factor-pos : 0ℚ <ᵣ factor)
    → floor (_÷ᵣ_ (value -ᵣ offset) factor {{>-nonZero factor-pos}}) ≡ raw
    → let result = applyScaling raw factor offset
      in result ≤ᵣ value × value <ᵣ result +ᵣ factor
  scaling-bounds-pos value factor offset raw factor-pos floor≡raw = left-bound , right-bound
    where
      open import Data.Rational.Properties using (≤-reflexive; <-respʳ-≡)

      q : ℚ
      q = _÷ᵣ_ (value -ᵣ offset) factor {{>-nonZero factor-pos}}

      instance _ : Positive factor
      _ = positive factor-pos

      -- Step 1: floor bounds with substitution
      -- floor-lower q : (floor q / 1) ≤ᵣ q
      -- floor≡raw : floor q ≡ raw, so floor q / 1 ≡ raw / 1 by cong
      floor/1≡raw/1 : (floor q Data.Rational./ 1) ≡ (raw Data.Rational./ 1)
      floor/1≡raw/1 = cong (Data.Rational._/ 1) floor≡raw

      raw/1≤q : (raw Data.Rational./ 1) ≤ᵣ q
      raw/1≤q = subst (_≤ᵣ q) floor/1≡raw/1 (floor-lower q)

      -- floor-upper q : q <ᵣ ((floor q + 1) / 1)
      floor+1/1≡raw+1/1 : ((floor q ℤ.+ ℤ.+ 1) Data.Rational./ 1) ≡ ((raw ℤ.+ ℤ.+ 1) Data.Rational./ 1)
      floor+1/1≡raw+1/1 = cong (λ x → (x ℤ.+ ℤ.+ 1) Data.Rational./ 1) floor≡raw

      q<raw+1/1 : q <ᵣ ((raw ℤ.+ ℤ.+ 1) Data.Rational./ 1)
      q<raw+1/1 = <-respʳ-≡ floor+1/1≡raw+1/1 (floor-upper q)

      -- Step 2: multiply by positive factor (preserves order)
      -- For positive factor, NonNegative and NonZero are derivable
      instance
        _ : NonNegative factor
        _ = pos⇒nonNeg factor
          where open import Data.Rational.Properties using (pos⇒nonNeg)

        _ : NonZero factor
        _ = >-nonZero factor-pos

      raw/1*f≤q*f : (raw Data.Rational./ 1) *ᵣ factor ≤ᵣ q *ᵣ factor
      raw/1*f≤q*f = *-monoʳ-≤-nonNeg factor raw/1≤q

      q*f<raw+1/1*f : q *ᵣ factor <ᵣ ((raw ℤ.+ ℤ.+ 1) Data.Rational./ 1) *ᵣ factor
      q*f<raw+1/1*f = *-monoˡ-<-pos factor q<raw+1/1

      -- Step 3: cancel division (q * f = value - offset)
      raw/1*f≤v-o : (raw Data.Rational./ 1) *ᵣ factor ≤ᵣ value -ᵣ offset
      raw/1*f≤v-o = subst ((raw Data.Rational./ 1) *ᵣ factor ≤ᵣ_) (÷-*-cancel (value -ᵣ offset) factor) raw/1*f≤q*f

      v-o<raw+1/1*f : value -ᵣ offset <ᵣ ((raw ℤ.+ ℤ.+ 1) Data.Rational./ 1) *ᵣ factor
      v-o<raw+1/1*f = subst (_<ᵣ ((raw ℤ.+ ℤ.+ 1) Data.Rational./ 1) *ᵣ factor) (÷-*-cancel (value -ᵣ offset) factor) q*f<raw+1/1*f

      -- Step 4: shift offset, use raw+1*f identity for upper bound
      left-bound : applyScaling raw factor offset ≤ᵣ value
      left-bound = ≤-shift-offset ((raw Data.Rational./ 1) *ᵣ factor) value offset raw/1*f≤v-o

      -- For right bound: v - o < raw/1*f + f, add offset to get v < raw/1*f + f + o
      -- Then rewrite: (raw/1*f + f) + o = (raw/1*f + o) + f = result + f by commutativity
      -- raw+1*f≡raw*f+f : (raw+1)/1 * f ≡ raw/1 * f + f
      v-o<raw/1*f+f : value -ᵣ offset <ᵣ (raw Data.Rational./ 1) *ᵣ factor +ᵣ factor
      v-o<raw/1*f+f = subst (value -ᵣ offset <ᵣ_) (raw+1*f≡raw*f+f raw factor) v-o<raw+1/1*f

      v<raw/1*f+f+o : value <ᵣ ((raw Data.Rational./ 1) *ᵣ factor +ᵣ factor) +ᵣ offset
      v<raw/1*f+f+o = <-shift-offset value ((raw Data.Rational./ 1) *ᵣ factor +ᵣ factor) offset v-o<raw/1*f+f

      -- (raw/1*f + f) + o = (raw/1*f + o) + f = result + f
      rearrange : ((raw Data.Rational./ 1) *ᵣ factor +ᵣ factor) +ᵣ offset ≡ applyScaling raw factor offset +ᵣ factor
      rearrange = begin
        ((raw Data.Rational./ 1) *ᵣ factor +ᵣ factor) +ᵣ offset  ≡⟨ ℚ-+-assoc ((raw Data.Rational./ 1) *ᵣ factor) factor offset ⟩
        (raw Data.Rational./ 1) *ᵣ factor +ᵣ (factor +ᵣ offset)  ≡⟨ cong ((raw Data.Rational./ 1) *ᵣ factor +ᵣ_) (ℚ-+-comm factor offset) ⟩
        (raw Data.Rational./ 1) *ᵣ factor +ᵣ (offset +ᵣ factor)  ≡⟨ sym (ℚ-+-assoc ((raw Data.Rational./ 1) *ᵣ factor) offset factor) ⟩
        applyScaling raw factor offset +ᵣ factor                  ∎
        where open import Data.Rational.Properties renaming (+-assoc to ℚ-+-assoc; +-comm to ℚ-+-comm)

      right-bound : value <ᵣ applyScaling raw factor offset +ᵣ factor
      right-bound = subst (value <ᵣ_) rearrange v<raw/1*f+f+o

  scaling-bounds-neg : ∀ (value factor offset : ℚ) (raw : ℤ)
    → (factor-neg : factor <ᵣ 0ℚ)
    → floor (_÷ᵣ_ (value -ᵣ offset) factor {{<-nonZero factor-neg}}) ≡ raw
    → let result = applyScaling raw factor offset
      in result +ᵣ factor <ᵣ value × value ≤ᵣ result
  scaling-bounds-neg value factor offset raw factor-neg floor≡raw = left-bound , right-bound
    where
      open import Data.Rational.Properties using (≤-reflexive; <-respʳ-≡)

      q : ℚ
      q = _÷ᵣ_ (value -ᵣ offset) factor {{<-nonZero factor-neg}}

      instance _ : Negative factor
      _ = negative factor-neg

      -- Step 1: floor bounds with substitution (same as positive case)
      floor/1≡raw/1 : (floor q Data.Rational./ 1) ≡ (raw Data.Rational./ 1)
      floor/1≡raw/1 = cong (Data.Rational._/ 1) floor≡raw

      raw/1≤q : (raw Data.Rational./ 1) ≤ᵣ q
      raw/1≤q = subst (_≤ᵣ q) floor/1≡raw/1 (floor-lower q)

      floor+1/1≡raw+1/1 : ((floor q ℤ.+ ℤ.+ 1) Data.Rational./ 1) ≡ ((raw ℤ.+ ℤ.+ 1) Data.Rational./ 1)
      floor+1/1≡raw+1/1 = cong (λ x → (x ℤ.+ ℤ.+ 1) Data.Rational./ 1) floor≡raw

      q<raw+1/1 : q <ᵣ ((raw ℤ.+ ℤ.+ 1) Data.Rational./ 1)
      q<raw+1/1 = <-respʳ-≡ floor+1/1≡raw+1/1 (floor-upper q)

      -- Step 2: multiply by negative factor (REVERSES order)
      -- raw/1 ≤ q becomes q*f ≤ raw/1*f
      -- q < raw+1/1 becomes raw+1/1*f < q*f
      instance
        _ : NonPositive factor
        _ = neg⇒nonPos factor

        _ : NonZero factor
        _ = <-nonZero factor-neg

      -- *-monoʳ-≤-nonPos : p ≤ q → (p * r) ≥ (q * r) for nonPos r
      -- So raw/1 ≤ q gives q*f ≤ raw/1*f
      q*f≤raw/1*f : q *ᵣ factor ≤ᵣ (raw Data.Rational./ 1) *ᵣ factor
      q*f≤raw/1*f = *-monoʳ-≤-nonPos factor raw/1≤q

      -- *-monoˡ-<-neg : p < q → (p * r) > (q * r) for neg r
      -- So q < raw+1/1 gives raw+1/1*f < q*f
      raw+1/1*f<q*f : ((raw ℤ.+ ℤ.+ 1) Data.Rational./ 1) *ᵣ factor <ᵣ q *ᵣ factor
      raw+1/1*f<q*f = *-monoˡ-<-neg factor q<raw+1/1

      -- Step 3: cancel division (q * f = value - offset)
      -- q*f ≤ raw/1*f becomes value - offset ≤ raw/1*f
      v-o≤raw/1*f : value -ᵣ offset ≤ᵣ (raw Data.Rational./ 1) *ᵣ factor
      v-o≤raw/1*f = subst (_≤ᵣ (raw Data.Rational./ 1) *ᵣ factor) (÷-*-cancel (value -ᵣ offset) factor) q*f≤raw/1*f

      -- raw+1/1*f < q*f becomes raw+1/1*f < value - offset
      raw+1/1*f<v-o : ((raw ℤ.+ ℤ.+ 1) Data.Rational./ 1) *ᵣ factor <ᵣ value -ᵣ offset
      raw+1/1*f<v-o = subst (((raw ℤ.+ ℤ.+ 1) Data.Rational./ 1) *ᵣ factor <ᵣ_) (÷-*-cancel (value -ᵣ offset) factor) raw+1/1*f<q*f

      -- Step 4: unshift offset
      -- For right bound: value - offset ≤ raw/1*f implies value ≤ raw/1*f + offset = result
      right-bound : value ≤ᵣ applyScaling raw factor offset
      right-bound = ≤-unshift-offset value ((raw Data.Rational./ 1) *ᵣ factor) offset v-o≤raw/1*f

      -- For left bound: raw+1/1*f < value - offset
      -- Convert raw+1/1*f to raw/1*f + f using raw+1*f≡raw*f+f
      raw/1*f+f<v-o : (raw Data.Rational./ 1) *ᵣ factor +ᵣ factor <ᵣ value -ᵣ offset
      raw/1*f+f<v-o = subst (_<ᵣ value -ᵣ offset) (raw+1*f≡raw*f+f raw factor) raw+1/1*f<v-o

      -- raw/1*f + f < value - offset implies (raw/1*f + f) + offset < value
      raw/1*f+f+o<v : ((raw Data.Rational./ 1) *ᵣ factor +ᵣ factor) +ᵣ offset <ᵣ value
      raw/1*f+f+o<v = <-unshift-offset value ((raw Data.Rational./ 1) *ᵣ factor +ᵣ factor) offset raw/1*f+f<v-o

      -- Rearrange: (raw/1*f + f) + o = result + f (same as positive case)
      rearrange : ((raw Data.Rational./ 1) *ᵣ factor +ᵣ factor) +ᵣ offset ≡ applyScaling raw factor offset +ᵣ factor
      rearrange = begin
        ((raw Data.Rational./ 1) *ᵣ factor +ᵣ factor) +ᵣ offset  ≡⟨ ℚ-+-assoc ((raw Data.Rational./ 1) *ᵣ factor) factor offset ⟩
        (raw Data.Rational./ 1) *ᵣ factor +ᵣ (factor +ᵣ offset)  ≡⟨ cong ((raw Data.Rational./ 1) *ᵣ factor +ᵣ_) (ℚ-+-comm factor offset) ⟩
        (raw Data.Rational./ 1) *ᵣ factor +ᵣ (offset +ᵣ factor)  ≡⟨ sym (ℚ-+-assoc ((raw Data.Rational./ 1) *ᵣ factor) offset factor) ⟩
        applyScaling raw factor offset +ᵣ factor                  ∎
        where open import Data.Rational.Properties renaming (+-assoc to ℚ-+-assoc; +-comm to ℚ-+-comm)

      left-bound : applyScaling raw factor offset +ᵣ factor <ᵣ value
      left-bound = subst (_<ᵣ value) rearrange raw/1*f+f+o<v

-- ═══════════════════════════════════════════════════════════════════════════
-- LAYER D: Structural bridge + final theorem
-- ═══════════════════════════════════════════════════════════════════════════
-- Pattern match on factor to extract floor equation, then apply Layer C.

-- The reverse direction: starting from ℚ value, removing then applying scaling
-- produces a value within one factor of the original
applyScaling-removeScaling-bounded : ∀ (value factor offset : ℚ) (raw : ℤ)
  → (factor≢0 : factor ≢ 0ℚ)
  → removeScaling value factor offset ≡ just raw
  → let result = applyScaling raw factor offset
    in (0ℚ <ᵣ factor → result ≤ᵣ value × value <ᵣ result +ᵣ factor)
     × (factor <ᵣ 0ℚ → result +ᵣ factor <ᵣ value × value ≤ᵣ result)
-- Pattern match on factor's numerator to make removeScaling reduce
-- Zero numerator: contradiction with factor≢0
applyScaling-removeScaling-bounded value factor@(mkℚ (+ 0) _ _) offset raw factor≢0 _ =
  ⊥-elim (ℚ-nonzero⇒num-nonzero factor factor≢0 refl)
-- Positive numerator: use scaling-bounds-pos
applyScaling-removeScaling-bounded value factor@(mkℚ (+ ℕ.suc _) _ _) offset raw factor≢0 remove≡just =
  pos-case , neg-absurd
  where
    open import Data.Rational.Properties using (<-irrefl; <-trans)

    -- Extract floor equation from remove≡just
    -- After pattern match, removeScaling reduces to just (floor (divideByFactor ...))
    -- Use ÷-via-ℚᵘ to bridge divideByFactor to ÷ᵣ
    numer : ℚ
    numer = value -ᵣ offset

    floor-eq-raw : floor (fromℚᵘ (toℚᵘ numer ÷ᵘ toℚᵘ factor)) ≡ raw
    floor-eq-raw = just-injective remove≡just

    floor-eq : floor (numer ÷ᵣ factor) ≡ raw
    floor-eq = trans (sym (cong floor (÷-via-ℚᵘ numer factor {{≢-nonZero factor≢0}}))) floor-eq-raw

    -- Factor is positive: mkℚ (+ ℕ.suc _) is definitionally positive
    factor-pos : 0ℚ <ᵣ factor
    factor-pos = positive⁻¹ factor
      where open import Data.Rational.Properties using (positive⁻¹)

    -- The positive case: apply scaling-bounds-pos
    pos-case : 0ℚ <ᵣ factor → applyScaling raw factor offset ≤ᵣ value × value <ᵣ applyScaling raw factor offset +ᵣ factor
    pos-case _ = scaling-bounds-pos value factor offset raw factor-pos floor-eq

    -- The negative case is absurd: factor is positive so can't be negative
    neg-absurd : factor <ᵣ 0ℚ → applyScaling raw factor offset +ᵣ factor <ᵣ value × value ≤ᵣ applyScaling raw factor offset
    neg-absurd factor<0 = ⊥-elim (<-irrefl refl (<-trans factor<0 factor-pos))

-- Negative numerator: use scaling-bounds-neg
applyScaling-removeScaling-bounded value factor@(mkℚ -[1+ _ ] _ _) offset raw factor≢0 remove≡just =
  pos-absurd , neg-case
  where
    open import Data.Rational.Properties using (<-irrefl; <-trans)

    -- Extract floor equation from remove≡just
    numer : ℚ
    numer = value -ᵣ offset

    floor-eq-raw : floor (fromℚᵘ (toℚᵘ numer ÷ᵘ toℚᵘ factor)) ≡ raw
    floor-eq-raw = just-injective remove≡just

    floor-eq : floor (numer ÷ᵣ factor) ≡ raw
    floor-eq = trans (sym (cong floor (÷-via-ℚᵘ numer factor {{≢-nonZero factor≢0}}))) floor-eq-raw

    -- Factor is negative: mkℚ -[1+ _ ] is definitionally negative
    factor-neg : factor <ᵣ 0ℚ
    factor-neg = negative⁻¹ factor
      where open import Data.Rational.Properties using (negative⁻¹)

    -- The positive case is absurd: factor is negative so can't be positive
    pos-absurd : 0ℚ <ᵣ factor → applyScaling raw factor offset ≤ᵣ value × value <ᵣ applyScaling raw factor offset +ᵣ factor
    pos-absurd 0<factor = ⊥-elim (<-irrefl refl (<-trans factor-neg 0<factor))

    -- The negative case: apply scaling-bounds-neg
    neg-case : factor <ᵣ 0ℚ → applyScaling raw factor offset +ᵣ factor <ᵣ value × value ≤ᵣ applyScaling raw factor offset
    neg-case _ = scaling-bounds-neg value factor offset raw factor-neg floor-eq

-- ============================================================================
-- LAYER 4: COMPOSITION - FULL ROUNDTRIP
-- ============================================================================
-- Combine all layers into the full signal extraction/injection proof

-- Helper: Define when a signal definition is well-formed
record WellFormedSignal (sig : SignalDef) : Set where
  field
    startBit-bounded : toℕ (SignalDef.startBit sig) < 64
    bitLength-positive : toℕ (SignalDef.bitLength sig) > 0
    bitLength-fits : toℕ (SignalDef.startBit sig) + toℕ (SignalDef.bitLength sig) ≤ 64
    factor-nonzero : ¬ (SignalDef.factor sig ≡ 0ℚ)
    ranges-consistent : SignalDef.minimum sig ≤ᵣ SignalDef.maximum sig

-- ═══════════════════════════════════════════════════════════════════════════
-- LAYER 4A: Core roundtrip (pure bytes level, no Maybe/guards)
-- ═══════════════════════════════════════════════════════════════════════════
-- Chain: extractBits ∘ injectBits → bitVecToℕ ∘ ℕToBitVec → toSigned ∘ fromSigned

private
  open import Aletheia.Data.BitVec.Conversion using (bitVec-roundtrip; ℕToBitVec; bitVecToℕ)
  open import Aletheia.CAN.Endianness using (extractBits-injectBits-roundtrip; swapBytes; swapBytes-involutive)

  -- Helper: SignedFits implies fromSigned is bounded
  -- This is the direction we need for injectSignal's guard
  SignedFits-implies-fromSigned-bounded : ∀ (raw : ℤ) (bitLength : ℕ)
    → bitLength > 0
    → SignedFits raw bitLength
    → fromSigned raw bitLength < 2 ^ bitLength
  SignedFits-implies-fromSigned-bounded (+ n) bitLength bl>0 n<half =
    -- n < 2^(bl-1) < 2^bl
    <-trans n<half (half<full bitLength bl>0)
    where
      open import Data.Nat.Properties as ℕP using (<-trans; ^-monoʳ-<; n<1+n; ≤-refl)
      -- 2^(bl-1) < 2^bl follows from 1<2 and bl-1 < bl
      half<full : ∀ bl → bl > 0 → 2 ^ (bl ∸ 1) < 2 ^ bl
      half<full (suc bl) _ = ^-monoʳ-< 2 1<2 (n<1+n bl)
        where
          1<2 : 1 < 2
          1<2 = s≤s (s≤s z≤n)
  SignedFits-implies-fromSigned-bounded -[1+ n ] bitLength bl>0 sucn≤half =
    -- fromSigned -[1+ n] bl = 2^bl - suc n
    -- Need: 2^bl - suc n < 2^bl, which is always true when 2^bl > 0
    m∸sucn<m (2 ^ bitLength) n (m^n>0 2 bitLength)
    where
      open import Data.Nat.Properties using (m∸n≤m; m^n>0)
      -- m ∸ suc n < m when m > 0
      m∸sucn<m : ∀ m n → m > 0 → m ∸ suc n < m
      m∸sucn<m (suc m) n _ = s≤s (m∸n≤m m n)

  -- Unified constraint: combines what we need for roundtrip
  -- For unsigned: raw is non-negative
  -- For signed: raw satisfies SignedFits
  data RawFits (raw : ℤ) (bitLength : ℕ) : Bool → Set where
    unsigned-fits : ∀ {n} → raw ≡ + n → n < 2 ^ bitLength → RawFits raw bitLength false
    signed-fits : SignedFits raw bitLength → RawFits raw bitLength true

  -- Derive fromSigned bound from RawFits
  RawFits-implies-bounded : ∀ (raw : ℤ) (bitLength : ℕ) (isSigned : Bool)
    → bitLength > 0
    → RawFits raw bitLength isSigned
    → fromSigned raw bitLength < 2 ^ bitLength
  RawFits-implies-bounded .(+ n) bitLength false bl>0 (unsigned-fits {n} refl n<2^bl) = n<2^bl
  RawFits-implies-bounded raw bitLength true bl>0 (signed-fits sf) =
    SignedFits-implies-fromSigned-bounded raw bitLength bl>0 sf

  -- Core roundtrip: at the bytes level, extraction recovers the original raw value
  -- No Maybe, no guards - just the pure mathematical roundtrip
  --
  -- Pipeline:
  --   raw → fromSigned → ℕToBitVec → injectBits → extractBits → bitVecToℕ → toSigned → raw
  --
  -- Unsigned case: raw = + n
  signal-roundtrip-unsigned :
    ∀ (n : ℕ) (bytes : Vec Byte 8) (startBit bitLength : ℕ)
    → (fits-in-frame : startBit + bitLength ≤ 64)
    → (n<2^bl : n < 2 ^ bitLength)
    → toSigned (bitVecToℕ (extractBits {bitLength}
        (injectBits {bitLength} bytes startBit (ℕToBitVec {bitLength} n n<2^bl))
        startBit)) bitLength false ≡ + n
  signal-roundtrip-unsigned n bytes startBit bitLength fits-in-frame n<2^bl =
    cong +_ unsigned-roundtrip
    where
      -- Abbreviation for the BitVec
      bv : BitVec bitLength
      bv = ℕToBitVec {bitLength} n n<2^bl

      -- Chain: extractBits ∘ injectBits = id (Layer 1)
      bits-roundtrip : extractBits {bitLength} (injectBits {bitLength} bytes startBit bv) startBit ≡ bv
      bits-roundtrip = extractBits-injectBits-roundtrip {bitLength} bytes startBit bv fits-in-frame

      -- Chain: bitVecToℕ ∘ ℕToBitVec = id (Layer 1.5)
      nat-roundtrip : bitVecToℕ bv ≡ n
      nat-roundtrip = bitVec-roundtrip bitLength n n<2^bl

      -- Combined: extractedUnsigned ≡ n
      unsigned-roundtrip : bitVecToℕ (extractBits {bitLength} (injectBits {bitLength} bytes startBit bv) startBit) ≡ n
      unsigned-roundtrip = trans (cong bitVecToℕ bits-roundtrip) nat-roundtrip

  -- Signed case: use toSigned-fromSigned-roundtrip
  signal-roundtrip-signed :
    ∀ (raw : ℤ) (bytes : Vec Byte 8) (startBit bitLength : ℕ)
    → (bitLength>0 : bitLength > 0)
    → (fits-in-frame : startBit + bitLength ≤ 64)
    → (sf : SignedFits raw bitLength)
    → (fits-in-bits : fromSigned raw bitLength < 2 ^ bitLength)
    → toSigned (bitVecToℕ (extractBits {bitLength}
        (injectBits {bitLength} bytes startBit (ℕToBitVec {bitLength} (fromSigned raw bitLength) fits-in-bits))
        startBit)) bitLength true ≡ raw
  signal-roundtrip-signed raw bytes startBit bitLength bitLength>0 fits-in-frame sf fits-in-bits =
    signed-proof
    where
      -- Abbreviation for the BitVec
      bv : BitVec bitLength
      bv = ℕToBitVec {bitLength} (fromSigned raw bitLength) fits-in-bits

      -- Chain: extractBits ∘ injectBits = id (Layer 1)
      bits-roundtrip : extractBits {bitLength} (injectBits {bitLength} bytes startBit bv) startBit ≡ bv
      bits-roundtrip = extractBits-injectBits-roundtrip {bitLength} bytes startBit bv fits-in-frame

      -- Chain: bitVecToℕ ∘ ℕToBitVec = id (Layer 1.5)
      nat-roundtrip : bitVecToℕ bv ≡ fromSigned raw bitLength
      nat-roundtrip = bitVec-roundtrip bitLength (fromSigned raw bitLength) fits-in-bits

      -- Combined: extractedUnsigned ≡ fromSigned raw bitLength
      unsigned-roundtrip : bitVecToℕ (extractBits {bitLength} (injectBits {bitLength} bytes startBit bv) startBit) ≡ fromSigned raw bitLength
      unsigned-roundtrip = trans (cong bitVecToℕ bits-roundtrip) nat-roundtrip

      -- Chain: toSigned ∘ fromSigned = id (Layer 2)
      signed-proof : toSigned (bitVecToℕ (extractBits {bitLength} (injectBits {bitLength} bytes startBit bv) startBit)) bitLength true ≡ raw
      signed-proof = trans (cong (λ x → toSigned x bitLength true) unsigned-roundtrip)
                           (toSigned-fromSigned-roundtrip raw bitLength bitLength>0 sf)

-- ============================================================================
-- LAYER 4: FULL SIGNAL ROUNDTRIP (through Maybe)
-- ============================================================================
-- The full composition: extractSignal ∘ injectSignal = id
-- This lifts the pure bytes-level roundtrip through Maybe and handles:
-- - Bounds checking guards
-- - Scaling operations
-- - Byte order swapping

{-
  Strategy: The full roundtrip proof requires showing that:
  1. injectSignal value sig byteOrder frame = just frame'
     (when bounds pass, removeScaling succeeds, and raw fits)
  2. extractSignal frame' sig byteOrder = just value
     (because we extract the same bits → same raw → same value)

  The key insight is that for a value = applyScaling raw factor offset,
  removeScaling will return exactly raw (no floor precision loss).

  Endianness handling: swapBytes is involutive, so:
  - Big-endian: swap → inject → swap → extract → swap
    The first swap-swap pair cancels, leaving inject → extract
-}

-- Full roundtrip theorem: extractSignal ∘ injectSignal = id
-- Preconditions:
-- 1. value = applyScaling raw factor offset (ensures removeScaling recovers raw exactly)
-- 2. inBounds value min max ≡ true (bounds check passes)
-- 3. factor ≢ 0 (well-formed signal)
-- 4. fits-in-bits: fromSigned raw bitLength < 2^bitLength

-- For now, we state the theorem for the unsigned case (isSigned = false)
-- The signed case follows the same structure with SignedFits constraint

-- Helper: compute signal value from raw integer
signalValue : ℤ → SignalDef → ℚ
signalValue raw sig = applyScaling raw (SignalDef.factor sig) (SignalDef.offset sig)

-- ============================================================================
-- REDUCTION LEMMAS: State exactly what injectSignal/extractSignal compute
-- ============================================================================

-- Helper: compute the frame that injectSignal produces
-- Uses injectPayload abstraction to factor out byte order handling
injectedFrame : ∀ (n : ℕ) (sig : SignalDef) (byteOrder : ByteOrder) (frame : CANFrame)
  → n < 2 ^ toℕ (SignalDef.bitLength sig)
  → CANFrame
injectedFrame n sig byteOrder frame n<2^bl =
  record frame { payload = injectPayload (toℕ (SignalDef.startBit sig)) (ℕToBitVec n n<2^bl) byteOrder (CANFrame.payload frame) }

-- Reduction Lemma A: injectSignal reduces to a known frame
-- This is more useful than existence because it eliminates ∃ from proofs
injectSignal-reduces-unsigned :
  ∀ (n : ℕ) (sig : SignalDef) (byteOrder : ByteOrder) (frame : CANFrame)
  → (bounds-ok : inBounds (signalValue (+ n) sig) (SignalDef.minimum sig) (SignalDef.maximum sig) ≡ true)
  → (factor≢0 : SignalDef.factor sig ≢ 0ℚ)
  → (n<2^bl : n < 2 ^ toℕ (SignalDef.bitLength sig))
  → injectSignal (signalValue (+ n) sig) sig byteOrder frame ≡ just (injectedFrame n sig byteOrder frame n<2^bl)
injectSignal-reduces-unsigned n sig byteOrder frame bounds-ok factor≢0 n<2^bl =
  helper bounds-ok remove-eq fits-check
  where
    open SignalDef sig
    open CANFrame frame
    open import Relation.Nullary.Decidable using (dec-yes-irr)
    open import Data.Nat.Properties using (<-irrelevant)

    value : ℚ
    value = signalValue (+ n) sig

    remove-eq : removeScaling value factor offset ≡ just (+ n)
    remove-eq = removeScaling-applyScaling-exact (+ n) factor offset factor≢0

    fits-check : (n Data.Nat.<? 2 ^ toℕ bitLength) ≡ yes n<2^bl
    fits-check = dec-yes-irr (n Data.Nat.<? 2 ^ toℕ bitLength) <-irrelevant n<2^bl

    helper : inBounds value minimum maximum ≡ true
           → removeScaling value factor offset ≡ just (+ n)
           → (n Data.Nat.<? 2 ^ toℕ bitLength) ≡ yes n<2^bl
           → injectSignal value sig byteOrder frame ≡ just (injectedFrame n sig byteOrder frame n<2^bl)
    helper bounds-eq remove-eq' fits-eq
      with inBounds value minimum maximum
    helper bounds-eq remove-eq' fits-eq | true
      with removeScaling value factor offset | remove-eq'
    ... | just .(+ n) | refl
      with n Data.Nat.<? 2 ^ toℕ bitLength | fits-eq
    ... | yes .n<2^bl | refl = refl
    helper () _ _ | false

-- Reduction Lemma B: extractSignal on injectedFrame returns the original value
-- Now uses the refactored extractSignal with computational core
extractSignal-reduces-unsigned :
  ∀ (n : ℕ) (sig : SignalDef) (byteOrder : ByteOrder) (frame : CANFrame)
  → (bounds-ok : inBounds (signalValue (+ n) sig) (SignalDef.minimum sig) (SignalDef.maximum sig) ≡ true)
  → (unsigned : SignalDef.isSigned sig ≡ false)
  → (fits-in-frame : toℕ (SignalDef.startBit sig) + toℕ (SignalDef.bitLength sig) ≤ 64)
  → (n<2^bl : n < 2 ^ toℕ (SignalDef.bitLength sig))
  → extractSignal (injectedFrame n sig byteOrder frame n<2^bl) sig byteOrder ≡ just (signalValue (+ n) sig)

-- LittleEndian case: no byte swapping
extractSignal-reduces-unsigned n sig LittleEndian frame bounds-ok unsigned fits-in-frame n<2^bl =
  proof
  where
    open SignalDef sig
    open CANFrame frame
    value : ℚ
    value = signalValue (+ n) sig

    -- The bytes we extract from: payload of injectedFrame = injectBits payload startBit bv
    injectedBytes : Data.Vec.Vec Byte 8
    injectedBytes = injectBits {toℕ bitLength} payload (toℕ startBit) (ℕToBitVec {toℕ bitLength} n n<2^bl)

    -- extractionBytes (injectedFrame ...) LittleEndian = payload of injectedFrame = injectedBytes
    -- (This is definitional for LittleEndian)

    -- Core roundtrip: extractSignalCore returns + n for unsigned signals
    core-eq : extractSignalCore injectedBytes sig ≡ + n
    core-eq rewrite unsigned = signal-roundtrip-unsigned n payload (toℕ startBit) (toℕ bitLength) fits-in-frame n<2^bl

    -- Scaling: scaleExtracted (+ n) sig = value (definitional)
    scale-eq : scaleExtracted (+ n) sig ≡ value
    scale-eq = refl

    -- The proof by rewriting
    proof : extractSignal (injectedFrame n sig LittleEndian frame n<2^bl) sig LittleEndian ≡ just value
    proof rewrite core-eq | bounds-ok = refl

-- BigEndian case: byte swapping cancels
extractSignal-reduces-unsigned n sig BigEndian frame bounds-ok unsigned fits-in-frame n<2^bl =
  proof
  where
    open SignalDef sig
    open CANFrame frame
    value : ℚ
    value = signalValue (+ n) sig

    -- For BigEndian, injectedFrame's payload = swapBytes (injectBits (swapBytes payload) startBit bv)
    swappedPayload : Data.Vec.Vec Byte 8
    swappedPayload = swapBytes payload

    injectedBytesSwapped : Data.Vec.Vec Byte 8
    injectedBytesSwapped = injectBits {toℕ bitLength} swappedPayload (toℕ startBit) (ℕToBitVec {toℕ bitLength} n n<2^bl)

    -- extractionBytes (injectedFrame ...) BigEndian = swapBytes (swapBytes injectedBytesSwapped) = injectedBytesSwapped
    swap-cancel : swapBytes (swapBytes injectedBytesSwapped) ≡ injectedBytesSwapped
    swap-cancel = swapBytes-involutive injectedBytesSwapped

    -- Core roundtrip on the swapped payload
    core-eq : extractSignalCore injectedBytesSwapped sig ≡ + n
    core-eq rewrite unsigned = signal-roundtrip-unsigned n swappedPayload (toℕ startBit) (toℕ bitLength) fits-in-frame n<2^bl

    -- The proof by rewriting
    proof : extractSignal (injectedFrame n sig BigEndian frame n<2^bl) sig BigEndian ≡ just value
    proof rewrite swap-cancel | core-eq | bounds-ok = refl

extractSignal-injectSignal-roundtrip-unsigned :
  ∀ (n : ℕ) (sig : SignalDef) (byteOrder : ByteOrder) (frame : CANFrame)
  → (bounds-ok : inBounds (signalValue (+ n) sig) (SignalDef.minimum sig) (SignalDef.maximum sig) ≡ true)
  → (factor≢0 : SignalDef.factor sig ≢ 0ℚ)
  → (unsigned : SignalDef.isSigned sig ≡ false)
  → (fits-in-frame : toℕ (SignalDef.startBit sig) + toℕ (SignalDef.bitLength sig) ≤ 64)
  → (n<2^bl : n < 2 ^ toℕ (SignalDef.bitLength sig))
  → (injectSignal (signalValue (+ n) sig) sig byteOrder frame >>= λ frame' →
       extractSignal frame' sig byteOrder) ≡ just (signalValue (+ n) sig)
extractSignal-injectSignal-roundtrip-unsigned n sig byteOrder frame bounds-ok factor≢0 unsigned fits-in-frame n<2^bl =
  proof
  where
    value : ℚ
    value = signalValue (+ n) sig

    -- Reduction lemma: injectSignal computes to just (injectedFrame ...)
    inject-reduces : injectSignal value sig byteOrder frame ≡ just (injectedFrame n sig byteOrder frame n<2^bl)
    inject-reduces = injectSignal-reduces-unsigned n sig byteOrder frame bounds-ok factor≢0 n<2^bl

    -- Reduction lemma: extractSignal on injectedFrame returns just value
    extract-reduces : extractSignal (injectedFrame n sig byteOrder frame n<2^bl) sig byteOrder ≡ just value
    extract-reduces = extractSignal-reduces-unsigned n sig byteOrder frame bounds-ok unsigned fits-in-frame n<2^bl

    -- Compose by rewriting: inject >>= extract = just injectedFrame >>= extract = extract injectedFrame = just value
    proof : (injectSignal value sig byteOrder frame >>= λ f → extractSignal f sig byteOrder) ≡ just value
    proof rewrite inject-reduces = extract-reduces

-- ============================================================================
-- LAYER 4B: SIGNED SIGNAL ROUNDTRIP
-- ============================================================================
-- Same pattern as unsigned, but uses SignedFits constraint and toSigned true

-- Reduction Lemma A (Signed): injectSignal reduces to a known frame
-- The raw value is fromSigned z bitLength, which we prove fits in bitLength bits
injectSignal-reduces-signed :
  ∀ (z : ℤ) (sig : SignalDef) (byteOrder : ByteOrder) (frame : CANFrame)
  → (bounds-ok : inBounds (signalValue z sig) (SignalDef.minimum sig) (SignalDef.maximum sig) ≡ true)
  → (factor≢0 : SignalDef.factor sig ≢ 0ℚ)
  → (bl>0 : toℕ (SignalDef.bitLength sig) > 0)
  → (sf : SignedFits z (toℕ (SignalDef.bitLength sig)))
  → let n = fromSigned z (toℕ (SignalDef.bitLength sig))
        n<2^bl = SignedFits-implies-fromSigned-bounded z (toℕ (SignalDef.bitLength sig)) bl>0 sf
    in injectSignal (signalValue z sig) sig byteOrder frame ≡ just (injectedFrame n sig byteOrder frame n<2^bl)
injectSignal-reduces-signed z sig byteOrder frame bounds-ok factor≢0 bl>0 sf =
  helper bounds-ok remove-eq fits-check
  where
    open SignalDef sig
    open CANFrame frame
    open import Relation.Nullary.Decidable using (dec-yes-irr)
    open import Data.Nat.Properties using (<-irrelevant)

    value : ℚ
    value = signalValue z sig

    n : ℕ
    n = fromSigned z (toℕ bitLength)

    n<2^bl : n < 2 ^ toℕ bitLength
    n<2^bl = SignedFits-implies-fromSigned-bounded z (toℕ bitLength) bl>0 sf

    remove-eq : removeScaling value factor offset ≡ just z
    remove-eq = removeScaling-applyScaling-exact z factor offset factor≢0

    fits-check : (n Data.Nat.<? 2 ^ toℕ bitLength) ≡ yes n<2^bl
    fits-check = dec-yes-irr (n Data.Nat.<? 2 ^ toℕ bitLength) <-irrelevant n<2^bl

    helper : inBounds value minimum maximum ≡ true
           → removeScaling value factor offset ≡ just z
           → (n Data.Nat.<? 2 ^ toℕ bitLength) ≡ yes n<2^bl
           → injectSignal value sig byteOrder frame ≡ just (injectedFrame n sig byteOrder frame n<2^bl)
    helper bounds-eq remove-eq' fits-eq
      with inBounds value minimum maximum
    helper bounds-eq remove-eq' fits-eq | true
      with removeScaling value factor offset | remove-eq'
    ... | just .z | refl
      with n Data.Nat.<? 2 ^ toℕ bitLength | fits-eq
    ... | yes .n<2^bl | refl = refl
    helper () _ _ | false

-- Reduction Lemma B (Signed): extractSignal on injectedFrame returns the original value
-- Uses signal-roundtrip-signed which uses toSigned with isSigned = true
extractSignal-reduces-signed :
  ∀ (z : ℤ) (sig : SignalDef) (byteOrder : ByteOrder) (frame : CANFrame)
  → (bounds-ok : inBounds (signalValue z sig) (SignalDef.minimum sig) (SignalDef.maximum sig) ≡ true)
  → (signed : SignalDef.isSigned sig ≡ true)
  → (bl>0 : toℕ (SignalDef.bitLength sig) > 0)
  → (sf : SignedFits z (toℕ (SignalDef.bitLength sig)))
  → (fits-in-frame : toℕ (SignalDef.startBit sig) + toℕ (SignalDef.bitLength sig) ≤ 64)
  → let n = fromSigned z (toℕ (SignalDef.bitLength sig))
        n<2^bl = SignedFits-implies-fromSigned-bounded z (toℕ (SignalDef.bitLength sig)) bl>0 sf
    in extractSignal (injectedFrame n sig byteOrder frame n<2^bl) sig byteOrder ≡ just (signalValue z sig)

-- LittleEndian case: no byte swapping
extractSignal-reduces-signed z sig LittleEndian frame bounds-ok signed bl>0 sf fits-in-frame =
  proof
  where
    open SignalDef sig
    open CANFrame frame
    value : ℚ
    value = signalValue z sig

    n : ℕ
    n = fromSigned z (toℕ bitLength)

    n<2^bl : n < 2 ^ toℕ bitLength
    n<2^bl = SignedFits-implies-fromSigned-bounded z (toℕ bitLength) bl>0 sf

    -- The bytes we extract from
    injectedBytes : Data.Vec.Vec Byte 8
    injectedBytes = injectBits {toℕ bitLength} payload (toℕ startBit) (ℕToBitVec {toℕ bitLength} n n<2^bl)

    -- Core roundtrip: extractSignalCore returns z for signed signals
    core-eq : extractSignalCore injectedBytes sig ≡ z
    core-eq rewrite signed = signal-roundtrip-signed z payload (toℕ startBit) (toℕ bitLength) bl>0 fits-in-frame sf n<2^bl

    -- The proof by rewriting
    proof : extractSignal (injectedFrame n sig LittleEndian frame n<2^bl) sig LittleEndian ≡ just value
    proof rewrite core-eq | bounds-ok = refl

-- BigEndian case: byte swapping cancels
extractSignal-reduces-signed z sig BigEndian frame bounds-ok signed bl>0 sf fits-in-frame =
  proof
  where
    open SignalDef sig
    open CANFrame frame
    value : ℚ
    value = signalValue z sig

    n : ℕ
    n = fromSigned z (toℕ bitLength)

    n<2^bl : n < 2 ^ toℕ bitLength
    n<2^bl = SignedFits-implies-fromSigned-bounded z (toℕ bitLength) bl>0 sf

    -- For BigEndian, injectedFrame's payload = swapBytes (injectBits (swapBytes payload) startBit bv)
    swappedPayload : Data.Vec.Vec Byte 8
    swappedPayload = swapBytes payload

    injectedBytesSwapped : Data.Vec.Vec Byte 8
    injectedBytesSwapped = injectBits {toℕ bitLength} swappedPayload (toℕ startBit) (ℕToBitVec {toℕ bitLength} n n<2^bl)

    -- extractionBytes (injectedFrame ...) BigEndian = swapBytes (swapBytes injectedBytesSwapped) = injectedBytesSwapped
    swap-cancel : swapBytes (swapBytes injectedBytesSwapped) ≡ injectedBytesSwapped
    swap-cancel = swapBytes-involutive injectedBytesSwapped

    -- Core roundtrip on the swapped payload
    core-eq : extractSignalCore injectedBytesSwapped sig ≡ z
    core-eq rewrite signed = signal-roundtrip-signed z swappedPayload (toℕ startBit) (toℕ bitLength) bl>0 fits-in-frame sf n<2^bl

    -- The proof by rewriting
    proof : extractSignal (injectedFrame n sig BigEndian frame n<2^bl) sig BigEndian ≡ just value
    proof rewrite swap-cancel | core-eq | bounds-ok = refl

-- Main theorem (Signed): inject then extract returns original value
extractSignal-injectSignal-roundtrip-signed :
  ∀ (z : ℤ) (sig : SignalDef) (byteOrder : ByteOrder) (frame : CANFrame)
  → (bounds-ok : inBounds (signalValue z sig) (SignalDef.minimum sig) (SignalDef.maximum sig) ≡ true)
  → (factor≢0 : SignalDef.factor sig ≢ 0ℚ)
  → (signed : SignalDef.isSigned sig ≡ true)
  → (bl>0 : toℕ (SignalDef.bitLength sig) > 0)
  → (sf : SignedFits z (toℕ (SignalDef.bitLength sig)))
  → (fits-in-frame : toℕ (SignalDef.startBit sig) + toℕ (SignalDef.bitLength sig) ≤ 64)
  → (injectSignal (signalValue z sig) sig byteOrder frame >>= λ frame' →
       extractSignal frame' sig byteOrder) ≡ just (signalValue z sig)
extractSignal-injectSignal-roundtrip-signed z sig byteOrder frame bounds-ok factor≢0 signed bl>0 sf fits-in-frame =
  proof
  where
    open SignalDef sig
    value : ℚ
    value = signalValue z sig

    n : ℕ
    n = fromSigned z (toℕ bitLength)

    n<2^bl : n < 2 ^ toℕ bitLength
    n<2^bl = SignedFits-implies-fromSigned-bounded z (toℕ bitLength) bl>0 sf

    -- Reduction lemma: injectSignal computes to just (injectedFrame ...)
    inject-reduces : injectSignal value sig byteOrder frame ≡ just (injectedFrame n sig byteOrder frame n<2^bl)
    inject-reduces = injectSignal-reduces-signed z sig byteOrder frame bounds-ok factor≢0 bl>0 sf

    -- Reduction lemma: extractSignal on injectedFrame returns just value
    extract-reduces : extractSignal (injectedFrame n sig byteOrder frame n<2^bl) sig byteOrder ≡ just value
    extract-reduces = extractSignal-reduces-signed z sig byteOrder frame bounds-ok signed bl>0 sf fits-in-frame

    -- Compose by rewriting
    proof : (injectSignal value sig byteOrder frame >>= λ f → extractSignal f sig byteOrder) ≡ just value
    proof rewrite inject-reduces = extract-reduces

-- ============================================================================
-- NON-OVERLAP PROPERTIES (bit-level, no ℚ)
-- ============================================================================
-- Prove that signals with disjoint bit ranges don't interfere

-- Definition: Two signals are disjoint if their bit ranges don't overlap
data SignalsDisjoint (sig₁ sig₂ : SignalDef) : Set where
  disjoint-left :
    toℕ (SignalDef.startBit sig₁) + toℕ (SignalDef.bitLength sig₁)
      ≤ toℕ (SignalDef.startBit sig₂)
    → SignalsDisjoint sig₁ sig₂
  disjoint-right :
    toℕ (SignalDef.startBit sig₂) + toℕ (SignalDef.bitLength sig₂)
      ≤ toℕ (SignalDef.startBit sig₁)
    → SignalsDisjoint sig₁ sig₂

-- Convert SignalsDisjoint to the ⊎ form needed by injectBits-preserves-disjoint
SignalsDisjoint→⊎ : ∀ {sig₁ sig₂} → SignalsDisjoint sig₁ sig₂
  → toℕ (SignalDef.startBit sig₁) + toℕ (SignalDef.bitLength sig₁) ≤ toℕ (SignalDef.startBit sig₂)
  ⊎ toℕ (SignalDef.startBit sig₂) + toℕ (SignalDef.bitLength sig₂) ≤ toℕ (SignalDef.startBit sig₁)
SignalsDisjoint→⊎ (disjoint-left p) = inj₁ p
SignalsDisjoint→⊎ (disjoint-right p) = inj₂ p

-- ============================================================================
-- extract-disjoint-inject: Extraction unaffected by disjoint injection
-- ============================================================================
-- Key insight: Use injectBits-preserves-disjoint at the bit level,
-- then lift through the signal abstraction layers.

-- For unsigned signals (simpler case, demonstrates the pattern)
extract-disjoint-inject-unsigned :
  ∀ (n : ℕ) (sig₁ sig₂ : SignalDef) (byteOrder : ByteOrder) (frame : CANFrame)
  → SignalsDisjoint sig₁ sig₂
  → (bounds-ok₁ : inBounds (signalValue (+ n) sig₁) (SignalDef.minimum sig₁) (SignalDef.maximum sig₁) ≡ true)
  → (factor≢0 : SignalDef.factor sig₁ ≢ 0ℚ)
  → (n<2^bl : n < 2 ^ toℕ (SignalDef.bitLength sig₁))
  → (fits₁ : toℕ (SignalDef.startBit sig₁) + toℕ (SignalDef.bitLength sig₁) ≤ 64)
  → (fits₂ : toℕ (SignalDef.startBit sig₂) + toℕ (SignalDef.bitLength sig₂) ≤ 64)
  → (injectSignal (signalValue (+ n) sig₁) sig₁ byteOrder frame >>= λ frame' →
       extractSignal frame' sig₂ byteOrder)
    ≡ extractSignal frame sig₂ byteOrder

-- LittleEndian case: no byte swapping
extract-disjoint-inject-unsigned n sig₁ sig₂ LittleEndian frame disj bounds-ok₁ factor≢0 n<2^bl fits₁ fits₂ =
  proof
  where
    open CANFrame frame

    value₁ : ℚ
    value₁ = signalValue (+ n) sig₁

    -- Reduction: injectSignal computes to just (injectedFrame ...)
    inject-reduces : injectSignal value₁ sig₁ LittleEndian frame ≡ just (injectedFrame n sig₁ LittleEndian frame n<2^bl)
    inject-reduces = injectSignal-reduces-unsigned n sig₁ LittleEndian frame bounds-ok₁ factor≢0 n<2^bl

    -- The injected bytes (LittleEndian: no swap)
    injectedBytes : Data.Vec.Vec Byte 8
    injectedBytes = injectBits {toℕ (SignalDef.bitLength sig₁)} payload (toℕ (SignalDef.startBit sig₁))
                      (ℕToBitVec {toℕ (SignalDef.bitLength sig₁)} n n<2^bl)

    -- Disjointness in ⊎ form
    disj⊎ : toℕ (SignalDef.startBit sig₁) + toℕ (SignalDef.bitLength sig₁) ≤ toℕ (SignalDef.startBit sig₂)
          ⊎ toℕ (SignalDef.startBit sig₂) + toℕ (SignalDef.bitLength sig₂) ≤ toℕ (SignalDef.startBit sig₁)
    disj⊎ = SignalsDisjoint→⊎ disj

    -- Key lemma: extraction at sig₂ is preserved through injection at sig₁
    bits-preserved : extractBits {toℕ (SignalDef.bitLength sig₂)} injectedBytes (toℕ (SignalDef.startBit sig₂))
                   ≡ extractBits {toℕ (SignalDef.bitLength sig₂)} payload (toℕ (SignalDef.startBit sig₂))
    bits-preserved = injectBits-preserves-disjoint payload
                       (toℕ (SignalDef.startBit sig₁)) (toℕ (SignalDef.startBit sig₂))
                       (ℕToBitVec {toℕ (SignalDef.bitLength sig₁)} n n<2^bl)
                       disj⊎ fits₁ fits₂

    -- extractSignalCore on injectedFrame equals extractSignalCore on original frame
    core-preserved : extractSignalCore injectedBytes sig₂ ≡ extractSignalCore payload sig₂
    core-preserved = cong (λ bits → toSigned (bitVecToℕ bits) (toℕ (SignalDef.bitLength sig₂)) (SignalDef.isSigned sig₂))
                          bits-preserved

    -- Full extraction is preserved (extractSignal is a thin wrapper around extractSignalCore)
    proof : (injectSignal value₁ sig₁ LittleEndian frame >>= λ frame' → extractSignal frame' sig₂ LittleEndian)
          ≡ extractSignal frame sig₂ LittleEndian
    proof rewrite inject-reduces | core-preserved = refl

-- BigEndian case: byte swapping cancels
extract-disjoint-inject-unsigned n sig₁ sig₂ BigEndian frame disj bounds-ok₁ factor≢0 n<2^bl fits₁ fits₂ =
  proof
  where
    open CANFrame frame

    value₁ : ℚ
    value₁ = signalValue (+ n) sig₁

    -- Reduction: injectSignal computes to just (injectedFrame ...)
    inject-reduces : injectSignal value₁ sig₁ BigEndian frame ≡ just (injectedFrame n sig₁ BigEndian frame n<2^bl)
    inject-reduces = injectSignal-reduces-unsigned n sig₁ BigEndian frame bounds-ok₁ factor≢0 n<2^bl

    -- For BigEndian: payload is swapped, injected, then swapped back
    swappedPayload : Data.Vec.Vec Byte 8
    swappedPayload = swapBytes payload

    injectedBytesSwapped : Data.Vec.Vec Byte 8
    injectedBytesSwapped = injectBits {toℕ (SignalDef.bitLength sig₁)} swappedPayload (toℕ (SignalDef.startBit sig₁))
                             (ℕToBitVec {toℕ (SignalDef.bitLength sig₁)} n n<2^bl)

    -- The final payload in injectedFrame is swapBytes injectedBytesSwapped
    -- When extracting with BigEndian, we swap again: swapBytes (swapBytes injectedBytesSwapped) = injectedBytesSwapped

    -- Disjointness in ⊎ form
    disj⊎ : toℕ (SignalDef.startBit sig₁) + toℕ (SignalDef.bitLength sig₁) ≤ toℕ (SignalDef.startBit sig₂)
          ⊎ toℕ (SignalDef.startBit sig₂) + toℕ (SignalDef.bitLength sig₂) ≤ toℕ (SignalDef.startBit sig₁)
    disj⊎ = SignalsDisjoint→⊎ disj

    -- Key lemma: extraction at sig₂ is preserved (on swapped bytes)
    bits-preserved : extractBits {toℕ (SignalDef.bitLength sig₂)} injectedBytesSwapped (toℕ (SignalDef.startBit sig₂))
                   ≡ extractBits {toℕ (SignalDef.bitLength sig₂)} swappedPayload (toℕ (SignalDef.startBit sig₂))
    bits-preserved = injectBits-preserves-disjoint swappedPayload
                       (toℕ (SignalDef.startBit sig₁)) (toℕ (SignalDef.startBit sig₂))
                       (ℕToBitVec {toℕ (SignalDef.bitLength sig₁)} n n<2^bl)
                       disj⊎ fits₁ fits₂

    -- Swap cancellation for extraction
    swap-cancel-injected : swapBytes (swapBytes injectedBytesSwapped) ≡ injectedBytesSwapped
    swap-cancel-injected = swapBytes-involutive injectedBytesSwapped

    -- extractSignalCore sees injectedBytesSwapped (after double swap cancels)
    core-preserved : extractSignalCore injectedBytesSwapped sig₂ ≡ extractSignalCore swappedPayload sig₂
    core-preserved = cong (λ bits → toSigned (bitVecToℕ bits) (toℕ (SignalDef.bitLength sig₂)) (SignalDef.isSigned sig₂))
                          bits-preserved

    -- Full proof
    proof : (injectSignal value₁ sig₁ BigEndian frame >>= λ frame' → extractSignal frame' sig₂ BigEndian)
          ≡ extractSignal frame sig₂ BigEndian
    proof rewrite inject-reduces | swap-cancel-injected | core-preserved = refl

-- For signed signals (same pattern as unsigned)
extract-disjoint-inject-signed :
  ∀ (z : ℤ) (sig₁ sig₂ : SignalDef) (byteOrder : ByteOrder) (frame : CANFrame)
  → SignalsDisjoint sig₁ sig₂
  → (bounds-ok₁ : inBounds (signalValue z sig₁) (SignalDef.minimum sig₁) (SignalDef.maximum sig₁) ≡ true)
  → (factor≢0 : SignalDef.factor sig₁ ≢ 0ℚ)
  → (bl>0 : toℕ (SignalDef.bitLength sig₁) > 0)
  → (sf : SignedFits z (toℕ (SignalDef.bitLength sig₁)))
  → (fits₁ : toℕ (SignalDef.startBit sig₁) + toℕ (SignalDef.bitLength sig₁) ≤ 64)
  → (fits₂ : toℕ (SignalDef.startBit sig₂) + toℕ (SignalDef.bitLength sig₂) ≤ 64)
  → (injectSignal (signalValue z sig₁) sig₁ byteOrder frame >>= λ frame' →
       extractSignal frame' sig₂ byteOrder)
    ≡ extractSignal frame sig₂ byteOrder

-- LittleEndian case
extract-disjoint-inject-signed z sig₁ sig₂ LittleEndian frame disj bounds-ok₁ factor≢0 bl>0 sf fits₁ fits₂ =
  proof
  where
    open CANFrame frame

    value₁ : ℚ
    value₁ = signalValue z sig₁

    n : ℕ
    n = fromSigned z (toℕ (SignalDef.bitLength sig₁))

    n<2^bl : n < 2 ^ toℕ (SignalDef.bitLength sig₁)
    n<2^bl = SignedFits-implies-fromSigned-bounded z (toℕ (SignalDef.bitLength sig₁)) bl>0 sf

    inject-reduces : injectSignal value₁ sig₁ LittleEndian frame ≡ just (injectedFrame n sig₁ LittleEndian frame n<2^bl)
    inject-reduces = injectSignal-reduces-signed z sig₁ LittleEndian frame bounds-ok₁ factor≢0 bl>0 sf

    injectedBytes : Data.Vec.Vec Byte 8
    injectedBytes = injectBits {toℕ (SignalDef.bitLength sig₁)} payload (toℕ (SignalDef.startBit sig₁))
                      (ℕToBitVec {toℕ (SignalDef.bitLength sig₁)} n n<2^bl)

    disj⊎ : toℕ (SignalDef.startBit sig₁) + toℕ (SignalDef.bitLength sig₁) ≤ toℕ (SignalDef.startBit sig₂)
          ⊎ toℕ (SignalDef.startBit sig₂) + toℕ (SignalDef.bitLength sig₂) ≤ toℕ (SignalDef.startBit sig₁)
    disj⊎ = SignalsDisjoint→⊎ disj

    bits-preserved : extractBits {toℕ (SignalDef.bitLength sig₂)} injectedBytes (toℕ (SignalDef.startBit sig₂))
                   ≡ extractBits {toℕ (SignalDef.bitLength sig₂)} payload (toℕ (SignalDef.startBit sig₂))
    bits-preserved = injectBits-preserves-disjoint payload
                       (toℕ (SignalDef.startBit sig₁)) (toℕ (SignalDef.startBit sig₂))
                       (ℕToBitVec {toℕ (SignalDef.bitLength sig₁)} n n<2^bl)
                       disj⊎ fits₁ fits₂

    core-preserved : extractSignalCore injectedBytes sig₂ ≡ extractSignalCore payload sig₂
    core-preserved = cong (λ bits → toSigned (bitVecToℕ bits) (toℕ (SignalDef.bitLength sig₂)) (SignalDef.isSigned sig₂))
                          bits-preserved

    proof : (injectSignal value₁ sig₁ LittleEndian frame >>= λ frame' → extractSignal frame' sig₂ LittleEndian)
          ≡ extractSignal frame sig₂ LittleEndian
    proof rewrite inject-reduces | core-preserved = refl

-- BigEndian case
extract-disjoint-inject-signed z sig₁ sig₂ BigEndian frame disj bounds-ok₁ factor≢0 bl>0 sf fits₁ fits₂ =
  proof
  where
    open CANFrame frame

    value₁ : ℚ
    value₁ = signalValue z sig₁

    n : ℕ
    n = fromSigned z (toℕ (SignalDef.bitLength sig₁))

    n<2^bl : n < 2 ^ toℕ (SignalDef.bitLength sig₁)
    n<2^bl = SignedFits-implies-fromSigned-bounded z (toℕ (SignalDef.bitLength sig₁)) bl>0 sf

    inject-reduces : injectSignal value₁ sig₁ BigEndian frame ≡ just (injectedFrame n sig₁ BigEndian frame n<2^bl)
    inject-reduces = injectSignal-reduces-signed z sig₁ BigEndian frame bounds-ok₁ factor≢0 bl>0 sf

    swappedPayload : Data.Vec.Vec Byte 8
    swappedPayload = swapBytes payload

    injectedBytesSwapped : Data.Vec.Vec Byte 8
    injectedBytesSwapped = injectBits {toℕ (SignalDef.bitLength sig₁)} swappedPayload (toℕ (SignalDef.startBit sig₁))
                             (ℕToBitVec {toℕ (SignalDef.bitLength sig₁)} n n<2^bl)

    disj⊎ : toℕ (SignalDef.startBit sig₁) + toℕ (SignalDef.bitLength sig₁) ≤ toℕ (SignalDef.startBit sig₂)
          ⊎ toℕ (SignalDef.startBit sig₂) + toℕ (SignalDef.bitLength sig₂) ≤ toℕ (SignalDef.startBit sig₁)
    disj⊎ = SignalsDisjoint→⊎ disj

    bits-preserved : extractBits {toℕ (SignalDef.bitLength sig₂)} injectedBytesSwapped (toℕ (SignalDef.startBit sig₂))
                   ≡ extractBits {toℕ (SignalDef.bitLength sig₂)} swappedPayload (toℕ (SignalDef.startBit sig₂))
    bits-preserved = injectBits-preserves-disjoint swappedPayload
                       (toℕ (SignalDef.startBit sig₁)) (toℕ (SignalDef.startBit sig₂))
                       (ℕToBitVec {toℕ (SignalDef.bitLength sig₁)} n n<2^bl)
                       disj⊎ fits₁ fits₂

    swap-cancel-injected : swapBytes (swapBytes injectedBytesSwapped) ≡ injectedBytesSwapped
    swap-cancel-injected = swapBytes-involutive injectedBytesSwapped

    core-preserved : extractSignalCore injectedBytesSwapped sig₂ ≡ extractSignalCore swappedPayload sig₂
    core-preserved = cong (λ bits → toSigned (bitVecToℕ bits) (toℕ (SignalDef.bitLength sig₂)) (SignalDef.isSigned sig₂))
                          bits-preserved

    proof : (injectSignal value₁ sig₁ BigEndian frame >>= λ frame' → extractSignal frame' sig₂ BigEndian)
          ≡ extractSignal frame sig₂ BigEndian
    proof rewrite inject-reduces | swap-cancel-injected | core-preserved = refl

-- ============================================================================
-- disjoint-signals-commute: Order-independent injection of disjoint signals
-- ============================================================================

-- Frame-level commutativity using the payloadIso abstraction
-- This lifts injectPayload-commute to frames uniformly for all byte orders
injectedFrame-commute :
  ∀ (n₁ n₂ : ℕ) (sig₁ sig₂ : SignalDef) (byteOrder : ByteOrder) (frame : CANFrame)
    (n₁<2^bl₁ : n₁ < 2 ^ toℕ (SignalDef.bitLength sig₁))
    (n₂<2^bl₂ : n₂ < 2 ^ toℕ (SignalDef.bitLength sig₂))
  → SignalsDisjoint sig₁ sig₂
  → (fits₁ : toℕ (SignalDef.startBit sig₁) + toℕ (SignalDef.bitLength sig₁) ≤ 64)
  → (fits₂ : toℕ (SignalDef.startBit sig₂) + toℕ (SignalDef.bitLength sig₂) ≤ 64)
  → injectedFrame n₂ sig₂ byteOrder (injectedFrame n₁ sig₁ byteOrder frame n₁<2^bl₁) n₂<2^bl₂
    ≡ injectedFrame n₁ sig₁ byteOrder (injectedFrame n₂ sig₂ byteOrder frame n₂<2^bl₂) n₁<2^bl₁
injectedFrame-commute n₁ n₂ sig₁ sig₂ bo frame n₁<2^bl₁ n₂<2^bl₂ disj fits₁ fits₂ =
  cong (λ p → record frame { payload = p }) payload-commute
  where
    open import Aletheia.CAN.Endianness using (injectPayload; injectPayload-commute)

    s₁ = toℕ (SignalDef.startBit sig₁)
    s₂ = toℕ (SignalDef.startBit sig₂)
    payload = CANFrame.payload frame
    bits₁ = ℕToBitVec n₁ n₁<2^bl₁
    bits₂ = ℕToBitVec n₂ n₂<2^bl₂

    -- The payload commutativity follows directly from injectPayload-commute
    payload-commute : injectPayload s₂ bits₂ bo (injectPayload s₁ bits₁ bo payload)
                    ≡ injectPayload s₁ bits₁ bo (injectPayload s₂ bits₂ bo payload)
    payload-commute = injectPayload-commute s₁ s₂ bits₁ bits₂ bo payload (SignalsDisjoint→⊎ disj) fits₁ fits₂

-- Unsigned signals: disjoint injections commute
disjoint-signals-commute-unsigned :
  ∀ (n₁ n₂ : ℕ) (sig₁ sig₂ : SignalDef) (byteOrder : ByteOrder) (frame : CANFrame)
  → SignalsDisjoint sig₁ sig₂
  → (bounds-ok₁ : inBounds (signalValue (+ n₁) sig₁) (SignalDef.minimum sig₁) (SignalDef.maximum sig₁) ≡ true)
  → (bounds-ok₂ : inBounds (signalValue (+ n₂) sig₂) (SignalDef.minimum sig₂) (SignalDef.maximum sig₂) ≡ true)
  → (factor≢0₁ : SignalDef.factor sig₁ ≢ 0ℚ)
  → (factor≢0₂ : SignalDef.factor sig₂ ≢ 0ℚ)
  → (n₁<2^bl₁ : n₁ < 2 ^ toℕ (SignalDef.bitLength sig₁))
  → (n₂<2^bl₂ : n₂ < 2 ^ toℕ (SignalDef.bitLength sig₂))
  → (fits₁ : toℕ (SignalDef.startBit sig₁) + toℕ (SignalDef.bitLength sig₁) ≤ 64)
  → (fits₂ : toℕ (SignalDef.startBit sig₂) + toℕ (SignalDef.bitLength sig₂) ≤ 64)
  → (injectSignal (signalValue (+ n₁) sig₁) sig₁ byteOrder frame >>= λ f₁ →
       injectSignal (signalValue (+ n₂) sig₂) sig₂ byteOrder f₁)
    ≡ (injectSignal (signalValue (+ n₂) sig₂) sig₂ byteOrder frame >>= λ f₂ →
       injectSignal (signalValue (+ n₁) sig₁) sig₁ byteOrder f₂)
disjoint-signals-commute-unsigned n₁ n₂ sig₁ sig₂ byteOrder frame disj bounds-ok₁ bounds-ok₂ factor≢0₁ factor≢0₂ n₁<2^bl₁ n₂<2^bl₂ fits₁ fits₂ =
  proof
  where
    v₁ = signalValue (+ n₁) sig₁
    v₂ = signalValue (+ n₂) sig₂

    -- Reduction lemmas
    inject₁-reduces : injectSignal v₁ sig₁ byteOrder frame ≡ just (injectedFrame n₁ sig₁ byteOrder frame n₁<2^bl₁)
    inject₁-reduces = injectSignal-reduces-unsigned n₁ sig₁ byteOrder frame bounds-ok₁ factor≢0₁ n₁<2^bl₁

    inject₂-reduces : injectSignal v₂ sig₂ byteOrder frame ≡ just (injectedFrame n₂ sig₂ byteOrder frame n₂<2^bl₂)
    inject₂-reduces = injectSignal-reduces-unsigned n₂ sig₂ byteOrder frame bounds-ok₂ factor≢0₂ n₂<2^bl₂

    frame₁ = injectedFrame n₁ sig₁ byteOrder frame n₁<2^bl₁
    frame₂ = injectedFrame n₂ sig₂ byteOrder frame n₂<2^bl₂

    inject₂-on-frame₁ : injectSignal v₂ sig₂ byteOrder frame₁ ≡ just (injectedFrame n₂ sig₂ byteOrder frame₁ n₂<2^bl₂)
    inject₂-on-frame₁ = injectSignal-reduces-unsigned n₂ sig₂ byteOrder frame₁ bounds-ok₂ factor≢0₂ n₂<2^bl₂

    inject₁-on-frame₂ : injectSignal v₁ sig₁ byteOrder frame₂ ≡ just (injectedFrame n₁ sig₁ byteOrder frame₂ n₁<2^bl₁)
    inject₁-on-frame₂ = injectSignal-reduces-unsigned n₁ sig₁ byteOrder frame₂ bounds-ok₁ factor≢0₁ n₁<2^bl₁

    -- Frame commutativity from the abstraction
    frames-equal : injectedFrame n₂ sig₂ byteOrder frame₁ n₂<2^bl₂ ≡ injectedFrame n₁ sig₁ byteOrder frame₂ n₁<2^bl₁
    frames-equal = injectedFrame-commute n₁ n₂ sig₁ sig₂ byteOrder frame n₁<2^bl₁ n₂<2^bl₂ disj fits₁ fits₂

    proof : (injectSignal v₁ sig₁ byteOrder frame >>= λ f₁ → injectSignal v₂ sig₂ byteOrder f₁)
          ≡ (injectSignal v₂ sig₂ byteOrder frame >>= λ f₂ → injectSignal v₁ sig₁ byteOrder f₂)
    proof rewrite inject₁-reduces | inject₂-reduces | inject₂-on-frame₁ | inject₁-on-frame₂ | frames-equal = refl

-- ============================================================================
-- IMPLEMENTATION NOTES
-- ============================================================================
{-
Proof Strategy:
===============

Phase 3 verification proof status (updated 2026-01-21):

PROOF STATUS BY LAYER:
======================

LAYER 0 (BitVec): ✅ COMPLETE
  - testBit-setBit-same, testBit-setBit-diff, setBit-setBit-comm
  - Location: Aletheia.Data.BitVec

LAYER 1 (Bit operations): ✅ COMPLETE
  - extractBits-injectBits-roundtrip ✅
  - injectBits-preserves-earlier-bit ✅
  - injectBits-preserves-later-bit ✅
  - injectBits-preserves-disjoint ✅
  - Location: Aletheia.CAN.Endianness

LAYER 2 (Integer conversion): ✅ COMPLETE
  - fromSigned-toSigned-roundtrip ✅
  - toSigned-fromSigned-roundtrip ✅
  - fromSigned-bounded-neg ✅
  - SignedFits-implies-fromSigned-bounded ✅
  - Location: This module (Properties.agda)

LAYER 3 (Scaling): ✅ COMPLETE (both directions)
  - removeScaling-applyScaling-exact ✅ (ℤ → ℚ → ℤ roundtrip, exact)
  - applyScaling-removeScaling-bounded ✅ (ℚ → ℤ → ℚ roundtrip, bounded by factor)
  - applyScaling-injective ✅
  - removeScaling-factor-zero-iff-nothing ✅
  - scaling-bounds-pos ✅, scaling-bounds-neg ✅
  - Location: This module (Properties.agda)

LAYER 4 (Composition): ✅ COMPLETE
  - extractSignal-injectSignal-roundtrip-unsigned ✅
  - extractSignal-injectSignal-roundtrip-signed ✅
  - injectSignal-reduces-unsigned ✅, injectSignal-reduces-signed ✅
  - extractSignal-reduces-unsigned ✅, extractSignal-reduces-signed ✅
  - Location: This module (Properties.agda)

  Key refactoring: extractSignal uses pure computational core functions
  (extractSignalCore, scaleExtracted, extractionBytes) to enable clean
  rewriting in proofs. See Aletheia.CAN.Encoding for these helpers.

NON-OVERLAP: TODO
  - disjoint-signals-commute (can use injectBits-preserves-disjoint)
  - extract-disjoint-inject (can use injectBits-preserves-disjoint)
-}
