{-# OPTIONS --safe --without-K #-}

-- All proofs complete! bitVec-roundtrip and bitVecToℕ-bounded proven without postulates.

-- Conversion between ℕ and BitVec at the serialization boundary.
--
-- Purpose: Prove ℕ ↔ BitVec roundtrip ONCE, then never reason about bits via ℕ again.
-- Operations: bitVecToℕ, ℕToBitVec, with roundtrip proof.
-- Role: Serialization boundary for CAN frames - isolates arithmetic from structure.
--
-- Philosophy: This is the ONLY module where we prove arithmetic facts about bits.
-- All other bit reasoning uses the structural BitVec abstraction.
module Aletheia.Data.BitVec.Conversion where

open import Aletheia.Data.BitVec
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _<_; _^_; _%_)
open import Data.Nat.DivMod using (_mod_; _/_)
open import Data.Fin using (Fin; toℕ; fromℕ<)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; inspect; [_])
open import Data.Vec using (Vec; []; _∷_)

-- ============================================================================
-- BITVEC → ℕ (always total)
-- ============================================================================

-- Convert a bitvector to a natural number (little-endian: LSB first)
bitVecToℕ : ∀ {n} → BitVec n → ℕ
bitVecToℕ [] = 0
bitVecToℕ (false ∷ bs) = 2 * bitVecToℕ bs
bitVecToℕ (true ∷ bs) = 1 + 2 * bitVecToℕ bs

-- ============================================================================
-- PARITY DECOMPOSITION (turn arithmetic into data)
-- ============================================================================

-- Non-dependent decomposition: every ℕ is either 2*k or 1+2*k
data ParityDecomp (m : ℕ) : Set where
  even : (k : ℕ) → m ≡ 2 * k → ParityDecomp m
  odd  : (k : ℕ) → m ≡ 1 + 2 * k → ParityDecomp m

-- Helper functions for parity decomposition
private
  open import Data.Nat using (s≤s; z≤n)
  open import Data.Nat.DivMod using (m≡m%n+[m/n]*n; m%n<n)
  open import Data.Nat.Properties using (+-comm; *-comm; +-identityˡ)
  open import Data.Empty using (⊥; ⊥-elim)
  open import Relation.Nullary using (¬_)

  -- If m % 2 ≡ 0, then m ≡ 2 * (m / 2)
  decomp-even : ∀ m → m % 2 ≡ 0 → m ≡ 2 * (m / 2)
  decomp-even m eq =
    begin
      m                     ≡⟨ m≡m%n+[m/n]*n m 2 ⟩
      m % 2 + (m / 2) * 2   ≡⟨ cong (_+ (m / 2) * 2) eq ⟩
      0 + (m / 2) * 2       ≡⟨ +-identityˡ ((m / 2) * 2) ⟩
      (m / 2) * 2           ≡⟨ *-comm (m / 2) 2 ⟩
      2 * (m / 2)
    ∎
    where open Relation.Binary.PropositionalEquality.≡-Reasoning

  -- If m % 2 ≡ 1, then m ≡ 1 + 2 * (m / 2)
  decomp-odd : ∀ m → m % 2 ≡ 1 → m ≡ 1 + 2 * (m / 2)
  decomp-odd m eq =
    begin
      m                     ≡⟨ m≡m%n+[m/n]*n m 2 ⟩
      m % 2 + (m / 2) * 2   ≡⟨ cong (_+ (m / 2) * 2) eq ⟩
      1 + (m / 2) * 2       ≡⟨ cong (1 +_) (*-comm (m / 2) 2) ⟩
      1 + 2 * (m / 2)
    ∎
    where open Relation.Binary.PropositionalEquality.≡-Reasoning

  -- m % 2 cannot be ≥ 2
  ¬m%2≥2 : ∀ m r → m % 2 ≡ suc (suc r) → ⊥
  ¬m%2≥2 m r eq =
    let bound : m % 2 < 2
        bound = m%n<n m 2
        bad : suc (suc r) < 2
        bad = subst (_< 2) eq bound
    in ¬sucr<2 r bad
    where
      open import Data.Nat.Properties using (≤⇒≯)
      open import Data.Nat using (_≤_; s≤s; z≤n)

      ¬sucr<2 : ∀ r → suc (suc r) < 2 → ⊥
      ¬sucr<2 r (s≤s (s≤s ()))

-- Prove decomposition using % and / (non-dependent!)
parity-decomp : ∀ m → ParityDecomp m
parity-decomp m with m % 2 | inspect (_% 2) m
... | zero | [ eq ] = even (m / 2) (decomp-even m eq)
... | suc zero | [ eq ] = odd (m / 2) (decomp-odd m eq)
... | suc (suc r) | [ eq ] = ⊥-elim (¬m%2≥2 m r eq)

-- ============================================================================
-- ARITHMETIC BRIDGE LEMMAS (confined plumbing - proven once)
-- ============================================================================

-- These four lemmas relate % and / to the canonical even/odd forms
-- They are the ONLY arithmetic facts needed for the reverse roundtrip
private
  open import Data.Fin using (toℕ)

  -- Arithmetic bridge lemmas using stdlib (no induction, no impossible cases!)
  open import Data.Nat.DivMod using (m*n%n≡0; m*n/n≡m; [m+kn]%n≡m%n; m≡m%n+[m/n]*n)
  open import Data.Nat.Properties using (*-comm; *-cancelʳ-≡)
  open import Data.Nat using (pred)
  open import Relation.Nullary using (¬_)

  -- Proof that 2 ≠ 0 (needed for cancellation)
  2≢0 : ¬ (2 ≡ 0)
  2≢0 ()

  even-mod-2 : ∀ k → (2 * k) % 2 ≡ 0
  even-mod-2 k = trans (cong (_% 2) (*-comm 2 k)) (m*n%n≡0 k 2)

  odd-mod-2 : ∀ k → (1 + 2 * k) % 2 ≡ 1
  odd-mod-2 k =
    begin
      (1 + 2 * k) % 2   ≡⟨ cong (_% 2) (cong (1 +_) (*-comm 2 k)) ⟩
      (1 + k * 2) % 2   ≡⟨ [m+kn]%n≡m%n 1 k 2 ⟩
      1 % 2             ≡⟨⟩
      1
    ∎
    where open import Relation.Binary.PropositionalEquality using (cong)
          open Relation.Binary.PropositionalEquality.≡-Reasoning

  even-div-2 : ∀ k → (2 * k) / 2 ≡ k
  even-div-2 k = trans (cong (_/ 2) (*-comm 2 k)) (m*n/n≡m k 2)

  odd-div-2 : ∀ k → (1 + 2 * k) / 2 ≡ k
  odd-div-2 k =
    let value = 1 + 2 * k
        -- Division algorithm: value ≡ value % 2 + (value / 2) * 2
        alg : value ≡ value % 2 + (value / 2) * 2
        alg = m≡m%n+[m/n]*n value 2
        -- We know value % 2 ≡ 1
        r≡1 : value % 2 ≡ 1
        r≡1 = odd-mod-2 k
        -- Substitute: value ≡ 1 + (value / 2) * 2
        step1 : value ≡ 1 + (value / 2) * 2
        step1 = trans alg (cong (λ x → x + (value / 2) * 2) r≡1)
        -- Cancel 1 using pred (suc is injective)
        step2 : 2 * k ≡ ((value / 2) * 2)
        step2 = cong pred step1
        -- Rewrite LHS to k * 2 form
        step3 : k * 2 ≡ ((value / 2) * 2)
        step3 = trans (sym (*-comm 2 k)) step2
        -- Cancel * 2 using nonzero proof (k * 2 ≡ (value/2) * 2  ⇒  k ≡ value/2)
        step4 : k ≡ value / 2
        step4 = *-cancelʳ-≡ k (value / 2) 2 step3
    in sym step4

-- ============================================================================
-- ℕ → BITVEC (using parity decomposition)
-- ============================================================================

-- Helper: halving preserves bounds
private
  half-bound-even : ∀ {m k n} → m ≡ 2 * k → m < 2 ^ suc n → k < 2 ^ n
  half-bound-even {m} {k} {n} eq bound =
    subst (_< 2 ^ n) (even-div-2 k) (m<n*o⇒m/o<n {2 * k} {2 ^ n} {2} bound'')
    where
      open import Data.Nat.DivMod using (m<n*o⇒m/o<n)
      open import Data.Nat.Properties using (*-identityˡ; *-comm)

      bound' : 2 * k < 2 ^ suc n
      bound' = subst (_< 2 ^ suc n) eq bound

      -- Normalize: 2 ^ suc n ≡ 2 ^ n * 2
      normalize : 2 ^ suc n ≡ 2 ^ n * 2
      normalize rewrite *-comm (2 ^ n) 2 | *-identityˡ (2 ^ n) = refl
        where
          open import Data.Nat.Properties using (*-comm; *-identityˡ)

      bound'' : 2 * k < 2 ^ n * 2
      bound'' = subst (2 * k <_) normalize bound'

      -- m<n*o⇒m/o<n {2*k} {2^n} {2} : 2*k < 2^n * 2 → (2*k)/2 < 2^n
      -- even-div-2   : (2*k)/2 ≡ k
      -- Transport: (2*k)/2 < 2^n to k < 2^n

  half-bound-odd : ∀ {m k n} → m ≡ 1 + 2 * k → m < 2 ^ suc n → k < 2 ^ n
  half-bound-odd {m} {k} {n} eq bound =
    subst (_< 2 ^ n) (even-div-2 k) (m<n*o⇒m/o<n {2 * k} {2 ^ n} {2} bound2k')
    where
      open import Data.Nat.DivMod using (m<n*o⇒m/o<n)
      open import Data.Nat.Properties using (n≤1+n; ≤-<-trans; *-identityˡ)
      open import Data.Nat using (_≤_; s≤s)

      -- Normalize: 2 ^ suc n ≡ 2 ^ n * 2
      normalize : 2 ^ suc n ≡ 2 ^ n * 2
      normalize rewrite *-comm (2 ^ n) 2 | *-identityˡ (2 ^ n) = refl
        where
          open import Data.Nat.Properties using (*-comm; *-identityˡ)

      bound' : 1 + 2 * k < 2 ^ suc n
      bound' = subst (_< 2 ^ suc n) eq bound

      bound'' : 1 + 2 * k < 2 ^ n * 2
      bound'' = subst (1 + 2 * k <_) normalize bound'

      -- Show 2*k ≤ 1 + 2*k using n≤1+n
      2k≤1+2k : 2 * k ≤ 1 + 2 * k
      2k≤1+2k = n≤1+n (2 * k)

      -- Use transitivity: 2*k ≤ 1 + 2*k < 2^n * 2 implies 2*k < 2^n * 2
      bound2k' : 2 * k < 2 ^ n * 2
      bound2k' = ≤-<-trans 2k≤1+2k bound''

      -- m<n*o⇒m/o<n {2*k} {2^n} {2} : 2*k < 2^n * 2 → (2*k)/2 < 2^n
      -- even-div-2   : (2*k)/2 ≡ k
      -- Transport: (2*k)/2 < 2^n to k < 2^n

-- Core conversion function: takes parity as a witness parameter
-- This is the key: parity is DATA, not COMPUTATION
-- Mutual with public API so core can recurse via wrapper
mutual
  private
    ℕToBitVec′ : ∀ {n} (value : ℕ) → ParityDecomp value → value < 2 ^ n → BitVec n
    ℕToBitVec′ {zero} value _ bound = []
    ℕToBitVec′ {suc n} value (even k eq) bound =
      false ∷ ℕToBitVec {n} k (half-bound-even {value} {k} {n} eq bound)
    ℕToBitVec′ {suc n} value (odd k eq) bound =
      true ∷ ℕToBitVec {n} k (half-bound-odd {value} {k} {n} eq bound)

  -- Public API: thin wrapper that computes parity once
  ℕToBitVec : ∀ {n} (value : ℕ) → value < 2 ^ n → BitVec n
  ℕToBitVec {n} value bound = ℕToBitVec′ {n} value (parity-decomp value) bound

-- ============================================================================
-- ROUNDTRIP PROOF (The hard part - proven ONCE)
-- ============================================================================

-- Helper: Division by 2 preserves bound
private
  div2-bound : ∀ value n → value < 2 ^ suc n → value / 2 < 2 ^ n
  div2-bound value n bound = m<n*o⇒m/o<n {value} {2 ^ n} {2} bound'
    where
      open import Data.Nat.DivMod using (m<n*o⇒m/o<n)
      open import Data.Nat.Properties using (*-comm; *-identityˡ)

      -- Normalize: 2 ^ suc n ≡ 2 ^ n * 2
      normalize : 2 ^ suc n ≡ 2 ^ n * 2
      normalize rewrite *-comm (2 ^ n) 2 | *-identityˡ (2 ^ n) = refl

      bound' : value < 2 ^ n * 2
      bound' = subst (value <_) normalize bound

{- ✅ COMPLETED: bitVec-roundtrip proven without postulates

   Property: bitVec-roundtrip
   ---------------------------
   Converting ℕ → BitVec → ℕ preserves the original value

   ∀ {n} (value : ℕ) (bound : value < 2^n)
     → bitVecToℕ (ℕToBitVec value bound) ≡ value

   Proof structure:
   - Induction on n
   - Base case (n = 0): value < 2^0 = 1, so value = 0. Trivial.
   - Inductive case:
     * Specialize division algorithm to base 2: value = (value % 2) + (value / 2) * 2
     * Prove arithmetic facts on ℕ (mod-div-when-1, mod-div-when-0)
     * Bridge Bool test to arithmetic via mod2≡1-from-bool, mod2≡0-from-bool
     * Apply inductive hypothesis with explicit type annotations

   Key lemmas:
   - m≡m%n+[m/n]*n from Data.Nat.DivMod (division algorithm)
   - toℕ-fromℕ< from Data.Fin.Properties (coherence between _mod_ and _%_)
   - Explicit type annotations to help unification with div-helper

   This is the ONLY place we need deep arithmetic reasoning.
-}

-- ============================================================================
-- BASE-2 SPECIALIZATION OF DIVISION ALGORITHM
-- ============================================================================
-- The stdlib provides m≡m%n+[m/n]*n generically, but does not specialize to base 2.
-- This is the right place to add that specialization (representation theorem).

private
  -- Step 1: Specialize division algorithm to base 2
  -- Use _%_ (ℕ → ℕ) not _mod_ (ℕ → Fin) to avoid coercion issues
  mod2-cases : ∀ value → value ≡ (value % 2) + (value / 2) * 2
  mod2-cases value =
    begin
      value
        ≡⟨ m≡m%n+[m/n]*n value 2 ⟩
      (value % 2) + (value / 2) * 2
        ∎
    where
      open import Data.Nat.DivMod using (m≡m%n+[m/n]*n)
      import Relation.Binary.PropositionalEquality as Eq
      open Eq.≡-Reasoning

  -- Step 2: Prove arithmetic facts directly on ℕ (no Bool encoding)
  mod-div-when-1 : ∀ value → (value % 2) ≡ 1 → value ≡ 1 + (value / 2) * 2
  mod-div-when-1 value h =
    begin
      value
        ≡⟨ mod2-cases value ⟩
      (value % 2) + (value / 2) * 2
        ≡⟨ cong (_+ (value / 2) * 2) h ⟩
      1 + (value / 2) * 2
        ∎
    where
      import Relation.Binary.PropositionalEquality as Eq
      open Eq.≡-Reasoning

  mod-div-when-0 : ∀ value → (value % 2) ≡ 0 → value ≡ (value / 2) * 2
  mod-div-when-0 value h =
    begin
      value
        ≡⟨ mod2-cases value ⟩
      (value % 2) + (value / 2) * 2
        ≡⟨ cong (_+ (value / 2) * 2) h ⟩
      0 + (value / 2) * 2
        ≡⟨⟩
      (value / 2) * 2
        ∎
    where
      import Relation.Binary.PropositionalEquality as Eq
      open Eq.≡-Reasoning

  -- Step 3: Bool conversion lemmas (bridge between test and arithmetic)
  -- Convert from toℕ (value mod 2) (Fin 2 → ℕ) to (value % 2) (ℕ)
  --
  -- Coherence lemma: toℕ ∘ _mod_ and _%_ are propositionally equal
  -- This bridges kernel primitives (mod-helper) and library wrappers
  -- Proof: Use toℕ-fromℕ< from stdlib to unfold the definitions
  open import Data.Nat using (NonZero)
  open import Data.Fin.Properties using (toℕ-fromℕ<)

  toℕ-mod-≡-% : ∀ m n .{{_ : NonZero n}} → toℕ (m mod n) ≡ m % n
  toℕ-mod-≡-% m n = toℕ-fromℕ< (m%n<n m n)
    where
      open import Data.Nat.DivMod using (m%n<n)

  mod2≡1-from-bool : ∀ value → (toℕ (value mod 2) Data.Nat.≡ᵇ 1) ≡ true → (value % 2) ≡ 1
  mod2≡1-from-bool value h =
    trans (sym (toℕ-mod-≡-% value 2)) (≡ᵇ⇒≡ (toℕ (value mod 2)) 1 (T-from-≡ h))
    where
      open import Data.Nat using (_≡ᵇ_)
      open import Data.Nat.Properties using (≡ᵇ⇒≡)
      open import Data.Bool using (T)
      -- Convert (x ≡ true) to T x
      T-from-≡ : ∀ {x} → x ≡ true → T x
      T-from-≡ {true} refl = _
      T-from-≡ {false} ()

  mod2≡0-from-bool : ∀ value → (toℕ (value mod 2) Data.Nat.≡ᵇ 1) ≡ false → (value % 2) ≡ 0
  mod2≡0-from-bool value h with value mod 2 in eq
  ... | Fin.zero = trans (sym (toℕ-mod-≡-% value 2)) (cong toℕ eq)
  ... | Fin.suc Fin.zero = ⊥-elim (true≢false h)
    where
      open import Data.Empty using (⊥; ⊥-elim)
      -- When value mod 2 = Fin.suc Fin.zero, toℕ (value mod 2) = 1, so (1 ≡ᵇ 1) = true
      -- But h says it's false, contradiction
      true≢false : true ≡ false → ⊥
      true≢false ()

-- Proof: Base-2 representation uniqueness under bound
-- This is the ONE place we pay the arithmetic tax (mod/div reasoning)
bitVec-roundtrip : ∀ n (value : ℕ) (bound : value < 2 ^ n)
  → bitVecToℕ (ℕToBitVec {n} value bound) ≡ value
bitVec-roundtrip zero value bound = sym (n<1⇒n≡0 bound)
  where
    open import Data.Nat.Properties using (n<1⇒n≡0)
bitVec-roundtrip (suc n) value bound = helper (parity-decomp value) refl
  where
    open import Data.Nat.Properties using (*-comm)
    import Relation.Binary.PropositionalEquality as Eq
    open Eq.≡-Reasoning

    -- Helper that takes parity as a parameter (avoids with-abstraction)
    helper : (pd : ParityDecomp value)
           → ℕToBitVec {suc n} value bound ≡ ℕToBitVec′ {suc n} value pd bound
           → bitVecToℕ (ℕToBitVec {suc n} value bound) ≡ value
    helper (even k eq) expand =
          let ih : bitVecToℕ (ℕToBitVec {n} k (half-bound-even {value} {k} {n} eq bound)) ≡ k
              ih = bitVec-roundtrip n k (half-bound-even {value} {k} {n} eq bound)
          in begin
            bitVecToℕ (ℕToBitVec {suc n} value bound)
              ≡⟨ cong bitVecToℕ expand ⟩
            2 * bitVecToℕ (ℕToBitVec {n} k (half-bound-even {value} {k} {n} eq bound))
              ≡⟨ cong (2 *_) ih ⟩
            2 * k
              ≡⟨ sym eq ⟩
            value
              ∎
    helper (odd k eq) expand =
          let ih : bitVecToℕ (ℕToBitVec {n} k (half-bound-odd {value} {k} {n} eq bound)) ≡ k
              ih = bitVec-roundtrip n k (half-bound-odd {value} {k} {n} eq bound)
          in begin
            bitVecToℕ (ℕToBitVec {suc n} value bound)
              ≡⟨ cong bitVecToℕ expand ⟩
            1 + 2 * bitVecToℕ (ℕToBitVec {n} k (half-bound-odd {value} {k} {n} eq bound))
              ≡⟨ cong (1 +_) (cong (2 *_) ih) ⟩
            1 + 2 * k
              ≡⟨ sym eq ⟩
            value
              ∎

-- ============================================================================
-- ADDITIONAL PROPERTIES (useful but not critical)
-- ============================================================================

-- Proof: bitVecToℕ always produces a value < 2^n
bitVecToℕ-bounded : ∀ {n} (bits : BitVec n) → bitVecToℕ bits < 2 ^ n
bitVecToℕ-bounded {zero} [] = s≤s z≤n
  where
    open import Data.Nat using (_≤_; z≤n; s≤s)
bitVecToℕ-bounded {suc n} (false ∷ bs) = *-monoʳ-< 2 (bitVecToℕ-bounded bs)
  where
    open import Data.Nat.Properties using (*-monoʳ-<)
bitVecToℕ-bounded {suc n} (true ∷ bs) = helper
  where
    open import Data.Nat using (_≤_)
    open import Data.Nat.Properties using (*-identityˡ; +-mono-≤; +-suc)
    open import Relation.Binary.PropositionalEquality using (subst; refl; sym)

    -- Normalize 2 * k to k + k to avoid 1 * k in normal form
    normalize₂ : ∀ k → 2 * k ≡ k + k
    normalize₂ k rewrite *-identityˡ k = refl

    -- Show suc k + suc k ≡ suc (suc (k + k))
    suc+suc : ∀ k → suc k + suc k ≡ suc (suc (k + k))
    suc+suc k rewrite +-suc k k = refl

    -- Clean proof using transport (no rewrite hell!)
    helper : bitVecToℕ (true ∷ bs) < 2 ^ suc n
    helper =
      let
        IH≤ : suc (bitVecToℕ bs) ≤ 2 ^ n
        IH≤ = bitVecToℕ-bounded bs

        summed : suc (bitVecToℕ bs) + suc (bitVecToℕ bs) ≤ 2 ^ n + 2 ^ n
        summed = +-mono-≤ IH≤ IH≤

        -- Transport RHS from (2 ^ n + 2 ^ n) to (2 * 2 ^ n) which is definitionally (2 ^ suc n)
        step1 : suc (bitVecToℕ bs) + suc (bitVecToℕ bs) ≤ 2 ^ suc n
        step1 = subst (λ y → suc (bitVecToℕ bs) + suc (bitVecToℕ bs) ≤ y) (sym (normalize₂ (2 ^ n))) summed

        -- Transport LHS using suc+suc
        step2 : suc (suc (bitVecToℕ bs + bitVecToℕ bs)) ≤ 2 ^ suc n
        step2 = subst (λ x → x ≤ 2 ^ suc n) (suc+suc (bitVecToℕ bs)) step1

        -- Final transport to match goal: suc (1 + normalize₂ (bitVecToℕ bs)) = suc (suc (bitVecToℕ bs + bitVecToℕ bs))
        final : bitVecToℕ (true ∷ bs) < 2 ^ suc n
        final = subst (λ x → suc (1 + x) ≤ 2 ^ suc n) (sym (normalize₂ (bitVecToℕ bs))) step2
      in
      final

-- Proof: ℕToBitVec is injective (follows directly from bitVec-roundtrip)
ℕToBitVec-injective : ∀ n (v₁ v₂ : ℕ) (b₁ : v₁ < 2 ^ n) (b₂ : v₂ < 2 ^ n)
  → ℕToBitVec {n} v₁ b₁ ≡ ℕToBitVec {n} v₂ b₂
  → v₁ ≡ v₂
ℕToBitVec-injective n v₁ v₂ b₁ b₂ eq = trans (trans (sym rt1) (cong bitVecToℕ eq)) rt2
  where
    open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

    rt1 : bitVecToℕ (ℕToBitVec {n} v₁ b₁) ≡ v₁
    rt1 = bitVec-roundtrip n v₁ b₁

    rt2 : bitVecToℕ (ℕToBitVec {n} v₂ b₂) ≡ v₂
    rt2 = bitVec-roundtrip n v₂ b₂

-- ============================================================================
-- BITVEC INJECTIVITY (structural proof, no arithmetic)
-- ============================================================================

-- Prove that bitVecToℕ is injective (structural induction on vectors)
-- This is the key lemma that makes reverse roundtrip trivial
private
  open import Data.Nat.Properties using (<-irrelevant; *-cancelˡ-≡; m+1+n≢m)
  open import Data.Empty using (⊥-elim)
  open import Data.Nat using (suc)

  -- Helper: even ≠ odd (2*a ≠ 1 + 2*b)
  -- Proof: 2*a % 2 ≡ 0, but (1 + 2*b) % 2 ≡ 1, contradiction
  even≢1+even : ∀ a b → 2 * a ≡ 1 + 2 * b → ⊥
  even≢1+even a b eq = absurd (trans (sym (even-mod-2 a)) (trans (cong (_% 2) eq) (odd-mod-2 b)))
    where
      absurd : 0 ≡ 1 → ⊥
      absurd ()

bitVecToℕ-injective : ∀ {n} (bs₁ bs₂ : BitVec n) → bitVecToℕ bs₁ ≡ bitVecToℕ bs₂ → bs₁ ≡ bs₂
bitVecToℕ-injective [] [] eq = refl
bitVecToℕ-injective (false ∷ bs₁) (false ∷ bs₂) eq =
  cong (false ∷_) (bitVecToℕ-injective bs₁ bs₂ (*-cancelˡ-≡ (bitVecToℕ bs₁) (bitVecToℕ bs₂) 2 eq))
bitVecToℕ-injective (false ∷ bs₁) (true ∷ bs₂) eq =
  ⊥-elim (even≢1+even (bitVecToℕ bs₁) (bitVecToℕ bs₂) eq)
bitVecToℕ-injective (true ∷ bs₁) (false ∷ bs₂) eq =
  ⊥-elim (even≢1+even (bitVecToℕ bs₂) (bitVecToℕ bs₁) (sym eq))
bitVecToℕ-injective (true ∷ bs₁) (true ∷ bs₂) eq =
  cong (true ∷_) (bitVecToℕ-injective bs₁ bs₂ (cancel-1+2*))
  where
    open import Data.Nat.Properties using (suc-injective)
    cancel-1+2* : bitVecToℕ bs₁ ≡ bitVecToℕ bs₂
    cancel-1+2* = *-cancelˡ-≡ (bitVecToℕ bs₁) (bitVecToℕ bs₂) 2 (suc-injective eq)

-- ============================================================================
-- REVERSE ROUNDTRIP PROOF (via injectivity - 2 lines!)
-- ============================================================================

-- Proof: Reverse round-trip (BitVec → ℕ → BitVec preserves structure)
-- Strategy: Use forward roundtrip + injectivity (no % 2, no with, no parity!)

bitVec-roundtrip-reverse : ∀ n (bits : BitVec n) (proof : bitVecToℕ bits < 2 ^ n)
  → ℕToBitVec {n} (bitVecToℕ bits) proof ≡ bits
bitVec-roundtrip-reverse n bits proof =
  bitVecToℕ-injective (ℕToBitVec (bitVecToℕ bits) proof) bits
    (bitVec-roundtrip n (bitVecToℕ bits) proof)

-- ============================================================================
-- IMPLEMENTATION NOTES
-- ============================================================================
{-
This module contains the ONLY arithmetic reasoning about bits in the entire
CAN encoding system.

Once we prove bitVec-roundtrip, all other modules work at the BitVec level:
- CAN.Endianness: extractBits/injectBits return/take BitVec
- CAN.Encoding: Convert to ℕ only at the toSigned boundary
- CAN.Encoding.Properties: Pure structural proofs, no arithmetic

The architecture:

  BitVec ←→ ℕ ←→ ℤ ←→ ℚ
  (struct) (arith) (signed) (physical)
     ↑
     └─ Prove roundtrip ONCE (this module)
     └─ All other reasoning stays in BitVec domain

This is the escape hatch from arithmetic hell.
-}
