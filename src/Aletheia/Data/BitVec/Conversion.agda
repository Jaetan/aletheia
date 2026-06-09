-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Conversion between ℕ and BitVec at the serialization boundary.
--
-- Purpose: Prove ℕ ↔ BitVec roundtrip ONCE, then never reason about bits via ℕ again.
-- Operations: bitVecToℕ, ℕToBitVec, with roundtrip proof.
-- Role: Serialization boundary for CAN frames - isolates arithmetic from structure.
--
-- Philosophy: This is the ONLY module where we prove arithmetic facts about bits.
-- All other bit reasoning uses the structural BitVec abstraction.
--
-- DEFER-stdlib-mandate (Cat 29): this module uses `.{{_ : NonZero n}}`
-- instance arguments on the stdlib's `_mod_` and `_%_` for ℕ (sites:
-- `toℕ-mod-≡-%`, `mod-pow2-mod2`, `%-cong`, `mod-pow2-div2`, `shiftR-mod-pow2`,
-- and their call chains). Stdlib mandates the instance arg on `_mod_`/`_%_`;
-- we cannot remove it without giving up stdlib modular arithmetic. Every call
-- site supplies the witness explicitly via `{{m^n≢0 …}}` / `{{m*n≢0 …}}`, so
-- instance resolution is trivial and introduces no ambiguity. This is the
-- DEFER recorded against Cat 29 per the universal rules' in-source exception
-- path.
module Aletheia.Data.BitVec.Conversion where

open import Aletheia.Data.BitVec using (BitVec)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _<_; _≤_; _^_; _%_; _<ᵇ_; s≤s; z≤n; pred; NonZero)
open import Data.Nat.DivMod using (_mod_; _/_; m≡m%n+[m/n]*n; m%n<n; m*n%n≡0; m*n/n≡m; [m+kn]%n≡m%n; m<n*o⇒m/o<n; m%[n*o]/o≡m/o%n)
open import Data.Nat.Properties using (*-comm; +-identityˡ; *-cancelʳ-≡; *-identityˡ; n≤1+n; ≤-<-trans; ≡ᵇ⇒≡; n<1⇒n≡0; *-monoʳ-<; +-mono-≤; +-suc; *-cancelˡ-≡; suc-injective; m^n≢0; m*n≢0; *-assoc; <-irrelevant; <ᵇ-reflects-<)
open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.Bool using (Bool; true; false; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary.Reflects using (ofʸ; ofⁿ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Data.Vec using ([]; _∷_; lookup)

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
      ¬sucr<2 : ∀ r → suc (suc r) < 2 → ⊥
      ¬sucr<2 r (s≤s (s≤s ()))

-- Prove decomposition using % and / (non-dependent!)
parity-decomp : ∀ m → ParityDecomp m
parity-decomp m with m % 2 in eq
... | zero        = even (m / 2) (decomp-even m eq)
... | suc zero    = odd (m / 2) (decomp-odd m eq)
... | suc (suc r) = ⊥-elim (¬m%2≥2 m r eq)

-- ============================================================================
-- ARITHMETIC BRIDGE LEMMAS (confined plumbing - proven once)
-- ============================================================================

-- These four lemmas relate % and / to the canonical even/odd forms
-- They are the ONLY arithmetic facts needed for the reverse roundtrip
-- Exported for use by Endianness equivalence proofs.

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
  where open Relation.Binary.PropositionalEquality.≡-Reasoning

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
      bound' : 2 * k < 2 ^ suc n
      bound' = subst (_< 2 ^ suc n) eq bound

      -- Normalize: 2 ^ suc n ≡ 2 ^ n * 2
      normalize : 2 ^ suc n ≡ 2 ^ n * 2
      normalize rewrite *-comm (2 ^ n) 2 | *-identityˡ (2 ^ n) = refl

      bound'' : 2 * k < 2 ^ n * 2
      bound'' = subst (2 * k <_) normalize bound'

  half-bound-odd : ∀ {m k n} → m ≡ 1 + 2 * k → m < 2 ^ suc n → k < 2 ^ n
  half-bound-odd {m} {k} {n} eq bound =
    subst (_< 2 ^ n) (even-div-2 k) (m<n*o⇒m/o<n {2 * k} {2 ^ n} {2} bound2k')
    where
      -- Normalize: 2 ^ suc n ≡ 2 ^ n * 2
      normalize : 2 ^ suc n ≡ 2 ^ n * 2
      normalize rewrite *-comm (2 ^ n) 2 | *-identityˡ (2 ^ n) = refl

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
-- Mutual with public API so core can recurse via wrapper.
-- The `value < 2 ^ n` bound is `@0`-erased (R19 cluster D, AGDA-A-16.4
-- 2026-05-09): the proof slot is structurally needed for type-checking
-- but never inspected at runtime, so MAlonzo can erase it.  Two
-- different proofs of `value < 2 ^ n` produce propositionally equal
-- BitVecs (witness propositional equality of `ℕToBitVec`'s output is
-- now trivial because the proof argument doesn't appear in the result).
-- Unblocks the `injectHelper` Bool fast-path in `Aletheia.CAN.Encoding`.
mutual
  private
    ℕToBitVec′ : ∀ {n} (value : ℕ) → ParityDecomp value → @0 (value < 2 ^ n) → BitVec n
    ℕToBitVec′ {zero} value _ bound = []
    ℕToBitVec′ {suc n} value (even k eq) bound =
      false ∷ ℕToBitVec {n} k (half-bound-even {value} {k} {n} eq bound)
    ℕToBitVec′ {suc n} value (odd k eq) bound =
      true ∷ ℕToBitVec {n} k (half-bound-odd {value} {k} {n} eq bound)

  -- Public API: thin wrapper that computes parity once
  ℕToBitVec : ∀ {n} (value : ℕ) → @0 (value < 2 ^ n) → BitVec n
  ℕToBitVec {n} value bound = ℕToBitVec′ {n} value (parity-decomp value) bound

-- ============================================================================
-- BOOL-DISPATCH SMART CONSTRUCTOR
-- ============================================================================
-- `mkBoundedBitVec` is the verified gateway from a raw ℕ to a `Maybe (BitVec bl)`,
-- doing the bound check via `_<ᵇ_` (Bool) rather than `_<?_` (Dec).  The bound
-- witness needed by `ℕToBitVec` is constructed in-place from `<ᵇ-reflects-<`'s
-- `ofʸ` payload and flows into `ℕToBitVec`'s `@0`-erased slot, so MAlonzo drops
-- it at runtime.  Net runtime cost: one Bool comparison + one `Maybe`
-- constructor — compared to `_<?_`'s `Dec` wrapper (yes/no constructor + the
-- Bool decision internally).
--
-- **Why `<ᵇ-reflects-<` instead of `with ... in eq`:** the `with ... in eq`
-- idiom builds an equation `(n <ᵇ 2 ^ bl) ≡ true` that needs to flow through
-- the consumer's `with`-abstraction.  When a consumer (e.g. a proof of the
-- form `mkBoundedBitVec-just`) tries to `with`-abstract over the same
-- scrutinee, Agda's elaborator generates an ill-typed with-function because
-- the inner `eq` binding doesn't propagate (cf.
-- `feedback_with_in_eq_outer_abstraction_barrier.md` + the empirically-
-- confirmed `n <ᵇ 2 ^ bl != w of type Bool` error this commit reproduces in
-- a 5-line minimal case).
--
-- `Reflects` carries the witness AS DATA inside the constructor (`ofʸ p`
-- when `b = true`).  Pattern-matching on the constructor automatically
-- substitutes `(n <ᵇ 2 ^ bl)` to `true`/`false` in both the runtime body and
-- any proof — no separate `eq` equation needs to thread through abstraction.
-- Both `mkBoundedBitVec` and its consumers can `with`-abstract over the
-- `Reflects` value without crossing the elaboration barrier.
-- Two-with abstraction is required: under `--without-K`, single-`with` on
-- `Reflects … (n <ᵇ 2 ^ bl)` hits a SplitError because the Boolean index is
-- an open expression.  First abstracting `n <ᵇ 2 ^ bl` to a fresh variable,
-- then matching the Reflects constructor against that variable, lets Agda
-- unify the index in each clause.
mkBoundedBitVec : (n bl : ℕ) → Maybe (BitVec bl)
mkBoundedBitVec n bl with n <ᵇ 2 ^ bl | <ᵇ-reflects-< n (2 ^ bl)
... | false | ofⁿ _    = nothing
... | true  | ofʸ n<bl = just (ℕToBitVec n n<bl)

-- Reduction lemma: when `n < 2 ^ bl` holds at the proof level,
-- `mkBoundedBitVec n bl` reduces to `just (ℕToBitVec n n<bl)`.  Consumers
-- compose this lemma into their own reduction chains via `trans` /
-- `with … | reduction-lemma` without needing to abstract over `n <ᵇ 2 ^ bl`.
mkBoundedBitVec-just : ∀ n bl (n<bl : n < 2 ^ bl)
                    → mkBoundedBitVec n bl ≡ just (ℕToBitVec n n<bl)
mkBoundedBitVec-just n bl n<bl with n <ᵇ 2 ^ bl | <ᵇ-reflects-< n (2 ^ bl)
... | true  | ofʸ n<bl' = cong (λ p → just (ℕToBitVec n p)) (<-irrelevant n<bl' n<bl)
... | false | ofⁿ ¬n<bl = ⊥-elim (¬n<bl n<bl)

-- ============================================================================
-- ROUNDTRIP PROOF (The hard part - proven ONCE)
-- ============================================================================

-- Helper: Division by 2 preserves bound
private
  div2-bound : ∀ value n → value < 2 ^ suc n → value / 2 < 2 ^ n
  div2-bound value n bound = m<n*o⇒m/o<n {value} {2 ^ n} {2} bound'
    where
      -- Normalize: 2 ^ suc n ≡ 2 ^ n * 2
      normalize : 2 ^ suc n ≡ 2 ^ n * 2
      normalize rewrite *-comm (2 ^ n) 2 | *-identityˡ (2 ^ n) = refl

      bound' : value < 2 ^ n * 2
      bound' = subst (value <_) normalize bound

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
  toℕ-mod-≡-% : ∀ m n .{{_ : NonZero n}} → toℕ (m mod n) ≡ m % n
  toℕ-mod-≡-% m n = toℕ-fromℕ< (m%n<n m n)

  mod2≡1-from-bool : ∀ value → (toℕ (value mod 2) Data.Nat.≡ᵇ 1) ≡ true → (value % 2) ≡ 1
  mod2≡1-from-bool value h =
    trans (sym (toℕ-mod-≡-% value 2)) (≡ᵇ⇒≡ (toℕ (value mod 2)) 1 (T-from-≡ h))
    where
      -- Convert (x ≡ true) to T x
      T-from-≡ : ∀ {x} → x ≡ true → T x
      T-from-≡ {true} refl = _
      T-from-≡ {false} ()

  mod2≡0-from-bool : ∀ value → (toℕ (value mod 2) Data.Nat.≡ᵇ 1) ≡ false → (value % 2) ≡ 0
  mod2≡0-from-bool value h with value mod 2 in eq
  ... | Fin.zero = trans (sym (toℕ-mod-≡-% value 2)) (cong toℕ eq)
  ... | Fin.suc Fin.zero = ⊥-elim (true≢false h)
    where
      true≢false : true ≡ false → ⊥
      true≢false ()

-- Proof: Base-2 representation uniqueness under bound
-- This is the ONE place we pay the arithmetic tax (mod/div reasoning)
bitVec-roundtrip : ∀ n (value : ℕ) (bound : value < 2 ^ n)
  → bitVecToℕ (ℕToBitVec {n} value bound) ≡ value
bitVec-roundtrip zero value bound = sym (n<1⇒n≡0 bound)
bitVec-roundtrip (suc n) value bound = helper (parity-decomp value) refl
  where
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
bitVecToℕ-bounded {suc n} (false ∷ bs) = *-monoʳ-< 2 (bitVecToℕ-bounded bs)
bitVecToℕ-bounded {suc n} (true ∷ bs) = helper
  where
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
-- SHIFT-RIGHT AND BIT-EXTRACTION LEMMAS
-- ============================================================================
-- These support the extractSignalCoreFast ≡ extractSignalCore proof
-- in Aletheia.CAN.Endianness.

-- Right-shift: x / 2^k via iterated division by 2.
-- Mirrors the private shiftR in CAN.Endianness.
shiftR-conv : ℕ → ℕ → ℕ
shiftR-conv x zero = x
shiftR-conv x (suc k) = shiftR-conv (x / 2) k

-- Bool to ℕ conversion
boolToℕ : Bool → ℕ
boolToℕ false = 0
boolToℕ true = 1

-- Core lemma: bit k of ℕToBitVec v equals shiftR v k % 2.
-- By induction on parity of v (even/odd decomposition) and position k.
ℕToBitVec-lookup : ∀ n (v : ℕ) (bound : v < 2 ^ n) (k : Fin n)
  → boolToℕ (lookup (ℕToBitVec v bound) k) ≡ shiftR-conv v (toℕ k) % 2
ℕToBitVec-lookup (suc n) v bound Fin.zero = go (parity-decomp v) refl
  where
    open Relation.Binary.PropositionalEquality.≡-Reasoning
    go : (pd : ParityDecomp v) → ℕToBitVec {suc n} v bound ≡ ℕToBitVec′ {suc n} v pd bound
       → boolToℕ (lookup (ℕToBitVec v bound) Fin.zero) ≡ v % 2
    go (even q eq) expand = begin
        boolToℕ (lookup (ℕToBitVec v bound) Fin.zero)
      ≡⟨ cong (λ x → boolToℕ (lookup x Fin.zero)) expand ⟩  0
      ≡⟨ sym (even-mod-2 q) ⟩  (2 * q) % 2
      ≡⟨ cong (_% 2) (sym eq) ⟩  v % 2  ∎
    go (odd q eq) expand = begin
        boolToℕ (lookup (ℕToBitVec v bound) Fin.zero)
      ≡⟨ cong (λ x → boolToℕ (lookup x Fin.zero)) expand ⟩  1
      ≡⟨ sym (odd-mod-2 q) ⟩  (1 + 2 * q) % 2
      ≡⟨ cong (_% 2) (sym eq) ⟩  v % 2  ∎
ℕToBitVec-lookup (suc n) v bound (Fin.suc k) = go (parity-decomp v) refl
  where
    open Relation.Binary.PropositionalEquality.≡-Reasoning
    go : (pd : ParityDecomp v) → ℕToBitVec {suc n} v bound ≡ ℕToBitVec′ {suc n} v pd bound
       → boolToℕ (lookup (ℕToBitVec v bound) (Fin.suc k)) ≡ shiftR-conv (v / 2) (toℕ k) % 2
    go (even q eq) expand = begin
        boolToℕ (lookup (ℕToBitVec v bound) (Fin.suc k))
      ≡⟨ cong (λ x → boolToℕ (lookup x (Fin.suc k))) expand ⟩
        boolToℕ (lookup (ℕToBitVec q (half-bound-even {v} {q} {n} eq bound)) k)
      ≡⟨ ℕToBitVec-lookup n q (half-bound-even {v} {q} {n} eq bound) k ⟩
        shiftR-conv q (toℕ k) % 2
      ≡⟨ cong (λ x → shiftR-conv x (toℕ k) % 2) (sym (even-div-2 q)) ⟩
        shiftR-conv ((2 * q) / 2) (toℕ k) % 2
      ≡⟨ cong (λ x → shiftR-conv (x / 2) (toℕ k) % 2) (sym eq) ⟩
        shiftR-conv (v / 2) (toℕ k) % 2  ∎
    go (odd q eq) expand = begin
        boolToℕ (lookup (ℕToBitVec v bound) (Fin.suc k))
      ≡⟨ cong (λ x → boolToℕ (lookup x (Fin.suc k))) expand ⟩
        boolToℕ (lookup (ℕToBitVec q (half-bound-odd {v} {q} {n} eq bound)) k)
      ≡⟨ ℕToBitVec-lookup n q (half-bound-odd {v} {q} {n} eq bound) k ⟩
        shiftR-conv q (toℕ k) % 2
      ≡⟨ cong (λ x → shiftR-conv x (toℕ k) % 2) (sym (odd-div-2 q)) ⟩
        shiftR-conv ((1 + 2 * q) / 2) (toℕ k) % 2
      ≡⟨ cong (λ x → shiftR-conv (x / 2) (toℕ k) % 2) (sym eq) ⟩
        shiftR-conv (v / 2) (toℕ k) % 2  ∎

-- Shifting by k < n bits and taking %2 depends only on the low 2^n bits.
-- Bridges extractCore (uses shiftR b k % 2, no mod) with byteToBitVec (applies % 256 = % 2^8).
private
  -- q * 2^(suc n) ≡ (q * 2^n) * 2  (factor out trailing *2)
  mul-2^suc-as-*2 : ∀ q n → q * (2 ^ suc n) ≡ (q * 2 ^ n) * 2
  mul-2^suc-as-*2 q n = trans (cong (q *_) (*-comm 2 (2 ^ n))) (sym (*-assoc q (2 ^ n) 2))

  -- (b % 2^(suc n)) % 2 ≡ b % 2
  -- b ≡ b%M + (b/M)*M, and (b/M)*M = ((b/M)*2^n)*2. Apply [m+kn]%n≡m%n.
  mod-pow2-mod2 : ∀ b n → .{{_ : NonZero (2 ^ suc n)}}
    → (b % (2 ^ suc n)) % 2 ≡ b % 2
  mod-pow2-mod2 b n = sym (begin
      b % 2
    ≡⟨ cong (_% 2) (m≡m%n+[m/n]*n b (2 ^ suc n)) ⟩
      (b % (2 ^ suc n) + b / (2 ^ suc n) * (2 ^ suc n)) % 2
    ≡⟨ cong (λ x → (b % (2 ^ suc n) + x) % 2) (mul-2^suc-as-*2 (b / (2 ^ suc n)) n) ⟩
      (b % (2 ^ suc n) + (b / (2 ^ suc n) * 2 ^ n) * 2) % 2
    ≡⟨ [m+kn]%n≡m%n (b % (2 ^ suc n)) (b / (2 ^ suc n) * 2 ^ n) 2 ⟩
      (b % (2 ^ suc n)) % 2
    ∎)
    where open Relation.Binary.PropositionalEquality.≡-Reasoning

  -- Congruence for _%_ that carries NonZero instances (avoids lambda-over-NonZero issue)
  %-cong : ∀ b {m n : ℕ} → .{{_ : NonZero m}} → .{{_ : NonZero n}} → m ≡ n → b % m ≡ b % n
  %-cong b refl = refl

  -- (b % 2^(suc n)) / 2 ≡ (b / 2) % 2^n
  -- From m%[n*o]/o≡m/o%n: b % (2^n * 2) / 2 ≡ b / 2 % 2^n.
  mod-pow2-div2 : ∀ b n → .{{_ : NonZero (2 ^ n)}} → .{{_ : NonZero (2 ^ suc n)}}
    → (b % (2 ^ suc n)) / 2 ≡ (b / 2) % (2 ^ n)
  mod-pow2-div2 b n =
    trans (cong (_/ 2) (%-cong b {{m^n≢0 2 (suc n)}} {{m*n≢0 (2 ^ n) 2}} (*-comm 2 (2 ^ n))))
          (m%[n*o]/o≡m/o%n b (2 ^ n) 2 {{m^n≢0 2 n}} {{_}} {{m*n≢0 (2 ^ n) 2}})

shiftR-mod-pow2 : ∀ b n k → .{{_ : NonZero (2 ^ n)}} → k < n
  → shiftR-conv b k % 2 ≡ shiftR-conv (b % (2 ^ n)) k % 2
shiftR-mod-pow2 b (suc n) zero _ =
  sym (mod-pow2-mod2 b n {{m^n≢0 2 (suc n)}})
shiftR-mod-pow2 b (suc n) (suc k) (s≤s k<n) = begin
    shiftR-conv (b / 2) k % 2
  ≡⟨ shiftR-mod-pow2 (b / 2) n k {{nzn}} k<n ⟩
    shiftR-conv ((b / 2) % (2 ^ n)) k % 2
  ≡⟨ cong (λ x → shiftR-conv x k % 2) (sym (mod-pow2-div2 b n {{nzn}} {{nzsn}})) ⟩
    shiftR-conv ((b % (2 ^ suc n)) / 2) k % 2
  ∎
  where open Relation.Binary.PropositionalEquality.≡-Reasoning
        instance nzn = m^n≢0 2 n
        instance nzsn = m^n≢0 2 (suc n)
