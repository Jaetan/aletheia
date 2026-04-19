{-# OPTIONS --safe --without-K #-}

-- Layer 3 (ℚ scaling) and Layers A/A'/C/D (floor bounds, normalization,
-- algebraic chain, structural bridge) for CAN signal encoding.
--
-- Purpose: Quarantine all rational arithmetic so the integer layer
--   (Properties.Arithmetic.Integer) and the composition layer
--   (Properties.Roundtrip) never touch ℚ field laws.
--
-- Layering (arithmetic firewall — each lower layer is quarantined):
--   * Layer 3: ℚ scaling. The ONLY place rational field laws are used. The
--     `ℚ-cancel` lemma and `÷-via-ℚᵘ` bridge localize representation details
--     so Layers 4+ never see `mkℚᵘ` / `toℚᵘ`.
--   * Layer A (floor bounds): `floor-lower`/`floor-upper` quarantine division.
--   * Layer A' (algebraic normalization): coercions, field identities,
--     distributivity — shifts/unshifts offsets, cancels subtractions.
--   * Layer C (algebraic chain): semantic core of the reverse direction.
--     Uses ONLY floor bounds, stdlib monotonicity, and Layer A' helpers.
--     NO begin…∎ chains, NO cong at this layer.
--   * Layer D (structural bridge): pattern-matches on factor's sign to
--     select positive/negative scaling bounds.
--
-- Public API:
--   Layer 3: removeScaling-zero⇒nothing; removeScaling-nothing⇒zero;
--            removeScaling-factor-zero-iff-nothing;
--            removeScaling-applyScaling-exact; applyScaling-injective
--   Layer D: applyScaling-removeScaling-bounded
--
-- DEFER-stdlib-mandate (Cat 29): this module uses `.{{_ : NonZero q}}` instance
-- arguments on the stdlib's `_÷_` for ℚ (sites: `toℚᵘ-homo-÷`, `÷-via-ℚᵘ`,
-- `ℚ-cancel`, `÷-*-cancel`, and the Layer D helpers that thread `>-nonZero` /
-- `<-nonZero` witnesses through `_÷ᵣ_`). Stdlib mandates the instance arg on
-- `_÷_`; we cannot remove it without giving up the stdlib division. No instance
-- search ambiguity is introduced — every call site supplies the witness
-- explicitly via `{{≢-nonZero …}}` / `{{>-nonZero …}}` / `{{<-nonZero …}}`,
-- so instance resolution is trivial. This is the DEFER recorded against Cat 29
-- per the universal rules' in-source exception path.
module Aletheia.CAN.Encoding.Properties.Arithmetic.Rational where

open import Aletheia.CAN.Encoding.Arithmetic using (applyScaling; removeScaling)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _<_; _≤_; _^_; _>_; z≤n; s≤s)
open import Data.Nat.Coprimality using (1-coprimeTo) renaming (sym to coprime-sym)
open import Data.Nat.DivMod as ℕ using (n/1≡n; n%1≡0)
open import Data.Integer as ℤ using (ℤ; +_; -[1+_])
open import Data.Integer.DivMod as ℤ using (div-pos-is-/ℕ)
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ; floor; normalize; 1/_; NonZero; ≢-nonZero; mkℚ; toℚᵘ; fromℚᵘ; _≤ᵇ_) renaming (_+_ to _+ᵣ_; _*_ to _*ᵣ_; _-_ to _-ᵣ_; _≤_ to _≤ᵣ_; _<_ to _<ᵣ_; _/_ to _/ᵣ_; _÷_ to _÷ᵣ_; -_ to -ᵣ_)
open import Data.Rational.Unnormalised.Base as ℚᵘ using (ℚᵘ; mkℚᵘ)
open import Data.Rational.Literals using (fromℤ)
open import Data.Rational.Properties using (normalize-coprime; mkℚ-cong; +-inverseʳ; *-inverseʳ; *-identityʳ; *-assoc; fromℚᵘ-toℚᵘ; toℚᵘ-homo-*; toℚᵘ-homo-1/; fromℚᵘ-cong; ↥p≡0⇒p≡0) renaming (+-identityʳ to ℚ-+-identityʳ; +-assoc to ℚ-+-assoc; ≤-antisym to ≤ᵣ-antisym; ≤ᵇ⇒≤ to ≤ᵇ⇒≤ᵣ)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open ≡-Reasoning
open import Relation.Nullary using (¬_)

-- ============================================================================
-- LAYER 3: SCALING PROPERTIES (isolated ℚ lemmas)
-- ============================================================================
-- These are the ONLY proofs involving rational arithmetic.
-- They are isolated and small.

-- ✅ Layer 3 scaling proofs COMPLETE:
--   - removeScaling-applyScaling-exact: ℤ → ℚ → ℤ roundtrip is exact
--   - applyScaling-injective: applyScaling is injective when factor ≠ 0
--   - removeScaling-factor-zero-iff-nothing: API contract for failure mode

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

-- Constructor disjointness helper: just x is not equal to nothing.
private
  just≢nothing : ∀ {a} {A : Set a} {x : A} → just x ≢ nothing
  just≢nothing ()

-- Semantic direction: nothing result implies factor was zero
-- The real theorem: proves the guard is the ONLY failure mode.
--
-- The proof case-splits on the two Bool comparisons inside the new isZero
-- fast path (`(factor ≤ᵇ 0ℚ) ∧ (0ℚ ≤ᵇ factor)`). When either is `false`,
-- `isZero factor` reduces to `false`, so `removeScaling` reduces to `just _`
-- and `result≡nothing : just _ ≡ nothing` is a direct contradiction. When
-- both are `true`, antisymmetry of `_≤_` on ℚ yields `factor ≡ 0ℚ` directly.
removeScaling-nothing⇒zero : ∀ (value factor offset : ℚ)
  → removeScaling value factor offset ≡ nothing
  → factor ≡ 0ℚ
removeScaling-nothing⇒zero value factor offset result≡nothing
  with factor ≤ᵇ 0ℚ in eq1 | 0ℚ ≤ᵇ factor in eq2
... | false | _     = ⊥-elim (just≢nothing result≡nothing)
... | true  | false = ⊥-elim (just≢nothing result≡nothing)
... | true  | true  = ≤ᵣ-antisym factor≤0 0≤factor
  where
    open import Relation.Binary.PropositionalEquality using (subst; sym)
    open import Data.Bool using (T)
    open import Data.Unit using (tt)
    factor≤0 : factor ≤ᵣ 0ℚ
    factor≤0 = ≤ᵇ⇒≤ᵣ (subst T (sym eq1) tt)
    0≤factor : 0ℚ ≤ᵣ factor
    0≤factor = ≤ᵇ⇒≤ᵣ (subst T (sym eq2) tt)

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
  z/1≡fromℤ : ∀ (z : ℤ) → z /ᵣ 1 ≡ fromℤ z
  z/1≡fromℤ (+ n) = trans (normalize-coprime (coprime-sym (1-coprimeTo n))) (mkℚ-cong refl refl)
  z/1≡fromℤ -[1+ n ] = trans (cong -ᵣ_ (normalize-coprime (coprime-sym (1-coprimeTo (suc n)))))
                        (trans (mkℚ-cong refl refl) refl)

  floor-int : ∀ (z : ℤ) → floor (z /ᵣ 1) ≡ z
  floor-int z = trans (cong floor (z/1≡fromℤ z)) (floor-fromℤ z)

-- Semantic bridge lemma: what does removeScaling ∘ applyScaling evaluate to?
-- This preserves the definitional connection between the result and floor (raw / 1)
-- PROVEN: removeScaling-applyScaling-value and removeScaling-applyScaling-exact
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
      -- Helper: (a + b) - b ≡ a (standard derivation from field laws).
      -- stdlib 2.3 `Data.Rational.Properties` has no lemma of this shape at
      -- propositional equality; the closest neighbour is `+-minus-telescope`
      -- in `Data.Rational.Unnormalised.Properties` (`(p - q) + (q - r) ≃ p - r`
      -- on ℚᵘ setoid equality `≃`), which would require `toℚᵘ`/`fromℚᵘ`
      -- transport to apply here — strictly more work than the 3-line local
      -- proof. Retained as a local helper; swap in a stdlib lemma if one
      -- lands on propositional-ℚ in a future stdlib bump.
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
      ≡ just (floor (raw /ᵣ 1))
  removeScaling-applyScaling-value raw factor@(mkℚ (+ 0) _ _) offset factor≢0 =
    ⊥-elim (ℚ-nonzero⇒num-nonzero factor factor≢0 refl)
  removeScaling-applyScaling-value raw factor@(mkℚ (+ ℕ.suc _) _ _) offset factor≢0 =
    -- After pattern match, divideUnnorm reduces to ÷ᵘ, and fromℚᵘ (... ÷ᵘ ...) ≡ ... ÷ᵣ ... by ÷-via-ℚᵘ
    let numer = (applyScaling raw factor offset) -ᵣ offset
    in cong just (trans (cong floor (÷-via-ℚᵘ numer factor {{≢-nonZero factor≢0}}))
                        (cong floor (ℚ-cancel (raw /ᵣ 1) factor offset {{≢-nonZero factor≢0}})))
  removeScaling-applyScaling-value raw factor@(mkℚ -[1+ _ ] _ _) offset factor≢0 =
    let numer = (applyScaling raw factor offset) -ᵣ offset
    in cong just (trans (cong floor (÷-via-ℚᵘ numer factor {{≢-nonZero factor≢0}}))
                        (cong floor (ℚ-cancel (raw /ᵣ 1) factor offset {{≢-nonZero factor≢0}})))

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
  floor-lower : ∀ (q : ℚ) → (floor q /ᵣ 1) ≤ᵣ q
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
  floor-upper : ∀ (q : ℚ) → q <ᵣ ((floor q ℤ.+ ℤ.+ 1) /ᵣ 1)
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
  -- Needed because stdlib's fromℤ-homo-+ is not available in stdlib 2.3
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
    ((raw ℤ.+ ℤ.+ 1) /ᵣ 1) *ᵣ f ≡ (raw /ᵣ 1) *ᵣ f +ᵣ f
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

  -- (raw/1 * f + f) + o ≡ applyScaling raw f o + f (rearrange for bounds proofs)
  apply-rearrange : ∀ (raw : ℤ) (factor offset : ℚ) →
    ((raw /ᵣ 1) *ᵣ factor +ᵣ factor) +ᵣ offset ≡ applyScaling raw factor offset +ᵣ factor
  apply-rearrange raw factor offset = begin
    ((raw /ᵣ 1) *ᵣ factor +ᵣ factor) +ᵣ offset  ≡⟨ ℚ-+-assoc ((raw /ᵣ 1) *ᵣ factor) factor offset ⟩
    (raw /ᵣ 1) *ᵣ factor +ᵣ (factor +ᵣ offset)  ≡⟨ cong ((raw /ᵣ 1) *ᵣ factor +ᵣ_) (ℚ-+-comm factor offset) ⟩
    (raw /ᵣ 1) *ᵣ factor +ᵣ (offset +ᵣ factor)  ≡⟨ sym (ℚ-+-assoc ((raw /ᵣ 1) *ᵣ factor) offset factor) ⟩
    applyScaling raw factor offset +ᵣ factor                  ∎
    where open import Data.Rational.Properties renaming (+-assoc to ℚ-+-assoc; +-comm to ℚ-+-comm)

  -- (x - c) + c ≡ x (additive cancellation)
  sub-add-cancel : ∀ (x c : ℚ) → (x -ᵣ c) +ᵣ c ≡ x
  sub-add-cancel x c = begin
    (x -ᵣ c) +ᵣ c      ≡⟨ ℚ-+-assoc x (-ᵣ c) c ⟩
    x +ᵣ ((-ᵣ c) +ᵣ c) ≡⟨ cong (x +ᵣ_) (ℚ-+-inverseˡ c) ⟩
    x +ᵣ 0ℚ            ≡⟨ ℚ-+-identityʳ x ⟩
    x                  ∎
    where open import Data.Rational.Properties renaming (+-assoc to ℚ-+-assoc; +-inverseˡ to ℚ-+-inverseˡ; +-identityʳ to ℚ-+-identityʳ)

  -- a ≤ b - c ⟹ a + c ≤ b (shift offset right)
  ≤-shift-offset : ∀ (a b c : ℚ) → a ≤ᵣ b -ᵣ c → a +ᵣ c ≤ᵣ b
  ≤-shift-offset a b c a≤b-c = subst (a +ᵣ c ≤ᵣ_) (sub-add-cancel b c) (+-monoˡ-≤ c a≤b-c)
    where open import Data.Rational.Properties using (+-monoˡ-≤)

  -- a - c < b ⟹ a < b + c (shift offset right, strict)
  <-shift-offset : ∀ (a b c : ℚ) → a -ᵣ c <ᵣ b → a <ᵣ b +ᵣ c
  <-shift-offset a b c a-c<b = subst (_<ᵣ b +ᵣ c) (sub-add-cancel a c) (+-monoˡ-< c a-c<b)
    where open import Data.Rational.Properties using (+-monoˡ-<)

  -- a - c ≤ b ⟹ a ≤ b + c (unshift offset, non-strict)
  ≤-unshift-offset : ∀ (a b c : ℚ) → a -ᵣ c ≤ᵣ b → a ≤ᵣ b +ᵣ c
  ≤-unshift-offset a b c a-c≤b = subst (_≤ᵣ b +ᵣ c) (sub-add-cancel a c) (+-monoˡ-≤ c a-c≤b)
    where open import Data.Rational.Properties using (+-monoˡ-≤)

  -- b < a - c ⟹ b + c < a (unshift offset, strict, flipped)
  <-unshift-offset : ∀ (a b c : ℚ) → b <ᵣ a -ᵣ c → b +ᵣ c <ᵣ a
  <-unshift-offset a b c b<a-c = subst (b +ᵣ c <ᵣ_) (sub-add-cancel a c) (+-monoˡ-< c b<a-c)
    where open import Data.Rational.Properties using (+-monoˡ-<)

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
      floor/1≡raw/1 : (floor q /ᵣ 1) ≡ (raw /ᵣ 1)
      floor/1≡raw/1 = cong (Data.Rational._/ 1) floor≡raw

      raw/1≤q : (raw /ᵣ 1) ≤ᵣ q
      raw/1≤q = subst (_≤ᵣ q) floor/1≡raw/1 (floor-lower q)

      -- floor-upper q : q <ᵣ ((floor q + 1) / 1)
      floor+1/1≡raw+1/1 : ((floor q ℤ.+ ℤ.+ 1) /ᵣ 1) ≡ ((raw ℤ.+ ℤ.+ 1) /ᵣ 1)
      floor+1/1≡raw+1/1 = cong (λ x → (x ℤ.+ ℤ.+ 1) /ᵣ 1) floor≡raw

      q<raw+1/1 : q <ᵣ ((raw ℤ.+ ℤ.+ 1) /ᵣ 1)
      q<raw+1/1 = <-respʳ-≡ floor+1/1≡raw+1/1 (floor-upper q)

      -- Step 2: multiply by positive factor (preserves order)
      -- For positive factor, NonNegative and NonZero are derivable
      instance
        _ : NonNegative factor
        _ = pos⇒nonNeg factor
          where open import Data.Rational.Properties using (pos⇒nonNeg)

        _ : NonZero factor
        _ = >-nonZero factor-pos

      raw/1*f≤q*f : (raw /ᵣ 1) *ᵣ factor ≤ᵣ q *ᵣ factor
      raw/1*f≤q*f = *-monoʳ-≤-nonNeg factor raw/1≤q

      q*f<raw+1/1*f : q *ᵣ factor <ᵣ ((raw ℤ.+ ℤ.+ 1) /ᵣ 1) *ᵣ factor
      q*f<raw+1/1*f = *-monoˡ-<-pos factor q<raw+1/1

      -- Step 3: cancel division (q * f = value - offset)
      raw/1*f≤v-o : (raw /ᵣ 1) *ᵣ factor ≤ᵣ value -ᵣ offset
      raw/1*f≤v-o = subst ((raw /ᵣ 1) *ᵣ factor ≤ᵣ_) (÷-*-cancel (value -ᵣ offset) factor) raw/1*f≤q*f

      v-o<raw+1/1*f : value -ᵣ offset <ᵣ ((raw ℤ.+ ℤ.+ 1) /ᵣ 1) *ᵣ factor
      v-o<raw+1/1*f = subst (_<ᵣ ((raw ℤ.+ ℤ.+ 1) /ᵣ 1) *ᵣ factor) (÷-*-cancel (value -ᵣ offset) factor) q*f<raw+1/1*f

      -- Step 4: shift offset, use raw+1*f identity for upper bound
      left-bound : applyScaling raw factor offset ≤ᵣ value
      left-bound = ≤-shift-offset ((raw /ᵣ 1) *ᵣ factor) value offset raw/1*f≤v-o

      -- For right bound: v - o < raw/1*f + f, add offset to get v < raw/1*f + f + o
      -- Then rewrite: (raw/1*f + f) + o = (raw/1*f + o) + f = result + f by commutativity
      -- raw+1*f≡raw*f+f : (raw+1)/1 * f ≡ raw/1 * f + f
      v-o<raw/1*f+f : value -ᵣ offset <ᵣ (raw /ᵣ 1) *ᵣ factor +ᵣ factor
      v-o<raw/1*f+f = subst (value -ᵣ offset <ᵣ_) (raw+1*f≡raw*f+f raw factor) v-o<raw+1/1*f

      v<raw/1*f+f+o : value <ᵣ ((raw /ᵣ 1) *ᵣ factor +ᵣ factor) +ᵣ offset
      v<raw/1*f+f+o = <-shift-offset value ((raw /ᵣ 1) *ᵣ factor +ᵣ factor) offset v-o<raw/1*f+f

      right-bound : value <ᵣ applyScaling raw factor offset +ᵣ factor
      right-bound = subst (value <ᵣ_) (apply-rearrange raw factor offset) v<raw/1*f+f+o

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
      floor/1≡raw/1 : (floor q /ᵣ 1) ≡ (raw /ᵣ 1)
      floor/1≡raw/1 = cong (Data.Rational._/ 1) floor≡raw

      raw/1≤q : (raw /ᵣ 1) ≤ᵣ q
      raw/1≤q = subst (_≤ᵣ q) floor/1≡raw/1 (floor-lower q)

      floor+1/1≡raw+1/1 : ((floor q ℤ.+ ℤ.+ 1) /ᵣ 1) ≡ ((raw ℤ.+ ℤ.+ 1) /ᵣ 1)
      floor+1/1≡raw+1/1 = cong (λ x → (x ℤ.+ ℤ.+ 1) /ᵣ 1) floor≡raw

      q<raw+1/1 : q <ᵣ ((raw ℤ.+ ℤ.+ 1) /ᵣ 1)
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
      q*f≤raw/1*f : q *ᵣ factor ≤ᵣ (raw /ᵣ 1) *ᵣ factor
      q*f≤raw/1*f = *-monoʳ-≤-nonPos factor raw/1≤q

      -- *-monoˡ-<-neg : p < q → (p * r) > (q * r) for neg r
      -- So q < raw+1/1 gives raw+1/1*f < q*f
      raw+1/1*f<q*f : ((raw ℤ.+ ℤ.+ 1) /ᵣ 1) *ᵣ factor <ᵣ q *ᵣ factor
      raw+1/1*f<q*f = *-monoˡ-<-neg factor q<raw+1/1

      -- Step 3: cancel division (q * f = value - offset)
      -- q*f ≤ raw/1*f becomes value - offset ≤ raw/1*f
      v-o≤raw/1*f : value -ᵣ offset ≤ᵣ (raw /ᵣ 1) *ᵣ factor
      v-o≤raw/1*f = subst (_≤ᵣ (raw /ᵣ 1) *ᵣ factor) (÷-*-cancel (value -ᵣ offset) factor) q*f≤raw/1*f

      -- raw+1/1*f < q*f becomes raw+1/1*f < value - offset
      raw+1/1*f<v-o : ((raw ℤ.+ ℤ.+ 1) /ᵣ 1) *ᵣ factor <ᵣ value -ᵣ offset
      raw+1/1*f<v-o = subst (((raw ℤ.+ ℤ.+ 1) /ᵣ 1) *ᵣ factor <ᵣ_) (÷-*-cancel (value -ᵣ offset) factor) raw+1/1*f<q*f

      -- Step 4: unshift offset
      -- For right bound: value - offset ≤ raw/1*f implies value ≤ raw/1*f + offset = result
      right-bound : value ≤ᵣ applyScaling raw factor offset
      right-bound = ≤-unshift-offset value ((raw /ᵣ 1) *ᵣ factor) offset v-o≤raw/1*f

      -- For left bound: raw+1/1*f < value - offset
      -- Convert raw+1/1*f to raw/1*f + f using raw+1*f≡raw*f+f
      raw/1*f+f<v-o : (raw /ᵣ 1) *ᵣ factor +ᵣ factor <ᵣ value -ᵣ offset
      raw/1*f+f<v-o = subst (_<ᵣ value -ᵣ offset) (raw+1*f≡raw*f+f raw factor) raw+1/1*f<v-o

      -- raw/1*f + f < value - offset implies (raw/1*f + f) + offset < value
      raw/1*f+f+o<v : ((raw /ᵣ 1) *ᵣ factor +ᵣ factor) +ᵣ offset <ᵣ value
      raw/1*f+f+o<v = <-unshift-offset value ((raw /ᵣ 1) *ᵣ factor +ᵣ factor) offset raw/1*f+f<v-o

      left-bound : applyScaling raw factor offset +ᵣ factor <ᵣ value
      left-bound = subst (_<ᵣ value) (apply-rearrange raw factor offset) raw/1*f+f+o<v

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
