{-# OPTIONS --safe --without-K #-}

-- Strip-after-scale substrate for the DecRat parser roundtrip
-- (Track B.3.d commit 2/6).
--
-- Purpose: the Shape B emitter writes every DecRat as
-- `<sign><int>.<frac>` with m = max(a ⊔ b, 1) fractional digits,
-- scaling the magnitude by 2^(m∸a) · 5^(m∸b) so the raw integer
-- denominator becomes 10^m = 2^m · 5^m.  The parser reconstructs
-- `(signed rawNum, m, m)` and canonicalisation then un-scales it
-- back to `(sign, a, b)`.  This file proves the arithmetic identity
-- that makes that collapse possible: stripping 2^p (resp. 5^p) from
-- a magnitude scaled by 2^p (resp. 5^p) is the identity on the
-- post-strip pair.
--
-- The main lemma `strip2-abs-factor` (and its 5-mirror) is
-- unconditional — it holds for any x, including zero and x with its
-- own 2-factors — because the stripper just peels off added primes
-- while its budget lasts.  Canonicality preconditions enter only at
-- the composed `canonicalizeNat-scale` / `canonicalizeDecRat-scale`
-- level, where we need `a > 0 ⇒ 2 ∤ x` and `b > 0 ⇒ 5 ∤ x` to
-- guarantee the post-scale strip exits with the *original*
-- magnitude, not a further-reduced one.
--
-- Proof shape, top to bottom:
--   1. `2∣x*2^suc` / `5∣x*5^suc`: witnesses used to force the `yes`
--      branch of the stripper's internal `with 2 ∣? n` / `5 ∣? n`.
--   2. `strip2-abs-factor` / `strip5-abs-factor`: unconditional
--      cancellation.  Induction on k, base case via `*-identityʳ`,
--      step case via `m*n/n≡m` after assoc/comm rearrangement.

module Aletheia.DBC.DecRat.ScaleLemmas where

open import Aletheia.DBC.DecRat
  using (stripShared2-abs ; stripShared5-abs ; canonicalizeNat ;
         stripShared2-abs-zero ; stripShared5-abs-zero)

open import Data.Nat.Base
  using (ℕ ; zero ; suc ; _+_ ; _*_ ; _^_ ; _<_ ; _>_ ; z<s)
  renaming (_/_ to _/ₙ_)
open import Data.Nat.Properties
  using (*-identityʳ ; *-assoc ; *-comm)
open import Data.Nat.DivMod
  using (m*n/n≡m)
open import Data.Nat.Divisibility
  using (_∣_ ; _∤_ ; _∣?_ ; divides)
open import Data.Nat.Primality
  using (prime[2] ; euclidsLemma)
open import Data.Product
  using (_×_ ; _,_)
open import Data.Sum
  using (inj₁ ; inj₂)
open import Data.Empty
  using (⊥-elim)
open import Relation.Nullary
  using (yes ; no ; ¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; cong ; module ≡-Reasoning)

------------------------------------------------------------------------
-- Divisibility witnesses for scaled magnitudes.

2∣x*2^suc : ∀ x k → 2 ∣ (x * 2 ^ suc k)
2∣x*2^suc x k = divides (x * 2 ^ k) eq
  where
    eq : x * 2 ^ suc k ≡ x * 2 ^ k * 2
    eq = trans (cong (x *_) (*-comm 2 (2 ^ k)))
               (sym (*-assoc x (2 ^ k) 2))

5∣x*5^suc : ∀ x k → 5 ∣ (x * 5 ^ suc k)
5∣x*5^suc x k = divides (x * 5 ^ k) eq
  where
    eq : x * 5 ^ suc k ≡ x * 5 ^ k * 5
    eq = trans (cong (x *_) (*-comm 5 (5 ^ k)))
               (sym (*-assoc x (5 ^ k) 5))

------------------------------------------------------------------------
-- Strip-after-scale cancellation (ℕ-level, unconditional).
--
-- Induction on k.  Base case: x * 2 ^ 0 = x * 1 = x, and 0 + j = j,
-- so both sides are literally equal after `*-identityʳ`.  Step case:
-- the inner `stripShared2-abs` `with` pattern is already committed to
-- `yes` by `2∣x*2^suc`, so the `no` branch is absurd.  In the `yes`
-- branch, compute `(x * 2 ^ suc k) /ₙ 2 ≡ x * 2 ^ k` via `m*n/n≡m`
-- after assoc/comm rearrangement, then apply the IH.

strip2-abs-factor : ∀ x k j →
  stripShared2-abs (x * 2 ^ k) (k + j) ≡ stripShared2-abs x j
strip2-abs-factor x zero    j rewrite *-identityʳ x = refl
strip2-abs-factor x (suc k) j with 2 ∣? (x * 2 ^ suc k)
... | no  2∤ = ⊥-elim (2∤ (2∣x*2^suc x k))
... | yes _  =
  begin
    stripShared2-abs ((x * 2 ^ suc k) /ₙ 2) (k + j)
      ≡⟨ cong (λ n → stripShared2-abs n (k + j)) divEq ⟩
    stripShared2-abs (x * 2 ^ k) (k + j)
      ≡⟨ strip2-abs-factor x k j ⟩
    stripShared2-abs x j
  ∎
  where
    open ≡-Reasoning
    divEq : (x * 2 ^ suc k) /ₙ 2 ≡ x * 2 ^ k
    divEq =
      begin
        (x * (2 * 2 ^ k)) /ₙ 2
          ≡⟨ cong (_/ₙ 2) (cong (x *_) (*-comm 2 (2 ^ k))) ⟩
        (x * (2 ^ k * 2)) /ₙ 2
          ≡⟨ cong (_/ₙ 2) (sym (*-assoc x (2 ^ k) 2)) ⟩
        (x * 2 ^ k * 2) /ₙ 2
          ≡⟨ m*n/n≡m (x * 2 ^ k) 2 ⟩
        x * 2 ^ k
      ∎

-- Mirror of strip2-abs-factor for 5.  Same structure, prime swap.

strip5-abs-factor : ∀ x k j →
  stripShared5-abs (x * 5 ^ k) (k + j) ≡ stripShared5-abs x j
strip5-abs-factor x zero    j rewrite *-identityʳ x = refl
strip5-abs-factor x (suc k) j with 5 ∣? (x * 5 ^ suc k)
... | no  5∤ = ⊥-elim (5∤ (5∣x*5^suc x k))
... | yes _  =
  begin
    stripShared5-abs ((x * 5 ^ suc k) /ₙ 5) (k + j)
      ≡⟨ cong (λ n → stripShared5-abs n (k + j)) divEq ⟩
    stripShared5-abs (x * 5 ^ k) (k + j)
      ≡⟨ strip5-abs-factor x k j ⟩
    stripShared5-abs x j
  ∎
  where
    open ≡-Reasoning
    divEq : (x * 5 ^ suc k) /ₙ 5 ≡ x * 5 ^ k
    divEq =
      begin
        (x * (5 * 5 ^ k)) /ₙ 5
          ≡⟨ cong (_/ₙ 5) (cong (x *_) (*-comm 5 (5 ^ k))) ⟩
        (x * (5 ^ k * 5)) /ₙ 5
          ≡⟨ cong (_/ₙ 5) (sym (*-assoc x (5 ^ k) 5)) ⟩
        (x * 5 ^ k * 5) /ₙ 5
          ≡⟨ m*n/n≡m (x * 5 ^ k) 5 ⟩
        x * 5 ^ k
      ∎

------------------------------------------------------------------------
-- "Strip is identity" when the prime doesn't divide the magnitude.
--
-- Precondition is gated on `0 < a` so that `a = 0` trivially satisfies
-- the hypothesis — stripShared2-abs just returns `(n, 0)` regardless
-- of whether 2 divides n.  The usable form is `(0 < a → 2 ∤ n)`,
-- which flows through the composition lemmas below.

stripShared2-abs-noDiv : ∀ n a → (0 < a → 2 ∤ n) → stripShared2-abs n a ≡ (n , a)
stripShared2-abs-noDiv n zero    _   = refl
stripShared2-abs-noDiv n (suc a) h   with 2 ∣? n
... | no  _   = refl
... | yes 2∣n = ⊥-elim (h z<s 2∣n)

stripShared5-abs-noDiv : ∀ n b → (0 < b → 5 ∤ n) → stripShared5-abs n b ≡ (n , b)
stripShared5-abs-noDiv n zero    _   = refl
stripShared5-abs-noDiv n (suc b) h   with 5 ∣? n
... | no  _   = refl
... | yes 5∣n = ⊥-elim (h z<s 5∣n)

------------------------------------------------------------------------
-- Atomic coprimality facts.  Proved by case analysis on the quotient
-- of the hypothetical divisibility: all quotient values yield an
-- absurd equation (`()`-closed) after `* 2` or `* 5` reduction.

2∤1 : 2 ∤ 1
2∤1 (divides zero    ())
2∤1 (divides (suc _) ())

2∤5 : 2 ∤ 5
2∤5 (divides zero                         ())
2∤5 (divides (suc zero)                   ())
2∤5 (divides (suc (suc zero))             ())
2∤5 (divides (suc (suc (suc _)))          ())

5∤1 : 5 ∤ 1
5∤1 (divides zero    ())
5∤1 (divides (suc _) ())

5∤2 : 5 ∤ 2
5∤2 (divides zero    ())
5∤2 (divides (suc _) ())

------------------------------------------------------------------------
-- 2 ∤ 5^q for every q.  Induction on q; step uses `euclidsLemma`
-- (contrapositive form) to reject 2 ∣ (5 * 5^q) via 2∤5 + IH on the
-- two factors.

2∤5^ : ∀ q → 2 ∤ 5 ^ q
2∤5^ zero    = 2∤1
2∤5^ (suc q) 2∣5·5^q with euclidsLemma 5 (5 ^ q) prime[2] 2∣5·5^q
... | inj₁ 2∣5    = 2∤5 2∣5
... | inj₂ 2∣5^q  = 2∤5^ q 2∣5^q

-- Preservation of 2-nondivisibility through multiplication by 5^q.
-- Euclid's lemma splits `2 ∣ (x * 5^q)` into `2 ∣ x` or `2 ∣ 5^q`,
-- both contradicted.
2∤x*5^ : ∀ x q → 2 ∤ x → 2 ∤ (x * 5 ^ q)
2∤x*5^ x q 2∤x 2∣x*5^q with euclidsLemma x (5 ^ q) prime[2] 2∣x*5^q
... | inj₁ 2∣x    = 2∤x 2∣x
... | inj₂ 2∣5^q  = 2∤5^ q 2∣5^q

------------------------------------------------------------------------
-- Rearrangement: `x * 2^p * 5^q ≡ x * 5^q * 2^p`.  Pure *-assoc / *-comm.

*-2^-5^-swap : ∀ x p q → x * 2 ^ p * 5 ^ q ≡ x * 5 ^ q * 2 ^ p
*-2^-5^-swap x p q =
  begin
    x * 2 ^ p * 5 ^ q
      ≡⟨ *-assoc x (2 ^ p) (5 ^ q) ⟩
    x * (2 ^ p * 5 ^ q)
      ≡⟨ cong (x *_) (*-comm (2 ^ p) (5 ^ q)) ⟩
    x * (5 ^ q * 2 ^ p)
      ≡⟨ sym (*-assoc x (5 ^ q) (2 ^ p)) ⟩
    x * 5 ^ q * 2 ^ p
  ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- canonicalizeNat on a zero magnitude collapses to `(0, 0, 0)` for
-- any exponents.  Uses the `-zero` lemmas already in `DecRat.agda`.

canonicalizeNat-zero : ∀ a b → canonicalizeNat 0 a b ≡ (0 , 0 , 0)
canonicalizeNat-zero a b
  with stripShared2-abs 0 a | stripShared2-abs-zero a
... | .(0 , 0) | refl
  with stripShared5-abs 0 b | stripShared5-abs-zero b
...   | .(0 , 0) | refl = refl

------------------------------------------------------------------------
-- canonicalizeNat on a scaled nonzero magnitude collapses the added
-- factors.  Given a canonical `(x, a, b)` with `x > 0` and the usual
-- two coprimality guards, scaling `x` by `2^p * 5^q` and canonicalising
-- with budget `(p + a, q + b)` restores `(x, a, b)`.

canonicalizeNat-scale-pos : ∀ x a b →
  (0 < a → 2 ∤ x) → (0 < b → 5 ∤ x) →
  ∀ p q →
  canonicalizeNat (x * 2 ^ p * 5 ^ q) (p + a) (q + b) ≡ (x , a , b)
canonicalizeNat-scale-pos x a b h2 h5 p q
  with stripShared2-abs (x * 2 ^ p * 5 ^ q) (p + a) | strip2
  where
    strip2 : stripShared2-abs (x * 2 ^ p * 5 ^ q) (p + a) ≡ (x * 5 ^ q , a)
    strip2 =
      begin
        stripShared2-abs (x * 2 ^ p * 5 ^ q) (p + a)
          ≡⟨ cong (λ n → stripShared2-abs n (p + a)) (*-2^-5^-swap x p q) ⟩
        stripShared2-abs (x * 5 ^ q * 2 ^ p) (p + a)
          ≡⟨ strip2-abs-factor (x * 5 ^ q) p a ⟩
        stripShared2-abs (x * 5 ^ q) a
          ≡⟨ stripShared2-abs-noDiv (x * 5 ^ q) a
               (λ a>0 → 2∤x*5^ x q (h2 a>0)) ⟩
        x * 5 ^ q , a
      ∎
      where open ≡-Reasoning
... | .(x * 5 ^ q , a) | refl
  with stripShared5-abs (x * 5 ^ q) (q + b) | strip5
  where
    strip5 : stripShared5-abs (x * 5 ^ q) (q + b) ≡ (x , b)
    strip5 =
      begin
        stripShared5-abs (x * 5 ^ q) (q + b)
          ≡⟨ strip5-abs-factor x q b ⟩
        stripShared5-abs x b
          ≡⟨ stripShared5-abs-noDiv x b h5 ⟩
        x , b
      ∎
      where open ≡-Reasoning
...   | .(x , b) | refl = refl
