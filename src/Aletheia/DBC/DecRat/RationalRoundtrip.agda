{-# OPTIONS --safe --without-K #-}

-- ℚ ↔ DecRat roundtrip lemmas.
--
-- Purpose: Close the JSON-boundary roundtrip `fromℚ? (toℚ d) ≡ just d`.
--   Used by EV_/SG_/Attrs migrations (Phase B.3.d pre-gate Commits 3-5) to
--   keep JSON roundtrip proofs closed after ℚ fields migrate to DecRat.
--   Proved once in this module; reused unchanged at each migration site.
--
-- Structure: strict abstraction layering, one layer per section.
--   Layer 1 — `stripFactor-peel` : peels `p^k` out of `p^k * m`.
--   Layer 2 — `canonicalizeDecRat-id` : `canonicalize` is a no-op on
--             already-canonical inputs.
--   Layer 3 — `toℚ-canonical-form` : characterise `toℚ d`'s numerator
--             and denominator via stdlib's `normalize-coprime` (black box).
--   Layer 4 — `toℚ-fromℚ?` : compose layers 1–3.
module Aletheia.DBC.DecRat.RationalRoundtrip where

open import Data.Nat.Base
  using (ℕ; zero; suc; _+_; _*_; _^_; _<_; _≤_; s≤s; z≤n; z<s; s<s;
         NonZero)
  renaming (_/_ to _/ₙ_; _%_ to _%ₙ_)
open import Data.Nat.Properties
  using (*-identityʳ; *-identityˡ; *-assoc; *-comm; *-zeroˡ; *-zeroʳ;
         m^n≢0; m*n≢0; m^n>0; *-cancelˡ-≡; <-irrefl;
         ≤-refl; <-trans; n<1+n; suc-injective)
  renaming (_≟_ to _≟ₙ_)
open import Data.Empty using (⊥-elim)
open import Data.Nat.Divisibility
  using (_∣_; _∤_; _∣?_; divides; ∣-refl; ∣-trans; ∣1⇒≡1; >⇒∤;
         m%n≡0⇒n∣m; n∣m⇒m%n≡0)
open import Data.Nat.DivMod using (m*n/n≡m; m*n%n≡0)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (yes; no; ¬_)

open import Data.Bool.Base using (Bool; true; false; T; not; _∧_)
open import Data.Bool.Properties using (T-irrelevant; T?)
open import Data.Unit using (⊤; tt)
open import Data.Integer.Base using (ℤ; +_; -[1+_]; +[1+_]; ∣_∣; sign; _◃_)
open import Data.Integer.Properties using (signᵢ◃∣i∣≡i; abs-◃)
open import Relation.Nullary.Decidable.Core using (isYes)
import Relation.Nullary.Decidable.Core as Dec
open import Data.Nat.Coprimality
  using (Coprime; coprime-divisor; 1-coprimeTo)
  renaming (sym to coprime-sym)
open import Data.Nat.Primality
  using (Prime; prime[2]; prime?; prime⇒irreducible; Irreducible)
open import Relation.Nullary.Decidable.Core using (toWitness)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Rational.Base
  using (ℚ; mkℚ; mkℚ+; normalize; -_; ↥_; ↧_; ↧ₙ_)
import Data.Rational.Base as ℚB
open import Data.Rational.Properties
  using (normalize-coprime; normalize-cong)

open import Aletheia.DBC.DecRat using
  (DecRat; mkDecRat; IsCanonical; isCanonicalᵇ; toℚ; fromℚ?;
   fromℚ?-raw; canonicalizeDecRat; canonicalizeNat;
   stripShared2-abs; stripShared5-abs; stripFactor-fuel)
import Aletheia.DBC.DecRat as D

-- ----------------------------------------------------------------------------
-- Layer 1 — `stripFactor-fuel` peeling
-- ----------------------------------------------------------------------------
--
-- Self-contained: no appeals to stdlib-ℚ; only ℕ arithmetic and divisibility.

-- Sentinel: when `p ∤ n`, `stripFactor-fuel _ _ n` returns `(0, n)`.
--
-- Proof: the function's `with n %ₙ p ≟ₙ 0` branches on modular divisibility;
--   `p ∤ n` rules out the `yes`, forcing the `no` branch which returns
--   `(0, n)` directly.  `zero` fuel returns the sentinel unconditionally.
stripFactor-step-no :
  ∀ fuel p n .{{_ : NonZero p}} →
    p ∤ n → stripFactor-fuel fuel p n ≡ (0 , n)
stripFactor-step-no zero    p n p∤n = refl
stripFactor-step-no (suc f) p n p∤n with n %ₙ p ≟ₙ 0
... | yes n%p≡0 = ⊥-elim (p∤n (m%n≡0⇒n∣m n p n%p≡0))
... | no  _     = refl

-- Step lemma: `stripFactor-fuel (suc f) p (p * suc y)` unfolds one recursion
--   step, factoring out one copy of `p`.  `suc y` ensures `0 < p * y`, which
--   is what the function's `with n /ₙ p` pattern-match on `| suc q-1` needs.
--
-- Proof:
--   (1) `(p * suc y) %ₙ p ≡ 0`  via `*-comm` + `m*n%n≡0`.
--   (2) `(p * suc y) /ₙ p ≡ suc y`  via `*-comm` + `m*n/n≡m`.
--   (3) Both with-abstractions fire on the witnesses; the `yes _` branch
--       and `.(suc y) | refl` match reduce the function to the recursive
--       case on `suc y`.
stripFactor-step-yes :
  ∀ f p y .{{_ : NonZero p}} →
    stripFactor-fuel (suc f) p (p * suc y) ≡
      (suc (proj₁ (stripFactor-fuel f p (suc y))) ,
       proj₂ (stripFactor-fuel f p (suc y)))
stripFactor-step-yes f p y = helper
  where
  pY : ℕ
  pY = p * suc y

  pY%p≡0 : pY %ₙ p ≡ 0
  pY%p≡0 = trans (cong (_%ₙ p) (*-comm p (suc y))) (m*n%n≡0 (suc y) p)

  pY/p≡sy : pY /ₙ p ≡ suc y
  pY/p≡sy = trans (cong (_/ₙ p) (*-comm p (suc y))) (m*n/n≡m (suc y) p)

  helper :
    stripFactor-fuel (suc f) p pY ≡
      (suc (proj₁ (stripFactor-fuel f p (suc y))) ,
       proj₂ (stripFactor-fuel f p (suc y)))
  helper with pY %ₙ p ≟ₙ 0
  ... | no nope = ⊥-elim (nope pY%p≡0)
  ... | yes _ with pY /ₙ p | pY/p≡sy
  ...         | .(suc y)   | refl = refl

-- Peeling theorem: `stripFactor-fuel` extracts exactly `k` factors of `p`
--   from `p^k * m`, provided `p ∤ m`, `0 < m`, and fuel exceeds `k`.
--
-- Proof: induction on `k`.
--   • k = 0 : `p^0 * m ≡ m` by `*-identityˡ`; reduces to `stripFactor-step-no`.
--   • k = suc k' : rewrite `p^(suc k') * m ≡ p * (p^k' * m)` by `*-assoc`,
--     peel one step via `stripFactor-step-yes`, and apply IH on `k'`.
stripFactor-peel :
  ∀ fuel p k m .{{_ : NonZero p}} .{{_ : NonZero m}} →
    p ∤ m → k < fuel →
    stripFactor-fuel fuel p (p ^ k * m) ≡ (k , m)
stripFactor-peel fuel p zero m p∤m _ =
  subst (λ z → stripFactor-fuel fuel p z ≡ (0 , m))
        (sym (*-identityˡ m))
        (stripFactor-step-no fuel p m p∤m)
stripFactor-peel (suc f) p (suc k) m@(suc m-1) p∤m (s≤s k<f) = goal
  where
  -- Unfold p^(suc k) * m = p * (p^k * m).
  assoc : p ^ (suc k) * m ≡ p * (p ^ k * m)
  assoc = *-assoc p (p ^ k) m

  -- 0 < p^k * m (via m^n>0 and NonZero m).
  instance
    p^k≢0 : NonZero (p ^ k)
    p^k≢0 = m^n≢0 p k

    p^km≢0 : NonZero (p ^ k * m)
    p^km≢0 = m*n≢0 (p ^ k) m

  -- Destructure p^k * m = suc y for some y (via NonZero instance).
  y : ℕ
  y = (p ^ k * m) Data.Nat.Base.∸ 1

  y≡ : p ^ k * m ≡ suc y
  y≡ = lemma-suc (p ^ k * m)
    where
    open import Data.Nat.Base using (_∸_)
    lemma-suc : (n : ℕ) .{{_ : NonZero n}} → n ≡ suc (n ∸ 1)
    lemma-suc (suc _) = refl

  -- Apply stripFactor-step-yes to peel one factor.
  step : stripFactor-fuel (suc f) p (p * (p ^ k * m)) ≡
           (suc (proj₁ (stripFactor-fuel f p (p ^ k * m))) ,
            proj₂ (stripFactor-fuel f p (p ^ k * m)))
  step = subst (λ z → stripFactor-fuel (suc f) p (p * z) ≡
                        (suc (proj₁ (stripFactor-fuel f p z)) ,
                         proj₂ (stripFactor-fuel f p z)))
               (sym y≡)
               (stripFactor-step-yes f p y)

  -- Apply IH on k.
  ih : stripFactor-fuel f p (p ^ k * m) ≡ (k , m)
  ih = stripFactor-peel f p k m p∤m k<f

  -- Combine: the suc-paired result.
  combined : stripFactor-fuel (suc f) p (p * (p ^ k * m)) ≡ (suc k , m)
  combined = trans step
                   (cong (λ pr → (suc (proj₁ pr) , proj₂ pr)) ih)

  -- Transport back through assoc to get target form.
  goal : stripFactor-fuel (suc f) p (p ^ (suc k) * m) ≡ (suc k , m)
  goal = trans (cong (λ z → stripFactor-fuel (suc f) p z) assoc) combined

-- ----------------------------------------------------------------------------
-- Layer 2 — `canonicalizeDecRat` is a no-op on canonical inputs.
-- ----------------------------------------------------------------------------
--
-- Bridge from the ℕ-level `IsCanonical` Bool-witness to identity behaviour
-- of `canonicalizeDecRat`.  Used in Layer 4 to close the round-trip after
-- `fromℚ?-raw` reaches its happy path.

-- Identity for `stripShared2-abs` when 2 ∤ n (or when twoExp = 0).
stripShared2-abs-id-∤ :
  ∀ n a → 2 ∤ n → stripShared2-abs n a ≡ (n , a)
stripShared2-abs-id-∤ n zero    _   = refl
stripShared2-abs-id-∤ n (suc a) 2∤n with 2 ∣? n
... | yes 2∣n = ⊥-elim (2∤n 2∣n)
... | no  _   = refl

stripShared2-abs-id-zero :
  ∀ n → stripShared2-abs n zero ≡ (n , zero)
stripShared2-abs-id-zero n = refl

-- Identity for `stripShared5-abs` when 5 ∤ n (or when fiveExp = 0).
stripShared5-abs-id-∤ :
  ∀ n b → 5 ∤ n → stripShared5-abs n b ≡ (n , b)
stripShared5-abs-id-∤ n zero    _   = refl
stripShared5-abs-id-∤ n (suc b) 5∤n with 5 ∣? n
... | yes 5∣n = ⊥-elim (5∤n 5∣n)
... | no  _   = refl

stripShared5-abs-id-zero :
  ∀ n → stripShared5-abs n zero ≡ (n , zero)
stripShared5-abs-id-zero n = refl

-- Bridge: T (not (isYes (p ∣? n))) → p ∤ n.
T-not-isYes-∤ :
  ∀ p n → T (not (isYes (p ∣? n))) → p ∤ n
T-not-isYes-∤ p n tw with p ∣? n
... | yes _   = ⊥-elim tw
... | no  ¬∣  = ¬∣

-- Project a T-witness over a boolean conjunction.
splitBool-T : ∀ {x y} → T (x ∧ y) → T x × T y
splitBool-T {true}  {true}  tt  = tt , tt
splitBool-T {true}  {false} ()
splitBool-T {false} {_}     ()

-- From a canonical witness, extract that `stripShared2-abs n a` is an
-- identity (n, a).  Dispatches on (n, a, b) to align with isCanonicalᵇ's
-- exhaustive pattern.
strips2-canonical :
  ∀ n a b → IsCanonical n a b → stripShared2-abs n a ≡ (n , a)
strips2-canonical zero    zero    zero    _  = refl
strips2-canonical zero    zero    (suc _) ()
strips2-canonical zero    (suc _) _       ()
strips2-canonical (suc n) zero    _       _  = refl
strips2-canonical (suc n) (suc a) zero    tw =
  stripShared2-abs-id-∤ (suc n) (suc a) (T-not-isYes-∤ 2 (suc n) tw)
strips2-canonical (suc n) (suc a) (suc b) tw =
  stripShared2-abs-id-∤ (suc n) (suc a)
    (T-not-isYes-∤ 2 (suc n) (proj₁ (splitBool-T tw)))

-- From a canonical witness, extract that `stripShared5-abs n b` is an
-- identity (n, b).
strips5-canonical :
  ∀ n a b → IsCanonical n a b → stripShared5-abs n b ≡ (n , b)
strips5-canonical zero    zero    zero    _  = refl
strips5-canonical zero    zero    (suc _) ()
strips5-canonical zero    (suc _) _       ()
strips5-canonical (suc n) _       zero    _  = refl
strips5-canonical (suc n) zero    (suc b) tw =
  stripShared5-abs-id-∤ (suc n) (suc b) (T-not-isYes-∤ 5 (suc n) tw)
strips5-canonical (suc n) (suc a) (suc b) tw =
  stripShared5-abs-id-∤ (suc n) (suc b)
    (T-not-isYes-∤ 5 (suc n) (proj₂ (splitBool-T tw)))

-- Headline: `canonicalizeDecRat` is identity on every `DecRat`.
--
-- `canonicalizeDecRat (numerator d) (twoExp d) (fiveExp d)` returns
-- `mkDecRat (sign num ◃ n') a' b' (some witness)`, where `(n', a', b')`
-- is the output of `canonicalizeNat`.  For canonical d, that output is
-- `(∣ num ∣, a, b)` (Layer 2 above).  `sign num ◃ ∣ num ∣ ≡ num` by
-- stdlib's `signᵢ◃∣i∣≡i`.  The `.canonical` field is irrelevant, so
-- `cong` on the numerator suffices once the with-abstraction matches.
-- mkDecRat congruent in all three numerical fields.  Irrelevant
-- `.canonical` field unifies via irrelevance once types align under refl.
mkDecRat-cong3 :
  ∀ {n₁ n₂ a₁ a₂ b₁ b₂}
    .{c₁ : IsCanonical ∣ n₁ ∣ a₁ b₁}
    .{c₂ : IsCanonical ∣ n₂ ∣ a₂ b₂} →
    n₁ ≡ n₂ → a₁ ≡ a₂ → b₁ ≡ b₂ →
    mkDecRat n₁ a₁ b₁ c₁ ≡ mkDecRat n₂ a₂ b₂ c₂
mkDecRat-cong3 refl refl refl = refl

-- `canonicalizeNat n a b ≡ (n, a, b)` for canonical inputs, derived by
-- composing `strips2-canonical` and `strips5-canonical` through
-- `canonicalizeNat`'s own nested with-abstractions.
canonicalizeNat-id-canonical :
  ∀ n a b → IsCanonical n a b → canonicalizeNat n a b ≡ (n , a , b)
canonicalizeNat-id-canonical n a b cr
  with stripShared2-abs n a | strips2-canonical n a b cr
... | .(n , a) | refl with stripShared5-abs n b | strips5-canonical n a b cr
...                      | .(n , b) | refl = refl

-- Pattern-match on records preserves irrelevant slots; equal numeric
-- fields suffice for record equality under `--without-K`.
DecRat-ext :
  ∀ (d₁ d₂ : DecRat) →
    DecRat.numerator d₁ ≡ DecRat.numerator d₂ →
    DecRat.twoExp d₁ ≡ DecRat.twoExp d₂ →
    DecRat.fiveExp d₁ ≡ DecRat.fiveExp d₂ →
    d₁ ≡ d₂
DecRat-ext (mkDecRat n a b _) (mkDecRat .n .a .b _) refl refl refl = refl

canonicalizeDecRat-id :
  ∀ (d : DecRat) →
    canonicalizeDecRat (DecRat.numerator d) (DecRat.twoExp d)
                       (DecRat.fiveExp d) ≡ d
canonicalizeDecRat-id d@(mkDecRat num a b canonical) =
  DecRat-ext (canonicalizeDecRat num a b) d num-eq a-eq b-eq
  where
  cr : IsCanonical ∣ num ∣ a b
  cr = Dec.recompute (T? (isCanonicalᵇ ∣ num ∣ a b)) canonical

  cnat-id : canonicalizeNat ∣ num ∣ a b ≡ (∣ num ∣ , a , b)
  cnat-id = canonicalizeNat-id-canonical ∣ num ∣ a b cr

  num-eq : DecRat.numerator (canonicalizeDecRat num a b) ≡ num
  num-eq = trans (cong (λ p → sign num ◃ proj₁ p) cnat-id)
                 (signᵢ◃∣i∣≡i num)

  a-eq : DecRat.twoExp (canonicalizeDecRat num a b) ≡ a
  a-eq = cong (λ p → proj₁ (proj₂ p)) cnat-id

  b-eq : DecRat.fiveExp (canonicalizeDecRat num a b) ≡ b
  b-eq = cong (λ p → proj₂ (proj₂ p)) cnat-id

-- ----------------------------------------------------------------------------
-- Layer 3 — `toℚ d` numerator/denominator characterisation
-- ----------------------------------------------------------------------------
--
-- For canonical d = mkDecRat num a b, `toℚ d ≡ mkℚ num ((2^a * 5^b) ∸ 1) c`
-- via stdlib's `normalize-coprime` (treated as a black box).  Bridge from
-- the boolean `IsCanonical` witness to nat-level `Coprime` is built bottom-up:
-- prime + ∤ → coprime, then product of coprimes, then prime power.

prime[5] : Prime 5
prime[5] = toWitness {a? = prime? 5} _

-- A prime that doesn't divide n is coprime to n.
∤-prime⇒coprime :
  ∀ n p → Prime p → p ∤ n → Coprime n p
∤-prime⇒coprime n p pp p∤n {d} (d∣n , d∣p)
  with prime⇒irreducible pp d∣p
... | inj₁ d≡1 = d≡1
... | inj₂ d≡p = ⊥-elim (p∤n (subst (_∣ n) d≡p d∣n))

-- Coprimality distributes over products on the right factor.
-- Proof: any common divisor d of n and (m * k) is also coprime to m
-- (via cnm + d∣n), so by `coprime-divisor` it must divide k; then
-- cnk forces d ≡ 1.
coprime-product :
  ∀ n m k → Coprime n m → Coprime n k → Coprime n (m * k)
coprime-product n m k cnm cnk {d} (d∣n , d∣mk) =
  cnk (d∣n , coprime-divisor cdm d∣mk)
  where
  cdm : Coprime d m
  cdm {e} (e∣d , e∣m) = cnm (∣-trans e∣d d∣n , e∣m)

-- Coprimality of n with a prime p lifts to coprimality with p^k.
coprime-prime-power :
  ∀ n p → Coprime n p → ∀ k → Coprime n (p ^ k)
coprime-prime-power n p cnp zero    = coprime-sym (1-coprimeTo n)
coprime-prime-power n p cnp (suc k) =
  coprime-product n p (p ^ k) cnp (coprime-prime-power n p cnp k)

-- Bridge: a canonical witness gives coprimality with 2^a * 5^b.
-- Case-split on n first (zero / suc) to dispatch the canonical witness
-- shape, then on (a, b) to discharge the trivial sub-goals.
IsCanonical→Coprime :
  ∀ n a b → IsCanonical n a b → Coprime n (2 ^ a * 5 ^ b)
-- n = zero : canonical forces (a, b) = (0, 0); other branches absurd.
IsCanonical→Coprime zero    zero    zero    _  =
  coprime-sym (1-coprimeTo 0)
IsCanonical→Coprime zero    zero    (suc _) ()
IsCanonical→Coprime zero    (suc _) _       ()
-- n = suc m, (a, b) = (0, 0) : 2^0 * 5^0 = 1; trivially coprime.
IsCanonical→Coprime (suc m) zero    zero    _  =
  coprime-sym (1-coprimeTo (suc m))
-- n = suc m, a = 0, b = suc b' : need 5 ∤ suc m from canonical.
IsCanonical→Coprime (suc m) zero    (suc b) cr =
  subst (Coprime (suc m)) (sym (*-identityˡ (5 ^ suc b)))
        (coprime-prime-power (suc m) 5
          (∤-prime⇒coprime (suc m) 5 prime[5]
            (T-not-isYes-∤ 5 (suc m) cr))
          (suc b))
-- n = suc m, a = suc a', b = 0 : need 2 ∤ suc m.
IsCanonical→Coprime (suc m) (suc a) zero    cr =
  subst (Coprime (suc m)) (sym (*-identityʳ (2 ^ suc a)))
        (coprime-prime-power (suc m) 2
          (∤-prime⇒coprime (suc m) 2 prime[2]
            (T-not-isYes-∤ 2 (suc m) cr))
          (suc a))
-- n = suc m, a = suc a', b = suc b' : need both.
IsCanonical→Coprime (suc m) (suc a) (suc b) cr =
  coprime-product (suc m) (2 ^ suc a) (5 ^ suc b)
    (coprime-prime-power (suc m) 2 cnp-2 (suc a))
    (coprime-prime-power (suc m) 5 cnp-5 (suc b))
  where
  parts : T (not (isYes (2 ∣? suc m))) ×
          T (not (isYes (5 ∣? suc m)))
  parts = splitBool-T cr

  cnp-2 : Coprime (suc m) 2
  cnp-2 = ∤-prime⇒coprime (suc m) 2 prime[2]
            (T-not-isYes-∤ 2 (suc m) (proj₁ parts))

  cnp-5 : Coprime (suc m) 5
  cnp-5 = ∤-prime⇒coprime (suc m) 5 prime[5]
            (T-not-isYes-∤ 5 (suc m) (proj₂ parts))

-- Denominator of toℚ d in `suc D` form.
2^a*5^b≡suc :
  ∀ a b → 2 ^ a * 5 ^ b ≡ suc ((2 ^ a * 5 ^ b) Data.Nat.Base.∸ 1)
2^a*5^b≡suc a b = lemma-suc (2 ^ a * 5 ^ b)
            {{Aletheia.DBC.DecRat.2^a·5^b-NonZero a b}}
  where
  open import Data.Nat.Base using (_∸_)
  lemma-suc : (n : ℕ) .{{_ : NonZero n}} → n ≡ suc (n ∸ 1)
  lemma-suc (suc _) = refl

-- Helper: bridge `normalize n (2^a * 5^b)` to `mkℚ (+ n) D _` form.
-- Uses normalize-cong to insert the suc-shape, then normalize-coprime
-- to discharge the normalization (no-op given coprimality).
normalize-canonical-+ :
  ∀ n a b →
    .(coprime-w : Coprime n (suc ((2 ^ a * 5 ^ b) Data.Nat.Base.∸ 1))) →
    normalize n (2 ^ a * 5 ^ b)
      {{Aletheia.DBC.DecRat.2^a·5^b-NonZero a b}}
      ≡ mkℚ (+ n) ((2 ^ a * 5 ^ b) Data.Nat.Base.∸ 1) coprime-w
normalize-canonical-+ n a b coprime-w =
  trans (normalize-cong {n} {2 ^ a * 5 ^ b} {n}
                        {suc ((2 ^ a * 5 ^ b) Data.Nat.Base.∸ 1)}
                        {{Aletheia.DBC.DecRat.2^a·5^b-NonZero a b}}
                        refl (2^a*5^b≡suc a b))
        (normalize-coprime coprime-w)

-- Numerator projection of toℚ for canonical d.
↥-toℚ-canonical :
  ∀ num a b .(c : IsCanonical ∣ num ∣ a b) →
    ↥ (toℚ (mkDecRat num a b c)) ≡ num
↥-toℚ-canonical (+ n) a b c =
  cong ↥_ (normalize-canonical-+ n a b coprime-w)
  where
  coprime-w : Coprime n (suc ((2 ^ a * 5 ^ b) Data.Nat.Base.∸ 1))
  coprime-w = subst (Coprime n) (2^a*5^b≡suc a b)
                    (IsCanonical→Coprime n a b
                      (Dec.recompute (T? (isCanonicalᵇ n a b)) c))
↥-toℚ-canonical -[1+ n ] a b c =
  cong (λ q → ↥ (- q)) (normalize-canonical-+ (suc n) a b coprime-w)
  where
  coprime-w : Coprime (suc n) (suc ((2 ^ a * 5 ^ b) Data.Nat.Base.∸ 1))
  coprime-w = subst (Coprime (suc n)) (2^a*5^b≡suc a b)
                    (IsCanonical→Coprime (suc n) a b
                      (Dec.recompute (T? (isCanonicalᵇ (suc n) a b)) c))

-- Denominator (in ℕ form: `suc denominator-1`) of toℚ for canonical d.
↧ₙ-toℚ-canonical :
  ∀ num a b .(c : IsCanonical ∣ num ∣ a b) →
    suc (ℚ.denominator-1 (toℚ (mkDecRat num a b c))) ≡ 2 ^ a * 5 ^ b
↧ₙ-toℚ-canonical (+ n) a b c =
  trans (cong (λ q → suc (ℚ.denominator-1 q))
              (normalize-canonical-+ n a b coprime-w))
        (sym (2^a*5^b≡suc a b))
  where
  coprime-w : Coprime n (suc ((2 ^ a * 5 ^ b) Data.Nat.Base.∸ 1))
  coprime-w = subst (Coprime n) (2^a*5^b≡suc a b)
                    (IsCanonical→Coprime n a b
                      (Dec.recompute (T? (isCanonicalᵇ n a b)) c))
↧ₙ-toℚ-canonical -[1+ n ] a b c =
  trans (cong (λ q → suc (ℚ.denominator-1 (- q)))
              (normalize-canonical-+ (suc n) a b coprime-w))
        (sym (2^a*5^b≡suc a b))
  where
  coprime-w : Coprime (suc n) (suc ((2 ^ a * 5 ^ b) Data.Nat.Base.∸ 1))
  coprime-w = subst (Coprime (suc n)) (2^a*5^b≡suc a b)
                    (IsCanonical→Coprime (suc n) a b
                      (Dec.recompute (T? (isCanonicalᵇ (suc n) a b)) c))

-- ----------------------------------------------------------------------------
-- Layer 4 — `fromℚ? (toℚ d) ≡ just d`
-- ----------------------------------------------------------------------------
--
-- Compose Layers 1–3.  Migration sites (EV_/SG_/Attrs) reuse this directly:
-- after a `ℚ`-typed JSON field flips to `DecRat`, the JSON roundtrip proof
-- closes via `fromℚ?-after-toℚ`.

-- Bound: n ≤ p^n for p ≥ 2.  Used to discharge the fuel side condition
-- of `stripFactor-peel`.  Proof: induction.
--   Step: `suc n ≤ 1 + p^n`  (from IH: n ≤ p^n; suc n ≤ suc p^n = 1 + p^n).
--         `1 + p^n ≤ p^n + p^n`  (from 1 ≤ p^n).
--         `p^n + p^n ≡ p^n + (p^n + 0)`  (via +-identityʳ).
--         `p^n + (p^n + 0) ≡ 2 * p^n`  (definition of *).
--         `2 * p^n ≤ p * p^n`  (from 2 ≤ p).
n≤p^n :
  ∀ p .{{_ : NonZero p}} → 2 ≤ p → ∀ n → n ≤ p ^ n
n≤p^n p _   zero    = z≤n
n≤p^n p 2≤p (suc n) = ≤-trans step₁ step₂
  where
  open import Data.Nat.Properties using (+-mono-≤; ≤-trans; ≤-refl; +-identityʳ;
                                          *-monoˡ-≤; *-monoʳ-≤; m≤n+m; m≤m+n)

  ih : n ≤ p ^ n
  ih = n≤p^n p 2≤p n

  -- 1 + n ≤ 1 + p^n ≤ p^n + p^n (via 1 ≤ p^n).
  step₁ : suc n ≤ p ^ n + p ^ n
  step₁ = +-mono-≤ (m^n>0 p n) ih

  -- p^n + p^n ≤ p * p^n = p^(suc n).
  -- Bridge: p^n + p^n ≡ p^n + (p^n + 0) (≡ 2 * p^n by definition) ≤ p * p^n.
  instance
    nz-pn : NonZero (p ^ n)
    nz-pn = m^n≢0 p n

  step₂ : p ^ n + p ^ n ≤ p ^ suc n
  step₂ = ≤-trans
    (subst (p ^ n + p ^ n ≤_)
           (cong (λ x → p ^ n + x) (sym (+-identityʳ (p ^ n))))
           ≤-refl)
    (*-monoˡ-≤ (p ^ n) 2≤p)

-- 2 ∤ 5^b.  Via Coprime 2 (5^b) (from prime + ∤) and the fact that a non-trivial
-- divisor of itself can't be coprime to anything containing it as a divisor.
2∤5^b : ∀ b → 2 ∤ 5 ^ b
2∤5^b b 2∣5^b = ⊥-elim (2≢1 (cnp-2-5^b (∣-refl , 2∣5^b)))
  where
  open import Data.Nat.Properties using () renaming (suc-injective to sj)

  c2-5 : Coprime 2 5
  c2-5 = ∤-prime⇒coprime 2 5 prime[5] (>⇒∤ {n = 2} (s≤s (s≤s (s≤s z≤n))))

  cnp-2-5^b : Coprime 2 (5 ^ b)
  cnp-2-5^b = coprime-prime-power 2 5 c2-5 b

  2≢1 : 2 ≢ 1
  2≢1 ()

-- 5 ∤ 1.  Via ∣1⇒≡1 + 5 ≢ 1.
5∤1 : 5 ∤ 1
5∤1 5∣1 with ∣1⇒≡1 5∣1
... | ()
  where open import Data.Nat.Divisibility using (∣1⇒≡1)

-- ============================================================================
-- Layer 4 — `fromℚ? (toℚ d) ≡ just d`
-- ============================================================================
--
-- Composes Layers 1-3.  The structure is: peel-2 + peel-5 characterise the
-- two nested `stripFactor-fuel` calls inside `fromℚ?-raw`; the "-suc" variants
-- relocate the witness to the `suc D` form the function actually pattern-
-- matches on.  Then a `bind-just-step`-style mirror (`fromℚ?-raw-suc`) walks
-- the three nested withs in the function body, discharging each via its
-- respective equation under `with x | eq`.  Finally `fromℚ?-after-toℚ`
-- composes through ↥/↧ₙ-toℚ-canonical and canonicalizeDecRat-id.

-- peel-2 : stripFactor-fuel (suc (2^a * 5^b)) 2 (2^a * 5^b) ≡ (a , 5^b).
-- Applies stripFactor-peel with k=a, m=5^b.  Fuel bound a ≤ 2^a * 5^b
-- discharged via `a ≤ 2^a` (n≤p^n) then `2^a ≤ 2^a * 5^b` (m≤m*n).
peel-2 : ∀ a b →
  stripFactor-fuel (suc (2 ^ a * 5 ^ b)) 2 (2 ^ a * 5 ^ b)
    ≡ (a , 5 ^ b)
peel-2 a b = stripFactor-peel (suc (2 ^ a * 5 ^ b)) 2 a (5 ^ b)
               (2∤5^b b) a<fuel
  where
  open import Data.Nat.Properties using (≤-trans; m≤m*n)

  instance
    nz-5^b : NonZero (5 ^ b)
    nz-5^b = m^n≢0 5 b

  a≤2^a : a ≤ 2 ^ a
  a≤2^a = n≤p^n 2 (s≤s (s≤s z≤n)) a

  2^a≤prod : 2 ^ a ≤ 2 ^ a * 5 ^ b
  2^a≤prod = m≤m*n (2 ^ a) (5 ^ b)

  a<fuel : a < suc (2 ^ a * 5 ^ b)
  a<fuel = s≤s (≤-trans a≤2^a 2^a≤prod)

-- peel-5 : stripFactor-fuel (suc (2^a * 5^b)) 5 (5^b) ≡ (b , 1).
-- Applies stripFactor-peel with k=b, m=1, bridging `5^b ≡ 5^b * 1` via
-- *-identityʳ.  Fuel bound b ≤ 2^a * 5^b via b ≤ 5^b (n≤p^n) then
-- 5^b ≤ 2^a * 5^b (m≤n*m).
peel-5 : ∀ a b →
  stripFactor-fuel (suc (2 ^ a * 5 ^ b)) 5 (5 ^ b) ≡ (b , 1)
peel-5 a b =
  subst (λ z → stripFactor-fuel (suc (2 ^ a * 5 ^ b)) 5 z ≡ (b , 1))
        (*-identityʳ (5 ^ b))
        (stripFactor-peel (suc (2 ^ a * 5 ^ b)) 5 b 1 5∤1 b<fuel)
  where
  open import Data.Nat.Properties using (≤-trans; m≤n*m)

  instance
    nz-2^a : NonZero (2 ^ a)
    nz-2^a = m^n≢0 2 a

  b≤5^b : b ≤ 5 ^ b
  b≤5^b = n≤p^n 5 (s≤s (s≤s z≤n)) b

  5^b≤prod : 5 ^ b ≤ 2 ^ a * 5 ^ b
  5^b≤prod = m≤n*m (5 ^ b) (2 ^ a)

  b<fuel : b < suc (2 ^ a * 5 ^ b)
  b<fuel = s≤s (≤-trans b≤5^b 5^b≤prod)

-- peel-{2,5}-suc : relocate peel-{2,5} to `suc D` form given `suc D ≡ 2^a*5^b`.
-- These are the forms `fromℚ?-raw num (suc D)` pattern-matches against.
peel-2-suc : ∀ D a b → suc D ≡ 2 ^ a * 5 ^ b →
  stripFactor-fuel (suc (suc D)) 2 (suc D) ≡ (a , 5 ^ b)
peel-2-suc D a b eq =
  subst (λ fuel → stripFactor-fuel fuel 2 (suc D) ≡ (a , 5 ^ b))
        (sym (cong suc eq))
        (subst (λ n → stripFactor-fuel (suc (2 ^ a * 5 ^ b)) 2 n
                        ≡ (a , 5 ^ b))
               (sym eq)
               (peel-2 a b))

peel-5-suc : ∀ D a b → suc D ≡ 2 ^ a * 5 ^ b →
  stripFactor-fuel (suc (suc D)) 5 (5 ^ b) ≡ (b , 1)
peel-5-suc D a b eq =
  subst (λ fuel → stripFactor-fuel fuel 5 (5 ^ b) ≡ (b , 1))
        (sym (cong suc eq))
        (peel-5 a b)

-- fromℚ?-raw-suc : dispatching mirror of the three withs in fromℚ?-raw.
-- Uses the `with x | eq` pattern (bind-just-step style) so the generated
-- with-function's equation type is a fresh variable, not a term containing
-- with-abstractions — avoiding the K-axiom issue documented in
-- `feedback_rewrite_k_bind_chain.md`.
fromℚ?-raw-suc :
  ∀ num D a b → suc D ≡ 2 ^ a * 5 ^ b →
    fromℚ?-raw num (suc D) ≡ just (canonicalizeDecRat num a b)
fromℚ?-raw-suc num D a b eq
  with stripFactor-fuel (suc (suc D)) 2 (suc D) | peel-2-suc D a b eq
... | .(a , 5 ^ b) | refl
    with stripFactor-fuel (suc (suc D)) 5 (5 ^ b) | peel-5-suc D a b eq
...   | .(b , 1) | refl
        with 1 ≟ₙ 1
...       | yes _    = refl
...       | no  1≢1  = ⊥-elim (1≢1 refl)

-- fromℚ?-raw-canonical-shape : lifts `fromℚ?-raw-suc` from the suc D form to
-- the direct `2^a * 5^b` form.  Uses subst (not rewrite) to avoid triggering
-- K on the function's internal with-abstractions.
fromℚ?-raw-canonical-shape :
  ∀ num a b →
    fromℚ?-raw num (2 ^ a * 5 ^ b) ≡ just (canonicalizeDecRat num a b)
fromℚ?-raw-canonical-shape num a b =
  subst (λ n → fromℚ?-raw num n ≡ just (canonicalizeDecRat num a b))
        (sym (2^a*5^b≡suc a b))
        (fromℚ?-raw-suc num ((2 ^ a * 5 ^ b) Data.Nat.Base.∸ 1) a b
                        (sym (2^a*5^b≡suc a b)))

-- fromℚ?-after-toℚ : universal roundtrip.  Composes canonicalizeDecRat-id
-- with ↥/↧ₙ-toℚ-canonical to align fromℚ? (toℚ d) with fromℚ?-raw-canonical-
-- shape, then reduces `just (canonicalizeDecRat num a b)` back to `just d`.
fromℚ?-after-toℚ : ∀ d → fromℚ? (toℚ d) ≡ just d
fromℚ?-after-toℚ d@(mkDecRat num a b c) =
  trans
    (cong₂ (λ i n → fromℚ?-raw i n)
           (↥-toℚ-canonical num a b c)
           (↧ₙ-toℚ-canonical num a b c))
    (trans (fromℚ?-raw-canonical-shape num a b)
           (cong just (canonicalizeDecRat-id d)))
