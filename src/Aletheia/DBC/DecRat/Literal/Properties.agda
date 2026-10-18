-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- What the literal core guarantees: a literal it holds has an exact
-- value with a reduced component of at least 2^64, and a literal it
-- does not hold reads to exactly the value of the digit fold.
module Aletheia.DBC.DecRat.Literal.Properties where

open import Data.Bool using (Bool; true; false; if_then_else_; _∨_; T)
open import Data.Char using (Char; toℕ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; foldl; length; reverse; _∷ʳ_)
open import Data.List.Properties using
  (foldl-++; reverse-++; reverse-involutive; length-reverse; length-++; unfold-reverse)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to All-++)
open import Data.Nat using
  (ℕ; zero; suc; _+_; _*_; _∸_; _^_; _≤_; _<_; _≤ᵇ_; _<ᵇ_; z≤n; s≤s; NonZero; ≢-nonZero)
  renaming (_/_ to _/ₙ_)
open import Data.Nat.Properties using
  (<ᵇ⇒<; ≡ᵇ⇒≡; ≡⇒≡ᵇ; ≤ᵇ⇒≤; ≤⇒≤ᵇ; *-identityʳ; +-identityʳ; +-assoc; *-assoc; *-comm; +-comm;
   *-distribʳ-+; m+n∸n≡m; m+[n∸m]≡n; ≤-trans; ≤-reflexive; m≤m*n; m≤n*m; m≤m+n; <⇒≤; ≰⇒>;
   *-monoˡ-≤; *-monoʳ-≤; *-cancelʳ-≤; ^-distribˡ-+-*; ^-distribʳ-*; ^-monoˡ-≤; ^-monoʳ-≤; m^n≢0;
   <-irrefl; <-trans; ≤-<-trans; <-≤-trans; +-monoˡ-≤; +-monoʳ-≤; +-monoʳ-<; m≤n+m; *-identityˡ; +-cancelˡ-<; ≤-refl; <⇒≤pred; n≤1+n)
open import Data.Nat.Divisibility using (_∣_; _∤_; _∣?_; divides; ∣m+n∣m⇒∣n; ∣n⇒∣m*n; ∣m⇒∣m*n)
open import Data.Nat.DivMod using (m*n/n≡m)
open import Data.Nat.Primality using (euclidsLemma)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; cong; cong₂; refl; subst; sym; trans; module ≡-Reasoning)
open import Relation.Nullary using (yes; no)

open import Data.Integer using (ℤ; +_; -[1+_]; ∣_∣)
open import Aletheia.DBC.DecRat using
  (DecRat; stripShared2-abs; stripShared5-abs; canonicalizeNat;
   stripShared2-abs-value; stripShared5-abs-value; prime[5])
open import Aletheia.DBC.DecRat.ScaleLemmas using
  (strip2-abs-factor; strip5-abs-factor; stripShared2-abs-noDiv; stripShared5-abs-noDiv;
   2∤x*5^; 2∤5; *-2^-5^-swap; canonicalizeNat-zero; canonicalizeNat-scale-pos)
open import Aletheia.Limits using (max-rational-component-magnitude)
open import Aletheia.DBC.DecRat.Magnitude using (SmallDecRat; smallDecRat-components) public
open import Aletheia.DBC.TextFormatter.Emitter using (showNat-chars)
open import Aletheia.DBC.TextParser.DecRatParse.Properties.Phase1Digits using (foldDigits-showNat-chars)
open import Aletheia.DBC.DecRat.Literal using
  (digitCutoff; digitValue; dropZeros; exponentHolds; exponentPlaces; exponentPower;
   foldDigits; heldDenominator; heldMagnitude; heldNumerator; isZeroDigit; natLiteral;
   placeCutoff; rawFromSignificand; rawLiteral; significand)

-- ============================================================================
-- DIGITS
-- ============================================================================

-- Every character's digit value is below 10.
digitValue<10 : ∀ c → digitValue c < 10
digitValue<10 c with toℕ c ∸ 48 <ᵇ 10 in eq
... | true  = <ᵇ⇒< (toℕ c ∸ 48) 10 (subst T (sym eq) tt)
... | false = s≤s z≤n

isZeroDigit-≡ : ∀ c → isZeroDigit c ≡ true → digitValue c ≡ 0
isZeroDigit-≡ c eq = ≡ᵇ⇒≡ (digitValue c) 0 (subst T (sym eq) tt)

isZeroDigit-≢ : ∀ c → isZeroDigit c ≡ false → digitValue c ≢ 0
isZeroDigit-≢ c eq v≡0 = subst T eq (≡⇒≡ᵇ (digitValue c) 0 v≡0)

-- The fold's step, named for the lemmas.
step : ℕ → Char → ℕ
step acc c = acc * 10 + digitValue c

-- A fold from any accumulator is the accumulator shifted past the run.
foldl-acc : ∀ acc cs → foldl step acc cs ≡ acc * 10 ^ length cs + foldDigits cs
foldl-acc acc []       = trans (sym (*-identityʳ acc)) (sym (+-identityʳ (acc * 1)))
foldl-acc acc (c ∷ cs) =
  begin
    foldl step (acc * 10 + digitValue c) cs
      ≡⟨ foldl-acc (acc * 10 + digitValue c) cs ⟩
    (acc * 10 + digitValue c) * 10 ^ length cs + foldDigits cs
      ≡⟨ cong (_+ foldDigits cs) (*-distribʳ-+ (10 ^ length cs) (acc * 10) (digitValue c)) ⟩
    acc * 10 * 10 ^ length cs + digitValue c * 10 ^ length cs + foldDigits cs
      ≡⟨ +-assoc (acc * 10 * 10 ^ length cs) _ _ ⟩
    acc * 10 * 10 ^ length cs + (digitValue c * 10 ^ length cs + foldDigits cs)
      ≡⟨ cong₂ _+_ (*-assoc acc 10 (10 ^ length cs)) (sym (foldl-acc (digitValue c) cs)) ⟩
    acc * (10 * 10 ^ length cs) + foldl step (digitValue c) cs
  ∎
  where open ≡-Reasoning

-- A run's value is its front shifted past its back, plus its back.
foldDigits-++ : ∀ xs ys → foldDigits (xs ++ ys) ≡ foldDigits xs * 10 ^ length ys + foldDigits ys
foldDigits-++ xs ys = trans (foldl-++ step 0 xs ys) (foldl-acc (foldDigits xs) ys)

-- A run of zero-valued characters.
Zeros : List Char → Set
Zeros = All (λ c → digitValue c ≡ 0)

foldDigits-zeros : ∀ {zs} → Zeros zs → foldDigits zs ≡ 0
foldDigits-zeros []            = refl
foldDigits-zeros {c ∷ zs} (z ∷ Z) rewrite z = foldDigits-zeros Z

Zeros-reverse : ∀ {zs} → Zeros zs → Zeros (reverse zs)
Zeros-reverse []                = []
Zeros-reverse {c ∷ zs} (z ∷ Z)
  rewrite unfold-reverse c zs = All-++ (Zeros-reverse Z) (z ∷ [])

-- The run is its dropped zeros followed by what `dropZeros` keeps.
dropZeros-spec : ∀ cs → Σ[ zs ∈ List Char ] (Zeros zs × cs ≡ zs ++ dropZeros cs)
dropZeros-spec []       = [] , [] , refl
dropZeros-spec (c ∷ cs) with isZeroDigit c in eq
... | true  = let zs , Z , e = dropZeros-spec cs
              in c ∷ zs , isZeroDigit-≡ c eq ∷ Z , cong (c ∷_) e
... | false = [] , [] , refl

-- The first character of a run is not zero-valued, or the run is empty.
HeadNonzero : List Char → Set
HeadNonzero []      = ⊤
HeadNonzero (c ∷ _) = digitValue c ≢ 0

dropZeros-head : ∀ cs → HeadNonzero (dropZeros cs)
dropZeros-head []       = tt
dropZeros-head (c ∷ cs) with isZeroDigit c in eq
... | true  = dropZeros-head cs
... | false = isZeroDigit-≢ c eq

HeadNonzero-++ : ∀ xs ys → HeadNonzero (xs ++ ys) → HeadNonzero xs
HeadNonzero-++ []      ys h = tt
HeadNonzero-++ (x ∷ _) ys h = h

-- Dropping leading zeros keeps the value.
foldDigits-dropZeros : ∀ cs → foldDigits cs ≡ foldDigits (dropZeros cs)
foldDigits-dropZeros cs with dropZeros-spec cs
... | zs , Z , e =
  begin
    foldDigits cs
      ≡⟨ cong foldDigits e ⟩
    foldDigits (zs ++ dropZeros cs)
      ≡⟨ foldDigits-++ zs (dropZeros cs) ⟩
    foldDigits zs * 10 ^ length (dropZeros cs) + foldDigits (dropZeros cs)
      ≡⟨ cong (λ v → v * 10 ^ length (dropZeros cs) + foldDigits (dropZeros cs)) (foldDigits-zeros Z) ⟩
    foldDigits (dropZeros cs)
  ∎
  where open ≡-Reasoning

-- A run whose first character is not zero-valued is at least 10 to its
-- length less one.
foldDigits-lower : ∀ c cs → digitValue c ≢ 0 → 10 ^ length cs ≤ foldDigits (c ∷ cs)
foldDigits-lower c cs c≢0 =
  subst (10 ^ length cs ≤_) (sym (foldl-acc (digitValue c) cs))
    (≤-trans (m≤m*n (10 ^ length cs) (digitValue c) ⦃ nonZero ⦄)
             (subst (_≤ digitValue c * 10 ^ length cs + foldDigits cs)
                    (*-comm (digitValue c) (10 ^ length cs))
                    (m≤m+n _ _)))
  where
    nonZero : NonZero (digitValue c)
    nonZero = ≢-nonZero c≢0

-- ============================================================================
-- THE SIGNIFICAND
-- ============================================================================

-- What `significand` returns: the reverse of a run `rev` whose first
-- character is not zero-valued, itself starting with a character that is
-- not zero-valued, and the run's value is the significand's shifted past
-- the trailing zeros counted.
record SignificandSpec (cs sig : List Char) (t : ℕ) : Set where
  field
    rev    : List Char
    sig≡   : sig ≡ reverse rev
    headR  : HeadNonzero rev
    headM  : HeadNonzero (reverse rev)
    value  : foldDigits cs ≡ foldDigits sig * 10 ^ t

significand-spec : ∀ cs → SignificandSpec cs (proj₁ (significand cs)) (proj₂ (significand cs))
significand-spec cs with dropZeros cs in eqL
... | []      = record
  { rev   = []
  ; sig≡  = refl
  ; headR = tt
  ; headM = tt
  ; value = trans (foldDigits-dropZeros cs) (cong foldDigits eqL)
  }
... | c ∷ cs′ = record
  { rev   = R
  ; sig≡  = refl
  ; headR = dropZeros-head (reverse L)
  ; headM = HeadNonzero-++ (reverse R) (reverse zs)
              (subst HeadNonzero L≡ (subst HeadNonzero eqL (dropZeros-head cs)))
  ; value = value
  }
  where
    open ≡-Reasoning
    L = c ∷ cs′
    R = dropZeros (reverse L)
    spec = dropZeros-spec (reverse L)
    zs = proj₁ spec
    Z : Zeros zs
    Z = proj₁ (proj₂ spec)
    revL≡ : reverse L ≡ zs ++ R
    revL≡ = proj₂ (proj₂ spec)
    L≡ : L ≡ reverse R ++ reverse zs
    L≡ = begin
      L                        ≡⟨ sym (reverse-involutive L) ⟩
      reverse (reverse L)      ≡⟨ cong reverse revL≡ ⟩
      reverse (zs ++ R)        ≡⟨ reverse-++ zs R ⟩
      reverse R ++ reverse zs  ∎
    t≡ : length L ∸ length R ≡ length zs
    t≡ = begin
      length L ∸ length R
        ≡⟨ cong (_∸ length R) (sym (length-reverse L)) ⟩
      length (reverse L) ∸ length R
        ≡⟨ cong (λ l → length l ∸ length R) revL≡ ⟩
      length (zs ++ R) ∸ length R
        ≡⟨ cong (_∸ length R) (length-++ zs) ⟩
      (length zs + length R) ∸ length R
        ≡⟨ m+n∸n≡m (length zs) (length R) ⟩
      length zs ∎
    value : foldDigits cs ≡ foldDigits (reverse R) * 10 ^ (length L ∸ length R)
    value = begin
      foldDigits cs
        ≡⟨ trans (foldDigits-dropZeros cs) (cong foldDigits eqL) ⟩
      foldDigits L
        ≡⟨ cong foldDigits L≡ ⟩
      foldDigits (reverse R ++ reverse zs)
        ≡⟨ foldDigits-++ (reverse R) (reverse zs) ⟩
      foldDigits (reverse R) * 10 ^ length (reverse zs) + foldDigits (reverse zs)
        ≡⟨ cong₂ (λ l v → foldDigits (reverse R) * 10 ^ l + v)
                 (length-reverse zs) (foldDigits-zeros (Zeros-reverse Z)) ⟩
      foldDigits (reverse R) * 10 ^ length zs + 0
        ≡⟨ +-identityʳ _ ⟩
      foldDigits (reverse R) * 10 ^ length zs
        ≡⟨ cong (λ l → foldDigits (reverse R) * 10 ^ l) (sym t≡) ⟩
      foldDigits (reverse R) * 10 ^ (length L ∸ length R) ∎

-- ============================================================================
-- CANONICALISATION OF A SHIFTED MAGNITUDE
-- ============================================================================

-- `canonicalizeNat` as its strips.
canonicalizeNat-unfold : ∀ n a b →
  canonicalizeNat n a b ≡
    ( proj₁ (stripShared5-abs (proj₁ (stripShared2-abs n a)) b)
    , proj₂ (stripShared2-abs n a)
    , proj₂ (stripShared5-abs (proj₁ (stripShared2-abs n a)) b))
canonicalizeNat-unfold n a b with stripShared2-abs n a
... | n₂ , a₂ with stripShared5-abs n₂ b
...   | n₅ , b₅ = refl

-- 5 divides neither a power of 2 nor an odd multiple of one.
5∤2^ : ∀ k → 5 ∤ 2 ^ k
5∤2^ zero    (divides zero    ())
5∤2^ zero    (divides (suc _) ())
5∤2^ (suc k) 5∣2·2^k with euclidsLemma 2 (2 ^ k) prime[5] 5∣2·2^k
... | inj₁ (divides zero    ())
... | inj₁ (divides (suc _) ())
... | inj₂ 5∣2^k = 5∤2^ k 5∣2^k

5∤x*2^ : ∀ x k → 5 ∤ x → 5 ∤ (x * 2 ^ k)
5∤x*2^ x k 5∤x 5∣x2^k with euclidsLemma x (2 ^ k) prime[5] 5∣x2^k
... | inj₁ 5∣x   = 5∤x 5∣x
... | inj₂ 5∣2^k = 5∤2^ k 5∣2^k

-- Halving an even number times a power of 5 halves the number.
halve-*5^ : ∀ x k → 2 ∣ x → (x * 5 ^ k) /ₙ 2 ≡ (x /ₙ 2) * 5 ^ k
halve-*5^ x k (divides q eq) rewrite eq =
  begin
    q * 2 * 5 ^ k /ₙ 2
      ≡⟨ cong (_/ₙ 2) (trans (*-assoc q 2 (5 ^ k)) (trans (cong (q *_) (*-comm 2 (5 ^ k))) (sym (*-assoc q (5 ^ k) 2)))) ⟩
    q * 5 ^ k * 2 /ₙ 2
      ≡⟨ m*n/n≡m (q * 5 ^ k) 2 ⟩
    q * 5 ^ k
      ≡⟨ cong (_* 5 ^ k) (sym (m*n/n≡m q 2)) ⟩
    q * 2 /ₙ 2 * 5 ^ k
  ∎
  where open ≡-Reasoning

-- A factor of a power of 5 rides through the 2-strip untouched.
strip2-abs-*5^ : ∀ x k j →
  stripShared2-abs (x * 5 ^ k) j ≡
    (proj₁ (stripShared2-abs x j) * 5 ^ k , proj₂ (stripShared2-abs x j))
strip2-abs-*5^ x k zero    = refl
strip2-abs-*5^ x k (suc j) with 2 ∣? x | 2 ∣? (x * 5 ^ k)
... | yes 2∣x | yes _     = trans (cong (λ m → stripShared2-abs m j) (halve-*5^ x k 2∣x))
                                  (strip2-abs-*5^ (x /ₙ 2) k j)
... | yes 2∣x | no  2∤x5  = ⊥-elim (2∤x5 (∣m⇒∣m*n (5 ^ k) 2∣x))
... | no  2∤x | yes 2∣x5  = ⊥-elim (2∤x*5^ x k 2∤x 2∣x5)
... | no  _   | no  _     = refl

-- Scaling a magnitude by 10^k and its exponents by k canonicalises to the
-- same triple.
canonicalizeNat-shift : ∀ x k j →
  canonicalizeNat (x * 2 ^ k * 5 ^ k) (k + j) (k + j) ≡ canonicalizeNat x j j
canonicalizeNat-shift x k j =
  begin
    canonicalizeNat (x * 2 ^ k * 5 ^ k) (k + j) (k + j)
      ≡⟨ canonicalizeNat-unfold (x * 2 ^ k * 5 ^ k) (k + j) (k + j) ⟩
    ( proj₁ (stripShared5-abs (proj₁ s2) (k + j)) , proj₂ s2 , proj₂ (stripShared5-abs (proj₁ s2) (k + j)) )
      ≡⟨ cong (λ p → ( proj₁ (stripShared5-abs (proj₁ p) (k + j)) , proj₂ p
                     , proj₂ (stripShared5-abs (proj₁ p) (k + j)) )) s2≡ ⟩
    ( proj₁ (stripShared5-abs (n₂ * 5 ^ k) (k + j)) , a₂ , proj₂ (stripShared5-abs (n₂ * 5 ^ k) (k + j)) )
      ≡⟨ cong (λ q → ( proj₁ q , a₂ , proj₂ q )) (strip5-abs-factor n₂ k j) ⟩
    ( proj₁ (stripShared5-abs n₂ j) , a₂ , proj₂ (stripShared5-abs n₂ j) )
      ≡⟨ sym (canonicalizeNat-unfold x j j) ⟩
    canonicalizeNat x j j
  ∎
  where
    open ≡-Reasoning
    s2 = stripShared2-abs (x * 2 ^ k * 5 ^ k) (k + j)
    n₂ = proj₁ (stripShared2-abs x j)
    a₂ = proj₂ (stripShared2-abs x j)
    s2≡ : s2 ≡ (n₂ * 5 ^ k , a₂)
    s2≡ = trans (cong (λ m → stripShared2-abs m (k + j)) (*-2^-5^-swap x k k))
                (trans (strip2-abs-factor (x * 5 ^ k) k j) (strip2-abs-*5^ x k j))

-- ============================================================================
-- THE VERDICT
-- ============================================================================

-- The exact canonical value of a digit run read at `places` and `power`.
exactTriple : List Char → ℕ → ℕ → ℕ × ℕ × ℕ
exactTriple digits places power =
  canonicalizeNat (foldDigits digits * 10 ^ power) places places

canonical : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ
canonical (n , a , b) = canonicalizeNat n a b

-- A reduced numerator or denominator of at least 2^64.
LargeComponent : ℕ × ℕ × ℕ → Set
LargeComponent (n , a , b) = heldMagnitude ≤ n ⊎ heldMagnitude ≤ 2 ^ a * 5 ^ b

Held : ℕ × ℕ × ℕ → Set
Held r = r ≡ heldNumerator ⊎ r ≡ heldDenominator

-- A raw value is read exactly, or held with a large component in the
-- exact value.
data Verdict (raw value : ℕ × ℕ × ℕ) : Set where
  exact : canonical raw ≡ value → Verdict raw value
  held  : Held raw → LargeComponent value → Verdict raw value

-- Small arithmetic facts.
2^64≡ : 2 ^ 64 ≡ heldMagnitude
2^64≡ = refl

10^n≡ : ∀ n → 10 ^ n ≡ 2 ^ n * 5 ^ n
10^n≡ n = ^-distribʳ-* n 2 5

2^64≤10^64 : heldMagnitude ≤ 10 ^ 64
2^64≤10^64 = ^-monoˡ-≤ 64 {2} {10} (s≤s (s≤s z≤n))

2^64≤5^64 : heldMagnitude ≤ 5 ^ 64
2^64≤5^64 = ^-monoˡ-≤ 64 {2} {5} (s≤s (s≤s z≤n))

-- `(a ∨ b) ≡ true` is one of them true.
∨-true : ∀ a b → (a ∨ b) ≡ true → a ≡ true ⊎ b ≡ true
∨-true true  _ _  = inj₁ refl
∨-true false b eq = inj₂ eq

≤ᵇ-false : ∀ m n → (m ≤ᵇ n) ≡ false → n < m
≤ᵇ-false m n eq = ≰⇒> (λ m≤n → subst T eq (≤⇒≤ᵇ m≤n))

-- A number ending in a nonzero digit is not divisible by both 2 and 5.
digit-nondiv : ∀ q d → d ≢ 0 → d < 10 → 2 ∤ (q * 10 + d) ⊎ 5 ∤ (q * 10 + d)
digit-nondiv q d d≢0 d<10 with 2 ∣? d | 5 ∣? d
... | no 2∤d | _      = inj₁ (λ 2∣v → 2∤d (∣m+n∣m⇒∣n 2∣v (∣n⇒∣m*n q (divides 5 refl))))
... | yes _  | no 5∤d = inj₂ (λ 5∣v → 5∤d (∣m+n∣m⇒∣n 5∣v (∣n⇒∣m*n q (divides 2 refl))))
... | yes 2∣d | yes (divides zero d≡0) = ⊥-elim (d≢0 d≡0)
... | yes 2∣d | yes (divides (suc zero) d≡5) = ⊥-elim (2∤5 (subst (2 ∣_) d≡5 2∣d))
... | yes _   | yes (divides (suc (suc q′)) d≡) = ⊥-elim (bad q′ (subst (_< 10) d≡ d<10))
  where
    bad : ∀ q′ → suc (suc q′) * 5 < 10 → ⊥
    bad q′ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ()))))))))))

-- The value of a significand's last digit: a significand is the reverse
-- of a run starting with a nonzero digit.
foldDigits-reverse-∷ : ∀ r rs → foldDigits (reverse (r ∷ rs)) ≡ foldDigits (reverse rs) * 10 + digitValue r
foldDigits-reverse-∷ r rs =
  trans (cong foldDigits (unfold-reverse r rs)) (foldDigits-++ (reverse rs) (r ∷ []))

significand-nondiv : ∀ r rs → digitValue r ≢ 0 →
  2 ∤ foldDigits (reverse (r ∷ rs)) ⊎ 5 ∤ foldDigits (reverse (r ∷ rs))
significand-nondiv r rs r≢0
  rewrite foldDigits-reverse-∷ r rs = digit-nondiv (foldDigits (reverse rs)) (digitValue r) r≢0 (digitValue<10 r)

-- The verdict for a nonempty significand `m ∷ ms` with `t` trailing zeros,
-- whose value is not divisible by both 2 and 5.
sig-verdict : ∀ m ms t places power → digitValue m ≢ 0 →
  2 ∤ foldDigits (m ∷ ms) ⊎ 5 ∤ foldDigits (m ∷ ms) →
  Verdict (rawFromSignificand (m ∷ ms , t) places power)
          (canonicalizeNat (foldDigits (m ∷ ms) * 10 ^ t * 10 ^ power) places places)
sig-verdict m ms t places power m≢0 nondiv with places ≤ᵇ power + t in le
... | true = covered
  where
    v = foldDigits (m ∷ ms)
    e = power + t ∸ places
    V = v * 10 ^ t * 10 ^ power
    places+e : places + e ≡ power + t
    places+e = m+[n∸m]≡n (≤ᵇ⇒≤ places (power + t) (subst T (sym le) tt))
    V≡ : V ≡ v * 10 ^ e * 2 ^ places * 5 ^ places
    V≡ = begin
      v * 10 ^ t * 10 ^ power
        ≡⟨ *-assoc v (10 ^ t) (10 ^ power) ⟩
      v * (10 ^ t * 10 ^ power)
        ≡⟨ cong (v *_) (sym (^-distribˡ-+-* 10 t power)) ⟩
      v * 10 ^ (t + power)
        ≡⟨ cong (λ n → v * 10 ^ n) (trans (+-comm t power) (sym places+e)) ⟩
      v * 10 ^ (places + e)
        ≡⟨ cong (λ n → v * 10 ^ n) (+-comm places e) ⟩
      v * 10 ^ (e + places)
        ≡⟨ cong (v *_) (^-distribˡ-+-* 10 e places) ⟩
      v * (10 ^ e * 10 ^ places)
        ≡⟨ cong (λ n → v * (10 ^ e * n)) (10^n≡ places) ⟩
      v * (10 ^ e * (2 ^ places * 5 ^ places))
        ≡⟨ sym (*-assoc v (10 ^ e) _) ⟩
      v * 10 ^ e * (2 ^ places * 5 ^ places)
        ≡⟨ sym (*-assoc (v * 10 ^ e) (2 ^ places) (5 ^ places)) ⟩
      v * 10 ^ e * 2 ^ places * 5 ^ places
      ∎
      where open ≡-Reasoning
    canonV : canonicalizeNat V places places ≡ (v * 10 ^ e , 0 , 0)
    canonV = begin
      canonicalizeNat V places places
        ≡⟨ cong (λ n → canonicalizeNat n places places) V≡ ⟩
      canonicalizeNat (v * 10 ^ e * 2 ^ places * 5 ^ places) places places
        ≡⟨ cong₂ (canonicalizeNat (v * 10 ^ e * 2 ^ places * 5 ^ places))
                 (sym (+-identityʳ places)) (sym (+-identityʳ places)) ⟩
      canonicalizeNat (v * 10 ^ e * 2 ^ places * 5 ^ places) (places + 0) (places + 0)
        ≡⟨ canonicalizeNat-scale-pos (v * 10 ^ e) 0 0 (λ ()) (λ ()) places places ⟩
      (v * 10 ^ e , 0 , 0)
      ∎
      where open ≡-Reasoning
    covered : Verdict (if digitCutoff ≤ᵇ length (m ∷ ms) + e
                         then heldNumerator else (foldDigits (m ∷ ms) * 10 ^ e , 0 , 0))
                      (canonicalizeNat V places places)
    covered with digitCutoff ≤ᵇ length (m ∷ ms) + e in cut
    ... | true  = held (inj₁ refl) (subst LargeComponent (sym canonV) (inj₁ large))
      where
        64≤ : 64 ≤ length ms + e
        64≤ with ≤ᵇ⇒≤ digitCutoff (suc (length ms) + e) (subst T (sym cut) tt)
        ... | s≤s h = h
        large : heldMagnitude ≤ v * 10 ^ e
        large = ≤-trans 2^64≤10^64
                (≤-trans (^-monoʳ-≤ 10 {64} {length ms + e} 64≤)
                (≤-trans (≤-reflexive (^-distribˡ-+-* 10 (length ms) e))
                         (*-monoˡ-≤ (10 ^ e) (foldDigits-lower m ms m≢0))))
    ... | false = exact (trans (canonicalizeNat-unfold (v * 10 ^ e) 0 0) (sym canonV))
... | false = uncovered
  where
    v = foldDigits (m ∷ ms)
    k = power + t
    d = places ∸ k
    V = v * 10 ^ t * 10 ^ power
    k<places : k < places
    k<places = ≤ᵇ-false places k le
    k+d : k + d ≡ places
    k+d = m+[n∸m]≡n (<⇒≤ k<places)
    V≡ : V ≡ v * 2 ^ k * 5 ^ k
    V≡ = begin
      v * 10 ^ t * 10 ^ power
        ≡⟨ *-assoc v (10 ^ t) (10 ^ power) ⟩
      v * (10 ^ t * 10 ^ power)
        ≡⟨ cong (v *_) (sym (^-distribˡ-+-* 10 t power)) ⟩
      v * 10 ^ (t + power)
        ≡⟨ cong (λ n → v * 10 ^ n) (+-comm t power) ⟩
      v * 10 ^ k
        ≡⟨ cong (v *_) (10^n≡ k) ⟩
      v * (2 ^ k * 5 ^ k)
        ≡⟨ sym (*-assoc v (2 ^ k) (5 ^ k)) ⟩
      v * 2 ^ k * 5 ^ k
      ∎
      where open ≡-Reasoning
    canonV : canonicalizeNat V places places ≡ canonicalizeNat v d d
    canonV = begin
      canonicalizeNat V places places
        ≡⟨ cong (λ n → canonicalizeNat n places places) V≡ ⟩
      canonicalizeNat (v * 2 ^ k * 5 ^ k) places places
        ≡⟨ cong₂ (canonicalizeNat (v * 2 ^ k * 5 ^ k)) (sym k+d) (sym k+d) ⟩
      canonicalizeNat (v * 2 ^ k * 5 ^ k) (k + d) (k + d)
        ≡⟨ canonicalizeNat-shift v k d ⟩
      canonicalizeNat v d d
      ∎
      where open ≡-Reasoning
    -- 10^64 ≤ v when the significand has at least `digitCutoff` digits.
    v-large : digitCutoff ≤ length (m ∷ ms) → 10 ^ 64 ≤ v
    v-large (s≤s 64≤) = ≤-trans (^-monoʳ-≤ 10 64≤) (foldDigits-lower m ms m≢0)
    -- The large component of `canonicalizeNat v d d`.
    large : 2 ∤ v ⊎ 5 ∤ v → (placeCutoff ≤ d ⊎ digitCutoff ≤ length (m ∷ ms))
          → LargeComponent (canonicalizeNat v d d)
    large (inj₁ 2∤v) which = subst LargeComponent (sym canon) (byPlaces which)
      where
        s5 = stripShared5-abs v d
        canon : canonicalizeNat v d d ≡ (proj₁ s5 , d , proj₂ s5)
        canon = trans (canonicalizeNat-unfold v d d)
                      (cong (λ p → (proj₁ (stripShared5-abs (proj₁ p) d) , proj₂ p , proj₂ (stripShared5-abs (proj₁ p) d)))
                            (stripShared2-abs-noDiv v d (λ _ → 2∤v)))
        value : v * 5 ^ proj₂ s5 ≡ proj₁ s5 * 5 ^ d
        value = stripShared5-abs-value v d
        byPlaces : (placeCutoff ≤ d ⊎ digitCutoff ≤ length (m ∷ ms)) → LargeComponent (proj₁ s5 , d , proj₂ s5)
        byPlaces (inj₁ 64≤d) = inj₂ (≤-trans (^-monoʳ-≤ 2 64≤d) (m≤m*n (2 ^ d) (5 ^ proj₂ s5) ⦃ m^n≢0 5 (proj₂ s5) ⦄))
        byPlaces (inj₂ 65≤s) with placeCutoff ≤ᵇ d in pl
        ... | true  = inj₂ (≤-trans (^-monoʳ-≤ 2 (≤ᵇ⇒≤ placeCutoff d (subst T (sym pl) tt)))
                                    (m≤m*n (2 ^ d) (5 ^ proj₂ s5) ⦃ m^n≢0 5 (proj₂ s5) ⦄))
        ... | false = inj₁ (≤-trans (m≤m*n heldMagnitude 5) (*-cancelʳ-≤ (heldMagnitude * 5) (proj₁ s5) (5 ^ 63) chain))
          where
            d≤63 : d ≤ 63
            d≤63 with ≤ᵇ-false placeCutoff d pl
            ... | s≤s h = h
            chain : heldMagnitude * 5 * 5 ^ 63 ≤ proj₁ s5 * 5 ^ 63
            chain = ≤-trans (≤-reflexive (trans (*-assoc heldMagnitude 5 (5 ^ 63)) (sym (10^n≡ 64))))
                    (≤-trans (v-large 65≤s)
                    (≤-trans (m≤m*n v (5 ^ proj₂ s5) ⦃ m^n≢0 5 (proj₂ s5) ⦄)
                    (≤-trans (≤-reflexive value)
                             (*-monoʳ-≤ (proj₁ s5) (^-monoʳ-≤ 5 d≤63)))))
    large (inj₂ 5∤v) which = subst LargeComponent (sym canon) (byPlaces which)
      where
        s2 = stripShared2-abs v d
        value : v * 2 ^ proj₂ s2 ≡ proj₁ s2 * 2 ^ d
        value = stripShared2-abs-value v d
        5∤n₂ : 5 ∤ proj₁ s2
        5∤n₂ 5∣n₂ = 5∤x*2^ v (proj₂ s2) 5∤v (subst (5 ∣_) (sym value) (∣m⇒∣m*n (2 ^ d) 5∣n₂))
        canon : canonicalizeNat v d d ≡ (proj₁ s2 , proj₂ s2 , d)
        canon = trans (canonicalizeNat-unfold v d d)
                      (cong (λ q → (proj₁ q , proj₂ s2 , proj₂ q)) (stripShared5-abs-noDiv (proj₁ s2) d (λ _ → 5∤n₂)))
        byPlaces : (placeCutoff ≤ d ⊎ digitCutoff ≤ length (m ∷ ms)) → LargeComponent (proj₁ s2 , proj₂ s2 , d)
        byPlaces (inj₁ 64≤d) = inj₂ (≤-trans 2^64≤5^64 (≤-trans (^-monoʳ-≤ 5 64≤d) (m≤n*m (5 ^ d) (2 ^ proj₂ s2) ⦃ m^n≢0 2 (proj₂ s2) ⦄)))
        byPlaces (inj₂ 65≤s) with placeCutoff ≤ᵇ d in pl
        ... | true  = inj₂ (≤-trans 2^64≤5^64 (≤-trans (^-monoʳ-≤ 5 (≤ᵇ⇒≤ placeCutoff d (subst T (sym pl) tt)))
                                                       (m≤n*m (5 ^ d) (2 ^ proj₂ s2) ⦃ m^n≢0 2 (proj₂ s2) ⦄)))
        ... | false = inj₁ (≤-trans (m≤m*n heldMagnitude 2) (*-cancelʳ-≤ (heldMagnitude * 2) (proj₁ s2) (2 ^ 63) chain))
          where
            d≤63 : d ≤ 63
            d≤63 with ≤ᵇ-false placeCutoff d pl
            ... | s≤s h = h
            -- 2^64 * 2 * 2^63 = 2^64 * 2^64 ≤ 2^64 * 5^64 = 10^64
            chain : heldMagnitude * 2 * 2 ^ 63 ≤ proj₁ s2 * 2 ^ 63
            chain = ≤-trans (≤-reflexive (*-assoc heldMagnitude 2 (2 ^ 63)))
                    (≤-trans (*-monoʳ-≤ heldMagnitude 2^64≤5^64)
                    (≤-trans (≤-reflexive (sym (10^n≡ 64)))
                    (≤-trans (v-large 65≤s)
                    (≤-trans (m≤m*n v (2 ^ proj₂ s2) ⦃ m^n≢0 2 (proj₂ s2) ⦄)
                    (≤-trans (≤-reflexive value)
                             (*-monoʳ-≤ (proj₁ s2) (^-monoʳ-≤ 2 d≤63)))))))
    uncovered : Verdict (if (placeCutoff ≤ᵇ d) ∨ (digitCutoff ≤ᵇ length (m ∷ ms))
                           then heldDenominator else (foldDigits (m ∷ ms) , d , d))
                        (canonicalizeNat V places places)
    uncovered with (placeCutoff ≤ᵇ d) ∨ (digitCutoff ≤ᵇ length (m ∷ ms)) in cut
    ... | true  = held (inj₂ refl) (subst LargeComponent (sym canonV) (large nondiv which))
      where
        which : placeCutoff ≤ d ⊎ digitCutoff ≤ length (m ∷ ms)
        which with ∨-true (placeCutoff ≤ᵇ d) (digitCutoff ≤ᵇ length (m ∷ ms)) cut
        ... | inj₁ p = inj₁ (≤ᵇ⇒≤ placeCutoff d (subst T (sym p) tt))
        ... | inj₂ q = inj₂ (≤ᵇ⇒≤ digitCutoff (length (m ∷ ms)) (subst T (sym q) tt))
    ... | false = exact (sym canonV)

-- A nonempty run reverses to a nonempty run.
reverse-∷ : ∀ (r : Char) rs → Σ[ m ∈ Char ] Σ[ ms ∈ List Char ] (reverse (r ∷ rs) ≡ m ∷ ms)
reverse-∷ r []        = r , [] , refl
reverse-∷ r (r′ ∷ rs) with reverse-∷ r′ rs
... | m , ms , eq = m , ms ++ (r ∷ []) , trans (unfold-reverse r (r′ ∷ rs)) (cong (_∷ʳ r) eq)

-- The verdict on every literal.
literal-verdict : ∀ digits places power →
  Verdict (rawLiteral digits places power) (exactTriple digits places power)
literal-verdict digits places power
  with significand digits | significand-spec digits
... | sig , t | spec
  with SignificandSpec.rev spec | SignificandSpec.sig≡ spec | SignificandSpec.headR spec
     | SignificandSpec.headM spec | SignificandSpec.value spec
...   | []     | refl | _   | _  | val
  rewrite val = exact (trans (canonicalizeNat-unfold 0 0 0) (sym (canonicalizeNat-zero places places)))
...   | r ∷ rs | refl | r≢0 | hM | val
  with reverse (r ∷ rs) | reverse-∷ r rs | significand-nondiv r rs r≢0
...     | _ | m , ms , refl | nondiv =
      subst (Verdict (rawFromSignificand (m ∷ ms , t) places power)) (sym shift)
            (sig-verdict m ms t places power hM nondiv)
      where
        shift : canonicalizeNat (foldDigits digits * 10 ^ power) places places
              ≡ canonicalizeNat (foldDigits (m ∷ ms) * 10 ^ t * 10 ^ power) places places
        shift = cong (λ n → canonicalizeNat (n * 10 ^ power) places places) val

-- ============================================================================
-- EXACTNESS UNDER THE BOUND
-- ============================================================================

-- Both components within the kernel's bound.
SmallTriple : ℕ × ℕ × ℕ → Set
SmallTriple (n , a , b) =
  n ≤ max-rational-component-magnitude × 2 ^ a * 5 ^ b ≤ max-rational-component-magnitude

-- A small value's components as the core's premise.
smallTriple : ∀ d → SmallDecRat d → SmallTriple (∣ DecRat.numerator d ∣ , DecRat.twoExp d , DecRat.fiveExp d)
smallTriple d small = smallDecRat-components d small

max<2^64 : max-rational-component-magnitude < heldMagnitude
max<2^64 = <ᵇ⇒< max-rational-component-magnitude heldMagnitude tt

small-not-large : ∀ r → SmallTriple r → LargeComponent r → ⊥
small-not-large (n , a , b) (n≤ , _)  (inj₁ 2^64≤n) = <-irrefl refl (≤-<-trans (≤-trans 2^64≤n n≤) max<2^64)
small-not-large (n , a , b) (_ , d≤)  (inj₂ 2^64≤d) = <-irrefl refl (≤-<-trans (≤-trans 2^64≤d d≤) max<2^64)

-- A literal whose exact value fits the bound is read exactly.
rawLiteral-exact : ∀ digits places power → SmallTriple (exactTriple digits places power)
                 → canonical (rawLiteral digits places power) ≡ exactTriple digits places power
rawLiteral-exact digits places power small with literal-verdict digits places power
... | exact e  = e
... | held _ l = ⊥-elim (small-not-large (exactTriple digits places power) small l)

-- A natural-number literal is its digits' value, or 2^64 when that value
-- is at least 10^64.
natLiteral-spec : ∀ digits →
  natLiteral digits ≡ foldDigits digits
  ⊎ (natLiteral digits ≡ heldMagnitude × 10 ^ 64 ≤ foldDigits digits)
natLiteral-spec digits with significand digits | significand-spec digits
... | [] , t | spec = inj₁ (sym (SignificandSpec.value spec))
... | m ∷ ms , t | spec
  with digitCutoff ≤ᵇ length (m ∷ ms) + (0 + t ∸ 0) in cut
...   | true  = inj₂ (refl , large)
  where
    m≢0 : digitValue m ≢ 0
    m≢0 = subst HeadNonzero (sym (SignificandSpec.sig≡ spec)) (SignificandSpec.headM spec)
    64≤ : 64 ≤ length ms + t
    64≤ with ≤ᵇ⇒≤ digitCutoff (suc (length ms) + t) (subst T (sym cut) tt)
    ... | s≤s h = h
    large : 10 ^ 64 ≤ foldDigits digits
    large = subst (10 ^ 64 ≤_) (sym (SignificandSpec.value spec))
              (≤-trans (^-monoʳ-≤ 10 {64} {length ms + t} 64≤)
              (≤-trans (≤-reflexive (^-distribˡ-+-* 10 (length ms) t))
                       (*-monoˡ-≤ (10 ^ t) (foldDigits-lower m ms m≢0))))
...   | false = inj₁ (sym (SignificandSpec.value spec))

natLiteral-exact : ∀ digits → foldDigits digits < 10 ^ 64 → natLiteral digits ≡ foldDigits digits
natLiteral-exact digits small with natLiteral-spec digits
... | inj₁ e          = e
... | inj₂ (_ , large) = ⊥-elim (<-irrefl refl (≤-<-trans large small))

max<10^64 : max-rational-component-magnitude < 10 ^ 64
max<10^64 = <ᵇ⇒< max-rational-component-magnitude (10 ^ 64) tt

-- A natural within the bound reads back from its own digits.
natLiteral-showNat-chars : ∀ n → n ≤ max-rational-component-magnitude →
  natLiteral (showNat-chars n) ≡ n
natLiteral-showNat-chars n n≤ =
  trans (natLiteral-exact (showNat-chars n)
          (subst (_< 10 ^ 64) (sym (foldDigits-showNat-chars n)) (≤-<-trans n≤ max<10^64)))
        (foldDigits-showNat-chars n)

-- ============================================================================
-- THE EXPONENT RULE
-- ============================================================================

-- A fold's value is below 10 to the run's length.
foldDigits-upper : ∀ cs → foldDigits cs < 10 ^ length cs
foldDigits-upper [] = s≤s z≤n
foldDigits-upper (c ∷ cs) =
  subst (_< 10 ^ suc (length cs)) (sym (foldl-acc (digitValue c) cs)) bound
  where
    k = length cs
    v = digitValue c
    v≤9 : v ≤ 9
    v≤9 = <⇒≤pred (digitValue<10 c)
    eq : 9 * 10 ^ k + 10 ^ k ≡ 10 ^ suc k
    eq = sym (trans (*-distribʳ-+ (10 ^ k) 9 1) (cong (λ w → 9 * 10 ^ k + w) (*-identityˡ (10 ^ k))))
    bound : v * 10 ^ k + foldDigits cs < 10 ^ suc k
    bound = ≤-<-trans (+-monoˡ-≤ (foldDigits cs) (*-monoˡ-≤ (10 ^ k) v≤9))
                      (subst (9 * 10 ^ k + foldDigits cs <_) eq
                             (+-monoʳ-< (9 * 10 ^ k) (foldDigits-upper cs)))

-- A natural is below 10 to the length of its own digits.
digits-upper : ∀ n → n < 10 ^ length (showNat-chars n)
digits-upper n = subst (_< 10 ^ length (showNat-chars n)) (foldDigits-showNat-chars n)
                       (foldDigits-upper (showNat-chars n))

-- A run with more significant digits than a number has digits folds to
-- more than that number.
longer-run-larger : ∀ n ds → length (showNat-chars n) < length (dropZeros ds) → n < foldDigits ds
longer-run-larger n ds lt with dropZeros ds in eq
... | []     = ⊥-elim (<-irrefl refl (≤-<-trans z≤n lt))
... | c ∷ cs =
  <-≤-trans (digits-upper n)
    (≤-trans (^-monoʳ-≤ 10 (pred-mono lt′))
      (≤-trans (foldDigits-lower c cs (subst HeadNonzero eq (dropZeros-head ds)))
               (≤-reflexive (sym (trans (foldDigits-dropZeros ds) (cong foldDigits eq))))))
  where
    lt′ : length (showNat-chars n) < suc (length cs)
    lt′ = lt
    pred-mono : ∀ {a b} → a < suc b → a ≤ b
    pred-mono (s≤s h) = h

-- An exponent the digit-count rule holds is past `places + t + digitCutoff`.
exponentHolds-large : ∀ places t ds → exponentHolds places t ds ≡ true
  → places + t + digitCutoff < foldDigits ds
exponentHolds-large places t ds eq =
  longer-run-larger (places + t + digitCutoff) ds
    (<ᵇ⇒< (length (showNat-chars (places + t + digitCutoff))) (length (dropZeros ds)) (subst T (sym eq) tt))

-- With such an exponent, the core holds the literal whichever way the
-- exponent points: the integer has at least `digitCutoff` digits, or the
-- value at least `placeCutoff` places.
exponent-held : ∀ m ms t places (x : ℤ) → places + t + digitCutoff < ∣ x ∣
  → Held (rawFromSignificand (m ∷ ms , t) (places + exponentPlaces x) (exponentPower x))
exponent-held m ms t places (+ e) lt
  rewrite +-identityʳ places
  with places ≤ᵇ e + t in le
... | false = ⊥-elim (<-irrefl refl
                 (<-≤-trans (<-trans (<-≤-trans (<-≤-trans (≤ᵇ-false places (e + t) le) (m≤m+n places t))
                                                (m≤m+n (places + t) digitCutoff))
                                     lt)
                            (m≤m+n e t)))
... | true with digitCutoff ≤ᵇ length (m ∷ ms) + (e + t ∸ places) in cut
...   | true  = inj₁ refl
...   | false = ⊥-elim (<-irrefl refl
                 (<-trans (≤ᵇ-false digitCutoff (length (m ∷ ms) + (e + t ∸ places)) cut)
                          (<-≤-trans digitCutoff<e∸places (m≤n+m (e + t ∸ places) (length (m ∷ ms))))))
  where
    digitCutoff<e∸places : digitCutoff < e + t ∸ places
    digitCutoff<e∸places = +-cancelˡ-< places digitCutoff (e + t ∸ places) (subst (places + digitCutoff <_)
      (sym (m+[n∸m]≡n (≤ᵇ⇒≤ places (e + t) (subst T (sym le) tt))))
      (≤-<-trans (+-monoˡ-≤ digitCutoff (m≤m+n places t)) (<-≤-trans lt (m≤m+n e t))))
exponent-held m ms t places -[1+ e ] lt
  with places + suc e ≤ᵇ 0 + t in le
... | true  = ⊥-elim (<-irrefl refl (≤-<-trans (≤ᵇ⇒≤ (places + suc e) t (subst T (sym le) tt))
                 (≤-<-trans (m≤n+m t places) (≤-<-trans (m≤m+n (places + t) digitCutoff) (<-≤-trans lt (m≤n+m (suc e) places))))))
... | false with (placeCutoff ≤ᵇ places + suc e ∸ (0 + t)) ∨ (digitCutoff ≤ᵇ length (m ∷ ms)) in cut
...   | true  = inj₂ refl
...   | false = ⊥-elim (<-irrefl refl (<-≤-trans (≤ᵇ-false placeCutoff (places + suc e ∸ t) (∨-false₁ cut))
                 (≤-trans (<⇒≤ placeCutoff<d) ≤-refl)))
  where
    ∨-false₁ : ∀ {a b} → (a ∨ b) ≡ false → a ≡ false
    ∨-false₁ {false} _ = refl
    placeCutoff<d : placeCutoff < places + suc e ∸ t
    placeCutoff<d = +-cancelˡ-< t placeCutoff (places + suc e ∸ t)
      (subst (t + placeCutoff <_) (sym (m+[n∸m]≡n (<⇒≤ t<ps)))
        (≤-<-trans step1 (<-≤-trans lt (m≤n+m (suc e) places))))
      where
        t<ps : t < places + suc e
        t<ps = ≤ᵇ-false (places + suc e) (0 + t) le
        step1 : t + placeCutoff ≤ places + t + digitCutoff
        step1 = ≤-trans (+-monoʳ-≤ t (n≤1+n placeCutoff)) (+-monoˡ-≤ digitCutoff (m≤n+m t places))

-- A literal the core holds, by its own rule or by the exponent rule,
-- has a large component in its exact value: the verdict says so, or the
-- held value canonicalises to itself and is at 2^64 outright.
held-large : ∀ digits places power → Held (rawLiteral digits places power)
           → LargeComponent (exactTriple digits places power)
held-large digits places power h with literal-verdict digits places power
... | held _ l = l
... | exact e  = subst LargeComponent (trans (sym (held-canonical h)) e) (large-of h)
  where
    held-canonical : ∀ {r} → Held r → canonical r ≡ r
    held-canonical (inj₁ refl) = refl
    held-canonical (inj₂ refl) = refl
    large-of : ∀ {r} → Held r → LargeComponent r
    large-of (inj₁ refl) = inj₁ ≤-refl
    large-of (inj₂ refl) = inj₂ (≤-reflexive (sym (*-identityʳ heldMagnitude)))
