-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Renderer FAITHFULNESS: the string `formatℚ-chars q` reads back as `q`.
--
-- `RationalRenderer.Properties` proves only CANONICALITY (`cong formatℚ`):
-- equal ℚ inputs render to byte-identical strings (determinism / no
-- cross-binding divergence).  It says nothing about the *value* the string
-- denotes — `formatℚ` could return `"banana"` and canonicality would hold.
--
-- This module closes that gap.  `Represents : List Char → ℚ → Set` is an
-- independent standard-numeral semantics (digit runs decoded by the existing
-- `parseDigitList` Horner fold; decimal `is.fs`; fraction `n/d`; leading `-`),
-- and `formatℚ-chars-represents` proves `Represents (formatℚ-chars q) q` for
-- every `q` — i.e. the renderer never misrepresents a value.
--
-- Reuse: digit faithfulness from `DecRatParse.Properties.Phase1Digits`
-- (`parseDigitList-show{Nat,ℕ-padded}-chars`), the `fromℚ?` soundness linchpin
-- (`RationalSoundness.toℚ-fromℚ?-sound`) for the decimal / k>18 branches, and
-- stdlib `↥p/↧p≡p` as the uniform value bridge.
--
-- LAYER A (this commit's first half): the relation + infrastructure —
-- all-digits of the emitters, the trailing-zero decomposition, Horner
-- append-zeros, and the decimal scaling lemma.  LAYER B (magnitude helper +
-- the headline theorem) builds on these.
module Aletheia.DBC.RationalRenderer.Faithful where

open import Data.Char using (Char) renaming (_≟_ to _≟ᶜ_)
open import Data.List using (List; []; _∷_; length; reverse; replicate; foldl)
  renaming (_++_ to _++ₗ_)
open import Data.List.Properties
  using (length-++; length-replicate; reverse-++; reverse-involutive;
         unfold-reverse; foldl-++)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as Allₚ
open import Data.Nat.Base
  using (ℕ; zero; suc; _+_; _*_; _^_; _⊔_; _<_; _≤_; _<ᵇ_; z≤n; s≤s; NonZero)
  renaming (_/_ to _/ₙ_; _%_ to _%ₙ_; _∸_ to _∸ₙ_)
open import Data.Nat.Properties
  using (m^n≢0; *-comm; *-assoc; *-identityʳ;
         +-comm; +-identityʳ; m∸n+n≡m; ^-distribˡ-+-*; *-distribʳ-+;
         *-cancelʳ-≡; suc-pred; n≤0⇒n≡0; m≤m⊔n; m≤n⊔m;
         <ᵇ⇒<; <⇒<ᵇ; <⇒≱; ≮⇒≥)
open import Data.Nat.DivMod using (m%n<n; m≡m%n+[m/n]*n)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Integer.Base using (ℤ; +_; -[1+_])
import Data.Integer.Base as ℤ
open import Data.Integer.Properties using (pos-*)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Maybe.Base using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Bool.Base using (true; false; T)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Rational.Base using (ℚ; _/_; -_; ↥_; ↧ₙ_; fromℚᵘ)
open import Data.Rational.Properties using (↥p/↧p≡p; fromℚᵘ-cong)
import Data.Rational.Unnormalised.Base as ℚᵘ
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open import Relation.Nullary using (yes; no; ¬_)

open import Aletheia.DBC.TextFormatter.Emitter using
  (digitChar; showNat-chars; showNat-chars-fuel; showℕ-padded-chars)
open import Aletheia.DBC.TextParser.DecRatParse using (parseDigitList; charToDigit)
open import Aletheia.DBC.TextParser.DecRatParse.Properties.Phase1Digits using
  (parseDigitList-showNat-chars; parseDigitList-showℕ-padded-chars; charToDigit-digitChar)
open import Aletheia.DBC.RationalRenderer using
  (formatℚ-chars; emitNbyD-chars; emitDecimal-trimmed-chars;
   emitMagnitude-trimmed-chars; joinIntFrac; maxDecimalPlaces;
   trimTrailingZeros; dropLeadingZeros)
open import Aletheia.DBC.DecRat using
  (DecRat; mkDecRat; toℚ; fromℚ?; 2^a·5^b-NonZero; fromℚᵘ-mkℚᵘ-/)
open import Aletheia.DBC.DecRat.RationalSoundness using (toℚ-fromℚ?-sound)
open import Aletheia.DBC.DecRat.RationalRoundtrip using
  (fromℚ?-after-toℚ; ↥-toℚ-canonical; ↧ₙ-toℚ-canonical)

------------------------------------------------------------------------
-- Standard-numeral semantics of a rendered string.
------------------------------------------------------------------------

-- A character that is one of the ten decimal digits.
DigitChar : Char → Set
DigitChar c = Σ[ d ∈ ℕ ] (d < 10 × c ≡ digitChar d)

AllDigits : List Char → Set
AllDigits = All DigitChar

-- `Represents cs q`: the character list `cs`, read under standard decimal /
-- fraction numeral semantics, denotes the rational `q`.  Each clause pins the
-- value as a function of the digit runs' `parseDigitList` values, so the
-- relation is emitter-independent (not a restatement of `formatℚ`).
data Represents : List Char → ℚ → Set where
  rep-int  : (ds : List Char) → AllDigits ds →
             Represents ds ((+ parseDigitList ds) / 1)
  rep-dec  : (is fs : List Char) → AllDigits is → AllDigits fs → fs ≢ [] →
             ⦃ _ : NonZero (10 ^ length fs) ⦄ →
             Represents (is ++ₗ '.' ∷ fs)
               ((+ (parseDigitList is * 10 ^ length fs + parseDigitList fs))
                  / (10 ^ length fs))
  rep-frac : (ns ds : List Char) → AllDigits ns → AllDigits ds →
             ⦃ _ : NonZero (parseDigitList ds) ⦄ →
             Represents (ns ++ₗ '/' ∷ ds)
               ((+ parseDigitList ns) / parseDigitList ds)
  rep-neg  : (cs : List Char) (q : ℚ) → Represents cs q →
             Represents ('-' ∷ cs) (- q)

------------------------------------------------------------------------
-- The emitters produce all-digit strings.
------------------------------------------------------------------------

private
  digitChar-DigitChar : ∀ n → DigitChar (digitChar (n %ₙ 10))
  digitChar-DigitChar n = n %ₙ 10 , m%n<n n 10 , refl

showNat-fuel-AllDigits : ∀ fuel n → AllDigits (showNat-chars-fuel fuel n)
showNat-fuel-AllDigits zero    _ = []
showNat-fuel-AllDigits (suc f) n with n /ₙ 10
... | zero  = digitChar-DigitChar n ∷ []
... | suc m = Allₚ.++⁺ (showNat-fuel-AllDigits f (suc m))
                       (digitChar-DigitChar n ∷ [])

showNat-AllDigits : ∀ n → AllDigits (showNat-chars n)
showNat-AllDigits n = showNat-fuel-AllDigits (suc n) n

showℕ-padded-AllDigits : ∀ w n → AllDigits (showℕ-padded-chars w n)
showℕ-padded-AllDigits zero    _ = []
showℕ-padded-AllDigits (suc w) n =
  Allₚ.++⁺ (showℕ-padded-AllDigits w (n /ₙ 10))
           (digitChar-DigitChar n ∷ [])

------------------------------------------------------------------------
-- Trailing-zero decomposition of `trimTrailingZeros`.
------------------------------------------------------------------------

private
  -- `reverse (replicate t x) ≡ replicate t x`.
  replicate-∷ʳ : ∀ t (x : Char) →
    replicate t x ++ₗ x ∷ [] ≡ replicate (suc t) x
  replicate-∷ʳ zero    x = refl
  replicate-∷ʳ (suc t) x = cong (x ∷_) (replicate-∷ʳ t x)

  reverse-replicate : ∀ t (x : Char) → reverse (replicate t x) ≡ replicate t x
  reverse-replicate zero    x = refl
  reverse-replicate (suc t) x = begin
    reverse (x ∷ replicate t x)      ≡⟨ unfold-reverse x (replicate t x) ⟩
    reverse (replicate t x) ++ₗ x ∷ []  ≡⟨ cong (_++ₗ x ∷ []) (reverse-replicate t x) ⟩
    replicate t x ++ₗ x ∷ []         ≡⟨ replicate-∷ʳ t x ⟩
    replicate (suc t) x ∎
    where open ≡-Reasoning

  -- Leading-zero peel: `ys` is a run of `t` zeros followed by `dropLeadingZeros ys`.
  dropLeadingZeros-decomp :
    ∀ ys → Σ[ t ∈ ℕ ] ys ≡ replicate t '0' ++ₗ dropLeadingZeros ys
  dropLeadingZeros-decomp []       = 0 , refl
  dropLeadingZeros-decomp (c ∷ cs) with c ≟ᶜ '0'
  ... | no  _    = 0 , refl
  ... | yes c≡0 with dropLeadingZeros-decomp cs
  ...   | (t , eq) = suc t , (begin
            c ∷ cs
              ≡⟨ cong (_∷ cs) c≡0 ⟩
            '0' ∷ cs
              ≡⟨ cong ('0' ∷_) eq ⟩
            '0' ∷ (replicate t '0' ++ₗ dropLeadingZeros cs)
              ∎)
            where open ≡-Reasoning

-- `xs ≡ trimTrailingZeros xs ++ replicate t '0'` for some `t`.
trim-decomp :
  ∀ xs → Σ[ t ∈ ℕ ] xs ≡ trimTrailingZeros xs ++ₗ replicate t '0'
trim-decomp xs with dropLeadingZeros-decomp (reverse xs)
... | (t , eq) = t , (begin
    xs
      ≡⟨ sym (reverse-involutive xs) ⟩
    reverse (reverse xs)
      ≡⟨ cong reverse eq ⟩
    reverse (replicate t '0' ++ₗ dropLeadingZeros (reverse xs))
      ≡⟨ reverse-++ (replicate t '0') (dropLeadingZeros (reverse xs)) ⟩
    reverse (dropLeadingZeros (reverse xs)) ++ₗ reverse (replicate t '0')
      ≡⟨ cong (trimTrailingZeros xs ++ₗ_) (reverse-replicate t '0') ⟩
    trimTrailingZeros xs ++ₗ replicate t '0' ∎)
    where open ≡-Reasoning

-- `All` is preserved by trimming (it drops a suffix).
trim-AllDigits : ∀ {xs} → AllDigits xs → AllDigits (trimTrailingZeros xs)
trim-AllDigits {xs} all-xs with trim-decomp xs
... | (t , eq) = Allₚ.++⁻ˡ (trimTrailingZeros xs) (subst AllDigits eq all-xs)

-- length bookkeeping: `length xs ≡ length (trim xs) + t`.
trim-length :
  ∀ xs → Σ[ t ∈ ℕ ] length xs ≡ length (trimTrailingZeros xs) + t
trim-length xs with trim-decomp xs
... | (t , eq) = t , (begin
    length xs
      ≡⟨ cong length eq ⟩
    length (trimTrailingZeros xs ++ₗ replicate t '0')
      ≡⟨ length-++ (trimTrailingZeros xs) ⟩
    length (trimTrailingZeros xs) + length (replicate t '0')
      ≡⟨ cong (λ z → length (trimTrailingZeros xs) + z) (length-replicate t) ⟩
    length (trimTrailingZeros xs) + t ∎)
    where open ≡-Reasoning

------------------------------------------------------------------------
-- Horner decode of a digit run with `t` trailing zeros = multiply by 10^t.
------------------------------------------------------------------------

private
  charToDigit-0 : charToDigit '0' ≡ 0
  charToDigit-0 = charToDigit-digitChar 0 (s≤s z≤n)

  foldl-zeros : ∀ acc t →
    foldl (λ a e → a * 10 + charToDigit e) acc (replicate t '0')
      ≡ acc * 10 ^ t
  foldl-zeros acc zero    = sym (*-identityʳ acc)
  foldl-zeros acc (suc t) = begin
    foldl step (acc * 10 + charToDigit '0') (replicate t '0')
      ≡⟨ cong (λ k → foldl step (acc * 10 + k) (replicate t '0')) charToDigit-0 ⟩
    foldl step (acc * 10 + 0) (replicate t '0')
      ≡⟨ cong (λ k → foldl step k (replicate t '0')) (+-identityʳ (acc * 10)) ⟩
    foldl step (acc * 10) (replicate t '0')
      ≡⟨ foldl-zeros (acc * 10) t ⟩
    acc * 10 * 10 ^ t
      ≡⟨ *-assoc acc 10 (10 ^ t) ⟩
    acc * (10 * 10 ^ t)
      ∎
    where
      open ≡-Reasoning
      step : ℕ → Char → ℕ
      step a e = a * 10 + charToDigit e

parseDigitList-append-zeros : ∀ xs t →
  parseDigitList (xs ++ₗ replicate t '0') ≡ parseDigitList xs * 10 ^ t
parseDigitList-append-zeros xs t = begin
  foldl step 0 (xs ++ₗ replicate t '0')
    ≡⟨ foldl-++ step 0 xs (replicate t '0') ⟩
  foldl step (foldl step 0 xs) (replicate t '0')
    ≡⟨ foldl-zeros (foldl step 0 xs) t ⟩
  foldl step 0 xs * 10 ^ t ∎
  where
    open ≡-Reasoning
    step : ℕ → Char → ℕ
    step a e = a * 10 + charToDigit e

------------------------------------------------------------------------
-- Foundational arithmetic for the value bridges.
------------------------------------------------------------------------

private
  -- Power of a product: stdlib has `^-distribˡ-+-*` (exponent split) but
  -- not the base split, so derive it here.
  ^-distrib-* : ∀ x y n → (x * y) ^ n ≡ x ^ n * y ^ n
  ^-distrib-* x y zero    = refl
  ^-distrib-* x y (suc n) = begin
    (x * y) * (x * y) ^ n
      ≡⟨ cong ((x * y) *_) (^-distrib-* x y n) ⟩
    (x * y) * (x ^ n * y ^ n)
      ≡⟨ *-assoc x y (x ^ n * y ^ n) ⟩
    x * (y * (x ^ n * y ^ n))
      ≡⟨ cong (x *_) (sym (*-assoc y (x ^ n) (y ^ n))) ⟩
    x * ((y * x ^ n) * y ^ n)
      ≡⟨ cong (λ z → x * (z * y ^ n)) (*-comm y (x ^ n)) ⟩
    x * ((x ^ n * y) * y ^ n)
      ≡⟨ cong (x *_) (*-assoc (x ^ n) y (y ^ n)) ⟩
    x * (x ^ n * (y * y ^ n))
      ≡⟨ sym (*-assoc x (x ^ n) (y * y ^ n)) ⟩
    (x * x ^ n) * (y * y ^ n) ∎
    where open ≡-Reasoning

  -- 10^m = 2^m · 5^m.
  10^≡2^*5^ : ∀ m → 10 ^ m ≡ 2 ^ m * 5 ^ m
  10^≡2^*5^ m = ^-distrib-* 2 5 m

  -- 2^(m∸k) · 2^k = 2^m  (for k ≤ m), and the same for any base.
  pow-split : ∀ x m k → k ≤ m → x ^ (m ∸ₙ k) * x ^ k ≡ x ^ m
  pow-split x m k k≤m = begin
    x ^ (m ∸ₙ k) * x ^ k
      ≡⟨ sym (^-distribˡ-+-* x (m ∸ₙ k) k) ⟩
    x ^ ((m ∸ₙ k) + k)
      ≡⟨ cong (x ^_) (m∸n+n≡m k≤m) ⟩
    x ^ m ∎
    where open ≡-Reasoning

  -- length of a fixed-width padded numeral is the width.
  showℕ-padded-length : ∀ w n → length (showℕ-padded-chars w n) ≡ w
  showℕ-padded-length zero    n = refl
  showℕ-padded-length (suc w) n = begin
    length (showℕ-padded-chars w (n /ₙ 10) ++ₗ digitChar (n %ₙ 10) ∷ [])
      ≡⟨ length-++ (showℕ-padded-chars w (n /ₙ 10)) ⟩
    length (showℕ-padded-chars w (n /ₙ 10)) + 1
      ≡⟨ cong (_+ 1) (showℕ-padded-length w (n /ₙ 10)) ⟩
    w + 1
      ≡⟨ +-comm w 1 ⟩
    suc w ∎
    where open ≡-Reasoning

  -- `(+A)/B ≡ (+C)/D` from the ℕ cross-multiplication `A * D ≡ C * B`.
  -- Routes through the unnormalised layer (`fromℚᵘ-mkℚᵘ-/` + `fromℚᵘ-cong`)
  -- so neither `_/_`'s gcd normaliser nor its NonZero instance argument
  -- needs to be unfolded — the same technique as `DecRat.canonicalize-value`.
  /-fromℕ-cross : ∀ A B C D ⦃ _ : NonZero B ⦄ ⦃ _ : NonZero D ⦄ →
    A * D ≡ C * B → (+ A) / B ≡ (+ C) / D
  /-fromℕ-cross A B C D cross = begin
    (+ A) / B
      ≡⟨ sym (fromℚᵘ-mkℚᵘ-/ (+ A) B) ⟩
    fromℚᵘ (ℚᵘ.mkℚᵘ (+ A) (B ∸ₙ 1))
      ≡⟨ fromℚᵘ-cong {ℚᵘ.mkℚᵘ (+ A) (B ∸ₙ 1)} {ℚᵘ.mkℚᵘ (+ C) (D ∸ₙ 1)}
                    (ℚᵘ.*≡* eqᵘ) ⟩
    fromℚᵘ (ℚᵘ.mkℚᵘ (+ C) (D ∸ₙ 1))
      ≡⟨ fromℚᵘ-mkℚᵘ-/ (+ C) D ⟩
    (+ C) / D ∎
    where
      open ≡-Reasoning
      eqᵘ : (+ A) ℤ.* (+ suc (D ∸ₙ 1)) ≡ (+ C) ℤ.* (+ suc (B ∸ₙ 1))
      eqᵘ = begin
        (+ A) ℤ.* (+ suc (D ∸ₙ 1))
          ≡⟨ cong (λ k → (+ A) ℤ.* (+ k)) (suc-pred D) ⟩
        (+ A) ℤ.* (+ D)
          ≡⟨ sym (pos-* A D) ⟩
        + (A * D)
          ≡⟨ cong +_ cross ⟩
        + (C * B)
          ≡⟨ pos-* C B ⟩
        (+ C) ℤ.* (+ B)
          ≡⟨ cong (λ k → (+ C) ℤ.* (+ k)) (sym (suc-pred B)) ⟩
        (+ C) ℤ.* (+ suc (B ∸ₙ 1)) ∎

  -- Reconcile the `suc (d ∸ 1)` denominator (as produced by `↥p/↧p≡p` on a
  -- directly-built `mkℚ`) with the bare `d`.  `suc (d∸1) ∸ 1 ≡ d∸1`
  -- definitionally, so the two `mkℚᵘ` cores coincide.
  /-suc-pred : ∀ (n : ℤ) (d : ℕ) ⦃ _ : NonZero d ⦄ → n / suc (d ∸ₙ 1) ≡ n / d
  /-suc-pred n d = begin
    n / suc (d ∸ₙ 1)
      ≡⟨ sym (fromℚᵘ-mkℚᵘ-/ n (suc (d ∸ₙ 1))) ⟩
    fromℚᵘ (ℚᵘ.mkℚᵘ n (d ∸ₙ 1))
      ≡⟨ fromℚᵘ-mkℚᵘ-/ n d ⟩
    n / d ∎
    where open ≡-Reasoning

------------------------------------------------------------------------
-- Fraction branch: `emitNbyD-chars num denom` reads back as `num / denom`.
------------------------------------------------------------------------

private
  -- Positive numerator: a bare `rep-frac`, with the value reconciled from
  -- the digit-faithfulness of both runs (`parseDigitList ∘ showNat ≡ id`).
  emitNbyD-represents⁺ : ∀ (n denom : ℕ) ⦃ nz : NonZero denom ⦄ →
    Represents (showNat-chars n ++ₗ '/' ∷ showNat-chars denom) ((+ n) / denom)
  emitNbyD-represents⁺ n denom ⦃ nz ⦄ =
    subst (Represents (showNat-chars n ++ₗ '/' ∷ showNat-chars denom)) value-eq
      (rep-frac (showNat-chars n) (showNat-chars denom)
                (showNat-AllDigits n) (showNat-AllDigits denom) ⦃ nz' ⦄)
    where
      instance
        nz' : NonZero (parseDigitList (showNat-chars denom))
        nz' = subst NonZero (sym (parseDigitList-showNat-chars denom)) nz
      cross : parseDigitList (showNat-chars n) * denom
            ≡ n * parseDigitList (showNat-chars denom)
      cross = trans (cong (_* denom) (parseDigitList-showNat-chars n))
                    (cong (n *_) (sym (parseDigitList-showNat-chars denom)))
      value-eq :
        (+ parseDigitList (showNat-chars n)) / parseDigitList (showNat-chars denom)
          ≡ (+ n) / denom
      value-eq = /-fromℕ-cross (parseDigitList (showNat-chars n))
                               (parseDigitList (showNat-chars denom))
                               n denom ⦃ nz' ⦄ ⦃ nz ⦄ cross

-- `emitNbyD-chars num denom` denotes `num / denom`.  Negative numerators
-- are a `rep-neg` wrap; `-[1+ n] / d ≡ - ((+ suc n) / d)` holds definitionally
-- (`Data.Rational.Base`'s `_/_` splits on the numerator's sign).
emitNbyD-represents : ∀ (num : ℤ) (denom : ℕ) ⦃ _ : NonZero denom ⦄ →
  Represents (emitNbyD-chars num denom) (num / denom)
emitNbyD-represents (+ n)    denom = emitNbyD-represents⁺ n denom
emitNbyD-represents -[1+ n ] denom =
  rep-neg (showNat-chars (suc n) ++ₗ '/' ∷ showNat-chars denom)
          ((+ suc n) / denom)
          (emitNbyD-represents⁺ (suc n) denom)

------------------------------------------------------------------------
-- Decimal branch: the trimmed magnitude emitter.
------------------------------------------------------------------------

private
  -- Pure-product rearrangements, discharged by the commutative-monoid
  -- solver (no `^`/`∸`/div-mod content — those stay explicit below).
  open +-*-Solver using (solve; _:=_; _:*_)

  shuffle5 : ∀ A P2 P5 Q2 Q5 →
    ((A * P2) * P5) * (Q2 * Q5) ≡ A * ((P2 * Q2) * (P5 * Q5))
  shuffle5 = solve 5 (λ A P2 P5 Q2 Q5 →
    ((A :* P2) :* P5) :* (Q2 :* Q5) := A :* ((P2 :* Q2) :* (P5 :* Q5))) refl

  shuffle3 : ∀ x y z → (x * y) * z ≡ (x * z) * y
  shuffle3 = solve 3 (λ x y z → (x :* y) :* z := (x :* z) :* y) refl

-- `joinIntFrac (showNat-chars ip) fr` (integer part `ip`, fractional digit
-- run `fr`) denotes `(ip · 10^|fr| + ⟦fr⟧) / 10^|fr|` — i.e. it splices the
-- two digit runs at the decimal point.  `fr = []` collapses to a `rep-int`
-- (`ip / 1`); a non-empty `fr` is a `rep-dec`.  Both cases reconcile the
-- integer part via `parseDigitList ∘ showNat ≡ id`.
joinIntFrac-represents :
  ∀ (ip : ℕ) (fr : List Char) → AllDigits fr →
    Represents (joinIntFrac (showNat-chars ip) fr)
               (_/_ (+ (ip * 10 ^ length fr + parseDigitList fr))
                    (10 ^ length fr) ⦃ m^n≢0 10 (length fr) ⦄)
joinIntFrac-represents ip [] _ =
  subst (λ v → Represents (showNat-chars ip) v) value-eq
        (rep-int (showNat-chars ip) (showNat-AllDigits ip))
  where
    num-eq : parseDigitList (showNat-chars ip) ≡ ip * 1 + 0
    num-eq = trans (parseDigitList-showNat-chars ip)
                   (sym (trans (+-identityʳ (ip * 1)) (*-identityʳ ip)))
    value-eq : _/_ (+ parseDigitList (showNat-chars ip)) 1 ⦃ m^n≢0 10 0 ⦄
             ≡ _/_ (+ (ip * 1 + 0)) 1 ⦃ m^n≢0 10 0 ⦄
    value-eq = cong (λ z → _/_ (+ z) 1 ⦃ m^n≢0 10 0 ⦄) num-eq
joinIntFrac-represents ip (c ∷ cs) all-cs =
  subst (λ z → Represents (showNat-chars ip ++ₗ '.' ∷ c ∷ cs)
                 (_/_ (+ (z * 10 ^ length (c ∷ cs) + parseDigitList (c ∷ cs)))
                      (10 ^ length (c ∷ cs)) ⦃ m^n≢0 10 (length (c ∷ cs)) ⦄))
        (parseDigitList-showNat-chars ip)
        (rep-dec (showNat-chars ip) (c ∷ cs)
                 (showNat-AllDigits ip) all-cs (λ ())
                 ⦃ m^n≢0 10 (length (c ∷ cs)) ⦄)

-- `emitMagnitude-trimmed-chars absNum a b` denotes `(+ absNum)/(2^a · 5^b)`.
-- Splits on `a ⊔ b`: zero ⇒ integer (`rep-int`); positive ⇒ scale into a
-- `10^m`-denominator decimal, divide into int/frac digit runs, trim, and
-- splice.  The value identity reconciles the scaled `_/_` with the original
-- via cross-multiplication (`/-fromℕ-cross`).
emitMagnitude-represents : ∀ (absNum a b : ℕ) →
  Represents (emitMagnitude-trimmed-chars absNum a b)
             (_/_ (+ absNum) (2 ^ a * 5 ^ b) ⦃ 2^a·5^b-NonZero a b ⦄)
emitMagnitude-represents absNum a b with a ⊔ b in eq
... | zero =
      subst (λ v → Represents (showNat-chars absNum) v) value-eq
            (rep-int (showNat-chars absNum) (showNat-AllDigits absNum))
      where
        open ≡-Reasoning
        a≡0 : a ≡ 0
        a≡0 = n≤0⇒n≡0 (subst (a ≤_) eq (m≤m⊔n a b))
        b≡0 : b ≡ 0
        b≡0 = n≤0⇒n≡0 (subst (b ≤_) eq (m≤n⊔m a b))
        cross : parseDigitList (showNat-chars absNum) * (2 ^ a * 5 ^ b) ≡ absNum * 1
        cross = begin
          parseDigitList (showNat-chars absNum) * (2 ^ a * 5 ^ b)
            ≡⟨ cong (_* (2 ^ a * 5 ^ b)) (parseDigitList-showNat-chars absNum) ⟩
          absNum * (2 ^ a * 5 ^ b)
            ≡⟨ cong (λ k → absNum * (2 ^ k * 5 ^ b)) a≡0 ⟩
          absNum * (2 ^ 0 * 5 ^ b)
            ≡⟨ cong (λ k → absNum * (2 ^ 0 * 5 ^ k)) b≡0 ⟩
          absNum * (2 ^ 0 * 5 ^ 0)
            ≡⟨⟩
          absNum * 1 ∎
        value-eq : _/_ (+ parseDigitList (showNat-chars absNum)) 1 ⦃ m^n≢0 10 0 ⦄
                 ≡ _/_ (+ absNum) (2 ^ a * 5 ^ b) ⦃ 2^a·5^b-NonZero a b ⦄
        value-eq = /-fromℕ-cross (parseDigitList (showNat-chars absNum)) 1
                                 absNum (2 ^ a * 5 ^ b)
                                 ⦃ m^n≢0 10 0 ⦄ ⦃ 2^a·5^b-NonZero a b ⦄ cross
... | suc m-1 =
      subst (λ v → Represents (joinIntFrac (showNat-chars intPart-val) fr) v)
            decode-value
            (joinIntFrac-represents intPart-val fr
              (trim-AllDigits (showℕ-padded-AllDigits m r)))
      where
        open ≡-Reasoning
        m : ℕ
        m = suc m-1
        instance
          10^m-nz : NonZero (10 ^ m)
          10^m-nz = m^n≢0 10 m
        scaledNum : ℕ
        scaledNum = absNum * 2 ^ (m ∸ₙ a) * 5 ^ (m ∸ₙ b)
        intPart-val : ℕ
        intPart-val = scaledNum /ₙ 10 ^ m
        r : ℕ
        r = scaledNum %ₙ 10 ^ m
        fracDigits : List Char
        fracDigits = showℕ-padded-chars m r
        fr : List Char
        fr = trimTrailingZeros fracDigits
        L : ℕ
        L = length fr
        pfr : ℕ
        pfr = parseDigitList fr
        D : ℕ
        D = 2 ^ a * 5 ^ b
        a≤m : a ≤ m
        a≤m = subst (a ≤_) eq (m≤m⊔n a b)
        b≤m : b ≤ m
        b≤m = subst (b ≤_) eq (m≤n⊔m a b)
        td : Σ[ s ∈ ℕ ] fracDigits ≡ fr ++ₗ replicate s '0'
        td = trim-decomp fracDigits
        t : ℕ
        t = proj₁ td
        fr-eq : fracDigits ≡ fr ++ₗ replicate t '0'
        fr-eq = proj₂ td
        m≡L+t : m ≡ L + t
        m≡L+t = begin
          m                                       ≡⟨ sym (showℕ-padded-length m r) ⟩
          length fracDigits                       ≡⟨ cong length fr-eq ⟩
          length (fr ++ₗ replicate t '0')         ≡⟨ length-++ fr ⟩
          L + length (replicate t '0')            ≡⟨ cong (λ z → L + z) (length-replicate t) ⟩
          L + t ∎
        r<10^m : r < 10 ^ m
        r<10^m = m%n<n scaledNum (10 ^ m)
        r≡pfr*10^t : r ≡ pfr * 10 ^ t
        r≡pfr*10^t = begin
          r                                       ≡⟨ sym (parseDigitList-showℕ-padded-chars m r r<10^m) ⟩
          parseDigitList fracDigits               ≡⟨ cong parseDigitList fr-eq ⟩
          parseDigitList (fr ++ₗ replicate t '0') ≡⟨ parseDigitList-append-zeros fr t ⟩
          pfr * 10 ^ t ∎
        divmod : scaledNum ≡ r + intPart-val * 10 ^ m
        divmod = m≡m%n+[m/n]*n scaledNum (10 ^ m)
        N : ℕ
        N = intPart-val * 10 ^ L + pfr
        N*10^t≡scaledNum : N * 10 ^ t ≡ scaledNum
        N*10^t≡scaledNum = begin
          N * 10 ^ t
            ≡⟨ *-distribʳ-+ (10 ^ t) (intPart-val * 10 ^ L) pfr ⟩
          intPart-val * 10 ^ L * 10 ^ t + pfr * 10 ^ t
            ≡⟨ cong (_+ pfr * 10 ^ t) (*-assoc intPart-val (10 ^ L) (10 ^ t)) ⟩
          intPart-val * (10 ^ L * 10 ^ t) + pfr * 10 ^ t
            ≡⟨ cong (λ k → intPart-val * k + pfr * 10 ^ t) (sym (^-distribˡ-+-* 10 L t)) ⟩
          intPart-val * 10 ^ (L + t) + pfr * 10 ^ t
            ≡⟨ cong (λ k → intPart-val * 10 ^ k + pfr * 10 ^ t) (sym m≡L+t) ⟩
          intPart-val * 10 ^ m + pfr * 10 ^ t
            ≡⟨ cong (λ z → intPart-val * 10 ^ m + z) (sym r≡pfr*10^t) ⟩
          intPart-val * 10 ^ m + r
            ≡⟨ +-comm (intPart-val * 10 ^ m) r ⟩
          r + intPart-val * 10 ^ m
            ≡⟨ sym divmod ⟩
          scaledNum ∎
        scaledNum*D≡absNum*10^m : scaledNum * D ≡ absNum * 10 ^ m
        scaledNum*D≡absNum*10^m = begin
          scaledNum * D
            ≡⟨ shuffle5 absNum (2 ^ (m ∸ₙ a)) (5 ^ (m ∸ₙ b)) (2 ^ a) (5 ^ b) ⟩
          absNum * ((2 ^ (m ∸ₙ a) * 2 ^ a) * (5 ^ (m ∸ₙ b) * 5 ^ b))
            ≡⟨ cong (λ k → absNum * (k * (5 ^ (m ∸ₙ b) * 5 ^ b))) (pow-split 2 m a a≤m) ⟩
          absNum * (2 ^ m * (5 ^ (m ∸ₙ b) * 5 ^ b))
            ≡⟨ cong (λ k → absNum * (2 ^ m * k)) (pow-split 5 m b b≤m) ⟩
          absNum * (2 ^ m * 5 ^ m)
            ≡⟨ cong (absNum *_) (sym (10^≡2^*5^ m)) ⟩
          absNum * 10 ^ m ∎
        left-eq : (N * D) * 10 ^ t ≡ absNum * 10 ^ m
        left-eq = begin
          (N * D) * 10 ^ t
            ≡⟨ shuffle3 N D (10 ^ t) ⟩
          (N * 10 ^ t) * D
            ≡⟨ cong (_* D) N*10^t≡scaledNum ⟩
          scaledNum * D
            ≡⟨ scaledNum*D≡absNum*10^m ⟩
          absNum * 10 ^ m ∎
        right-eq : (absNum * 10 ^ L) * 10 ^ t ≡ absNum * 10 ^ m
        right-eq = begin
          (absNum * 10 ^ L) * 10 ^ t
            ≡⟨ *-assoc absNum (10 ^ L) (10 ^ t) ⟩
          absNum * (10 ^ L * 10 ^ t)
            ≡⟨ cong (absNum *_) (sym (^-distribˡ-+-* 10 L t)) ⟩
          absNum * 10 ^ (L + t)
            ≡⟨ cong (λ k → absNum * 10 ^ k) (sym m≡L+t) ⟩
          absNum * 10 ^ m ∎
        decode-cross : N * D ≡ absNum * 10 ^ L
        decode-cross = *-cancelʳ-≡ (N * D) (absNum * 10 ^ L) (10 ^ t)
                         ⦃ m^n≢0 10 t ⦄ (trans left-eq (sym right-eq))
        decode-value : _/_ (+ N) (10 ^ L) ⦃ m^n≢0 10 L ⦄
                     ≡ _/_ (+ absNum) (2 ^ a * 5 ^ b) ⦃ 2^a·5^b-NonZero a b ⦄
        decode-value = /-fromℕ-cross N (10 ^ L) absNum (2 ^ a * 5 ^ b)
                         ⦃ m^n≢0 10 L ⦄ ⦃ 2^a·5^b-NonZero a b ⦄ decode-cross

------------------------------------------------------------------------
-- HEADLINE: the renderer is faithful — `formatℚ-chars q` denotes `q`.
------------------------------------------------------------------------

-- The string produced by `formatℚ-chars q`, read back under the
-- `Represents` standard-numeral semantics, denotes exactly `q`.  Mirrors
-- `formatℚ-chars`'s `with fromℚ? q | maxDecimalPlaces <ᵇ (a ⊔ b)` case tree:
--   • `nothing`        → fraction `↥q / ↧ₙq`, bridged to `q` by `↥p/↧p≡p`.
--   • `just _ | true`  → fraction `n / 2^a·5^b` (k>18 fallback).
--   • `just _ | false` → trimmed decimal of the same value.
-- The two `just` branches bridge to `q` via the `fromℚ?` soundness linchpin
-- (`toℚ-fromℚ?-sound`), composed with `↥p/↧p≡p` on the directly-built `toℚ`.
formatℚ-chars-represents : ∀ q → Represents (formatℚ-chars q) q
formatℚ-chars-represents q with fromℚ? q in fq-eq
... | nothing =
      subst (λ v → Represents (emitNbyD-chars (↥ q) (↧ₙ q)) v)
            (↥p/↧p≡p q)
            (emitNbyD-represents (↥ q) (↧ₙ q))
... | just (mkDecRat n a b c) with maxDecimalPlaces <ᵇ (a ⊔ b)
...   | true =
        subst (λ v → Represents (emitNbyD-chars n (2 ^ a * 5 ^ b)) v) nd≡q
              (emitNbyD-represents n (2 ^ a * 5 ^ b) ⦃ 2^a·5^b-NonZero a b ⦄)
        where
          nd≡q : _/_ n (2 ^ a * 5 ^ b) ⦃ 2^a·5^b-NonZero a b ⦄ ≡ q
          nd≡q = trans (sym (/-suc-pred n (2 ^ a * 5 ^ b) ⦃ 2^a·5^b-NonZero a b ⦄))
                       (trans (↥p/↧p≡p (toℚ (mkDecRat n a b c)))
                              (toℚ-fromℚ?-sound q (mkDecRat n a b c) fq-eq))
...   | false = helper n nd≡q
        where
          nd≡q : _/_ n (2 ^ a * 5 ^ b) ⦃ 2^a·5^b-NonZero a b ⦄ ≡ q
          nd≡q = trans (sym (/-suc-pred n (2 ^ a * 5 ^ b) ⦃ 2^a·5^b-NonZero a b ⦄))
                       (trans (↥p/↧p≡p (toℚ (mkDecRat n a b c)))
                              (toℚ-fromℚ?-sound q (mkDecRat n a b c) fq-eq))
          -- Split the (signed) numerator: `+ k` is a bare magnitude; `-[1+ k]`
          -- is a `rep-neg` wrap (`-[1+ k] / d ≡ - ((+ suc k) / d)` definitionally).
          helper : (num : ℤ) →
                   _/_ num (2 ^ a * 5 ^ b) ⦃ 2^a·5^b-NonZero a b ⦄ ≡ q →
                   Represents (emitDecimal-trimmed-chars num a b) q
          helper (+ k) eq =
            subst (λ v → Represents (emitMagnitude-trimmed-chars k a b) v) eq
                  (emitMagnitude-represents k a b)
          helper -[1+ k ] eq =
            subst (λ v → Represents ('-' ∷ emitMagnitude-trimmed-chars (suc k) a b) v) eq
                  (rep-neg (emitMagnitude-trimmed-chars (suc k) a b)
                           (_/_ (+ suc k) (2 ^ a * 5 ^ b) ⦃ 2^a·5^b-NonZero a b ⦄)
                           (emitMagnitude-represents (suc k) a b))

------------------------------------------------------------------------
-- SHAPE CANONICALITY: the renderer emits the UNIQUE canonical spelling.
------------------------------------------------------------------------
-- Faithfulness (above) pins the VALUE but not the spelling — `Represents`
-- accepts `2/6`, `0.50`, `1/2` for the same value.  These theorems pin the
-- SHAPE, so the per-binding golden examples are redundant:
--   • a value renders as the reduced FRACTION `↥q / ↧ₙq` exactly when it is
--     NOT a ≤ maxDecimalPlaces terminating decimal;
--   • otherwise it renders as that terminating decimal of `↥q`.
-- The branch is characterised purely by the `fromℚ?` soundness linchpin
-- (`just d → toℚ d ≡ q`) and roundtrip (`fromℚ? (toℚ d) ≡ just d`) — DecRat
-- values are canonical, so roundtrip returns the SAME `d`; no denominator
-- prime-factorisation or minimal-exponent reasoning is needed.

-- `q` is a terminating decimal of at most `maxDecimalPlaces` places.
BoundedDec : ℚ → Set
BoundedDec q =
  Σ[ d ∈ DecRat ] (toℚ d ≡ q × (DecRat.twoExp d ⊔ DecRat.fiveExp d) ≤ maxDecimalPlaces)

private
  just≢nothing : ∀ {d : DecRat} → just d ≢ nothing
  just≢nothing ()

  -- fromℚ? q recovers any DecRat that maps to q (roundtrip + soundness, with
  -- DecRat canonicity making the recovered value the SAME `d`).
  fromℚ?-of-value : ∀ q d → toℚ d ≡ q → fromℚ? q ≡ just d
  fromℚ?-of-value q d td≡q = trans (cong fromℚ? (sym td≡q)) (fromℚ?-after-toℚ d)

  -- fromℚ? q ≡ nothing ⟹ no DecRat maps to q (so q is not terminating).
  nothing→¬bounded : ∀ q → fromℚ? q ≡ nothing → ¬ BoundedDec q
  nothing→¬bounded q eq (d , td≡q , _) =
    just≢nothing (trans (sym (fromℚ?-of-value q d td≡q)) eq)

  -- fromℚ? q's canonical d over the bound ⟹ no ≤bound DecRat maps to q
  -- (roundtrip makes fromℚ?'s d the unique one).
  overbound→¬bounded : ∀ q d → fromℚ? q ≡ just d →
    maxDecimalPlaces < (DecRat.twoExp d ⊔ DecRat.fiveExp d) → ¬ BoundedDec q
  overbound→¬bounded q d eq over (d′ , td′≡q , le) =
    <⇒≱ over (subst (λ z → (DecRat.twoExp z ⊔ DecRat.fiveExp z) ≤ maxDecimalPlaces) d′≡d le)
    where
      d′≡d : d′ ≡ d
      d′≡d = just-injective (trans (sym (fromℚ?-of-value q d′ td′≡q)) eq)

  -- fromℚ? q's canonical d within the bound ⟹ q is a bounded terminating decimal.
  within→bounded : ∀ q d → fromℚ? q ≡ just d →
    (DecRat.twoExp d ⊔ DecRat.fiveExp d) ≤ maxDecimalPlaces → BoundedDec q
  within→bounded q d eq le = d , toℚ-fromℚ?-sound q d eq , le

-- A non-terminating (or over-bound) value renders as the REDUCED fraction
-- `↥q / ↧ₙq` — pins both the fraction branch AND lowest terms (ℚ's `↥`/`↧ₙ`
-- are coprime, so a regression emitting `2/6` for 1/3 would break this).
formatℚ-fraction-form : ∀ q → ¬ BoundedDec q →
  formatℚ-chars q ≡ emitNbyD-chars (↥ q) (↧ₙ q)
formatℚ-fraction-form q ¬bd with fromℚ? q in eq
... | nothing = refl
... | just d@(mkDecRat n a b c) with maxDecimalPlaces <ᵇ (a ⊔ b) in beq
...   | true  = cong₂ emitNbyD-chars n≡↥q den≡↧ₙq
        where
          td≡q : toℚ d ≡ q
          td≡q = toℚ-fromℚ?-sound q d eq
          n≡↥q : n ≡ ↥ q
          n≡↥q = trans (sym (↥-toℚ-canonical n a b c)) (cong (λ x → ↥ x) td≡q)
          den≡↧ₙq : 2 ^ a * 5 ^ b ≡ ↧ₙ q
          den≡↧ₙq = trans (sym (↧ₙ-toℚ-canonical n a b c)) (cong (λ x → ↧ₙ x) td≡q)
...   | false = ⊥-elim (¬bd (within→bounded q d eq
                  (≮⇒≥ (λ lt → subst T beq (<⇒<ᵇ lt)))))

-- A bounded terminating value renders as the trimmed decimal of `↥q` — pins
-- the decimal branch (its trailing-zero trimming is in `formatℚ-trimmed`).
formatℚ-decimal-form : ∀ q → BoundedDec q →
  Σ[ a ∈ ℕ ] Σ[ b ∈ ℕ ] (formatℚ-chars q ≡ emitDecimal-trimmed-chars (↥ q) a b)
formatℚ-decimal-form q bd with fromℚ? q in eq
... | nothing = ⊥-elim (nothing→¬bounded q eq bd)
... | just d@(mkDecRat n a b c) with maxDecimalPlaces <ᵇ (a ⊔ b) in beq
...   | true  = ⊥-elim (overbound→¬bounded q d eq
                  (<ᵇ⇒< maxDecimalPlaces (a ⊔ b) (subst T (sym beq) tt)) bd)
...   | false = a , b , cong (λ x → emitDecimal-trimmed-chars x a b) n≡↥q
        where
          n≡↥q : n ≡ ↥ q
          n≡↥q = trans (sym (↥-toℚ-canonical n a b c))
                       (cong (λ x → ↥ x) (toℚ-fromℚ?-sound q d eq))

------------------------------------------------------------------------
-- TRIMMED: decimal outputs carry no trailing zero (the cluster-Y shape).
------------------------------------------------------------------------
-- Faithfulness + the branch theorems above leave one shape freedom: a decimal
-- fractional part could carry a trailing `0` (`0.50` is value-faithful).  This
-- pins it shut: every decimal the renderer emits has a trimmed fractional part.

-- A character list whose first element is not '0' (vacuously true when empty).
HeadNotZero : List Char → Set
HeadNotZero []      = ⊤
HeadNotZero (c ∷ _) = c ≢ '0'

-- A list with no trailing '0' = its reverse has no leading '0'.
NoTrailingZeros : List Char → Set
NoTrailingZeros cs = HeadNotZero (reverse cs)

private
  -- `dropLeadingZeros` peels every leading '0', so its result starts non-'0'.
  drop-noleading : ∀ ys → HeadNotZero (dropLeadingZeros ys)
  drop-noleading []       = tt
  drop-noleading (c ∷ cs) with c ≟ᶜ '0'
  ... | yes _   = drop-noleading cs
  ... | no  c≢0 = c≢0

-- `trimTrailingZeros` (= reverse ∘ dropLeadingZeros ∘ reverse) leaves no
-- trailing '0' — the lemma a regression dropping the trim step would break.
trim-notrailing : ∀ cs → NoTrailingZeros (trimTrailingZeros cs)
trim-notrailing cs =
  subst HeadNotZero
        (sym (reverse-involutive (dropLeadingZeros (reverse cs))))
        (drop-noleading (reverse cs))

-- Shape of the magnitude emitter: either a bare integer digit run, or
-- `intPart "." frac` with the fractional part TRIMMED (no trailing '0').
-- Mirrors `emitMagnitude-trimmed-chars`'s `with a ⊔ b` and `joinIntFrac`'s
-- split, so a regression that stopped trimming the fractional part would fail
-- to discharge the `NoTrailingZeros` obligation here.
emitMagnitude-shape : ∀ absNum a b →
  (Σ[ ip ∈ List Char ]
     (emitMagnitude-trimmed-chars absNum a b ≡ ip × AllDigits ip))
  ⊎ (Σ[ ip ∈ List Char ] Σ[ fr ∈ List Char ]
       (emitMagnitude-trimmed-chars absNum a b ≡ ip ++ₗ '.' ∷ fr
        × AllDigits ip × NoTrailingZeros fr))
emitMagnitude-shape absNum a b with a ⊔ b
... | zero    = inj₁ (showNat-chars absNum , refl , showNat-AllDigits absNum)
... | suc m-1 =
        let m          = suc m-1
            instance
              scale-NonZero : NonZero (10 ^ m)
              scale-NonZero = m^n≢0 10 m
            scaledNum  = absNum * 2 ^ (m ∸ₙ a) * 5 ^ (m ∸ₙ b)
            intPart    = showNat-chars (scaledNum /ₙ 10 ^ m)
            fracDigits = showℕ-padded-chars m (scaledNum %ₙ 10 ^ m)
        in helper intPart fracDigits (trimTrailingZeros fracDigits)
                  (showNat-AllDigits (scaledNum /ₙ 10 ^ m)) refl
  where
    helper : ∀ ip fd fr → AllDigits ip → trimTrailingZeros fd ≡ fr →
      (Σ[ ip′ ∈ List Char ] (joinIntFrac ip fr ≡ ip′ × AllDigits ip′))
      ⊎ (Σ[ ip′ ∈ List Char ] Σ[ fr′ ∈ List Char ]
           (joinIntFrac ip fr ≡ ip′ ++ₗ '.' ∷ fr′ × AllDigits ip′ × NoTrailingZeros fr′))
    helper ip fd []       allip teq = inj₁ (ip , refl , allip)
    helper ip fd (c ∷ cs) allip teq =
      inj₂ (ip , c ∷ cs , refl , allip , subst NoTrailingZeros teq (trim-notrailing fd))
