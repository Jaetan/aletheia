-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Phase 1 of the `parseDecRat` roundtrip proof — digit-character
-- arithmetic and list-level lemmas.  Carved out of the historical
-- `Aletheia.DBC.TextParser.DecRatParse.Properties` mega-module when it
-- was split into submodules.
--
-- Self-contained: no parser machinery and no DecRat algebra needed.
-- Imports are the strict subset of the original module's import block
-- that this phase consumes.
--
-- Public surface preserved via re-export at
-- `DecRatParse.Properties.agda` so downstream consumers see no
-- name-resolution change.  Phase organisation:
--
--   * 1.1: Digit-character roundtrip (concrete 0..9 reductions).
--   * 1.2: Generic foldl snoc over any digit converter.
--   * 1.3: showNat-chars fuel bound.
--   * 1.4: foldl-f ∘ showNat-chars ≡ id (digit-converter-generic).
--   * 1.5: foldl-f ∘ showℕ-padded-chars ≡ id (under n < 10^w).
module Aletheia.DBC.TextParser.DecRatParse.Properties.Phase1Digits where

open import Data.Char using (Char)
open import Data.List using ([]; _∷_; foldl) renaming (_++_ to _++ₗ_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _/_; _%_; _^_;
         _<_; z≤n; s≤s)
open import Data.Nat.Properties
  using (*-comm; +-comm; +-identityʳ; ≤-<-trans; n<1+n; ^-monoʳ-<)
open import Data.Nat.DivMod
  using (m%n<n; m≡m%n+[m/n]*n; m<n*o⇒m/o<n)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; module ≡-Reasoning)

open import Aletheia.DBC.TextFormatter.Emitter
  using (digitChar; showNat-chars; showNat-chars-fuel; showℕ-padded-chars)
open import Aletheia.DBC.DecRat.Literal using (digitValue; foldDigits)

-- ============================================================================
-- Phase 1.1: Digit-character roundtrip (concrete 0..9 reductions)
-- ============================================================================

-- `digitValue ∘ digitChar ≡ id` on [0..9]: ten concrete reductions
-- through the built-in `primCharToNat '0'..'9' ≡ 48..57`.  The
-- catch-all absurd branch forces the `d < 10` precondition to do work
-- (without it the emitter's `digitChar d` for `d ≥ 10` would collapse
-- to `'0'` silently).
digitValue-digitChar : ∀ d → d < 10 → digitValue (digitChar d) ≡ d
digitValue-digitChar 0 _ = refl
digitValue-digitChar 1 _ = refl
digitValue-digitChar 2 _ = refl
digitValue-digitChar 3 _ = refl
digitValue-digitChar 4 _ = refl
digitValue-digitChar 5 _ = refl
digitValue-digitChar 6 _ = refl
digitValue-digitChar 7 _ = refl
digitValue-digitChar 8 _ = refl
digitValue-digitChar 9 _ = refl
digitValue-digitChar (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _))))))))))
  (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ()))))))))))

-- ============================================================================
-- Phase 1.2: Generic foldl snoc over any digit converter
-- ============================================================================

-- Inner helper: left-fold over `xs ++ [d]` from an arbitrary starting
-- accumulator `acc` equals the left-fold over `xs` from `acc`, then
-- one more step `* 10 + f d`.  `acc` must vary in the statement for
-- the induction step to type-check (the recursive call threads
-- `acc * 10 + f x` through).  Parameterised over the digit converter
-- `f : Char → ℕ`; `foldDigits` is the instance at `f = digitValue`.
-- Pure list-level fact independent of parsing.
foldl-digit-++-snoc : (f : Char → ℕ) → ∀ xs d (acc : ℕ) →
  foldl (λ a e → a * 10 + f e) acc (xs ++ₗ d ∷ []) ≡
  foldl (λ a e → a * 10 + f e) acc xs * 10 + f d
foldl-digit-++-snoc f []       d acc = refl
foldl-digit-++-snoc f (x ∷ xs) d acc =
  foldl-digit-++-snoc f xs d (acc * 10 + f x)

-- Specialisation to `foldDigits = foldl digitValue 0`.  Used by
-- the fractional-part roundtrip in `foldDigits-showℕ-padded-chars`.
foldDigits-++-snoc : ∀ xs d →
  foldDigits (xs ++ₗ d ∷ []) ≡ foldDigits xs * 10 + digitValue d
foldDigits-++-snoc xs d = foldl-digit-++-snoc digitValue xs d 0

-- ============================================================================
-- Phase 1.3: showNat-chars fuel bound
-- ============================================================================

-- `n < 10 ^ suc n` for every `n`.  Precondition needed to drive
-- `foldl-digit-showNat-chars-fuel` on `showNat-chars n =
-- showNat-chars-fuel (suc n) n`.  Loose bound — the actual digit
-- count of `n` is `⌊log₁₀ n⌋ + 1`, far less than `suc n` — but
-- `suc n` is easy to establish without `log`, and the fuel only
-- needs to be *enough*, not *tight*.
--
-- Induction on n:
--   * 0 < 10               (base; `s≤s z≤n`).
--   * suc n < 10^(suc (suc n)): chain IH `n < 10^(suc n)` (giving
--     `suc n ≤ 10^(suc n)`) with `10^(suc n) < 10^(suc (suc n))`
--     (from `^-monoʳ-<` at base `10 > 1` and `suc n < suc (suc n)`).
n<10^suc-n : ∀ n → n < 10 ^ suc n
n<10^suc-n zero    = s≤s z≤n
n<10^suc-n (suc n) =
  ≤-<-trans (n<10^suc-n n) (^-monoʳ-< 10 (s≤s (s≤s z≤n)) (n<1+n (suc n)))

-- `n / 10 < 10^w` given `n < 10^(suc w) = 10 * 10^w`.  Used by both
-- the fuel theorem below (recursive step) and
-- `foldl-digit-showℕ-padded-chars` (recursive step) to shrink the
-- fuel / width precondition to the IH's form.  Built on stdlib's
-- `m<n*o⇒m/o<n`; the `*-comm` is needed because the exponent
-- convention `10^(suc w) = 10 * 10^w` does not match the lemma's
-- `n * o` order directly (it wants `10^w * 10`).
n/10<10^w : ∀ w n → n < 10 ^ suc w → n / 10 < 10 ^ w
n/10<10^w w n n<10^[1+w] =
  m<n*o⇒m/o<n (subst (n <_) (*-comm 10 (10 ^ w)) n<10^[1+w])

-- ============================================================================
-- Phase 1.4: foldl-f ∘ showNat-chars ≡ id (digit-converter-generic)
-- ============================================================================

-- Fuel-parameterised roundtrip core over an arbitrary digit converter
-- `f : Char → ℕ` satisfying `f (digitChar d) ≡ d` for `d < 10`.
-- Induction on `fuel`:
--   * `fuel = 0`: `n < 10^0 = 1` forces `n ≡ 0`; `showNat-chars-fuel
--     0 _ = []` so `foldl f 0 [] = 0 = n`.
--   * `fuel = suc f'`: case-split on `n / 10 in eq`:
--     - `n / 10 = 0`: emitter writes `[digitChar (n % 10)]`.
--       `foldl f 0 [d] = 0 * 10 + f d = f d`.
--       `f (digitChar (n % 10)) ≡ n % 10` by `f-digitChar` (valid
--       since `n % 10 < 10`).  `n ≡ n % 10` because `n ≡ n % 10 +
--       (n / 10) * 10 ≡ n % 10 + 0 * 10 ≡ n % 10` (via
--       `m≡m%n+[m/n]*n` + `eq` + `+-identityʳ`).
--     - `n / 10 = suc m`: emitter writes `showNat-chars-fuel f' (suc
--       m) ++ [digitChar (n % 10)]`.  `foldl-digit-++-snoc` splits
--       off the last digit; IH applied at `f'` and `suc m` (with
--       bound `suc m < 10^f'` via `n/10<10^w` + `eq`) closes the
--       prefix; `m≡m%n+[m/n]*n` + `+-comm` + `eq` reassemble `n`.
foldl-digit-showNat-chars-fuel :
  (f : Char → ℕ) →
  (f-digitChar : ∀ d → d < 10 → f (digitChar d) ≡ d) →
  ∀ fuel n → n < 10 ^ fuel →
  foldl (λ a e → a * 10 + f e) 0 (showNat-chars-fuel fuel n) ≡ n
foldl-digit-showNat-chars-fuel _ _ zero    zero    _ = refl
foldl-digit-showNat-chars-fuel _ _ zero    (suc _) (s≤s ())
foldl-digit-showNat-chars-fuel f f-digitChar (suc f') n n<10^[1+f'] with n / 10 in eq
... | zero  = lemma-zero
  where
    open ≡-Reasoning
    -- `n ≡ n % 10` under `n / 10 ≡ 0`.  `zero * 10` reduces to `zero`
    -- definitionally; the final `+-identityʳ` strips the trailing `+ 0`.
    n≡n%10 : n ≡ n % 10
    n≡n%10 =
      trans (m≡m%n+[m/n]*n n 10)
            (trans (cong (λ k → n % 10 + k * 10) eq)
                   (+-identityʳ (n % 10)))
    lemma-zero : foldl (λ a e → a * 10 + f e) 0
                   (digitChar (n % 10) ∷ []) ≡ n
    lemma-zero =
      begin
        foldl (λ a e → a * 10 + f e) 0 (digitChar (n % 10) ∷ [])
          ≡⟨⟩
        f (digitChar (n % 10))
          ≡⟨ f-digitChar (n % 10) (m%n<n n 10) ⟩
        n % 10
          ≡⟨ sym n≡n%10 ⟩
        n
      ∎
... | suc m = lemma-suc
  where
    open ≡-Reasoning
    -- `suc m < 10^f'`: transport the generic `n / 10 < 10^f'` through `eq`.
    1+m<10^f' : suc m < 10 ^ f'
    1+m<10^f' = subst (_< 10 ^ f') eq (n/10<10^w f' n n<10^[1+f'])
    lemma-suc : foldl (λ a e → a * 10 + f e) 0
                  (showNat-chars-fuel f' (suc m) ++ₗ digitChar (n % 10) ∷ [])
                  ≡ n
    lemma-suc =
      begin
        foldl (λ a e → a * 10 + f e) 0
              (showNat-chars-fuel f' (suc m) ++ₗ digitChar (n % 10) ∷ [])
          ≡⟨ foldl-digit-++-snoc f (showNat-chars-fuel f' (suc m))
                                   (digitChar (n % 10)) 0 ⟩
        foldl (λ a e → a * 10 + f e) 0 (showNat-chars-fuel f' (suc m)) * 10
          + f (digitChar (n % 10))
          ≡⟨ cong (λ k → k * 10 + f (digitChar (n % 10)))
                  (foldl-digit-showNat-chars-fuel f f-digitChar f' (suc m)
                     1+m<10^f') ⟩
        suc m * 10 + f (digitChar (n % 10))
          ≡⟨ cong ((suc m * 10) +_) (f-digitChar (n % 10) (m%n<n n 10)) ⟩
        suc m * 10 + n % 10
          ≡⟨ sym (cong (λ k → k * 10 + n % 10) eq) ⟩
        n / 10 * 10 + n % 10
          ≡⟨ +-comm (n / 10 * 10) (n % 10) ⟩
        n % 10 + n / 10 * 10
          ≡⟨ sym (m≡m%n+[m/n]*n n 10) ⟩
        n
      ∎

-- Specialisations: pin `f` to each concrete digit converter.

-- `foldDigits ∘ showNat-chars ≡ id`: the integer part of every
-- emitted number reads back to itself.
foldDigits-showNat-chars : ∀ n → foldDigits (showNat-chars n) ≡ n
foldDigits-showNat-chars n =
  foldl-digit-showNat-chars-fuel digitValue digitValue-digitChar
    (suc n) n (n<10^suc-n n)

-- ============================================================================
-- Phase 1.5: foldl-f ∘ showℕ-padded-chars ≡ id (under n < 10^w)
-- ============================================================================

-- Width-bounded roundtrip for the fractional-digit emitter, generic
-- over the digit converter `f`.  Unlike `showNat-chars`,
-- `showℕ-padded-chars` is structurally recursive on `width` (not on a
-- separate `fuel` argument), so we induct on `width` directly.  The
-- precondition `n < 10^w` is exactly the statement that `n` fits in
-- `w` base-10 digits; the Shape B emitter enforces it at every call
-- site via `n = scaledNum % 10^m`.
--
-- The suc-case reasoning mirrors the `suc m` case of the fuel
-- theorem above (same snoc + IH + `m≡m%n+[m/n]*n` rearrangement).
foldl-digit-showℕ-padded-chars :
  (f : Char → ℕ) →
  (f-digitChar : ∀ d → d < 10 → f (digitChar d) ≡ d) →
  ∀ w n → n < 10 ^ w →
  foldl (λ a e → a * 10 + f e) 0 (showℕ-padded-chars w n) ≡ n
foldl-digit-showℕ-padded-chars _ _ zero    zero    _ = refl
foldl-digit-showℕ-padded-chars _ _ zero    (suc _) (s≤s ())
foldl-digit-showℕ-padded-chars f f-digitChar (suc w) n n<10^[1+w] =
  begin
    foldl (λ a e → a * 10 + f e) 0
          (showℕ-padded-chars w (n / 10) ++ₗ digitChar (n % 10) ∷ [])
      ≡⟨ foldl-digit-++-snoc f (showℕ-padded-chars w (n / 10))
                               (digitChar (n % 10)) 0 ⟩
    foldl (λ a e → a * 10 + f e) 0 (showℕ-padded-chars w (n / 10)) * 10
      + f (digitChar (n % 10))
      ≡⟨ cong (λ k → k * 10 + f (digitChar (n % 10)))
              (foldl-digit-showℕ-padded-chars f f-digitChar w (n / 10)
                 (n/10<10^w w n n<10^[1+w])) ⟩
    n / 10 * 10 + f (digitChar (n % 10))
      ≡⟨ cong ((n / 10 * 10) +_) (f-digitChar (n % 10) (m%n<n n 10)) ⟩
    n / 10 * 10 + n % 10
      ≡⟨ +-comm (n / 10 * 10) (n % 10) ⟩
    n % 10 + n / 10 * 10
      ≡⟨ sym (m≡m%n+[m/n]*n n 10) ⟩
    n
  ∎
  where open ≡-Reasoning

-- Specialisation used by the fractional-part roundtrip: the
-- fractional digits are emitted by `showℕ-padded-chars m (scaledNum %
-- 10^m)` and read back by `foldDigits`.
foldDigits-showℕ-padded-chars : ∀ w n → n < 10 ^ w →
  foldDigits (showℕ-padded-chars w n) ≡ n
foldDigits-showℕ-padded-chars =
  foldl-digit-showℕ-padded-chars digitValue digitValue-digitChar
