-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- ℚ → DecRat soundness: `fromℚ? q ≡ just d → toℚ d ≡ q`.
--
-- Dual to `RationalRoundtrip.agda`'s `fromℚ? (toℚ d) ≡ just d`.  Where that
-- module shows every DecRat survives a round-trip THROUGH ℚ, this module shows
-- the partial inverse is FAITHFUL: whenever `fromℚ?` accepts a rational, the
-- DecRat it returns names the very same ℚ.
--
-- Linchpin for the rational-renderer faithfulness track: the renderer's decimal
-- branch dispatches on `fromℚ? q | just (mkDecRat n a b _)`, so its decimal
-- output represents `q` only if that DecRat does.
--
-- Structure:
--   Layer 1 — `stripFactor-fuel-value` : the forward value invariant
--             `n ≡ p ^ e * r` for `(e , r) = stripFactor-fuel _ p n`.  (The
--             roundtrip module proved the reverse direction, `stripFactor-peel`.)
--   Layer 2 — `↥-toℚ` / `↧-toℚ` : project `toℚ d`'s ℚ-numerator/denominator
--             (`toℚ` η-reduces because `DecRat` is a record).
--   Layer 3 — `toℚ-fromℚ?-sound` : mirror `fromℚ?-raw`'s three `with`s, use the
--             value invariant to recover `↧ₙ q = 2^a · 5^b`, and discharge the
--             ℚ cross-multiplication with the existing `canonicalize-value-ℚᵘ`.
module Aletheia.DBC.DecRat.RationalSoundness where

open import Data.Nat.Base
  using (ℕ; zero; suc; _*_; _^_; _∸_; NonZero)
  renaming (_/_ to _/ₙ_; _%_ to _%ₙ_)
open import Data.Nat.Properties
  using (*-identityˡ; *-identityʳ; *-assoc; *-comm)
  renaming (_≟_ to _≟ₙ_)
open import Data.Nat.DivMod using (m/n*n≡m)
open import Data.Nat.Divisibility using (m%n≡0⇒n∣m)
open import Data.Integer.Base using (ℤ; +_; ∣_∣; sign; _◃_)
import Data.Integer.Base as ℤ
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Rational.Base using (ℚ; mkℚ; *≡*; ↥_; ↧_)
open import Data.Rational.Properties using (≃⇒≡)
import Data.Rational.Unnormalised.Base as ℚᵘ
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; module ≡-Reasoning)
open import Relation.Nullary using (yes; no)
open import Function.Base using (_∋_)

open import Aletheia.DBC.DecRat using
  (DecRat; mkDecRat; toℚ; fromℚ?;
   canonicalize; canonicalizeDecRat; canonicalize-value-ℚᵘ;
   stripFactor-fuel; 2^a·5^b-NonZero)

------------------------------------------------------------------------
-- Local helper
------------------------------------------------------------------------

-- `suc (n ∸ 1) ≡ n` for NonZero n.  (RationalRoundtrip states the mirror
-- `2^a*5^b≡suc`; re-derived locally to keep this module self-contained.)
sucpred : (n : ℕ) .{{_ : NonZero n}} → suc (n ∸ 1) ≡ n
sucpred (suc _) = refl

------------------------------------------------------------------------
-- Layer 1 — forward value invariant of `stripFactor-fuel`
------------------------------------------------------------------------

-- `stripFactor-fuel fuel p n` returns `(e , r)` with `n ≡ p ^ e * r`.
-- Holds unconditionally (any fuel, any n): every early-stop branch returns
-- `(0 , n)` and `n ≡ p ^ 0 * n`; the recursive branch peels one `p`,
-- reconstructed via `p ∣ n`.  Mirrors the function's three `with`s so the
-- LHS reduces in lockstep.
stripFactor-fuel-value :
  ∀ fuel p n .{{_ : NonZero p}} →
    n ≡ p ^ proj₁ (stripFactor-fuel fuel p n)
          * proj₂ (stripFactor-fuel fuel p n)
stripFactor-fuel-value zero    p n = sym (*-identityˡ n)
stripFactor-fuel-value (suc f) p n with n %ₙ p ≟ₙ 0
... | no  _      = sym (*-identityˡ n)
... | yes n%p≡0 with n /ₙ p in q-eq
...   | zero    = sym (*-identityˡ n)
...   | suc q-1 = sym (begin
        p ^ suc (proj₁ er) * proj₂ er
          ≡⟨ *-assoc p (p ^ proj₁ er) (proj₂ er) ⟩
        p * (p ^ proj₁ er * proj₂ er)
          ≡⟨ cong (p *_) (sym ih) ⟩
        p * suc q-1
          ≡⟨ cong (p *_) (sym q-eq) ⟩
        p * (n /ₙ p)
          ≡⟨ recon ⟩
        n ∎)
  where
    open ≡-Reasoning
    er = stripFactor-fuel f p (suc q-1)
    ih : suc q-1 ≡ p ^ proj₁ er * proj₂ er
    ih = stripFactor-fuel-value f p (suc q-1)
    recon : p * (n /ₙ p) ≡ n
    recon = trans (*-comm p (n /ₙ p)) (m/n*n≡m (m%n≡0⇒n∣m n p n%p≡0))

------------------------------------------------------------------------
-- Layer 2 — `toℚ d`'s ℚ-numerator / ℚ-denominator
------------------------------------------------------------------------
--
-- `DecRat` is a record, so `toℚ d = mkℚ (DecRat.numerator d) (…) (…)`
-- η-reduces for any `d`.  For `d = canonicalizeDecRat num a b` the fields
-- reduce (product-η on the inner `with`) to `canonicalize num a b`'s
-- projections, so the two helpers below hold by `refl` / one `sucpred`.

↥-toℚ-cDR :
  ∀ num a b →
    ↥ (toℚ (canonicalizeDecRat num a b)) ≡ proj₁ (canonicalize num a b)
↥-toℚ-cDR num a b = refl

↧-toℚ-cDR :
  ∀ num a b →
    ↧ (toℚ (canonicalizeDecRat num a b))
      ≡ + (2 ^ proj₁ (proj₂ (canonicalize num a b))
            * 5 ^ proj₂ (proj₂ (canonicalize num a b)))
↧-toℚ-cDR num a b =
  cong +_ (sucpred (2 ^ proj₁ (proj₂ (canonicalize num a b))
                     * 5 ^ proj₂ (proj₂ (canonicalize num a b)))
                   ⦃ 2^a·5^b-NonZero (proj₁ (proj₂ (canonicalize num a b)))
                                     (proj₂ (proj₂ (canonicalize num a b))) ⦄)

------------------------------------------------------------------------
-- Layer 3 — soundness
------------------------------------------------------------------------

toℚ-fromℚ?-sound : ∀ q d → fromℚ? q ≡ just d → toℚ d ≡ q
toℚ-fromℚ?-sound (mkℚ num den-1 cop) d eq
  with stripFactor-fuel (suc (suc den-1)) 2 (suc den-1) in s2
... | (a , after2)
  with stripFactor-fuel (suc (suc den-1)) 5 after2 in s5
... | (b , after5)
  with after5 ≟ₙ 1
... | no  _ = nothing≢just eq
  where
    nothing≢just : ∀ {A B : Set} {x : A} → (Maybe A ∋ nothing) ≡ just x → B
    nothing≢just ()
... | yes a5≡1 =
      trans (cong toℚ (sym (just-injective eq))) (≃⇒≡ (*≡* crossmult))
  where
    open ≡-Reasoning

    -- Recover the denominator: it was fully factored into 2^a · 5^b.
    val2 : suc den-1 ≡ 2 ^ a * after2
    val2 = trans (stripFactor-fuel-value (suc (suc den-1)) 2 (suc den-1))
                 (cong (λ pr → 2 ^ proj₁ pr * proj₂ pr) s2)

    val5 : after2 ≡ 5 ^ b
    val5 = trans (stripFactor-fuel-value (suc (suc den-1)) 5 after2)
                 (trans (cong (λ pr → 5 ^ proj₁ pr * proj₂ pr) s5)
                        (trans (cong (5 ^ b *_) a5≡1) (*-identityʳ (5 ^ b))))

    dene : suc den-1 ≡ 2 ^ a * 5 ^ b
    dene = trans val2 (cong (2 ^ a *_) val5)

    -- The cross-multiplication witnessing canonicalize is value-preserving.
    eqᵘ-raw :
      num ℤ.* (+ suc (2 ^ proj₁ (proj₂ (canonicalize num a b))
                       * 5 ^ proj₂ (proj₂ (canonicalize num a b)) ∸ 1))
      ≡ proj₁ (canonicalize num a b) ℤ.* (+ suc (2 ^ a * 5 ^ b ∸ 1))
    eqᵘ-raw with canonicalize-value-ℚᵘ num a b
    ... | ℚᵘ.*≡* e = e

    eqᵘ' :
      num ℤ.* (+ (2 ^ proj₁ (proj₂ (canonicalize num a b))
                   * 5 ^ proj₂ (proj₂ (canonicalize num a b))))
      ≡ proj₁ (canonicalize num a b) ℤ.* (+ (2 ^ a * 5 ^ b))
    eqᵘ' =
      trans (cong (λ z → num ℤ.* (+ z))
                  (sym (sucpred (2 ^ proj₁ (proj₂ (canonicalize num a b))
                                  * 5 ^ proj₂ (proj₂ (canonicalize num a b)))
                                ⦃ 2^a·5^b-NonZero (proj₁ (proj₂ (canonicalize num a b)))
                                                  (proj₂ (proj₂ (canonicalize num a b))) ⦄)))
            (trans eqᵘ-raw
                   (cong (λ z → proj₁ (canonicalize num a b) ℤ.* (+ z))
                         (sucpred (2 ^ a * 5 ^ b) ⦃ 2^a·5^b-NonZero a b ⦄)))

    crossmult :
      ↥ (toℚ (canonicalizeDecRat num a b)) ℤ.* (+ suc den-1)
      ≡ num ℤ.* ↧ (toℚ (canonicalizeDecRat num a b))
    crossmult = begin
      ↥ (toℚ (canonicalizeDecRat num a b)) ℤ.* (+ suc den-1)
        ≡⟨ cong (λ z → ↥ (toℚ (canonicalizeDecRat num a b)) ℤ.* (+ z)) dene ⟩
      ↥ (toℚ (canonicalizeDecRat num a b)) ℤ.* (+ (2 ^ a * 5 ^ b))
        ≡⟨ cong (ℤ._* (+ (2 ^ a * 5 ^ b))) (↥-toℚ-cDR num a b) ⟩
      proj₁ (canonicalize num a b) ℤ.* (+ (2 ^ a * 5 ^ b))
        ≡⟨ sym eqᵘ' ⟩
      num ℤ.* (+ (2 ^ proj₁ (proj₂ (canonicalize num a b))
                   * 5 ^ proj₂ (proj₂ (canonicalize num a b))))
        ≡⟨ cong (num ℤ.*_) (sym (↧-toℚ-cDR num a b)) ⟩
      num ℤ.* ↧ (toℚ (canonicalizeDecRat num a b))
      ∎
