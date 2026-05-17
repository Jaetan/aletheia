{-# OPTIONS --safe --without-K #-}

-- Correctness properties for `Aletheia.DBC.RationalRenderer`.
--
-- The cluster-Y stage-2 design moves the renderer into the Agda kernel
-- so that all three bindings (Python, Go, C++) share a single
-- implementation through the FFI.  This module proves the property
-- that justifies the architectural choice:
--
--   formatRational-canonical:
--     For any two `(numerator, denominator)` pairs that name the same
--     rational value (i.e. produce the same canonical ℚ via stdlib
--     `_/_`), `formatRational` produces byte-identical strings.
--
-- This makes cross-binding parity an architectural invariant rather
-- than a test convention — bindings cannot construct two ℚs that
-- name the same value yet render differently.  The proof reduces to
-- `cong formatℚ` because the public wrapper is `formatRational n d
-- = formatℚ (n / d)` and `_/_` already normalises.
--
-- Bound on the canonical-output property: it holds when both
-- denominators are non-zero.  The defensive `denom = 0` case returns
-- the constant `"0"` and trivially agrees with itself, so the only
-- pair the property excludes is the asymmetric `(d₁ = 0, d₂ > 0)`
-- case where one side is the defensive sentinel and the other a
-- decimal expansion.  Bindings never reach the `denom = 0` branch
-- in production code (Python `Fraction` rejects it on construction;
-- Go/C++ `Rational{n, 0}` is a programmer error).
module Aletheia.DBC.RationalRenderer.Properties where

open import Data.Integer.Base using (ℤ)
open import Data.Nat.Base using (ℕ; zero; suc; NonZero)
open import Data.Rational.Base using (ℚ; _/_)
open import Data.String.Base using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Aletheia.DBC.RationalRenderer using (formatRational; formatℚ)

------------------------------------------------------------------------
-- CROSS-BINDING UNIFORMITY: the renderer is a function on ℚ
------------------------------------------------------------------------

-- Trivial congruence on `formatℚ`.  Stated explicitly so downstream
-- proofs can `import` it without re-deriving.
formatℚ-cong :
  {q₁ q₂ : ℚ} → q₁ ≡ q₂ → formatℚ q₁ ≡ formatℚ q₂
formatℚ-cong = cong formatℚ

------------------------------------------------------------------------
-- CANONICAL-OUTPUT THEOREM
------------------------------------------------------------------------

-- Two `(numerator, denominator)` pairs that produce the same canonical
-- ℚ via stdlib `_/_` produce byte-identical renderer outputs.
--
-- Practical reading: a binding can hold an unreduced Rational like
-- `{4, 8}` and still get the same string as a Python `Fraction(1, 2)`
-- — they construct identical canonical ℚ inside the kernel before
-- the renderer ever runs.
formatRational-canonical :
  ∀ n₁ n₂ d₁ d₂ .{{nz₁ : NonZero d₁}} .{{nz₂ : NonZero d₂}} →
  (n₁ / d₁) ≡ (n₂ / d₂) →
  formatRational n₁ d₁ ≡ formatRational n₂ d₂
formatRational-canonical n₁ n₂ (suc _) (suc _) eq = cong formatℚ eq
