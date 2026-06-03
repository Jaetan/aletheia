-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Cross-binding-identical Rational pretty-printer (R20 cluster Y stage 2).
--
-- Replaces three independent per-binding implementations (Python
-- `_format_rational`, Go `formatRational`, C++ `format_value(const
-- Rational&)`) with a single Agda kernel function exported via the
-- Haskell shim.  The bindings call `aletheia_format_rational` and pass
-- the resulting CString through.
--
-- Public surface:
--
--   `formatℚ : ℚ → String`
--     Cross-binding-identical pretty-printer.  For ℚ values whose
--     canonical denominator divides a power of 10 (terminating in
--     decimal) AND requires `≤ 18` decimal places, emits the exact
--     decimal expansion with trailing zeros trimmed and the decimal
--     point dropped when the fractional part is empty (`Rational 1 2`
--     → `"0.5"`, `Rational 42 1` → `"42"`, `Rational 0 5` → `"0"`).
--     Otherwise emits `"<numerator>/<denominator>"` in lowest terms
--     (`Rational 1 3` → `"1/3"`, `Rational 1 524288` → `"1/524288"`).
--
--   `formatRational : ℤ → ℕ → String`
--     FFI-callable wrapper.  Defensive on `denom = 0` (returns
--     `"0"`).  Otherwise constructs a canonical ℚ via stdlib `_/_`
--     and dispatches to `formatℚ`.  Cross-binding parity follows
--     trivially: `(k * num) / (k * denom) ≡ num / denom` as ℚ, so
--     `formatRational (k * n) (k * d) ≡ formatRational n d`.
--
-- Algorithm (cross-binding identical):
--
--   1. Construct canonical ℚ q from raw (num, denom).
--   2. Try ℚ → DecRat decomposition (denom = 2^a × 5^b).  Reuses
--      `Aletheia.DBC.DecRat.fromℚ?`.
--   3. If decomposition fails OR `max(a, b) > 18`, emit reduced
--      `numerator/denominator` literal.
--   4. Otherwise compute exact decimal expansion via integer
--      arithmetic (scale numerator by `2^(m-a) · 5^(m-b)` where
--      `m = max(a, b)`, divide by `10^m`).  Trim trailing zeros from
--      the fractional part; drop the decimal point when fractional
--      is empty.
--
-- The cluster-Y output convention (`"42"` not `"42.0"`, `"0"` not
-- `"0.0"`) intentionally diverges from `Aletheia.DBC.TextFormatter.
-- Emitter.showDecRat-dec-chars`'s "Shape B" — which is fine because
-- the renderer here is for human-readable predicate display, not the
-- DBC text-format roundtrip.
module Aletheia.DBC.RationalRenderer where

open import Data.Bool using (true; false)
open import Data.Char using (Char) renaming (_≟_ to _≟ᶜ_)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (List; []; _∷_; reverse) renaming (_++_ to _++ₗ_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _⊔_; _<ᵇ_; _∸_; _*_; _^_; NonZero)
  renaming (_/_ to _/ₙ_; _%_ to _%ₙ_)
open import Data.Nat.Properties using (m^n≢0)
open import Data.Rational.Base using (ℚ; _/_)
import Data.Rational.Base as ℚ
open import Data.String using (String; fromList)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Aletheia.DBC.DecRat using
  (DecRat; mkDecRat; fromℚ?)
open import Aletheia.DBC.TextFormatter.Emitter using
  (showNat-chars; showInt-chars; showℕ-padded-chars)

-- ============================================================================
-- THRESHOLD
-- ============================================================================

-- Pathological terminating Rationals where `max(twoExp, fiveExp) > 18`
-- fall back to N/D for cross-binding parity.  Go and C++ would otherwise
-- risk int64 multiplier overflow at `2^k · 5^k = 10^k`; Python uses
-- arbitrary-precision ints but applies the same fallback so the three
-- bindings produce byte-identical output.  Typical DBC predicate values
-- stay well under k=10.
maxDecimalPlaces : ℕ
maxDecimalPlaces = 18

-- ============================================================================
-- TRIM TRAILING ZEROS — cluster-Y convention
-- ============================================================================

-- Drop leading characters equal to '0' from a list.  Used on the
-- reverse of the fractional digits to peel trailing zeros.
private
  dropLeadingZeros : List Char → List Char
  dropLeadingZeros []       = []
  dropLeadingZeros (c ∷ cs) with ⌊ c ≟ᶜ '0' ⌋
  ... | true  = dropLeadingZeros cs
  ... | false = c ∷ cs

-- Trim trailing '0' characters.  Implemented via two `reverse`s rather
-- than direct end-walking because `reverse` is structural and stdlib
-- `dropWhile` does not give a clean Decidable instance on Char.
trimTrailingZeros : List Char → List Char
trimTrailingZeros cs = reverse (dropLeadingZeros (reverse cs))

-- ============================================================================
-- DECIMAL MAGNITUDE EMITTER (cluster-Y convention, no mandatory ".0")
-- ============================================================================

-- Append "." + fractional digits to the integer part — but only when the
-- fractional list is non-empty (after trimming).  `Rational 42 1` → "42"
-- (no decimal point); `Rational 1 2` → "0.5".
private
  joinIntFrac : List Char → List Char → List Char
  joinIntFrac intPart []       = intPart
  joinIntFrac intPart (c ∷ cs) = intPart ++ₗ ('.' ∷ c ∷ cs)

-- Emit `absNum / (2^a · 5^b)` as a decimal `List Char` in cluster-Y
-- shape.  When `a = b = 0` the value is integer; otherwise scale into a
-- digit stream of length `m+1` where `m = max(a, b)`, split at the
-- decimal point, and trim trailing zeros.
emitMagnitude-trimmed-chars : (absNum a b : ℕ) → List Char
emitMagnitude-trimmed-chars absNum a b with a ⊔ b
... | zero      = showNat-chars absNum
... | suc m-1 =
        let m         = suc m-1
            instance
              scale-NonZero : NonZero (10 ^ m)
              scale-NonZero = m^n≢0 10 m
            scaledNum  = absNum * 2 ^ (m ∸ a) * 5 ^ (m ∸ b)
            scale      = 10 ^ m
            intPart    = showNat-chars (scaledNum /ₙ scale)
            fracDigits = showℕ-padded-chars m (scaledNum %ₙ scale)
        in joinIntFrac intPart (trimTrailingZeros fracDigits)

-- Sign-prefix wrapper (mirrors `showInt-chars` shape for the magnitude
-- emitter).
emitDecimal-trimmed-chars : (num : ℤ) (a b : ℕ) → List Char
emitDecimal-trimmed-chars (+ n)        a b = emitMagnitude-trimmed-chars n a b
emitDecimal-trimmed-chars -[1+ n ]     a b = '-' ∷ emitMagnitude-trimmed-chars (suc n) a b

-- ============================================================================
-- N/D LITERAL EMITTER (non-terminating fallback OR k > 18 fallback)
-- ============================================================================

-- Build "<num>/<denom>" as a `List Char`.  Numerator is signed; the
-- denominator is `ℕ` and always positive.  No sign prefix on the
-- denominator side ("/<denom>" never starts with '-').
emitNbyD-chars : (num : ℤ) (denom : ℕ) → List Char
emitNbyD-chars num denom =
  showInt-chars num ++ₗ ('/' ∷ showNat-chars denom)

-- Compute `2^a · 5^b` as the denominator for the k > 18 N/D fallback
-- (the DecRat carries `(twoExp, fiveExp)` rather than the denominator
-- directly).
private
  decRatDenom : (a b : ℕ) → ℕ
  decRatDenom a b = 2 ^ a * 5 ^ b

-- ============================================================================
-- PUBLIC API
-- ============================================================================

-- Render a canonical ℚ.  Cross-binding parity is automatic: equal ℚ
-- inputs produce equal outputs (function extensionality).
formatℚ-chars : ℚ → List Char
formatℚ-chars q with fromℚ? q
formatℚ-chars q | nothing  =
  -- Non-terminating: emit reduced "<num>/<denom>" using ℚ's canonical
  -- numerator and denominator (ℚ is in lowest terms by construction).
  emitNbyD-chars (ℚ.numerator q) (suc (ℚ.denominator-1 q))
formatℚ-chars q | just (mkDecRat n a b _) with maxDecimalPlaces <ᵇ (a ⊔ b)
... | true  = emitNbyD-chars n (decRatDenom a b)
... | false = emitDecimal-trimmed-chars n a b

formatℚ : ℚ → String
formatℚ q = fromList (formatℚ-chars q)

-- FFI-callable wrapper.  Defensive on `denom = 0` (returns `"0"`,
-- which is the same defensive value the bindings used pre-Stage-2 on
-- invalid input).  Otherwise constructs canonical ℚ via stdlib `_/_`
-- and dispatches to `formatℚ`.
--
-- Canonical-output property (proof obligation discharged by stdlib `_/_`
-- normalisation + function extensionality on ℚ):
--   `∀ k → 0 < k → formatRational (+ k * num) (k * denom)`
--      `≡ formatRational num denom`
formatRational : ℤ → ℕ → String
formatRational _   zero        = fromList ('0' ∷ [])
formatRational num (suc d-1) = formatℚ (num / suc d-1)
