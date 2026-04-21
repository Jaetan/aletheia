{-# OPTIONS --safe --without-K #-}

-- Lexical emitters for the DBC text format (Phase B.3.c.1 — companion to
-- `Aletheia.DBC.TextParser.Lexer`).
--
-- Purpose: Centralise the per-terminal canonical emission choices so every
-- higher-level emitter in B.3.c.2+ produces the same lexical image.
--
-- Canonical emission policy:
--   * `showℕ-dec` / `showℤ-dec` — plain decimal digits via `Data.Nat.Show` /
--     `Data.Integer.Show` (aliased with a `-dec` suffix as the naming anchor
--     for future hex/binary variants, e.g. signal-overlap hex traces).
--   * `quoteStringLit` — wrap in `"..."` with CSV-style `""` escape on inner
--     quotes (mirrors `Lexer.parseStringLit` exactly; NOT JSON backslash).
--   * `showℚ-dec` — canonical `n.d` decimal emission.  Stdlib
--     `Data.Rational.Show.show` emits `p/q` fraction form, which is not
--     DBC-grammar syntax; the SG_ `factor`/`offset`/`minimum`/`maximum`
--     columns and the BA_ `FLOAT` / `AVFloat` payloads demand plain decimal.
--     Implementation: long division with a 15-fractional-digit cap.
--     Terminating-decimal rationals (reduced `p/q` where `q = 2^a · 5^b`
--     with `a + b ≤ 15`) roundtrip exactly; non-terminating ones truncate,
--     and the B.3.d roundtrip proof is conditioned on the terminating
--     class.  Every corpus-observed factor/offset (cantools emits from
--     Python `decimal`/`float`) falls in that class.
module Aletheia.DBC.TextFormatter.Emitter where

open import Data.Bool using (if_then_else_)
open import Data.Char using (Char) renaming (_≟_ to _≟ᶜ_)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (foldr)
open import Data.Nat using (ℕ; zero; suc; _*_; _/_; _%_)
open import Data.Rational as Rat using (ℚ)
open import Data.Rational.Unnormalised as ℚᵘ using (mkℚᵘ)
open import Data.String using (String; toList; fromChar) renaming (_++_ to _++ₛ_)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Data.Integer.Show using () renaming (show to showℤ)
open import Data.Nat.Show using () renaming (show to showℕ)

-- ============================================================================
-- NUMERIC EMITTERS
-- ============================================================================

showℕ-dec : ℕ → String
showℕ-dec = showℕ

showℤ-dec : ℤ → String
showℤ-dec = showℤ

-- ============================================================================
-- STRING LITERALS
-- ============================================================================

-- Emit a DBC-escaped inner character (quotes doubled, everything else pass-
-- through).  `fromChar` returns the one-character String needed by `++ₛ`.
escapeChar : Char → String
escapeChar c = if ⌊ c ≟ᶜ '"' ⌋ then "\"\"" else fromChar c

-- Wrap a string in `"..."` and escape inner quotes per CSV-style DBC escape.
-- Matches `Lexer.parseStringLit` exactly so roundtrip proofs in B.3.d compose
-- cleanly.
quoteStringLit : String → String
quoteStringLit s = "\"" ++ₛ foldr (λ c acc → escapeChar c ++ₛ acc) "\"" (toList s)

-- ============================================================================
-- RATIONAL NUMBERS (decimal)
-- ============================================================================

private
  -- Long-division helper: emit up to `fuel` decimal digits of `r / (suc
  -- denom-1)`.  Passing `denom-1 : ℕ` raw (instead of reconstructing the
  -- NonZero denominator internally) keeps the `NonZero (suc _)` instance
  -- visible at every recursive call without plumbing evidence.  Returns
  -- "" once fuel hits zero or the remainder drops to zero — the latter
  -- is the terminating-decimal exit.
  fracDigits : (fuel r denom-1 : ℕ) → String
  fracDigits zero       _         _       = ""
  fracDigits (suc _)    zero      _       = ""
  fracDigits (suc fuel) (suc r-1) denom-1 =
    let r10 = (suc r-1) * 10
    in showℕ (r10 / suc denom-1) ++ₛ
       fracDigits fuel (r10 % suc denom-1) denom-1

-- Canonical `n.d` decimal emission for ℚ (see module-header rationale).
-- Three cases mirror the three reachable shapes of `toℚᵘ r`.  The stored
-- ℚᵘ field is already `denominator-1` (i.e. `ℚᵘ.denominator-1 = d - 1`);
-- pattern-matching against `(suc d-2)` binds `d-2 = d - 2`, so the actual
-- denominator is `suc (suc d-2)` and the `fracDigits` third argument —
-- which itself takes a d-1 encoding — is `suc d-2`.  (Historical note:
-- an earlier revision matched `(suc d-1)` and used `suc d-1` as the
-- denominator; that was off-by-one — it divided/mod-ed by `d - 1`
-- instead of `d`, so e.g. `157/50` emitted as the 15-digit truncation
-- of `157/49` = `"3.204081632653061"` instead of `"3.14"`.)
--   * denom-1 = 0  (integer) — delegate to `showℤ`, which already handles
--     sign.  `ℚ` coprimality guarantees the stored denominator-1 is 0
--     exactly when the value is an integer.
--   * positive non-integer — `intPart "." fracDigits`.
--   * negative non-integer — `"-" intPart "." fracDigits` on the absolute
--     value.  `-[1+ n ]` encodes `-(n+1)`, so the absolute is `suc n`.
showℚ-dec : ℚ → String
showℚ-dec r with Rat.toℚᵘ r
... | mkℚᵘ num       zero      = showℤ num
... | mkℚᵘ (+ n)     (suc d-2) =
      showℕ (n / suc (suc d-2)) ++ₛ "." ++ₛ
      fracDigits 15 (n % suc (suc d-2)) (suc d-2)
... | mkℚᵘ -[1+ n ] (suc d-2) =
      "-" ++ₛ showℕ (suc n / suc (suc d-2)) ++ₛ "." ++ₛ
      fracDigits 15 (suc n % suc (suc d-2)) (suc d-2)
