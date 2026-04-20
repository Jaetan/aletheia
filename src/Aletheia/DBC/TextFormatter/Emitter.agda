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
--   * Rationals (`factor` / `offset` / `minimum` / `maximum` on signals, and
--     the `ATFloat` / `AVFloat` attribute payloads) emit in canonical `n.d`
--     form with no exponent — implemented alongside the SG_ / BA_* emitters
--     in a later B.3.c sub-commit.  Intentionally not present in this module
--     yet: a placeholder would be a code smell because no caller in B.3.c.1
--     needs rational emission.
module Aletheia.DBC.TextFormatter.Emitter where

open import Data.Bool using (if_then_else_)
open import Data.Char using (Char) renaming (_≟_ to _≟ᶜ_)
open import Data.Integer using (ℤ)
open import Data.List using (foldr)
open import Data.Nat using (ℕ)
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
