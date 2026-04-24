{-# OPTIONS --safe --without-K #-}

-- Lexical emitters for the DBC text format (Phase B.3.c.1 — companion to
-- `Aletheia.DBC.TextParser.Lexer`).
--
-- Purpose: Centralise the per-terminal canonical emission choices so every
-- higher-level emitter in B.3.c.2+ produces the same lexical image.
--
-- Layer-1 form (B.3.d Option 3a, 2026-04-24):
--   Every emitter in this module is `List Char`-valued — the substrate
--   the per-primitive roundtrip proofs reason about.  No `String` /
--   `++ₛ` appears in the formatter; the only `String`-typed boundary
--   in the entire formatter pipeline is `Aletheia.DBC.TextFormatter.
--   formatText : DBC → String`, which is `fromList ∘ formatChars`.
--   See `memory/project_b3d_stdlib_audit.md` for why this layout
--   reduces the universal-roundtrip axiom budget to exactly two
--   (`toList∘fromList`, `fromList∘toList`).
--
-- Canonical emission policy:
--   * `showℕ-dec-chars` / `showℤ-dec-chars` — plain decimal digits via
--     local structural-recursion implementations (`showNat-chars`,
--     `showInt-chars`) so per-primitive roundtrip proofs in
--     `DecRatParse.Properties` and the upcoming layer-2 modules can
--     reason about them directly.  Stdlib's `Data.Nat.Show.show` and
--     `Data.Integer.Show.show` use well-founded recursion via
--     `<-wellFounded-fast` and are difficult to reason about
--     structurally.
--   * `quoteStringLit-chars` — wrap in `"..."` with CSV-style `""`
--     escape on inner quotes (mirrors `Lexer.parseStringLit` exactly;
--     NOT JSON backslash).
module Aletheia.DBC.TextFormatter.Emitter where

open import Data.Bool using (if_then_else_)
open import Data.Char using (Char) renaming (_≟_ to _≟ᶜ_)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (List; []; _∷_; foldr) renaming (_++_ to _++ₗ_)
open import Data.Nat using (ℕ; zero; suc; _*_; _/_; _%_; _∸_; _^_; _⊔_; NonZero)
open import Data.Nat.Properties using (m^n≢0)
open import Data.String using (String; toList)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Aletheia.DBC.DecRat using (DecRat; mkDecRat)

-- ============================================================================
-- DIGIT CHARACTER
-- ============================================================================

-- Canonical digit character for a value in {0..9}.  Out-of-range inputs
-- (≥ 10) return `'0'`; callers rely on the `_%_` bound to stay in range.
-- Ten explicit clauses keep `charToDigit (digitChar d) ≡ d` reducing to
-- `refl` on each `d < 10` branch in the roundtrip proof (closed-term
-- reduction of `primCharToNat '0' = 48` etc.).
digitChar : ℕ → Char
digitChar 0 = '0'
digitChar 1 = '1'
digitChar 2 = '2'
digitChar 3 = '3'
digitChar 4 = '4'
digitChar 5 = '5'
digitChar 6 = '6'
digitChar 7 = '7'
digitChar 8 = '8'
digitChar 9 = '9'
digitChar _ = '0'

-- ============================================================================
-- NATURAL-NUMBER EMITTERS
-- ============================================================================

-- Emit `n` as exactly `width` decimal digits (as `List Char`), left-padded
-- with `'0'`.  Structural recursion on `width`; the high digit (position
-- `10^(width−1)`) comes from the IH on `n / 10`, the low digit from
-- `n % 10`.
showℕ-padded-chars : (width n : ℕ) → List Char
showℕ-padded-chars zero    _ = []
showℕ-padded-chars (suc w) n =
  showℕ-padded-chars w (n / 10) ++ₗ digitChar (n % 10) ∷ []

-- Decimal digit representation of a natural as a `List Char`.  Local
-- substitute for stdlib's `Data.Nat.Show.toDecimalChars` (which uses
-- well-founded recursion via `<-wellFounded-fast` and is difficult to
-- reason about directly).  Produces identical output for all ℕ inputs.
-- `DecRatParse/Properties` closes the roundtrip against `parseDigitList`.
--
-- Fuel-bound structural recursion: `fuel = suc n` is sufficient because
-- the number of decimal digits of `n` is at most `suc n` (loose bound,
-- but easy to establish without `log`).  The `fuel = zero` clause
-- returns `[]` and is provably unreachable from the public entry point
-- via the `n < 10 ^ fuel` precondition the proof will carry.
showNat-chars-fuel : (fuel n : ℕ) → List Char
showNat-chars-fuel zero    _ = []
showNat-chars-fuel (suc f) n with n / 10
... | zero  = digitChar (n % 10) ∷ []
... | suc m = showNat-chars-fuel f (suc m) ++ₗ digitChar (n % 10) ∷ []

showNat-chars : ℕ → List Char
showNat-chars n = showNat-chars-fuel (suc n) n

-- Public alias used by the per-section emitters; reserves the `-dec`
-- suffix as the naming anchor for future hex/binary variants (e.g.
-- signal-overlap hex traces).
showℕ-dec-chars : ℕ → List Char
showℕ-dec-chars = showNat-chars

-- ============================================================================
-- INTEGER EMITTERS
-- ============================================================================

-- Emit a signed integer as `List Char`.  Positive (`+ n`) and zero share
-- the natural-number form; negative (`-[1+ n ]`) prefixes a `'-'` and
-- emits `suc n` (since `-[1+ n ]` encodes `-(n+1)`).
showInt-chars : ℤ → List Char
showInt-chars (+ n)      = showNat-chars n
showInt-chars -[1+ n ]   = '-' ∷ showNat-chars (suc n)

showℤ-dec-chars : ℤ → List Char
showℤ-dec-chars = showInt-chars

-- ============================================================================
-- STRING-LITERAL EMITTERS
-- ============================================================================

-- Emit a DBC-escaped inner character: `'"'` becomes `"\"\""` (two `"`
-- characters), every other character emits as itself.
escapeChar-chars : Char → List Char
escapeChar-chars c = if ⌊ c ≟ᶜ '"' ⌋ then '"' ∷ '"' ∷ [] else c ∷ []

-- Wrap a string in `"..."` and escape inner quotes per CSV-style DBC
-- escape.  Matches `Lexer.parseStringLit` exactly so roundtrip proofs
-- in B.3.d compose cleanly.  The right fold accumulates the closing
-- `"` into the seed so the inner-character expansion sees its own
-- tail naturally.
quoteStringLit-chars : String → List Char
quoteStringLit-chars s =
  '"' ∷ foldr (λ c acc → escapeChar-chars c ++ₗ acc) ('"' ∷ []) (toList s)

-- ============================================================================
-- DECIMAL RATIONALS — Shape B emitter (DecRat substrate)
-- ============================================================================
--
-- `showDecRat-dec-chars` is an *exact* decimal emitter for the DecRat
-- substrate (see `Aletheia.DBC.DecRat`).  Every DecRat value `num /
-- (2^a · 5^b)` is a terminating decimal with at most `max(a, b)`
-- fractional digits, so no fuel cap is required — the representation
-- itself bounds the digit count.
--
-- Shape B: *always* emit `<sign><int>.<frac>` with at least 1
-- fractional digit.  For integers like `(+ 3, 0, 0)` the output is
-- `"3.0"`, not `"3"`.  The user OK'd this (2026-04-22) because it
-- collapses the parser-side roundtrip to a single composition path —
-- the parser always takes the `(just fracChars)` branch of
-- `buildNumber`, never the integer fallback.  A single-path proof is
-- dramatically shorter than a two-branch one.
--
-- The scaling `scaledNum = |num| · 2^(m−a) · 5^(m−b)` rewrites the
-- value as `scaledNum / 10^m`, where `m = max(a, b) ⊔ 1`.  Standard
-- long-division against `10^m` then yields the integer part and the
-- fractional part; the fractional part is emitted with exactly `m`
-- digits via `showℕ-padded-chars`.

-- Common scaling step: `scaledNum = |num| · 2^(m−a) · 5^(m−b)` where
-- `m = max(a, b) ⊔ 1`.  Factored out of `showDecRat-dec-chars`'s three
-- sign clauses so each clause differs only in the sign prefix and the
-- source of the `ℕ` absolute value.  Un-privatised so
-- `DecRatParse.Properties` can reason about the scaling shape
-- symbolically; same precedent as `manyHelper` in
-- `Aletheia.Parser.Combinators`.
emitMagnitude-chars : (absNum a b : ℕ) → List Char
emitMagnitude-chars absNum a b =
  let m         = (a ⊔ b) ⊔ 1
      scaledNum = absNum * 2 ^ (m ∸ a) * 5 ^ (m ∸ b)
      scale     = 10 ^ m
      instance
        scale-nonZero : NonZero scale
        scale-nonZero = m^n≢0 10 m
  in showNat-chars (scaledNum / scale)
       ++ₗ '.' ∷ showℕ-padded-chars m (scaledNum % scale)

-- Shape B emitter for DecRat (`List Char` form).  Three clauses mirror
-- the three reachable shapes of `numerator : ℤ`:
--   * `+ 0`         — emit `"0.0…"` (m ≥ 1 fractional digits); no sign.
--   * `+ suc n`     — positive magnitude, no minus sign.
--   * `-[1+ n ]`    — negative, emit `'-' ∷` followed by magnitude of
--                     `suc n`.
-- All three call `emitMagnitude-chars` with the ℕ absolute value.
showDecRat-dec-chars : DecRat → List Char
showDecRat-dec-chars (mkDecRat (+ zero)  a b _) = emitMagnitude-chars 0       a b
showDecRat-dec-chars (mkDecRat (+ suc n) a b _) = emitMagnitude-chars (suc n) a b
showDecRat-dec-chars (mkDecRat -[1+ n ]  a b _) =
  '-' ∷ emitMagnitude-chars (suc n) a b
