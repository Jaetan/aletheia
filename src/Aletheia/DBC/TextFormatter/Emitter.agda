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
open import Data.Integer using (ℤ; +_; -[1+_]; ∣_∣)
open import Data.List using (List; []; _∷_; foldr) renaming (_++_ to _++ₗ_)
open import Data.Nat using (ℕ; zero; suc; _*_; _/_; _%_; _∸_; _^_; _⊔_; NonZero)
open import Data.Nat.Properties using (m^n≢0)
open import Data.Rational as Rat using (ℚ)
open import Data.Rational.Unnormalised as ℚᵘ using (mkℚᵘ)
open import Data.String using (String; toList; fromList; fromChar) renaming (_++_ to _++ₛ_)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Aletheia.DBC.DecRat using (DecRat; mkDecRat)

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

-- ============================================================================
-- DECIMAL RATIONALS — Shape B emitter
-- ============================================================================
--
-- `showDecRat-dec` is an *exact* decimal emitter for the DecRat substrate
-- (see `Aletheia.DBC.DecRat`).  Every DecRat value `num / (2^a · 5^b)` is a
-- terminating decimal with at most `max(a, b)` fractional digits, so no
-- fuel cap is required — the representation itself bounds the digit count.
--
-- Shape B: *always* emit `<sign><int>.<frac>` with at least 1 fractional
-- digit.  For integers like `(+ 3, 0, 0)` the output is `"3.0"`, not `"3"`.
-- The user has OK'd this (2026-04-22) because it collapses the parser-side
-- roundtrip to a single composition path — the parser always takes the
-- `(just fracChars)` branch of `buildNumber`, never the integer fallback.
-- A single-path proof is dramatically shorter than a two-branch one.
--
-- The scaling `scaledNum = |num| · 2^(m−a) · 5^(m−b)` rewrites the value as
-- `scaledNum / 10^m`, where `m = max(a, b) ⊔ 1`.  Standard long-division
-- against `10^m` then yields the integer part and the fractional part; the
-- fractional part is emitted with exactly `m` digits via `showℕ-padded`.
--
-- Roundtrip direction (proven in `DBC/TextParser/DecRatParse/Properties`):
-- parser reads `<int>.<frac>` as `(intValue · 10^|frac| + fracValue) /
-- 10^|frac|`, and `canonicalize` strips the shared 2- and 5- factors back
-- to `(num, a, b)`.  The substrate for this is
-- `ScaleLemmas.canonicalizeNat-scale-pos`.
--
-- Two-layer API (2026-04-22 user decision; see
-- `memory/project_b3d_stdlib_audit.md`):
--   * `showDecRat-dec-chars : DecRat → List Char` — the *primitive* emitter,
--     built with `List._++_` (`++ₗ`).  Per-primitive roundtrip proofs land
--     against this layer to sidestep the `toList-++ₛ` substrate gap (only
--     stdlib-provable via `trustMe` under `--with-K`).
--   * `showDecRat-dec    : DecRat → String`       — `fromList ∘
--     showDecRat-dec-chars`, the user-facing boundary sugar.  String wall
--     resurfaces only at the top-level `parseText (formatText d)` aggregator
--     (B.3.d layer 4), which is the one load-bearing site for the
--     substrate decision.
--
-- Every intermediate helper (`showℕ-padded`, `emitMagnitude`) gains the
-- same `-chars` pair: `xxx-chars : ... → List Char` is the primitive,
-- `xxx : ... → String` is the `fromList`-wrapped sugar kept around so
-- prose callers reading the emitter see `String`-valued emitters.

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

-- Emit `n` as exactly `width` decimal digits (as `List Char`), left-padded
-- with `'0'`.  Structural recursion on `width`; the high digit (position
-- `10^(width−1)`) comes from the IH on `n / 10`, the low digit from
-- `n % 10`.  Primitive form — `showℕ-padded` wraps this in `fromList`.
showℕ-padded-chars : (width n : ℕ) → List Char
showℕ-padded-chars zero    _ = []
showℕ-padded-chars (suc w) n =
  showℕ-padded-chars w (n / 10) ++ₗ digitChar (n % 10) ∷ []

-- `String`-valued boundary wrapper over `showℕ-padded-chars`.
showℕ-padded : (width n : ℕ) → String
showℕ-padded w n = fromList (showℕ-padded-chars w n)

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

-- Common scaling step (List Char layer): `scaledNum = |num| · 2^(m−a) ·
-- 5^(m−b)` where `m = max(a, b) ⊔ 1`.  Factored out of
-- `showDecRat-dec-chars`'s three sign clauses so each clause differs
-- only in the sign prefix and the source of the `ℕ` absolute value.
-- No sign handling here.  Uses the local `showNat-chars` (not stdlib
-- `toDecimalChars`) for the integer part so the per-primitive roundtrip
-- proof in `DecRatParse.Properties` can reason about it structurally.
-- Un-privatised so `DecRatParse.Properties` (Part C) can reason about
-- the scaling shape symbolically; same precedent as `manyHelper` in
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

-- `String`-valued boundary wrapper, kept for local symmetry with
-- `emitMagnitude-chars` even though currently only `showDecRat-dec`
-- consumes the chars form (via `showDecRat-dec-chars`).
emitMagnitude : (absNum a b : ℕ) → String
emitMagnitude absNum a b = fromList (emitMagnitude-chars absNum a b)

-- Shape B emitter for DecRat (primitive `List Char` form).  Three clauses
-- mirror the three reachable shapes of `numerator : ℤ`:
--   * `+ 0`         — emit `"0.0…"` (m ≥ 1 fractional digits); no minus sign.
--   * `+ suc n`     — positive magnitude, no minus sign.
--   * `-[1+ n ]`    — negative, emit `'-' ∷` followed by magnitude of `suc n`.
-- All three call `emitMagnitude-chars` with the ℕ absolute value, which is
-- `∣ num ∣` evaluated at each constructor.  (`∣ + n ∣ = n` and `∣ -[1+ n ]
-- ∣ = suc n`, already reduced by `Data.Integer.Base`.)
showDecRat-dec-chars : DecRat → List Char
showDecRat-dec-chars (mkDecRat (+ zero)  a b _) = emitMagnitude-chars 0       a b
showDecRat-dec-chars (mkDecRat (+ suc n) a b _) = emitMagnitude-chars (suc n) a b
showDecRat-dec-chars (mkDecRat -[1+ n ]  a b _) =
  '-' ∷ emitMagnitude-chars (suc n) a b

-- Boundary-sugar wrapper: `String`-valued form of `showDecRat-dec-chars`.
-- This is the user-facing export; the `List Char` primitive above is what
-- `DecRatParse.Properties` reasons about.  `toList (showDecRat-dec d) ≡
-- showDecRat-dec-chars d` holds by `Data.String.Properties.toList-fromList`
-- (only provable via `trustMe` under `--with-K` in stdlib), so the
-- top-level `parseText (formatText d)` aggregator must route through the
-- layer-1 substrate decision rather than through `showDecRat-dec` directly.
showDecRat-dec : DecRat → String
showDecRat-dec d = fromList (showDecRat-dec-chars d)
