{-# OPTIONS --without-K #-}

-- DBC decimal-rational parser — terminal for `scale`, `offset`, `min`,
-- `max`, environment-variable bounds, value-table keys.
--
-- Shape B grammar (matches the Shape B emitter in
-- `Aletheia.DBC.TextFormatter.Emitter.showDecRat-dec` exactly):
--
--   decrat       ::= "-"? nat "." digit+
--
-- Unlike `Aletheia.Protocol.JSON.Parse.parseRational`, the DBC grammar
-- does *not* allow scientific notation (`[eE][+-]?digits`) and *does*
-- require a mandatory `"." digit+` fractional part (so the `|frac| ≥ 1`
-- invariant always holds — this is what lets the roundtrip proof take a
-- single composition path rather than splitting on "integer vs. decimal"
-- input shape).
--
-- Output: a canonical `DecRat`.  The parser computes the raw integer
-- numerator `n · 10^k + fracValue` and the denominator exponents
-- `(twoExp, fiveExp) = (k, k)` (since `10^k = 2^k · 5^k`), attaches the
-- sign, then routes through `canonicalizeDecRat` from
-- `Aletheia.DBC.DecRat` to strip shared factors of 2 and 5 and produce
-- the canonical witness.  The roundtrip proof in
-- `Aletheia.DBC.TextParser.DecRatParse.Properties` leans on
-- `Aletheia.DBC.DecRat.ScaleLemmas.canonicalizeNat-scale-pos` to
-- undo this exact `x · 2^p · 5^q` scaling on parse-of-emit.
module Aletheia.DBC.TextParser.DecRatParse where

open import Data.Char using (Char; toℕ)
open import Data.List using (List; []; _∷_; foldl; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)
open import Data.Integer using (ℤ; +_; -[1+_]) renaming (-_ to -ℤ_)

open import Aletheia.Parser.Combinators using
  (Parser; pure; _>>=_; _*>_; char; digit; optional; some)
open import Aletheia.DBC.DecRat using (DecRat; canonicalizeDecRat)
open import Aletheia.DBC.TextParser.Lexer using (parseNatural)

-- Helper: digit character → natural (ASCII '0'..'9' → 0..9).  Mirrors
-- `Aletheia.Protocol.JSON.Parse.parseRational`'s inner `charToDigit` so
-- the roundtrip proof can appeal to the same reduction behaviour.
charToDigit : Char → ℕ
charToDigit c = toℕ c ∸ 48

-- Left-to-right digit accumulator: parse `"042"` into `42`.  Matches
-- `Aletheia.Protocol.JSON.Parse.parseRational`'s inner `parseDigitList`
-- in both shape (`foldl` with `acc * 10 + _`) and initial value (0).
-- The Shape B emitter's high-to-low digit emission order was chosen
-- specifically so this `foldl` form reads it back correctly.
parseDigitList : List Char → ℕ
parseDigitList = foldl (λ acc d → acc * 10 + charToDigit d) 0

-- Build a signed integer from a sign flag and a ℕ magnitude.  Matches
-- `Aletheia.Protocol.JSON.Parse.parseRational`'s inner `parseIntHelper`:
-- "-0" collapses to `+0` (not `-0`), so Shape B's "always emit .frac"
-- rule preserves equality on zero DecRat.
applySign : Maybe Char → ℕ → ℤ
applySign nothing       n       = + n
applySign (just _)      zero    = + 0
applySign (just _)      (suc n) = -[1+ n ]

-- Build the canonical DecRat from the parsed components.
--   * `neg` — the optional leading `'-'` flag.
--   * `intPart` — the pre-decimal natural-number part.
--   * `fracChars` — the post-decimal digit list (always non-empty in
--     Shape B; here we let length 0 collapse to 0 denominator without
--     a separate case because `10 ^ 0 = 1` keeps the shape consistent).
-- The raw numerator `intPart · 10^k + fracValue` is paired with
-- `(twoExp, fiveExp) = (k, k)` where `k = length fracChars`.  Routing
-- through `canonicalizeDecRat` strips the shared 2- and 5-factors.
buildDecRat : Maybe Char → ℕ → List Char → DecRat
buildDecRat neg intPart fracChars =
  let k        = length fracChars
      fracVal  = parseDigitList fracChars
      rawAbs   = intPart * 10 ^ k + fracVal
      rawSigned = applySign neg rawAbs
  in canonicalizeDecRat rawSigned k k

-- Parse a DBC decimal rational in Shape B form: `"-?" nat "." digit+`.
-- Matches `showDecRat-dec` exactly; the roundtrip proof is
-- `Aletheia.DBC.TextParser.DecRatParse.Properties`.
parseDecRat : Parser DecRat
parseDecRat = do
  neg ← optional (char '-')
  n   ← parseNatural
  _   ← char '.'
  fd  ← some digit
  pure (buildDecRat neg n fd)
