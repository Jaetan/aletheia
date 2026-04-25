{-# OPTIONS --without-K #-}

-- DBC decimal-rational parser — terminal for `scale`, `offset`, `min`,
-- `max`, environment-variable bounds, value-table keys, and (post-3c-pre)
-- attribute values whose wire form is a bare integer (subsumes the
-- former `parseInt` branch of `parseRawAttrValue`).
--
-- Two shapes accepted, in `<|>` order:
--
--   1. Frac form (Shape B emitter `showDecRat-dec`):
--        decrat       ::= "-"? nat "." digit+
--      Mandatory fraction; this matches every numeric DBC slot whose
--      value is emitted as DecRat (factor / offset / min / max / value-
--      table key / EnvVar bounds), where the formatter always emits a
--      `'.'` plus at least one fractional digit.
--
--   2. Bare-int form (mirrors `Protocol/JSON.Parse.parseInt`'s shape):
--        decrat       ::= "-"? nat
--      The integer is then promoted to `DecRat` via `buildDecRat ... []`
--      (empty fractional part → denominator = 1).  This admits cantools-
--      style attribute values like `BA_ "X" BO_ 400 50;` (note bare
--      `50`, no `.frac`).
--
-- Order matters: the frac form is tried first via `<|>`, so an input
-- like `42.5` is committed to the longer frac match rather than being
-- split into bare-int `42` + leftover `.5`.  When the frac branch fails
-- (no `.` after the natural-number prefix), `<|>` falls through to the
-- bare-int branch with the parser state restored.
--
-- Unlike `Aletheia.Protocol.JSON.Parse.parseRational`, the DBC grammar
-- does *not* allow scientific notation (`[eE][+-]?digits`).
--
-- Output: a canonical `DecRat`.  Both branches feed `buildDecRat`, which
-- computes the raw integer numerator `n · 10^k + fracValue` and the
-- denominator exponents `(twoExp, fiveExp) = (k, k)` (since `10^k = 2^k
-- · 5^k`, with `k = length fracChars` — `0` for the bare-int branch),
-- attaches the sign, then routes through `canonicalizeDecRat` from
-- `Aletheia.DBC.DecRat` to strip shared factors of 2 and 5 and produce
-- the canonical witness.  The roundtrip proofs in
-- `Aletheia.DBC.TextParser.DecRatParse.Properties` lean on
-- `Aletheia.DBC.DecRat.ScaleLemmas.canonicalizeNat-scale-pos` to
-- undo this exact `x · 2^p · 5^q` scaling on parse-of-emit.
module Aletheia.DBC.TextParser.DecRatParse where

open import Data.Char using (Char; toℕ)
open import Data.List using (List; []; _∷_; foldl; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)
open import Data.Integer using (ℤ; +_; -[1+_]) renaming (-_ to -ℤ_)

open import Aletheia.Parser.Combinators using
  (Parser; pure; _>>=_; _*>_; _<|>_; char; digit; optional; some)
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

-- Frac form (Shape B): `"-?" nat "." digit+`.  Matches `showDecRat-dec`
-- exactly; the per-shape roundtrip proofs in
-- `Aletheia.DBC.TextParser.DecRatParse.Properties` are stated about this
-- inner parser (`parseDecRatFrac-roundtrip-suffix` and friends).
parseDecRatFrac : Parser DecRat
parseDecRatFrac = do
  neg ← optional (char '-')
  n   ← parseNatural
  _   ← char '.'
  fd  ← some digit
  pure (buildDecRat neg n fd)

-- Bare-int form: `"-?" nat`.  Mirrors `Protocol/JSON.Parse.parseInt`'s
-- shape but lifts the result into `DecRat` (denominator = 1) via
-- `buildDecRat ... []`.  Subsumes the dropped third branch of
-- `parseRawAttrValue`.  No suffix-bound `.` check is performed here —
-- the surrounding `<|>` in `parseDecRat` already commits to the frac
-- form first when applicable, so this branch only fires after the frac
-- form has failed.
parseDecRatBareInt : Parser DecRat
parseDecRatBareInt = do
  neg ← optional (char '-')
  n   ← parseNatural
  pure (buildDecRat neg n [])

-- Parse a DBC decimal rational: try the frac form first, fall through to
-- the bare-int form.  The `<|>` backtracks to the original parser state
-- on left-branch failure (see `Aletheia.Parser.Combinators._<|>_`), so
-- partial consumption by the frac branch is harmless.
parseDecRat : Parser DecRat
parseDecRat = parseDecRatFrac <|> parseDecRatBareInt
