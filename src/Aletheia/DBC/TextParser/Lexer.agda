-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Lexical primitives for the DBC text format.
--
-- Purpose: Share the character-class predicates plus identifier/string/ws/
-- newline lexers used by every DBC text parser.
--
-- Grammar slice covered (BNF from `Aletheia.DBC.TextParser`, section H):
--   identifier   ::= (letter | "_") (letter | digit | "_")*
--   string-lit   ::= '"' (any-char-but-quote | '""')* '"'
--   ws           ::= (" " | "\t")+
--   newline      ::= "\n" | "\r\n"
--   nat          ::= digit+
-- A number with a sign, a fraction or an exponent is read by
-- `Aletheia.DBC.TextParser.DecRatParse`, on `parseDigits`.
--
-- `Identifier.name` is `List Char`, so the lexer builds Identifiers directly via
-- `mkIdentFromChars` (axiom-free) with no String bridge.  RULE: keep it that way —
-- an axiom-consuming bridge here would drop this module, and everything under
-- `DBC/TextParser/` that transitively imports it, out of `--safe`.
module Aletheia.DBC.TextParser.Lexer where

open import Data.Bool using (Bool; true; false; _∨_; not; if_then_else_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Char using (Char) renaming (_≟_ to _≟ᶜ_)
open import Data.Char.Base using (isDigit)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _∸_; _+_)
open import Data.List using (length; takeWhileᵇ)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Aletheia.Limits using (max-identifier-length)
open import Aletheia.Parser.Position using (Position; advancePosition)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Aletheia.Parser.Combinators using
  ( Parser; pure; _>>=_; _<$>_; _<|>_; _*>_; satisfy; char; string; many; some
  ; ParseResult; mkResult; at; refuse; refused )

open import Aletheia.DBC.Identifier using
  ( Identifier; mkIdent; isIdentStart; isIdentCont; mkIdentFromChars
  ; parseIdentifierField; TooLong; BadChars ) public

open import Aletheia.DBC.DecRat.Literal using (natLiteral)

-- A run of one or more digits, as read.
parseDigits : Parser (List Char)
parseDigits = some (satisfy isDigit)

-- A natural number: its digits, or 2^64 when the run holds at least 65
-- significant digits (`Aletheia.DBC.DecRat.Literal.natLiteral`), which the
-- bound checks after the parse refuse.
parseNatural : Parser ℕ
parseNatural = natLiteral <$> parseDigits

-- ============================================================================
-- CHARACTER CLASSES
-- ============================================================================
-- `isIdentStart` / `isIdentCont` are defined in `Aletheia.DBC.Identifier` and
-- re-exported via the `open import ... public` above, so this module is the
-- surface for the DBC text's lexical primitives.

-- Intraline whitespace — matches the grammar `ws ::= (" " | "\t")+`.
-- Explicitly excludes newlines so lexers sharing a BNF line cannot swallow
-- the line terminator.
isHSpace : Char → Bool
isHSpace c = ⌊ c ≟ᶜ ' ' ⌋ ∨ ⌊ c ≟ᶜ '\t' ⌋

-- Non-newline char predicate.  Dual of `isNewlineStart`: `isNonNewline c`
-- holds iff `c` is neither `'\n'` nor `'\r'`, the char is safe to consume
-- inside a single line.  The Format DSL's `nonNewlineRun` reads with it (the
-- `BS_:` line's opaque tail among its users).
isNonNewline : Char → Bool
isNonNewline c = not (⌊ c ≟ᶜ '\n' ⌋ ∨ ⌊ c ≟ᶜ '\r' ⌋)

-- ============================================================================
-- IDENTIFIERS
-- ============================================================================

-- At most `n` characters satisfying `pred`, read one at a time; stops at the
-- first other character or when `n` are read.  Structural on the input; the
-- counter is data beside it.
atMost : ℕ → (Char → Bool) → Parser (List Char)
atMost _       _    pos []       = at pos , just (mkResult [] pos [])
atMost zero    _    pos input    = at pos , just (mkResult [] pos input)
atMost (suc n) pred pos (c ∷ cs) with pred c
... | false = at pos , just (mkResult [] pos (c ∷ cs))
... | true with atMost n pred (advancePosition pos c) cs
...   | pos′ , just r  = pos′ , just (mkResult (c ∷ ParseResult.value r) (ParseResult.position r) (ParseResult.remaining r))
...   | pos′ , nothing = pos′ , nothing

-- The run of identifier characters: a start character, then at most
-- `max-identifier-length ∸ 1` continuation characters.
identRun : Parser (List Char)
identRun =
  satisfy isIdentStart >>= λ h →
  atMost (max-identifier-length ∸ 1) isIdentCont >>= λ t →
  pure (h ∷ t)

-- How many characters at the head satisfy `pred`.
countWhile : (Char → Bool) → List Char → ℕ
countWhile _    []       = 0
countWhile pred (c ∷ cs) = if pred c then suc (countWhile pred cs) else 0

-- The one identifier decision on a finished run, read from `start`: the
-- identifier, or the refusal on the watermark.
decideName : Position → List Char → Parser Identifier
decideName start run pos input with parseIdentifierField run
... | inj₂ i = at pos , just (mkResult i pos input)
... | inj₁ e = refuse (refused start e) pos input

-- After the run: a further identifier character is the 129th, and the name
-- is refused by its length, counted to its end; otherwise the decision.
decideRun : Position → List Char → Parser Identifier
decideRun start run pos [] = decideName start run pos []
decideRun start run pos (c ∷ cs) with isIdentCont c
... | true  = refuse (refused start (TooLong (length run + suc (countWhile isIdentCont cs)))) pos (c ∷ cs)
... | false = decideName start run pos (c ∷ cs)

-- An identifier, read where `pos` stands: the run, then the decision, a
-- refusal carrying `pos` as the name's start.  A word starting with a
-- character no identifier starts with (a digit) is read to its end and
-- refused as not an identifier, as the JSON route refuses the same name.
parseIdentifier : Parser Identifier
parseIdentifier pos [] = at pos , nothing
parseIdentifier pos (c ∷ cs) =
  if isIdentStart c then (identRun >>= decideRun pos) pos (c ∷ cs)
  else if isIdentCont c then refuse (refused pos (BadChars (c ∷ takeWhileᵇ isIdentCont cs))) pos (c ∷ cs)
  else (at pos , nothing)

-- On a start character the identifier parser is the run then the decision.
parseIdentifier-start : ∀ pos h cs → isIdentStart h ≡ true
  → parseIdentifier pos (h ∷ cs) ≡ (identRun >>= decideRun pos) pos (h ∷ cs)
parseIdentifier-start pos h cs eq rewrite eq = refl

-- A word: the identifier grammar alone, every character kept, no decision.
-- The `NS_` block's keyword lines are words.
parseWord : Parser (List Char)
parseWord =
  satisfy isIdentStart >>= λ h →
  many (satisfy isIdentCont) >>= λ t →
  pure (h ∷ t)

-- ============================================================================
-- STRING LITERALS
-- ============================================================================

-- DBC string escape uses CSV-style doubled quote (`""` → `"`), NOT JSON-style
-- backslash escape.  Mirrors `TextFormatter.Emitter.quoteStringLit` exactly so
-- the roundtrip proof composes cleanly.
parseStringChar : Parser Char
parseStringChar =
  (string "\"\"" *> pure '"') <|>
  satisfy (λ c → not ⌊ c ≟ᶜ '"' ⌋)

-- Returns the raw `List Char` body so the roundtrip composes axiom-free
-- against `quoteStringLit-chars` (also List-Char-valued).
parseStringLit : Parser (List Char)
parseStringLit = do
  _ ← char '"'
  chars ← many parseStringChar
  _ ← char '"'
  pure chars

-- ============================================================================
-- WHITESPACE & NEWLINES
-- ============================================================================

-- Mandatory intraline whitespace (one or more `' '` / `'\t'`).
parseWS : Parser (List Char)
parseWS = some (satisfy isHSpace)

-- Optional intraline whitespace (zero or more).
parseWSOpt : Parser (List Char)
parseWSOpt = many (satisfy isHSpace)

-- `"\r\n"` is tried before `"\n"` so CRLF inputs are not left with a stray
-- `\r` on the next line start.  See BNF line `newline ::= "\n" | "\r\n"`.
parseNewline : Parser Char
parseNewline = (string "\r\n" *> pure '\n') <|> char '\n'
