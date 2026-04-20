{-# OPTIONS --safe --without-K #-}

-- Lexical primitives for the DBC text format (Phase B.3.c.1).
--
-- Purpose: Share the character-class predicates plus identifier/string/ws/
-- newline lexers used by every DBC text parser in B.3.c.2+.
--
-- Grammar slice covered (BNF from `Aletheia.DBC.TextParser`, section H):
--   identifier   ::= (letter | "_") (letter | digit | "_")*
--   string-lit   ::= '"' (any-char-but-quote | '""')* '"'
--   ws           ::= (" " | "\t")+
--   newline      ::= "\n" | "\r\n"
--   rational, integer-lit, nat — re-exported from the JSON parser (same
--   grammar shape: `-?digit+ (\.digit+)? ([eE][+-]?digit+)?`).
--
-- Why re-export instead of duplicate: DBC-text rationals share the exact
-- grammar of the JSON parser's rationals, and `Aletheia.Protocol.JSON.Parse`
-- is already exercised by its own corpus.  Hoisting to a neutral
-- `Aletheia.Parser.Lexical` would broaden the blast radius of the code move
-- beyond B.3.c.1's scope; a future B.3.k cleanup can do that once the DBC
-- text parser has its own test matrix.
module Aletheia.DBC.TextParser.Lexer where

open import Data.Bool using (Bool; _∨_; not)
open import Data.Char using (Char) renaming (_≟_ to _≟ᶜ_)
open import Data.Char.Base using (isAlpha)
open import Data.List using (List; []; _∷_)
open import Data.String using (String; fromList)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Aletheia.Parser.Combinators using
  (Parser; pure; _>>=_; _<|>_; _*>_;
   satisfy; char; string; many; some; isAlphaNum)

open import Aletheia.Protocol.JSON.Parse using (parseNatural; parseInt; parseRational) public

-- ============================================================================
-- CHARACTER CLASSES
-- ============================================================================

isIdentStart : Char → Bool
isIdentStart c = isAlpha c ∨ ⌊ c ≟ᶜ '_' ⌋

isIdentCont : Char → Bool
isIdentCont c = isAlphaNum c ∨ ⌊ c ≟ᶜ '_' ⌋

-- Intraline whitespace — matches the grammar `ws ::= (" " | "\t")+`.
-- Explicitly excludes newlines so lexers sharing a BNF line cannot swallow
-- the line terminator.
isHSpace : Char → Bool
isHSpace c = ⌊ c ≟ᶜ ' ' ⌋ ∨ ⌊ c ≟ᶜ '\t' ⌋

-- ============================================================================
-- IDENTIFIERS
-- ============================================================================

parseIdentifier : Parser String
parseIdentifier = do
  h ← satisfy isIdentStart
  t ← many (satisfy isIdentCont)
  pure (fromList (h ∷ t))

-- ============================================================================
-- STRING LITERALS
-- ============================================================================

-- DBC string escape uses CSV-style doubled quote (`""` → `"`), NOT JSON-style
-- backslash escape.  Mirrors `TextFormatter.Emitter.quoteStringLit` exactly so
-- the B.3.d roundtrip proof composes cleanly.
parseStringChar : Parser Char
parseStringChar =
  (string "\"\"" *> pure '"') <|>
  satisfy (λ c → not ⌊ c ≟ᶜ '"' ⌋)

parseStringLit : Parser String
parseStringLit = do
  _ ← char '"'
  chars ← many parseStringChar
  _ ← char '"'
  pure (fromList chars)

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
