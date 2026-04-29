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
--
-- 3d.4 (2026-04-26): `Identifier.name : List Char` now, so this module no
-- longer needs `Substrate.Unsafe.mkIdentFromCharsUnsafe` to bridge between
-- the consumed char list and the String-internal Identifier.  The lexer
-- builds Identifiers directly via `mkIdentFromChars` (axiom-free), which
-- lets this module — and the 47 modules under `DBC/TextParser/` that
-- transitively import it — drop back to `--safe`.
module Aletheia.DBC.TextParser.Lexer where

open import Data.Bool using (Bool; _∨_; not)
open import Data.Char using (Char) renaming (_≟_ to _≟ᶜ_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String; fromList)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Aletheia.Parser.Combinators using
  (Parser; pure; fail; _>>=_; _<|>_; _*>_;
   satisfy; char; string; many; some)

open import Aletheia.DBC.Identifier using
  (Identifier; mkIdent; isIdentStart; isIdentCont; mkIdentFromChars) public

open import Aletheia.Protocol.JSON.Parse using (parseNatural; parseInt; parseRational) public

-- ============================================================================
-- CHARACTER CLASSES
-- ============================================================================
-- `isIdentStart` / `isIdentCont` are defined in `Aletheia.DBC.Identifier` and
-- re-exported via the `open import ... public` above, so this module remains
-- the canonical surface for DBC-text lexical primitives.

-- Intraline whitespace — matches the grammar `ws ::= (" " | "\t")+`.
-- Explicitly excludes newlines so lexers sharing a BNF line cannot swallow
-- the line terminator.
isHSpace : Char → Bool
isHSpace c = ⌊ c ≟ᶜ ' ' ⌋ ∨ ⌊ c ≟ᶜ '\t' ⌋

-- Non-newline char predicate.  Dual of `isNewlineStart` — `isNonNewline c`
-- holds iff `c` is neither `'\n'` nor `'\r'`, i.e., the char is safe to
-- consume inside a single line.  Used by `parseBitTiming`'s opaque-tail
-- consumer (`many (satisfy isNonNewline)`) and by the Format DSL
-- `nonNewlineRun` constructor.
isNonNewline : Char → Bool
isNonNewline c = not (⌊ c ≟ᶜ '\n' ⌋ ∨ ⌊ c ≟ᶜ '\r' ⌋)

-- ============================================================================
-- IDENTIFIERS
-- ============================================================================

-- Build an Identifier from chars after satisfy accepted the head and `many
-- (satisfy isIdentCont)` accepted every element of the tail.  After 3d.4,
-- this is axiom-free: `mkIdentFromChars` (in `Aletheia.DBC.Identifier`)
-- stores the char list directly as the Identifier's `name` field, with the
-- `T (validIdentifierᵇ (h ∷ t))` witness coming from the `T?` decision.
--
-- Split into an outer `buildIdent h t = fromMaybeIdent (mkIdentFromChars
-- (h ∷ t))` rather than a top-level `with` so the layer-2 roundtrip proof
-- (`Properties.Primitives.parseIdentifier-roundtrip`) can substitute the
-- `mkIdentFromChars`-result via `cong` — the `with` form's internal
-- case-split would be opaque to outer rewrites.  Exposed (not private) so
-- the roundtrip proof can name them explicitly in `bind-just-step`
-- continuations.  The `nothing` branch is logically unreachable here (the
-- structural guarantees of `satisfy isIdentStart >>= many (satisfy
-- isIdentCont)` imply `validIdentifierᵇ (h ∷ t) = true`) but the parser
-- machinery still requires a `Maybe`-shaped match.
fromMaybeIdent : Maybe Identifier → Parser Identifier
fromMaybeIdent (just i) = pure i
fromMaybeIdent nothing  = fail

buildIdent : Char → List Char → Parser Identifier
buildIdent h t = fromMaybeIdent (mkIdentFromChars (h ∷ t))

parseIdentifier : Parser Identifier
parseIdentifier =
  satisfy isIdentStart >>= λ h →
  many (satisfy isIdentCont) >>= λ t →
  buildIdent h t

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

-- Post 3d.4 + JSON-mirror returns the raw `List Char` body so the roundtrip
-- composes axiom-free against `quoteStringLit-chars` (also List-Char-valued).
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
