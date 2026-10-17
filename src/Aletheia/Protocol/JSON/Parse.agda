-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- JSON parser (uses parser combinators, structurally recursive).
--
-- Purpose: Parse JSON strings into the JSON data type.
-- Supports: null, booleans, numbers (integer/decimal/scientific), strings, arrays, objects.
-- Rational: Decimals parsed to exact ℚ representation (e.g., 3.14 → 314/100).
module Aletheia.Protocol.JSON.Parse where

open import Data.String using (String; toList; fromList)
open import Data.List using (List; []; _∷_)
open import Data.Char using (Char) renaming (_≟_ to _≟ᶜ_)
open import Data.Char.Base using (isDigit)
open import Data.Bool using (true; false; not; _∧_)
open import Data.Maybe using (Maybe; just; nothing; fromMaybe; maybe′) renaming (map to mapₘ)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Rational as Rat using (ℚ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Aletheia.Parser.Combinators using (Parser; pure; fail; _>>=_; _<$>_; _<|>_; _*>_; _<*_; satisfy; char; digit; spaces; string; many; some; optional; runParser)
open import Aletheia.DBC.DecRat using (toℚ)
open import Aletheia.DBC.DecRat.Literal using (natLiteral; scientificLiteral)
open import Aletheia.Protocol.JSON.Types using (JSON; JNull; JBool; JNumber; JString; JArray; JObject)

-- ============================================================================
-- PRIMITIVE PARSERS
-- ============================================================================

-- A run of one or more digits, as read.
parseDigits : Parser (List Char)
parseDigits = some (satisfy isDigit)

-- A natural number: its digits, or 2^64 when the run holds at least 65
-- significant digits (`Aletheia.DBC.DecRat.Literal.natLiteral`), which the
-- bound checks after the parse refuse.
parseNatural : Parser ℕ
parseNatural = natLiteral <$> parseDigits

-- Parse integer (with optional minus sign)
parseInt : Parser ℤ
parseInt = do
  neg ← optional (char '-')
  n ← parseNatural
  parseIntHelper neg n
  where
    parseIntHelper : Maybe Char → ℕ → Parser ℤ
    parseIntHelper nothing n = pure (+ n)
    parseIntHelper (just _) zero = pure (+ 0)
    parseIntHelper (just _) (suc n') = pure (-[1+ n' ])

-- Helper: <$ operator (discard result, return constant)
_<$_ : ∀ {A B : Set} → A → Parser B → Parser A
a <$ p = p >>= λ _ → pure a

infixl 4 _<$_

-- ============================================================================
-- JSON VALUE PARSERS
-- ============================================================================

parseNull : Parser JSON
parseNull = JNull <$ string "null"

parseBoolean : Parser JSON
parseBoolean =
  (JBool true <$ string "true") <|>
  (JBool false <$ string "false")

-- A rational number: integers, decimals and scientific notation, read
-- through the one literal core (`Aletheia.DBC.DecRat.Literal`): the
-- significand's digits are folded only when the value fits, and the
-- exponent's digits are folded only when they can matter, so the cost is
-- linear in the literal's length and a literal past the component bound
-- is held at 2^64 for the bound check after the parse.
-- Examples: "42" → 42/1, "3.14" → 314/100, "-1.5" → -3/2, "-0.1" → -1/10,
--           "1e-7" → 1/10000000, "2.5E+3" → 2500/1.
parseRational : Parser ℚ
parseRational = do
  neg  ← optional (char '-')
  int  ← parseDigits
  frac ← optional (char '.' *> some digit)
  exp  ← optional parseExponent
  pure (toℚ (scientificLiteral neg int (fromMaybe [] frac)
                               (expSign exp) (expDigits exp)))
  where
    -- The exponent part: e/E, an optional sign, digits.
    parseExponent : Parser (Maybe Char × List Char)
    parseExponent = do
      _      ← char 'e' <|> char 'E'
      sign   ← optional (char '+' <|> char '-')
      digits ← parseDigits
      pure (sign , digits)

    expSign : Maybe (Maybe Char × List Char) → Maybe Char
    expSign = maybe′ proj₁ nothing

    expDigits : Maybe (Maybe Char × List Char) → List Char
    expDigits = maybe′ proj₂ []

parseNumber : Parser JSON
parseNumber = JNumber <$> parseRational

-- Parse a literal (non-escape) character inside a JSON string.
-- Excludes the closing quote and the escape introducer.
parseLiteralStringChar : Parser Char
parseLiteralStringChar = satisfy (λ c → not ⌊ c ≟ᶜ '"' ⌋ ∧ not ⌊ c ≟ᶜ '\\' ⌋)

-- Decode the second character of a JSON escape sequence.
-- Supports the ASCII-range escapes JSON.stringify (Python json, Go
-- encoding/json, JavaScript) emits: \" \\ \/ \n \t \r \b \f.  Unicode
-- \uXXXX escapes are intentionally unsupported — DBC text and the rest
-- of the protocol stay within ASCII.
decodeEscape : Char → Parser Char
decodeEscape '"'  = pure '"'
decodeEscape '\\' = pure '\\'
decodeEscape '/'  = pure '/'
decodeEscape 'n'  = pure '\n'
decodeEscape 't'  = pure '\t'
decodeEscape 'r'  = pure '\r'
decodeEscape 'b'  = pure '\b'
decodeEscape 'f'  = pure '\f'
decodeEscape _    = fail

-- Parse a JSON escape sequence: '\' followed by one of the recognised
-- second chars; consumes 2 input chars and produces the decoded char.
parseEscapeChar : Parser Char
parseEscapeChar = do
  _ ← char '\\'
  c ← satisfy (λ _ → true)
  decodeEscape c

-- Parse a single character inside a JSON string — either an escape
-- sequence or a literal char.  Termination: each branch consumes ≥1
-- input char, so `many parseStringChar` makes progress.
parseStringChar : Parser Char
parseStringChar = parseEscapeChar <|> parseLiteralStringChar

parseString : Parser JSON
parseString = do
  _ ← char '"'
  chars ← many parseStringChar
  _ ← char '"'
  pure (JString chars)

-- Parse JSON with a character list as termination measure, as `many` does:
-- each nesting level drops one element of it, so the recursion is structural.
parseJSONHelper : List Char → Parser JSON
parseJSONHelper []          pos input = pos , nothing  -- Nested deeper than the measure is long
parseJSONHelper (_ ∷ bound) pos input = (spaces *> parseValue <* spaces) pos input
  where
    mutual
      -- Parse a single JSON value
      parseValue : Parser JSON
      parseValue =
        parseNull <|> parseBoolean <|> parseNumber <|> parseString <|>
        parseArray <|> parseObject

      -- Parse array, recursing on the shorter measure
      parseArray : Parser JSON
      parseArray = do
        _ ← char '['
        _ ← spaces
        elements ← parseArrayElements
        _ ← spaces
        _ ← char ']'
        pure (JArray elements)
        where
          parseArrayElements : Parser (List JSON)
          parseArrayElements =
            (do
              first ← parseJSONHelper bound  -- Recursive call with the shorter measure
              rest ← many (spaces *> char ',' *> spaces *> parseJSONHelper bound)
              pure (first ∷ rest))
            <|> pure []

      -- Parse object, recursing on the shorter measure
      parseObject : Parser JSON
      parseObject = do
        _ ← char '{'
        _ ← spaces
        fields ← parseObjectFields
        _ ← spaces
        _ ← char '}'
        pure (JObject fields)
        where
          parseObjectFields : Parser (List (String × JSON))
          parseObjectFields =
            (do
              first ← parseObjectField
              rest ← many (spaces *> char ',' *> spaces *> parseObjectField)
              pure (first ∷ rest))
            <|> pure []
            where
              parseObjectField : Parser (String × JSON)
              parseObjectField = do
                str ← parseString
                key ← extractString str
                _ ← spaces
                _ ← char ':'
                _ ← spaces
                val ← parseJSONHelper bound  -- Recursive call with the shorter measure
                pure (key , val)
                where
                  extractString : JSON → Parser String
                  extractString (JString cs) = pure (fromList cs)
                  extractString _ = fail

-- Entry point: the input itself is the termination measure, bounding the
-- recursion depth by its length.  The adversarial-input nesting-depth
-- cap (`max-nesting-depth`, 64) is enforced ONE LAYER UP by `processJSONLine`
-- (`Main/JSON.agda`) as a typed `InputBoundExceeded NestingDepth …`
-- rejection.
-- Placing the check at the handler boundary rather than inside `parseJSON`
-- keeps the parser as the pure inverse of `formatJSON` (no `nothing`-as-bound
-- punning) and exposes the structured `bound_kind / observed / limit` triple
-- on the wire via `Protocol/ResponseFormat.errorExtras`.
parseJSON : Parser JSON
parseJSON pos input = parseJSONHelper input pos input

-- ============================================================================
-- HELPER: RUN JSON PARSER
-- ============================================================================

-- Parse JSON from string.  Drops the failure watermark (proj₂ of the
-- driver pair) — positioned JSON errors surface via `Main.JSON`'s
-- driver, which consumes the full pair.
fromString : String → Maybe JSON
fromString input = mapₘ proj₁ (proj₂ (runParser parseJSON (toList input)))
