-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- The JSON parser: RFC 8259's grammar, on parser combinators that recurse
-- structurally on the input.
--
-- It reads a whole text holding one value and nothing after it.  Whitespace
-- is RFC 8259's four characters; an integer part is `0` or starts with a
-- digit from 1 to 9; a string holds no raw character below U+0020, and a
-- `\u` escape names a Unicode scalar value, a surrogate pair read as one
-- character and a lone half refused.  Numbers are read exactly as rationals
-- (`Aletheia.DBC.DecRat.Literal`): "42" is 42/1, "3.14" is 314/100, "1e-7"
-- is 1/10000000.
module Aletheia.Protocol.JSON.Parse where

open import Data.String using (String; fromList)
open import Data.List using (List; []; _∷_; [_])
open import Data.Char using (Char; _≈ᵇ_)
open import Data.Char.Base using (toℕ; fromℕ)
open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.Bool.ListAction using (any)
open import Data.Maybe using (Maybe; just; nothing; fromMaybe; maybe′)
open import Data.Nat using (ℕ; _+_; _*_; _∸_; _<ᵇ_)
open import Data.Rational using (ℚ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Aletheia.Parser.Combinators using
  (Parser; pure; fail; _>>=_; _<$>_; _<*>_; _<|>_; _*>_; _<*_; satisfy; char; anyChar;
   string; many; optional; eof)
open import Aletheia.DBC.DecRat using (toℚ)
open import Aletheia.DBC.DecRat.Literal using (scientificLiteral)
open import Aletheia.Protocol.JSON.Types using (JSON; JNull; JBool; JNumber; JString; JArray; JObject)

-- ============================================================================
-- WHITESPACE AND LITERALS
-- ============================================================================

-- Space, horizontal tab, line feed, carriage return.
whitespace : List Char
whitespace = ' ' ∷ '\t' ∷ '\n' ∷ '\r' ∷ []

isWhitespace : Char → Bool
isWhitespace c = any (c ≈ᵇ_) whitespace

ws : Parser (List Char)
ws = many (satisfy isWhitespace)

_<$_ : ∀ {A B : Set} → A → Parser B → Parser A
a <$ p = p >>= λ _ → pure a

infixl 4 _<$_

parseNull : Parser JSON
parseNull = JNull <$ string "null"

parseBoolean : Parser JSON
parseBoolean = (JBool true <$ string "true") <|> (JBool false <$ string "false")

-- ============================================================================
-- NUMBERS
-- ============================================================================

-- A decimal digit, `0` to `9`.  Decided on the character's code, so a
-- proof can read what it accepted.
isDigitChar : Char → Bool
isDigitChar c = (47 <ᵇ toℕ c) ∧ (toℕ c <ᵇ 58)

isNonZeroDigit : Char → Bool
isNonZeroDigit c = isDigitChar c ∧ not (c ≈ᵇ '0')

digit : Parser Char
digit = satisfy isDigitChar

-- A run of one or more digits, as read.
digitRun : Parser (List Char)
digitRun = _∷_ <$> digit <*> many digit

-- `0`, or a digit from 1 to 9 followed by digits.
parseIntPart : Parser (List Char)
parseIntPart =
  ([_] <$> char '0') <|>
  (_∷_ <$> satisfy isNonZeroDigit <*> many digit)

-- An exponent's sign and digits, after its `e` or `E`.
exponentParts : Char → Maybe Char → List Char → Maybe Char × List Char
exponentParts _ sign digits = sign , digits

-- The exponent: `e` or `E`, an optional sign, digits.
parseExponent : Parser (Maybe Char × List Char)
parseExponent = exponentParts <$> (char 'e' <|> char 'E') <*> optional (char '+' <|> char '-') <*> digitRun

-- A number's value, through the literal core `scientificLiteral`: it folds
-- the significand's digits only while the value fits and the exponent's only
-- while they can matter, so the cost is linear in the literal's length, and
-- a literal past the component bound is held for the bound check after the
-- parse.
literalValue : Maybe Char → List Char → Maybe (List Char) → Maybe (Maybe Char × List Char) → ℚ
literalValue neg int frac exp =
  toℚ (scientificLiteral neg int (fromMaybe [] frac) (maybe′ proj₁ nothing exp) (maybe′ proj₂ [] exp))

parseRational : Parser ℚ
parseRational =
  literalValue <$> optional (char '-') <*> parseIntPart <*> optional (char '.' *> digitRun)
               <*> optional parseExponent

parseNumber : Parser JSON
parseNumber = JNumber <$> parseRational

-- ============================================================================
-- STRINGS
-- ============================================================================

-- A character a string may hold as it is: U+0020 and above, except the
-- quotation mark and the reverse solidus.
isUnescaped : Char → Bool
isUnescaped c = (31 <ᵇ toℕ c) ∧ not (c ≈ᵇ '"') ∧ not (c ≈ᵇ '\\')

isHexDigit : Char → Bool
isHexDigit c = isDigitChar c ∨ ((96 <ᵇ toℕ c) ∧ (toℕ c <ᵇ 103)) ∨ ((64 <ᵇ toℕ c) ∧ (toℕ c <ᵇ 71))

-- A hex digit's value, for a character `isHexDigit` accepts.
hexDigitValue : Char → ℕ
hexDigitValue c =
  if isDigitChar c then toℕ c ∸ 48 else if 96 <ᵇ toℕ c then toℕ c ∸ 87 else toℕ c ∸ 55

hexDigit : Parser ℕ
hexDigit = hexDigitValue <$> satisfy isHexDigit

-- The UTF-16 code unit four hex digits write.
codeUnit : ℕ → ℕ → ℕ → ℕ → ℕ
codeUnit a b c d = ((a * 16 + b) * 16 + c) * 16 + d

hex4 : Parser ℕ
hex4 = codeUnit <$> hexDigit <*> hexDigit <*> hexDigit <*> hexDigit

isHighSurrogate : ℕ → Bool
isHighSurrogate n = (55295 <ᵇ n) ∧ (n <ᵇ 56320)

isLowSurrogate : ℕ → Bool
isLowSurrogate n = (56319 <ᵇ n) ∧ (n <ᵇ 57344)

-- The second half of a surrogate pair: `\u` and a low half at once.
lowSurrogate : ℕ → Parser Char
lowSurrogate high =
  char '\\' *> char 'u' *> hex4 >>= λ low →
  if isLowSurrogate low
  then pure (fromℕ (65536 + (high ∸ 55296) * 1024 + (low ∸ 56320)))
  else fail

-- The character a `\u` escape names.  A lone surrogate half is refused
-- before `fromℕ`, which would turn it into U+FFFD.
unicodeEscape : Parser Char
unicodeEscape =
  hex4 >>= λ unit →
  if isHighSurrogate unit then lowSurrogate unit
  else if isLowSurrogate unit then fail
  else pure (fromℕ unit)

-- The one-character escapes: the character after the `\`, and the
-- character the escape names.
shortEscapes : List (Char × Char)
shortEscapes =
  ('"' , '"') ∷ ('\\' , '\\') ∷ ('/' , '/') ∷ ('b' , '\b') ∷ ('f' , '\f') ∷ ('n' , '\n') ∷ ('r' , '\r') ∷
  ('t' , '\t') ∷ []

-- The value a character has in a table of pairs, the first if several.
lookupᶜ : Char → List (Char × Char) → Maybe Char
lookupᶜ _ []              = nothing
lookupᶜ c ((k , v) ∷ kvs) = if c ≈ᵇ k then just v else lookupᶜ c kvs

-- The character an escape names, from the character after the `\`.
decodeEscape : Char → Parser Char
decodeEscape c = if c ≈ᵇ 'u' then unicodeEscape else maybe′ pure fail (lookupᶜ c shortEscapes)

parseEscape : Parser Char
parseEscape = char '\\' *> anyChar >>= decodeEscape

parseStringChar : Parser Char
parseStringChar = parseEscape <|> satisfy isUnescaped

-- A string's characters, between its quotation marks.
parseStringChars : Parser (List Char)
parseStringChars = char '"' *> many parseStringChar <* char '"'

parseString : Parser JSON
parseString = JString <$> parseStringChars

-- ============================================================================
-- VALUES
-- ============================================================================

-- An object member from its key's characters and its value.
memberOf : List Char → JSON → String × JSON
memberOf key value = fromList key , value

-- A structural character with whitespace on both sides: `[`, `{`, `]`, `}`,
-- `:` and `,`.
structural : Char → Parser Char
structural c = ws *> char c <* ws

-- The measure drops one element per nesting level, so the recursion is
-- structural; `parseJSON` passes the input itself, which bounds the depth
-- by its length.
mutual
  parseValue : List Char → Parser JSON
  parseValue []      = fail
  parseValue (_ ∷ b) =
    parseNull <|> parseBoolean <|> parseNumber <|> parseString <|> parseArray b <|> parseObject b

  parseArray : List Char → Parser JSON
  parseArray b = structural '[' *> (JArray <$> (parseValues b <|> pure [])) <* structural ']'

  parseValues : List Char → Parser (List JSON)
  parseValues b = _∷_ <$> parseValue b <*> many (structural ',' *> parseValue b)

  parseObject : List Char → Parser JSON
  parseObject b = structural '{' *> (JObject <$> (parseMembers b <|> pure [])) <* structural '}'

  parseMembers : List Char → Parser (List (String × JSON))
  parseMembers b = _∷_ <$> parseMember b <*> many (structural ',' *> parseMember b)

  parseMember : List Char → Parser (String × JSON)
  parseMember b = memberOf <$> (parseStringChars <* structural ':') <*> parseValue b

-- A whole text: one value, whitespace around it, nothing after.  The
-- nesting-depth bound (`max-nesting-depth`) is checked on the parsed tree by
-- `processJSONLine` (`Main/JSON.agda`), which reports it as a typed bound
-- refusal.
parseJSON : Parser JSON
parseJSON pos input = (ws *> parseValue input <* ws <* eof) pos input
