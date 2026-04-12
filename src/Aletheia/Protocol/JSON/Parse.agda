{-# OPTIONS --safe --without-K #-}

-- JSON parser (uses parser combinators, structurally recursive).
--
-- Purpose: Parse JSON strings into the JSON data type.
-- Supports: null, booleans, numbers (integer/decimal/scientific), strings, arrays, objects.
-- Rational: Decimals parsed to exact ℚ representation (e.g., 3.14 → 314/100).
module Aletheia.Protocol.JSON.Parse where

open import Data.String using (String; toList; fromList)
open import Data.List using (List; []; _∷_; foldl; length)
open import Data.Char using (Char; toℕ) renaming (_≟_ to _≟ᶜ_)
open import Data.Char.Base using (isDigit)
open import Data.Bool using (true; false; not)
open import Data.Maybe using (Maybe; just; nothing) renaming (_>>=_ to _>>=ₘ_; map to mapₘ)
open import Data.Nat using (ℕ; zero; suc; _*_; _+_; _∸_)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Rational as Rat using (ℚ; _/_; -_) renaming (_*_ to _*ᵣ_)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Aletheia.Parser.Combinators using (Parser; pure; fail; _>>=_; _<$>_; _<|>_; _*>_; _<*_; satisfy; char; digit; spaces; string; many; some; optional; runParser)
open import Aletheia.Prelude using (ℕtoℚ)
open import Aletheia.Protocol.JSON.Types using (JSON; JNull; JBool; JNumber; JString; JArray; JObject)

-- ============================================================================
-- PRIMITIVE PARSERS
-- ============================================================================

-- Helper: Digit to natural
digitToNat : Char → ℕ
digitToNat '0' = 0
digitToNat '1' = 1
digitToNat '2' = 2
digitToNat '3' = 3
digitToNat '4' = 4
digitToNat '5' = 5
digitToNat '6' = 6
digitToNat '7' = 7
digitToNat '8' = 8
digitToNat '9' = 9
digitToNat _   = 0

-- Parse natural number
parseNatural : Parser ℕ
parseNatural = do
  digits ← some (satisfy isDigit)
  pure (foldl (λ acc d → acc * 10 + digitToNat d) 0 digits)

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

-- Parse a rational number (handles integers, decimals, and scientific notation)
-- Examples: "42" → 42/1, "3.14" → 314/100, "-1.5" → -3/2, "-0.1" → -1/10
--           "1e-7" → 1/10000000, "2.5E+3" → 2500/1
--
-- Note: parseInt loses the sign for "-0" (returns +0). To handle negative
-- fractions like "-0.1" correctly, we parse the sign separately and apply
-- it to the final ℚ value (via Data.Rational.negate).
parseRational : Parser ℚ
parseRational = do
  neg ← optional (char '-')
  n ← parseNatural
  frac ← optional (char '.' *> some digit)
  exp ← optional parseExponent
  pure (applySign neg (applyExp (buildNumber n frac) exp))
  where
    -- Parse exponent part: e/E [+/-] digits
    parseExponent : Parser ℤ
    parseExponent = do
      _ ← char 'e' <|> char 'E'
      sign ← optional (char '+' <|> char '-')
      digits ← parseNatural
      expHelper sign digits
      where
        expHelper : Maybe Char → ℕ → Parser ℤ
        expHelper (just '-') zero = pure (+ 0)
        expHelper (just '-') (suc n') = pure -[1+ n' ]
        expHelper _ n' = pure (+ n')

    -- Compute 10^n, returns suc n to prove NonZero
    power10 : ℕ → ℕ
    power10 zero = suc 0
    power10 (suc n) with power10 n
    ... | suc m = suc (9 + m * 10)
    ... | zero = suc 0  -- Unreachable but needed for coverage

    ascii-zero : ℕ
    ascii-zero = 48

    charToDigit : Char → ℕ
    charToDigit c = toℕ c ∸ ascii-zero

    parseDigitList : List Char → ℕ
    parseDigitList = foldl (λ acc d → acc * 10 + charToDigit d) 0

    buildNumber : ℕ → Maybe (List Char) → ℚ
    buildNumber n nothing = (+ n) / 1
    buildNumber n (just fracChars) with power10 (length fracChars)
    ... | suc scale =
      let fracValue = parseDigitList fracChars
      in (+ (n * suc scale + fracValue)) / suc scale
    ... | zero = (+ n) / 1  -- Unreachable but needed for coverage

    -- Apply scientific notation exponent to a rational.
    -- Positive exp: multiply by 10^e. Negative exp: divide by 10^|e|.
    applyExp : ℚ → Maybe ℤ → ℚ
    applyExp q nothing = q
    applyExp q (just (+ zero)) = q
    applyExp q (just (+ suc e)) = q *ᵣ ℕtoℚ (power10 (suc e))
    applyExp q (just -[1+ e ]) with power10 (suc e)
    ... | suc d = q *ᵣ ((+ 1) / suc d)
    ... | zero = q  -- Unreachable: power10 always returns suc

    applySign : Maybe Char → ℚ → ℚ
    applySign nothing  q = q
    applySign (just _) q = - q

parseNumber : Parser JSON
parseNumber = JNumber <$> parseRational

-- Parse a single character inside a JSON string
-- Accepts all characters except quotes (escape sequences intentionally unsupported)
parseStringChar : Parser Char
parseStringChar = satisfy (λ c → not ⌊ c ≟ᶜ '"' ⌋)

parseString : Parser JSON
parseString = do
  _ ← char '"'
  chars ← many parseStringChar
  _ ← char '"'
  pure (JString (fromList chars))

-- Parse JSON using input length as termination measure (like 'many' does)
-- This makes the structural recursion explicit to Agda's termination checker
parseJSONHelper : ℕ → Parser JSON
parseJSONHelper zero pos input = nothing  -- No budget left, fail
parseJSONHelper (suc n) pos input = (spaces *> parseValue <* spaces) pos input
  where
    mutual
      -- Parse a single JSON value
      parseValue : Parser JSON
      parseValue =
        parseNull <|> parseBoolean <|> parseNumber <|> parseString <|>
        parseArray <|> parseObject

      -- Parse array using structurally smaller n
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
              first ← parseJSONHelper n  -- Recursive call with smaller n
              rest ← many (spaces *> char ',' *> spaces *> parseJSONHelper n)
              pure (first ∷ rest))
            <|> pure []

      -- Parse object using structurally smaller n
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
                val ← parseJSONHelper n  -- Recursive call with smaller n
                pure (key , val)
                where
                  extractString : JSON → Parser String
                  extractString (JString s) = pure s
                  extractString _ = fail

-- Public API: parseJSON wraps helper with input length
parseJSON : Parser JSON
parseJSON pos input = parseJSONHelper (length input) pos input

-- ============================================================================
-- HELPER: RUN JSON PARSER
-- ============================================================================

-- Parse JSON from string
fromString : String → Maybe JSON
fromString input = mapₘ proj₁ (runParser parseJSON (toList input))
