{-# OPTIONS --safe --without-K #-}

-- JSON data types, parser, and formatter with rational number support.
--
-- Purpose: Core JSON handling for streaming protocol (parse/format JSON).
-- Types: JSON (JNull, JBool, JNumber, JString, JArray, JObject).
-- Operations: parseJSON (String → JSON), formatJSON (JSON → String).
-- Role: Foundation for all protocol communication (commands, responses, data frames).
--
-- Rational encoding: Supports both decimal (3.14) and object ({"numerator": 1, "denominator": 3"}).
-- Parser accepts both formats, formatter outputs object format for exact representation.
module Aletheia.Protocol.JSON where

open import Data.String using (String; toList; fromList) renaming (_++_ to _++ₛ_)
open import Data.List using (List; []; _∷_; foldl; length)
open import Data.Char using (Char; toℕ) renaming (_≟_ to _≟ᶜ_)
open import Data.Char.Base using (isDigit)
open import Data.Bool using (Bool; true; false; if_then_else_; not)
open import Data.Maybe using (Maybe; just; nothing; map) renaming (_>>=_ to _>>=ₘ_)
open import Data.Nat using (ℕ; zero; suc; _*_; _+_; _∸_)
open import Data.Integer using (ℤ; +_; -[1+_]; ∣_∣)
open import Data.Rational as Rat using (ℚ; mkℚ; _/_; toℚᵘ; -_) renaming (_*_ to _*ᵣ_)
open import Data.Nat.Coprimality as Coprime using (sym; 1-coprimeTo)
open import Data.Rational.Unnormalised as ℚᵘ using (ℚᵘ; mkℚᵘ)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Nat.Divisibility using (_∣?_)
open import Aletheia.Parser.Combinators using (Parser; pure; fail; _>>=_; _<$>_; _<|>_; _*>_; _<*_; satisfy; char; digit; spaces; string; many; some; optional; runParser)
open import Aletheia.Prelude using (lookupByKey)
import Data.Integer.Show as IntShow
open import Data.Nat.Show as ℕShow using (show)

-- ============================================================================
-- JSON DATA TYPES
-- ============================================================================

-- JSON value representation
-- Numbers are represented as rationals (ℚ) to support decimal values
data JSON : Set where
  JNull   : JSON
  JBool   : Bool → JSON
  JNumber : ℚ → JSON
  JString : String → JSON
  JArray  : List JSON → JSON
  JObject : List (String × JSON) → JSON

-- ============================================================================
-- JSON LOOKUP HELPERS
-- ============================================================================

-- Get string value from JSON
getString : JSON → Maybe String
getString (JString s) = just s
getString _ = nothing

-- Get boolean value from JSON
getBool : JSON → Maybe Bool
getBool (JBool b) = just b
getBool _ = nothing

-- Get integer value from JSON (rational must be an integer)
-- Works by checking if numerator is divisible by denominator
-- NOTE: ℚᵘ stores denominator-1, so actual denominator = pattern + 1
getInt : JSON → Maybe ℤ
getInt (JNumber r) = checkInteger (Rat.toℚᵘ r)
  where
    -- Divide integer by suc n (automatically proves NonZero)
    divideInteger : ℤ → ℕ → ℤ
    divideInteger (+ m) zero = + m  -- Denominator is 1, return as-is
    divideInteger -[1+ m ] zero = -[1+ m ]  -- Denominator is 1, return as-is
    divideInteger (+ m) (suc n) = + (m Data.Nat./ (suc (suc n)))
    divideInteger -[1+ m ] (suc n) = -[1+ (m Data.Nat./ (suc (suc n))) ]

    checkInteger : ℚᵘ → Maybe ℤ
    checkInteger (ℚᵘ.mkℚᵘ num denom-1) with (suc denom-1) ∣? ∣ num ∣
    ... | yes _ = just (divideInteger num denom-1)
    ... | no _ = nothing
getInt _ = nothing

-- Convert ℕ to ℚ using mkℚ directly (bypasses GCD normalization in _/_).
-- This allows toℚᵘ to reduce by definition: toℚᵘ (mkℚ (+ n) 0 _) = mkℚᵘ (+ n) 0
-- Critical for roundtrip proofs of metric operators and DBC formatter.
ℕtoℚ : ℕ → ℚ
ℕtoℚ n = mkℚ (+ n) 0 (Coprime.sym (1-coprimeTo n))

-- Extract natural number from JSON (rational must be positive integer)
getNat : JSON → Maybe ℕ
getNat (JNumber r) = extractNat (getInt (JNumber r))
  where
    extractNat : Maybe ℤ → Maybe ℕ
    extractNat (just (+ n)) = just n
    extractNat _ = nothing
getNat _ = nothing

-- Get rational value from JSON (supports both decimal and object formats)
-- Accepts: JNumber (direct rational) or {"numerator": n, "denominator": d}
getRational : JSON → Maybe ℚ
getRational (JNumber r) = just r
getRational (JObject fields) =
  lookupByKey "numerator" fields >>=ₘ λ numJSON →
  getInt numJSON >>=ₘ λ num →
  lookupByKey "denominator" fields >>=ₘ λ denomJSON →
  getNat denomJSON >>=ₘ λ where
    zero    → nothing
    (suc d) → just (num / suc d)
getRational _ = nothing

-- Get array value from JSON
getArray : JSON → Maybe (List JSON)
getArray (JArray xs) = just xs
getArray _ = nothing

-- Get object value from JSON
getObject : JSON → Maybe (List (String × JSON))
getObject (JObject fields) = just fields
getObject _ = nothing

-- Generic lookup combinator: lookup key, then extract with given function
-- This pattern is repeated for all typed lookups, so we factor it out
private
  lookupWith : {A : Set} → (JSON → Maybe A) → String → List (String × JSON) → Maybe A
  lookupWith extract key obj with lookupByKey key obj
  ... | nothing = nothing
  ... | just v = extract v

-- Typed lookup helpers (all use the generic combinator)
lookupString : String → List (String × JSON) → Maybe String
lookupString = lookupWith getString

lookupBool : String → List (String × JSON) → Maybe Bool
lookupBool = lookupWith getBool

lookupInt : String → List (String × JSON) → Maybe ℤ
lookupInt = lookupWith getInt

lookupNat : String → List (String × JSON) → Maybe ℕ
lookupNat = lookupWith getNat

lookupRational : String → List (String × JSON) → Maybe ℚ
lookupRational = lookupWith getRational

lookupArray : String → List (String × JSON) → Maybe (List JSON)
lookupArray = lookupWith getArray

lookupObject : String → List (String × JSON) → Maybe (List (String × JSON))
lookupObject = lookupWith getObject

-- ============================================================================
-- JSON FORMATTER (Structurally recursive on JSON)
-- ============================================================================

-- Format JSON as string (structurally recursive on JSON data type)
-- DESIGN: Escape sequences intentionally unsupported. The Aletheia protocol uses
--         a constrained JSON subset where strings contain no quotes or escape chars.
--         This simplifies both code and proofs without limiting protocol functionality.
-- Format a rational: integers as decimal notation, non-integers as object
formatRational : ℚ → String
formatRational r with Rat.toℚᵘ r
... | ℚᵘ.mkℚᵘ num zero =
      -- Denominator is 1, format as integer
      IntShow.show num
... | ℚᵘ.mkℚᵘ num (suc denom-1) =
      -- Denominator > 1, format as object for exact representation
      "{\"numerator\": " ++ₛ IntShow.show num ++ₛ
      ", \"denominator\": " ++ₛ ℕShow.show (suc (suc denom-1)) ++ₛ "}"

formatJSON : JSON → String
formatJSON JNull = "null"
formatJSON (JBool true) = "true"
formatJSON (JBool false) = "false"
formatJSON (JNumber n) = formatRational n
formatJSON (JString s) = "\"" ++ₛ s ++ₛ "\""
formatJSON (JArray xs) = "[" ++ₛ formatJSONList xs ++ₛ"]"
  where
    formatJSONList : List JSON → String
    formatJSONList [] = ""
    formatJSONList (x ∷ []) = formatJSON x
    formatJSONList (x ∷ xs) = formatJSON x ++ₛ ", " ++ₛ formatJSONList xs
formatJSON (JObject fields) = "{" ++ₛ formatFields fields ++ₛ"}"
  where
    formatField : String × JSON → String
    formatField (key , val) = "\"" ++ₛ key ++ₛ"\": " ++ₛ formatJSON val

    formatFields : List (String × JSON) → String
    formatFields [] = ""
    formatFields (f ∷ []) = formatField f
    formatFields (f ∷ fs) = formatField f ++ₛ ", " ++ₛ formatFields fs

-- ============================================================================
-- JSON PARSER (Uses parser combinators which are structurally recursive)
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

-- Parse JSON primitives
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
fromString input = map proj₁ (runParser parseJSON (toList input))
