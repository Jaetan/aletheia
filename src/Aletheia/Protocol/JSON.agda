{-# OPTIONS --safe --without-K #-}

-- JSON data types, parser, and formatter with rational number support.
-- Rationals are represented as {"numerator": n, "denominator": d} objects.

module Aletheia.Protocol.JSON where

open import Data.String using (String; _≟_; toList; fromList) renaming (_++_ to _++S_)
open import Data.List using (List; []; _∷_; map; foldr) renaming (_++_ to _++L_)
open import Data.Char using (Char)
open import Data.Bool using (Bool; true; false; if_then_else_; not; _∨_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _*_; _+_; _∸_)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Rational as Rat using (ℚ; mkℚ; _/_; toℚᵘ)
open import Data.Rational.Unnormalised as ℚᵘ using (ℚᵘ; mkℚᵘ; ↥_; ↧_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Function using (_∘_; id)
open import Aletheia.Parser.Combinators
open import Data.Integer.Show as IntShow using ()
open import Data.Rational.Show as RatShow using ()

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

-- Look up a key in a JSON object
lookup : String → List (String × JSON) → Maybe JSON
lookup key [] = nothing
lookup key ((k , v) ∷ rest) =
  if ⌊ k ≟ key ⌋ then just v else lookup key rest

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
    open import Data.Nat.Divisibility using (_∣?_)
    open import Data.Integer using (+_; -[1+_]; ∣_∣)
    open import Relation.Nullary using (yes; no)

    -- Divide integer by suc n (automatically proves NonZero)
    divideInteger : ℤ → ℕ → ℤ
    divideInteger (+ m) zero = + m  -- Denominator is 1, return as-is
    divideInteger -[1+ m ] zero = -[1+ m ]  -- Denominator is 1, return as-is
    divideInteger (+ m) (Data.Nat.suc n) = + (m Data.Nat./ (Data.Nat.suc (Data.Nat.suc n)))
    divideInteger -[1+ m ] (Data.Nat.suc n) = -[1+ (m Data.Nat./ (Data.Nat.suc (Data.Nat.suc n))) ]

    checkInteger : ℚᵘ → Maybe ℤ
    checkInteger (ℚᵘ.mkℚᵘ num denom-1) with (Data.Nat.suc denom-1) ∣? ∣ num ∣
    ... | yes _ = just (divideInteger num denom-1)
    ... | no _ = nothing
getInt _ = nothing

-- Get natural number value from JSON (for array indices, etc.)
-- Extract natural number from JSON (rational must be positive integer)
getNat : JSON → Maybe ℕ
getNat (JNumber r) = extractNat (getInt (JNumber r))
  where
    extractNat : Maybe ℤ → Maybe ℕ
    extractNat (just (Data.Integer.+ n)) = just n
    extractNat _ = nothing
getNat _ = nothing

-- Get rational value from JSON (supports both decimal and object formats)
-- Accepts: JNumber (direct rational) or {"numerator": n, "denominator": d}
getRational : JSON → Maybe ℚ
getRational (JNumber r) = just r
getRational (JObject fields) = parseRationalObject fields
  where
    parseRationalObject : List (String × JSON) → Maybe ℚ
    parseRationalObject fields with lookup "numerator" fields
    ... | nothing = nothing
    ... | just numJSON with getInt numJSON
    ...   | nothing = nothing
    ...   | just num with lookup "denominator" fields
    ...     | nothing = nothing
    ...     | just denomJSON with getNat denomJSON
    ...       | nothing = nothing
    ...       | just Data.Nat.zero = nothing  -- Denominator cannot be zero
    ...       | just (Data.Nat.suc d) = just (num / (Data.Nat.suc d))  -- NonZero proved by suc
getRational _ = nothing

-- Get array value from JSON
getArray : JSON → Maybe (List JSON)
getArray (JArray xs) = just xs
getArray _ = nothing

-- Get object value from JSON
getObject : JSON → Maybe (List (String × JSON))
getObject (JObject fields) = just fields
getObject _ = nothing

-- Lookup and extract string in one step
lookupString : String → List (String × JSON) → Maybe String
lookupString key obj with lookup key obj
... | nothing = nothing
... | just v = getString v

-- Lookup and extract boolean in one step
lookupBool : String → List (String × JSON) → Maybe Bool
lookupBool key obj with lookup key obj
... | nothing = nothing
... | just v = getBool v

-- Lookup and extract integer in one step
lookupInt : String → List (String × JSON) → Maybe ℤ
lookupInt key obj with lookup key obj
... | nothing = nothing
... | just v = getInt v

-- Lookup and extract natural in one step
lookupNat : String → List (String × JSON) → Maybe ℕ
lookupNat key obj with lookup key obj
... | nothing = nothing
... | just v = getNat v

-- Lookup and extract array in one step
lookupArray : String → List (String × JSON) → Maybe (List JSON)
lookupArray key obj with lookup key obj
... | nothing = nothing
... | just v = getArray v

-- Lookup and extract object in one step
lookupObject : String → List (String × JSON) → Maybe (List (String × JSON))
lookupObject key obj with lookup key obj
... | nothing = nothing
... | just v = getObject v

-- ============================================================================
-- JSON FORMATTER (Structurally recursive on JSON)
-- ============================================================================

-- Escape special characters in strings
escapeChar : Char → String
escapeChar '"'  = "\\\""
escapeChar '\\' = "\\\\"
escapeChar '\n' = "\\n"
escapeChar '\t' = "\\t"
escapeChar c    = fromList (c ∷ [])

escapeString : String → String
escapeString s = foldr _++S_ "" (map escapeChar (toList s))

-- Format JSON as string (structurally recursive on JSON data type)
-- Format a rational as a JSON object with numerator and denominator
formatRational : ℚ → String
formatRational r with Rat.toℚᵘ r
... | ℚᵘ.mkℚᵘ num denom-1 =
      "{\"numerator\": " ++S IntShow.show num ++S
      ", \"denominator\": " ++S ℕShow.show (Data.Nat.suc denom-1) ++S "}"
  where
    open import Data.Nat.Show as ℕShow using (show)

formatJSON : JSON → String
formatJSON JNull = "null"
formatJSON (JBool true) = "true"
formatJSON (JBool false) = "false"
formatJSON (JNumber n) = formatRational n
formatJSON (JString s) = "\"" ++S escapeString s ++S "\""
formatJSON (JArray xs) = "[" ++S formatJSONList xs ++S "]"
  where
    formatJSONList : List JSON → String
    formatJSONList [] = ""
    formatJSONList (x ∷ []) = formatJSON x
    formatJSONList (x ∷ xs) = formatJSON x ++S ", " ++S formatJSONList xs
formatJSON (JObject fields) = "{" ++S formatFields fields ++S "}"
  where
    formatField : String × JSON → String
    formatField (key , val) = "\"" ++S escapeString key ++S "\": " ++S formatJSON val

    formatFields : List (String × JSON) → String
    formatFields [] = ""
    formatFields (f ∷ []) = formatField f
    formatFields (f ∷ fs) = formatField f ++S ", " ++S formatFields fs

-- ============================================================================
-- JSON PARSER (Uses parser combinators which are structurally recursive)
-- ============================================================================

-- isDigit is already defined in Parser.Combinators, use that

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
  pure (foldl (λ acc d → acc Data.Nat.* 10 Data.Nat.+ digitToNat d) 0 digits)
  where
    open import Data.Nat using (_*_; _+_)
    foldl = Data.List.foldl

-- Parse integer (with optional minus sign)
parseInt : Parser ℤ
parseInt = do
  neg ← optional (char '-')
  n ← parseNatural
  parseIntHelper neg n
  where
    parseIntHelper : Maybe Char → ℕ → Parser ℤ
    parseIntHelper nothing n = pure (+ n)
    parseIntHelper (just _) Data.Nat.zero = pure (+ 0)
    parseIntHelper (just _) (Data.Nat.suc n') = pure (-[1+ n' ])

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

-- Parse a rational number (handles integers and decimals)
-- Examples: "42" → 42/1, "3.14" → 314/100, "-1.5" → -3/2
parseRational : Parser ℚ
parseRational = buildNumber <$> parseInt <*> optional (char '.' *> some digit)
  where
    open import Data.Char using (toℕ)
    open import Data.List using (foldl; length)

    -- Compute 10^n, returns suc n to prove NonZero
    power10 : ℕ → ℕ
    power10 zero = suc 0
    power10 (suc n) with power10 n
    ... | suc m = suc (9 + m * 10)
    ... | zero = suc 0  -- Unreachable but needed for coverage

    charToDigit : Char → ℕ
    charToDigit c = toℕ c ∸ 48

    parseDigitList : List Char → ℕ
    parseDigitList = foldl (λ acc d → acc * 10 + charToDigit d) 0

    buildNumber : ℤ → Maybe (List Char) → ℚ
    buildNumber intPart nothing = intPart / 1
    buildNumber intPart (just fracChars) with power10 (length fracChars)
    ... | suc scale =
      let fracValue = parseDigitList fracChars
      in ((intPart Data.Integer.* (+ suc scale)) Data.Integer.+ (+ fracValue)) / suc scale
    ... | zero = intPart / 1  -- Unreachable but needed for coverage

parseNumber : Parser JSON
parseNumber = JNumber <$> parseRational

-- Parse a single character inside a JSON string (handles escape sequences)
parseStringChar : Parser Char
parseStringChar = parseEscaped <|> parseNormal
  where
    parseEscaped : Parser Char
    parseEscaped = do
      _ ← char '\\'
      c ← anyChar
      pure (if ⌊ c Data.Char.≟ '"' ⌋ then '"'
            else if ⌊ c Data.Char.≟ '\\' ⌋ then '\\'
            else if ⌊ c Data.Char.≟ 'n' ⌋ then '\n'
            else if ⌊ c Data.Char.≟ 't' ⌋ then '\t'
            else c)  -- Unknown escape, keep as-is

    parseNormal : Parser Char
    parseNormal = satisfy (λ c → not (⌊ c Data.Char.≟ '"' ⌋ ∨ ⌊ c Data.Char.≟ '\\' ⌋))

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
parseJSON pos input = parseJSONHelper (Data.List.length input) pos input

-- ============================================================================
-- HELPER: RUN JSON PARSER
-- ============================================================================

-- Parse JSON from string
fromString : String → Maybe JSON
fromString input = Data.Maybe.map proj₁ (runParser parseJSON (toList input))
