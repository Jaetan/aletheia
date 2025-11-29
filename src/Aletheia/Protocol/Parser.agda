{-# OPTIONS --safe --without-K #-}

module Aletheia.Protocol.Parser where

open import Aletheia.Protocol.Command
open import Aletheia.Parser.Combinators
open import Data.String using (String; fromList; _++_; toList)
open import Data.List using (List; _∷_; [])
open import Data.Char using (Char)
open import Data.Bool using (Bool; not)
open import Data.Rational using (ℚ; mkℚ)
open import Data.Integer using (ℤ; +_)
open import Data.Vec using (Vec; _∷_; [])
open import Data.Fin using (Fin; #_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _+_; _*_; suc; zero)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Char using (_≟_)
open import Function using (_∘_)
open import Aletheia.CAN.Frame using (Byte)
-- Import rational parser from DBC module (reuse the decimal → rational conversion)
open import Aletheia.DBC.Parser using (rational)

-- ============================================================================
-- YAML PRIMITIVES (reuse from DBC parser patterns)
-- ============================================================================

-- Pre-computed character codes for efficiency
private
  code-0 : ℕ
  code-0 = 48

  code-A : ℕ
  code-A = 65

  code-a : ℕ
  code-a = 97

-- Convert hex character ('0'-'9', 'A'-'F', 'a'-'f') to natural number (0-15)
hexCharToNat : Char → Maybe ℕ
hexCharToNat c with Data.Char.toℕ c
... | n with (48 Data.Nat.≤ᵇ n) Data.Bool.∧ (n Data.Nat.≤ᵇ 57)  -- '0'-'9'
...   | Data.Bool.true = just (n Data.Nat.∸ 48)
...   | Data.Bool.false with (65 Data.Nat.≤ᵇ n) Data.Bool.∧ (n Data.Nat.≤ᵇ 70)  -- 'A'-'F'
...     | Data.Bool.true = just (n Data.Nat.∸ 55)
...     | Data.Bool.false with (97 Data.Nat.≤ᵇ n) Data.Bool.∧ (n Data.Nat.≤ᵇ 102)  -- 'a'-'f'
...       | Data.Bool.true = just (n Data.Nat.∸ 87)
...       | Data.Bool.false = nothing
  where
    open import Data.Nat using (_≤ᵇ_; _∸_)
    open import Data.Bool using (_∧_)

-- Parse a string in double quotes
quotedString : Parser String
quotedString =
  fromList <$> (char '"' *> many (satisfy λ c → not ⌊ c ≟ '"' ⌋) <* char '"')

-- Parse a key-value pair: "key: value"
keyValue : String → Parser String
keyValue key =
  string key *> char ':' *> spaces *> quotedString

-- Parse "command: CommandName"
parseCommandType : Parser String
parseCommandType = keyValue "command"

-- ============================================================================
-- INDENTATION STRIPPING (for YAML literal blocks)
-- ============================================================================

private
  open import Data.List.Base using (foldr; map)

  -- Count leading spaces in a list of chars (pure function)
  leadingSpaces : List Char → ℕ
  leadingSpaces [] = 0
  leadingSpaces (' ' ∷ cs) = suc (leadingSpaces cs)
  leadingSpaces (_ ∷ _) = 0

  -- Split list on a character, returning list of lists
  splitOn : Char → List Char → List (List Char)
  splitOn sep = foldr step ([] ∷ [])
    where
      open import Data.Bool using (true; false)
      step : Char → List (List Char) → List (List Char)
      step c [] = (c ∷ []) ∷ []
      step c (curr ∷ rest) with ⌊ c ≟ sep ⌋
      ... | true = [] ∷ (curr ∷ rest)
      ... | false = (c ∷ curr) ∷ rest

  -- Join lists with separator
  joinWith : Char → List (List Char) → List Char
  joinWith sep [] = []
  joinWith sep (x ∷ []) = x
  joinWith sep (x ∷ xs) = x Data.List.++ (sep ∷ joinWith sep xs)

  -- Find first non-empty line and get its indentation
  findIndent : List (List Char) → ℕ
  findIndent [] = 0
  findIndent ([] ∷ rest) = findIndent rest
  findIndent (line ∷ _) = leadingSpaces line

  -- Strip n characters from start of each line
  stripLines : ℕ → List (List Char) → List (List Char)
  stripLines n = map (Data.List.drop n)
    where open import Data.List using (drop)

  -- Strip common indentation from content (YAML literal block style)
  stripIndent : List Char → List Char
  stripIndent content = joinWith '\n' (stripLines indent lines)
    where
      lines = splitOn '\n' content
      indent = findIndent lines

-- Parse multiline YAML content after "key: |"
-- Strips YAML literal block indentation before passing to DBC parser
multilineValue : String → Parser String
multilineValue key =
  (λ chars → fromList (stripIndent chars)) <$>
    (string key *> char ':' *> spaces *> optional (char '|') *> newline *> many anyChar)

-- Parse content between markers
-- Format: key: |\n<content>\n---
multilineSection : String → Parser String
multilineSection key pos input = helper ((string key *> char ':' *> spaces *> optional (char '|') *> newline) pos input)
  where
    open import Data.List using (reverse; length)
    open import Aletheia.Parser.Combinators using (mkResult; position; remaining; value)

    -- Parse until we see \n---\n or end of input
    -- Uses input length as fuel (principled termination)
    contentUntilMarker : Position → List Char → Maybe (ParseResult (List Char))
    contentUntilMarker pos₂ input₂ = go (length input₂) [] pos₂ input₂
      where
        go : ℕ → List Char → Position → List Char → Maybe (ParseResult (List Char))
        go zero acc p i = just (mkResult (reverse acc) p i)  -- Fuel exhausted
        go (suc fuel) acc p i with (newline *> string "---") p i
        ... | just r = just (mkResult (reverse acc) (position r) (remaining r))
        ... | nothing with anyChar p i
        ...   | just r₁ = go fuel (value r₁ ∷ acc) (position r₁) (remaining r₁)
        ...   | nothing = nothing

    helper : Maybe (ParseResult Char) → Maybe (ParseResult String)
    helper nothing = nothing
    helper (just result) with contentUntilMarker (position result) (remaining result)
    ... | nothing = nothing
    ... | just contentResult = just (mkResult (fromList (stripIndent (value contentResult))) (position contentResult) (remaining contentResult))

-- Parse a single hex byte "0xNN" → Fin 256
-- Uses modulo to automatically prove the result is in bounds
hexByte : Parser Byte
hexByte =
  string "0x" *>
  (parseTwo <$> anyChar <*> anyChar)
  where
    open import Data.Nat.DivMod using (_mod_)

    parseTwo : Char → Char → Byte
    parseTwo hi lo with hexCharToNat hi | hexCharToNat lo
    ... | just h | just l = (h * 16 + l) mod 256  -- Modulo returns Fin 256 automatically!
    ... | just h | nothing = Data.Fin.zero  -- Debug: low nibble failed
    ... | nothing | just l = Data.Fin.zero  -- Debug: high nibble failed
    ... | nothing | nothing = Data.Fin.zero  -- Debug: both failed

-- Parse exactly 8 hex bytes separated by spaces: "0x12 0x34 0x56 0x78 0x9A 0xBC 0xDE 0xF0"
-- Returns Vec Byte 8 (exactly 8 bytes, no more, no less)
byteArray : Parser (Vec Byte 8)
byteArray =
  buildVec
    <$> hexByte <* spaces
    <*> hexByte <* spaces
    <*> hexByte <* spaces
    <*> hexByte <* spaces
    <*> hexByte <* spaces
    <*> hexByte <* spaces
    <*> hexByte <* spaces
    <*> hexByte
  where
    -- Build Vec Byte 8 from 8 individual bytes
    buildVec : Byte → Byte → Byte → Byte → Byte → Byte → Byte → Byte → Vec Byte 8
    buildVec b0 b1 b2 b3 b4 b5 b6 b7 = b0 Data.Vec.∷ b1 Data.Vec.∷ b2 Data.Vec.∷ b3 Data.Vec.∷ b4 Data.Vec.∷ b5 Data.Vec.∷ b6 Data.Vec.∷ b7 Data.Vec.∷ Data.Vec.[]

-- Parse "frame: 0x00 0x01 ..." key-value pair
parseFrame : Parser (Vec Byte 8)
parseFrame =
  string "frame" *> char ':' *> spaces *> byteArray

-- Parse "value: 123.45" key-value pair for signal values
parseValue : Parser ℚ
parseValue =
  string "value" *> char ':' *> spaces *> rational

-- ============================================================================
-- COMMAND PARSER
-- ============================================================================

-- Main command parser - OPTION C: Complete restructure
--
-- DEBUG HISTORY: Spent ~3 hours debugging routing issues:
-- - Attempt 1: if-then-else with _==_ → routed to Echo
-- - Attempt 2: <|> with separate parsers → routed to Echo
-- - Attempt 3: `with` pattern matching on Dec → routed to Echo
-- - Attempt 4: Explicit alternatives → STILL routed to Echo (ParseDBC worked, others didn't)
--
-- ROOT CAUSE HYPOTHESIS: Parser combinator state/backtracking issue that's not obvious
--
-- OPTION C STRATEGY: Parse entire command manually, dispatch explicitly
-- Goal: "Get every intelligent bit inside Agda" - so we'll make it maximally explicit
parseCommand : Parser Command
parseCommand =
  -- Step 1: Parse command type literally, character by character
  parseCommandLiteral >>= dispatch
  where
    -- Parse the entire "command: \"Name\"" structure and return Name
    parseCommandLiteral : Parser String
    parseCommandLiteral =
      string "command" *>
      char ':' *>
      spaces *>
      quotedString  -- This returns the command name without quotes

    -- Explicitly dispatch based on EXACT string match
    -- No clever parser combinators, just direct string comparison
    dispatch : String → Parser Command
    dispatch cmdName = newline *> route cmdName
      where
        open import Data.String.Properties using (_==_)
        open import Data.Bool using (Bool; true; false)

        -- Body parsers (after command type is determined)
        parseParseDBCBody : Parser Command
        parseParseDBCBody = ParseDBC <$> multilineValue "yaml"

        parseExtractSignalBody : Parser Command
        parseExtractSignalBody =
          mkExtractSignal
            <$> (keyValue "message" <* newline)
            <*> (keyValue "signal" <* newline)
            <*> (parseFrame <* newline)
            <*> multilineValue "dbc_yaml"
          where
            mkExtractSignal : String → String → Vec Byte 8 → String → Command
            mkExtractSignal msgName sigName frameBytes dbcYaml =
              ExtractSignal dbcYaml msgName sigName frameBytes

        parseInjectSignalBody : Parser Command
        parseInjectSignalBody =
          mkInjectSignal
            <$> (keyValue "message" <* newline)
            <*> (keyValue "signal" <* newline)
            <*> (parseValue <* newline)
            <*> (parseFrame <* newline)
            <*> multilineValue "dbc_yaml"
          where
            mkInjectSignal : String → String → ℚ → Vec Byte 8 → String → Command
            mkInjectSignal msgName sigName sigValue frameBytes dbcYaml =
              InjectSignal dbcYaml msgName sigName sigValue frameBytes

        parseCheckLTLBody : Parser Command
        parseCheckLTLBody =
          mkCheckLTL
            <$> (multilineSection "dbc_yaml" <* newline)
            <*> (multilineSection "trace_yaml" <* newline)
            <*> multilineValue "property_yaml"
          where
            mkCheckLTL : String → String → String → Command
            mkCheckLTL dbcYaml traceYaml propertyYaml =
              CheckLTL dbcYaml traceYaml propertyYaml

        -- Route function (uses the parsers defined above)
        -- Pattern match on Bool result of string equality
        route : String → Parser Command
        route name with name == "ParseDBC"
        ... | true  = parseParseDBCBody
        ... | false with name == "ExtractSignal"
        ...     | true  = parseExtractSignalBody
        ...     | false with name == "InjectSignal"
        ...       | true  = parseInjectSignalBody
        ...       | false with name == "CheckLTL"
        ...         | true  = parseCheckLTLBody
        ...         | false = fail  -- Unknown command
