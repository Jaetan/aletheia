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
open import Data.Nat using (ℕ; _+_; _*_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Char using (_≟_)
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

-- Parse newline
newline : Parser Char
newline = char '\n'

-- Parse a key-value pair: "key: value"
keyValue : String → Parser String
keyValue key =
  string key *> char ':' *> spaces *> quotedString

-- Parse "command: CommandName"
parseCommandType : Parser String
parseCommandType = keyValue "command"

-- Parse multiline string after "yaml:" or "dbc_yaml:"
-- For Phase 1, we'll use a simplified approach: read until end of input
multilineValue : String → Parser String
multilineValue key =
  string key *> char ':' *> spaces *>
  (fromList <$> many anyChar)

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
    ... | _ | _ = Data.Fin.zero  -- Fallback to 0 for invalid hex (should not happen for valid input)

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
-- COMMAND PARSERS
-- ============================================================================

-- Parse Echo command: command: "Echo"\nmessage: "text"
parseEcho : Parser Command
parseEcho =
  mkEcho <$> (parseCommandType <* newline) <*> keyValue "message"
  where
    mkEcho : String → String → Command
    mkEcho _ msg = Echo msg

-- Parse ParseDBC command: command: "ParseDBC"\nyaml: ...
parseParseDBC : Parser Command
parseParseDBC =
  mkParseDBC <$> (parseCommandType <* newline) <*> multilineValue "yaml"
  where
    mkParseDBC : String → String → Command
    mkParseDBC _ yaml = ParseDBC yaml

-- Parse ExtractSignal command:
-- command: "ExtractSignal"
-- dbc_yaml: |
--   ...
-- message: "MessageName"
-- signal: "SignalName"
-- frame: "0x00 0x01 0x02 0x03 0x04 0x05 0x06 0x07"
parseExtractSignal : Parser Command
parseExtractSignal =
  mkExtractSignal
    <$> (parseCommandType <* newline)
    <*> (multilineValue "dbc_yaml" <* newline)
    <*> (keyValue "message" <* newline)
    <*> (keyValue "signal" <* newline)
    <*> parseFrame
  where
    mkExtractSignal : String → String → String → String → Vec Byte 8 → Command
    mkExtractSignal _ dbcYaml msgName sigName frameBytes =
      ExtractSignal dbcYaml msgName sigName frameBytes

-- Parse InjectSignal command:
-- command: "InjectSignal"
-- dbc_yaml: |
--   ...
-- message: "MessageName"
-- signal: "SignalName"
-- value: 123.45
-- frame: "0x00 0x01 0x02 0x03 0x04 0x05 0x06 0x07"
parseInjectSignal : Parser Command
parseInjectSignal =
  mkInjectSignal
    <$> (parseCommandType <* newline)
    <*> (multilineValue "dbc_yaml" <* newline)
    <*> (keyValue "message" <* newline)
    <*> (keyValue "signal" <* newline)
    <*> (parseValue <* newline)
    <*> parseFrame
  where
    mkInjectSignal : String → String → String → String → ℚ → Vec Byte 8 → Command
    mkInjectSignal _ dbcYaml msgName sigName sigValue frameBytes =
      InjectSignal dbcYaml msgName sigName sigValue frameBytes

-- Main command parser - tries each command type
-- Order matters: try more specific parsers first
parseCommand : Parser Command
parseCommand =
  parseEcho <|> parseParseDBC <|> parseExtractSignal <|> parseInjectSignal
