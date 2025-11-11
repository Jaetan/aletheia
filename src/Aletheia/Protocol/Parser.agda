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

-- For Phase 1, we'll implement just Echo and ParseDBC
-- ExtractSignal and InjectSignal require parsing byte arrays and rationals,
-- which we'll defer for now

-- Main command parser - tries each command type
parseCommand : Parser Command
parseCommand =
  parseEcho <|> parseParseDBC
