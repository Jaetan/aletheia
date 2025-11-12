{-# OPTIONS --safe --without-K #-}

-- Minimal test to debug what parseCommandType returns
module test_command_parser where

open import Data.String using (String; toList; fromList)
open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)
open import Aletheia.Parser.Combinators
open import Aletheia.Protocol.Parser using (parseCommandType)
open import Data.Char using (Char)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Test input strings
testEcho : String
testEcho = "command: \"Echo\""

testParseDB C : String
testParseDBC = "command: \"ParseDBC\""

testExtractSignal : String
testExtractSignal = "command: \"ExtractSignal\""

testInjectSignal : String
testInjectSignal = "command: \"InjectSignal\""

-- Test function to run parser and return result
testParser : String → Maybe String
testParser input = runParser parseCommandType (toList input)

-- Expected results (for manual verification)
-- testParser testEcho should return: just "Echo"
-- testParser testParseDBC should return: just "ParseDBC"
-- testParser testExtractSignal should return: just "ExtractSignal"
-- testParser testInjectSignal should return: just "InjectSignal"
