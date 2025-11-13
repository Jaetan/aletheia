{-# OPTIONS --safe --without-K #-}

module Aletheia.DebugDBC where

open import Aletheia.DBC.Parser using (parseDBC)
open import Aletheia.DBC.ParserTraced using (parseDBCSimple)
open import Aletheia.DBC.Types
open import Aletheia.Parser.Tracing
open import Aletheia.Parser.Combinators using (Parser; runParser)
open import Data.String using (String; toList; _++_)
open import Data.List using (List)
open import Data.Char using (Char)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; proj₁; proj₂)

-- | Test parseDBC with detailed tracing
testParseDBC : String → String
testParseDBC input =
  let res = parseDBCSimple (toList input)
      result = proj₁ res
      trace = proj₂ res
  in formatResult result trace
  where
    formatResult : Maybe DBC → String → String
    formatResult nothing trace = "PARSE FAILED\n\nTrace:\n" ++ trace
    formatResult (just _) trace = "PARSE SUCCESS\n\nTrace:\n" ++ trace

-- | Test input: 2-space indented DBC YAML
testInput2Space : String
testInput2Space = "  version: \"1.0\"\n\n  messages:\n    - id: 0x100\n      name: \"Test\"\n      dlc: 8\n      sender: \"ECU\"\n      signals:\n        - name: \"TestSignal\"\n          start_bit: 0\n          bit_length: 8\n          byte_order: \"little_endian\"\n          value_type: \"unsigned\"\n          factor: 1\n          offset: 0\n          minimum: 0\n          maximum: 255\n          unit: \"\"\n"

-- | Test input: no indentation (known to work)
testInputNoIndent : String
testInputNoIndent = "version: \"1.0\"\n\nmessages:\n  - id: 0x100\n    name: \"Test\"\n    dlc: 8\n    sender: \"ECU\"\n    signals:\n      - name: \"TestSignal\"\n        start_bit: 0\n        bit_length: 8\n        byte_order: \"little_endian\"\n        value_type: \"unsigned\"\n        factor: 1\n        offset: 0\n        minimum: 0\n        maximum: 255\n        unit: \"\"\n"

-- | Main debug function  - run both tests
debugBoth : String
debugBoth =
  "=== TEST 1: No indent (should work) ===\n" ++
  testParseDBC testInputNoIndent ++
  "\n\n=== TEST 2: 2-space indent (currently fails) ===\n" ++
  testParseDBC testInput2Space
