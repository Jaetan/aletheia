{-# OPTIONS --safe --without-K #-}

module Aletheia.DBC.ParserTraced where

open import Aletheia.DBC.Types
open import Aletheia.DBC.Parser using (parseMessage; quotedString; natural; parseDBC; keyValue; hexNumber)
open import Aletheia.Parser.Combinators using (Parser; runParser; atIndent; string; withBaseIndent; _>>=_; _*>_; pure; char; newline)
open import Aletheia.Parser.Tracing
open import Data.String as String using (String; toList; fromList)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Char using (Char)
open import Data.Nat using (ℕ; _+_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)

-- Traced version of parseDBC with detailed instrumentation
parseDBCTraced : ℕ → List Char → TracedResult DBC
parseDBCTraced pos input =
  traced nothing
    (Message "→ Entering parseDBCTraced" ∷
     Message (String._++_ "  Input starts with: " (preview 40 input)) ∷
     Message "  Attempting withBaseIndent..." ∷
     Message "  Step 1: Skip empty lines" ∷ [])

-- Simpler traced parser - just trace the key steps
parseDBCSimple : List Char → Maybe DBC × String
parseDBCSimple input =
  let msg1 = String._++_ (String._++_ "[1] Input: " (preview 30 input)) "\n"

      -- Try parsing version
      versionResult = runParser (atIndent 0 (keyValue "version" quotedString)) input
      msg2 = case versionResult of λ where
        nothing → "[2] ✗ Failed to parse version at indent 0\n"
        (just _) → "[2] ✓ Parsed version at indent 0\n"

      -- Try with base indent 2
      version2Result = runParser (atIndent 2 (keyValue "version" quotedString)) input
      msg3 = case version2Result of λ where
        nothing → "[3] ✗ Failed to parse version at indent 2\n"
        (just _) → "[3] ✓ Parsed version at indent 2\n"

      -- Try just parsing "version"
      versionStrResult = runParser (string "version") input
      msg4 = case versionStrResult of λ where
        nothing → "[4] ✗ Failed to parse string 'version'\n"
        (just _) → "[4] ✓ Parsed string 'version'\n"

      -- Test parsing up to "id: 0x100"
      test5 = runParser
        (withBaseIndent λ base →
          atIndent base (keyValue "version" quotedString) *>
          newline *> newline *>
          atIndent base (string "messages:") *>
          newline *>
          atIndent (base + 2) (char '-' *> char ' ' *> keyValue "id" hexNumber))
        input
      msg5 = case test5 of λ where
        nothing → "[5] ✗ Failed parsing 'id: 0x100'\n"
        (just _) → "[5] ✓ Parsed 'id: 0x100'\n"

      -- Test parsing id + name
      test6 = runParser
        (withBaseIndent λ base →
          let fieldIndent = base + 4 in
          atIndent base (keyValue "version" quotedString) *>
          newline *> newline *>
          atIndent base (string "messages:") *>
          newline *>
          atIndent (base + 2) (char '-' *> char ' ' *> keyValue "id" hexNumber) *>
          newline *>
          atIndent fieldIndent (keyValue "name" quotedString))
        input
      msg6 = case test6 of λ where
        nothing → "[6] ✗ Failed parsing id + name\n"
        (just _) → "[6] ✓ Parsed id + name\n"

      -- Test parsing id + name + dlc + sender
      test7 = runParser
        (withBaseIndent λ base →
          let fieldIndent = base + 4 in
          atIndent base (keyValue "version" quotedString) *>
          newline *> newline *>
          atIndent base (string "messages:") *>
          newline *>
          atIndent (base + 2) (char '-' *> char ' ' *> keyValue "id" hexNumber) *>
          newline *>
          atIndent fieldIndent (keyValue "name" quotedString) *>
          newline *>
          atIndent fieldIndent (keyValue "dlc" natural) *>
          newline *>
          atIndent fieldIndent (keyValue "sender" quotedString))
        input
      msg7 = case test7 of λ where
        nothing → "[7] ✗ Failed parsing id + name + dlc + sender\n"
        (just _) → "[7] ✓ Parsed id + name + dlc + sender\n"

      -- Test parsing up to "signals:" header
      test8 = runParser
        (withBaseIndent λ base →
          let fieldIndent = base + 4 in
          atIndent base (keyValue "version" quotedString) *>
          newline *> newline *>
          atIndent base (string "messages:") *>
          newline *>
          atIndent (base + 2) (char '-' *> char ' ' *> keyValue "id" hexNumber) *>
          newline *>
          atIndent fieldIndent (keyValue "name" quotedString) *>
          newline *>
          atIndent fieldIndent (keyValue "dlc" natural) *>
          newline *>
          atIndent fieldIndent (keyValue "sender" quotedString) *>
          newline *>
          atIndent fieldIndent (string "signals:"))
        input
      msg8 = case test8 of λ where
        nothing → "[8] ✗ Failed parsing up to 'signals:'\n"
        (just _) → "[8] ✓ Parsed up to 'signals:'\n"

      -- Test parsing signals: + first signal name
      test9 = runParser
        (withBaseIndent λ base →
          let fieldIndent = base + 4
              signalIndent = base + 6
          in
          atIndent base (keyValue "version" quotedString) *>
          newline *> newline *>
          atIndent base (string "messages:") *>
          newline *>
          atIndent (base + 2) (char '-' *> char ' ' *> keyValue "id" hexNumber) *>
          newline *>
          atIndent fieldIndent (keyValue "name" quotedString) *>
          newline *>
          atIndent fieldIndent (keyValue "dlc" natural) *>
          newline *>
          atIndent fieldIndent (keyValue "sender" quotedString) *>
          newline *>
          atIndent fieldIndent (string "signals:") *>
          newline *>
          atIndent signalIndent (char '-' *> char ' ' *> keyValue "name" quotedString))
        input
      msg9 = case test9 of λ where
        nothing → "[9] ✗ Failed parsing first signal name\n"
        (just _) → "[9] ✓ Parsed first signal name\n"

      -- Test parsing signal: name + start_bit + bit_length
      test10 = runParser
        (withBaseIndent λ base →
          let fieldIndent = base + 4
              signalIndent = base + 6
              signalFieldIndent = base + 8
          in
          atIndent base (keyValue "version" quotedString) *>
          newline *> newline *>
          atIndent base (string "messages:") *>
          newline *>
          atIndent (base + 2) (char '-' *> char ' ' *> keyValue "id" hexNumber) *>
          newline *>
          atIndent fieldIndent (keyValue "name" quotedString) *>
          newline *>
          atIndent fieldIndent (keyValue "dlc" natural) *>
          newline *>
          atIndent fieldIndent (keyValue "sender" quotedString) *>
          newline *>
          atIndent fieldIndent (string "signals:") *>
          newline *>
          atIndent signalIndent (char '-' *> char ' ' *> keyValue "name" quotedString) *>
          newline *>
          atIndent signalFieldIndent (keyValue "start_bit" natural) *>
          newline *>
          atIndent signalFieldIndent (keyValue "bit_length" natural))
        input
      msg10 = case test10 of λ where
        nothing → "[10] ✗ Failed parsing signal name + start_bit + bit_length\n"
        (just _) → "[10] ✓ Parsed signal name + start_bit + bit_length\n"

      trace = msg1 String.++ msg2 String.++ msg3 String.++ msg4 String.++ msg5 String.++ msg6 String.++ msg7 String.++ msg8 String.++ msg9 String.++ msg10
  in (nothing , trace)
  where
    case_of_ : ∀ {A B : Set} → A → (A → B) → B
    case x of f = f x
