{-# OPTIONS --safe --without-K #-}

module Aletheia.DBC.Parser where

open import Aletheia.DBC.Types
open import Aletheia.Parser.Combinators
open import Aletheia.CAN.Frame
open import Aletheia.CAN.Signal
open import Aletheia.CAN.Endianness
open import Data.List using (List; []; _∷_; map)
open import Data.String as String using (String; toList; fromList)
open import Data.Char using (Char)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _+_; _*_; zero; suc)
open import Data.Fin using (Fin; fromℕ)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Rational using (ℚ; mkℚ)
open import Data.Integer as ℤ using (ℤ; +_; -[1+_])
open import Data.Product using (_×_; _,_)
open import Function using (_∘_)

-- ============================================================================
-- YAML PRIMITIVE PARSERS
-- ============================================================================

-- Parse a quoted string
quotedString : Parser String
quotedString =
  char '"' *>
  (fromList <$> many (noneOf ('"' ∷ []))) <*
  char '"'

-- Parse an unquoted identifier/string (letters, digits, underscore, hyphen)
identifier : Parser String
identifier =
  fromList <$> some (satisfy isIdentChar)
  where
    isIdentChar : Char → Bool
    isIdentChar c = isAlphaNum c ∨ (c Data.Char.≈ᵇ '_') ∨ (c Data.Char.≈ᵇ '-')
      where
        open import Data.Char using (_≈ᵇ_)
        open import Data.Bool using (_∨_)

-- Parse either quoted or unquoted string
yamlString : Parser String
yamlString = quotedString <|> identifier

-- Parse a natural number
natural : Parser ℕ
natural = parseDigits <$> some digit
  where
    parseDigits : List Char → ℕ
    parseDigits = Data.List.foldl (λ acc d → acc * 10 + charToDigit d) 0
      where
        open import Data.List using (foldl)
        charToDigit : Char → ℕ
        charToDigit c = Data.Char.toℕ c Data.Nat.∸ 48
          where
            open import Data.Char using (toℕ)
            open import Data.Nat using (_∸_)

-- Parse a hexadecimal number (0xNN format)
hexNumber : Parser ℕ
hexNumber =
  string "0x" *>
  (parseHexDigits <$> some hexDigit)
  where
    hexDigit : Parser Char
    hexDigit = oneOf ('0' ∷ '1' ∷ '2' ∷ '3' ∷ '4' ∷ '5' ∷ '6' ∷ '7' ∷ '8' ∷ '9' ∷
                      'a' ∷ 'b' ∷ 'c' ∷ 'd' ∷ 'e' ∷ 'f' ∷
                      'A' ∷ 'B' ∷ 'C' ∷ 'D' ∷ 'E' ∷ 'F' ∷ [])

    parseHexDigits : List Char → ℕ
    parseHexDigits = Data.List.foldl (λ acc d → acc * 16 + hexCharToNat d) 0
      where
        open import Data.List using (foldl)
        hexCharToNat : Char → ℕ
        hexCharToNat c =
          let n = Data.Char.toℕ c
          in if (48 Data.Nat.≤ᵇ n) Data.Bool.∧ (n Data.Nat.≤ᵇ 57)  -- '0'-'9'
             then n Data.Nat.∸ 48
             else if (97 Data.Nat.≤ᵇ n) Data.Bool.∧ (n Data.Nat.≤ᵇ 102)  -- 'a'-'f'
                  then n Data.Nat.∸ 87
                  else n Data.Nat.∸ 55  -- 'A'-'F'
          where
            open import Data.Char using (toℕ)
            open import Data.Nat using (_∸_; _≤ᵇ_)
            open import Data.Bool using (_∧_)

-- Parse a signed integer
integer : Parser ℤ
integer =
  ((char '-' *> (negateℤ <$> natural)) <|> ((λ n → + n) <$> natural))
  where
    negateℤ : ℕ → ℤ
    negateℤ zero = + 0
    negateℤ (suc n) = -[1+ n ]

-- Parse a rational number (handles "1.5", "0.25", etc.)
-- TODO Phase 5: Full implementation with NonZero proofs for divisor
-- Current: Simplified parser that converts to rational via integer approximation
rational : Parser ℚ
rational =
  parseRational <$> integer <*> optional (char '.' *> some digit)
  where
    optional : ∀ {A : Set} → Parser A → Parser (Maybe A)
    optional p input with p input
    ... | nothing = just (nothing , input)
    ... | just (x , rest) = just (just x , rest)

    parseRational : ℤ → Maybe (List Char) → ℚ
    parseRational intPart nothing = intPart Data.Rational./ 1
      where open import Data.Rational using (_/_)
    parseRational intPart (just fracChars) =
      -- Simplified: Parse integer part only, ignore fractional part for Phase 1
      -- This works for DBC files with integer-valued parameters
      -- Full fractional parsing requires NonZero proof for power10 (deferred to Phase 5)
      intPart Data.Rational./ 1
      where
        open import Data.Rational using (_/_)

-- ============================================================================
-- YAML STRUCTURE PARSERS
-- ============================================================================

-- Parse newline
newline : Parser Char
newline = char '\n'

-- Parse indentation (spaces)
indent : ℕ → Parser (List Char)
indent n = count n space

-- Parse "key: value" pair
keyValue : ∀ {A : Set} → String → Parser A → Parser A
keyValue key valueParser =
  string key *> spaces *> char ':' *> spaces *> valueParser

-- Parse a YAML list item at given indentation level (starts with "- ")
listItem : ∀ {A : Set} → ℕ → Parser A → Parser A
listItem indentLevel itemParser =
  indent indentLevel *> char '-' *> spaces *> itemParser

-- ============================================================================
-- DBC-SPECIFIC PARSERS
-- ============================================================================

-- Parse ByteOrder from string
parseByteOrder : Parser ByteOrder
parseByteOrder =
  (string "little_endian" *> pure LittleEndian) <|>
  (string "big_endian" *> pure BigEndian)

-- Parse boolean from unsigned/signed
parseSigned : Parser Bool
parseSigned =
  (string "unsigned" *> pure false) <|>
  (string "signed" *> pure true)

-- Parse a signal definition
parseSignalDef : ℕ → Parser DBCSignal
parseSignalDef indentLevel =
  parseFields (mkSignal "" zero zero LittleEndian false ((+ 0) Data.Rational./ 1) ((+ 0) Data.Rational./ 1) ((+ 0) Data.Rational./ 1) ((+ 0) Data.Rational./ 1) "")
  where
    open import Data.Rational using (_/_)
    open import Data.Fin using (zero)

    -- Helper to accumulate signal fields
    mkSignal : String → Fin 64 → Fin 65 → ByteOrder → Bool → ℚ → ℚ → ℚ → ℚ → String → DBCSignal
    mkSignal name startBit bitLen byteOrd isSig fac off minVal maxVal unit =
      record
        { name = name
        ; signalDef = record
            { startBit = startBit
            ; bitLength = bitLen
            ; isSigned = isSig
            ; factor = fac
            ; offset = off
            ; minimum = minVal
            ; maximum = maxVal
            }
        ; byteOrder = byteOrd
        ; unit = unit
        }

    parseFields : DBCSignal → Parser DBCSignal
    parseFields sig =
      (newline *> indent (indentLevel + 2) *> keyValue "name" quotedString >>= λ n →
       newline *> indent (indentLevel + 2) *> keyValue "start_bit" natural >>= λ sb →
       newline *> indent (indentLevel + 2) *> keyValue "bit_length" natural >>= λ bl →
       newline *> indent (indentLevel + 2) *> keyValue "byte_order" quotedString *> parseByteOrder >>= λ bo →
       newline *> indent (indentLevel + 2) *> keyValue "value_type" quotedString *> parseSigned >>= λ vs →
       newline *> indent (indentLevel + 2) *> keyValue "factor" rational >>= λ f →
       newline *> indent (indentLevel + 2) *> keyValue "offset" rational >>= λ o →
       newline *> indent (indentLevel + 2) *> keyValue "minimum" rational >>= λ minV →
       newline *> indent (indentLevel + 2) *> keyValue "maximum" rational >>= λ maxV →
       newline *> indent (indentLevel + 2) *> keyValue "unit" quotedString >>= λ u →
       pure (mkSignal n (sb mod 64) (bl mod 65) bo vs f o minV maxV u))
      <|> pure sig
      where
        open import Data.Nat.DivMod using (_mod_)

-- Parse a message definition
parseMessage : ℕ → Parser DBCMessage
parseMessage indentLevel =
  listItem indentLevel (
    keyValue "id" hexNumber >>= λ msgId →
    newline *> indent (indentLevel + 2) *> keyValue "name" quotedString >>= λ msgName →
    newline *> indent (indentLevel + 2) *> keyValue "dlc" natural >>= λ msgDlc →
    newline *> indent (indentLevel + 2) *> keyValue "sender" quotedString >>= λ sender →
    newline *> indent (indentLevel + 2) *> string "signals:" *>
    many (parseSignalDef (indentLevel + 2)) >>= λ sigs →
    pure (record
      { id = msgId mod 2048
      ; name = msgName
      ; dlc = msgDlc mod 9
      ; sender = sender
      ; signals = sigs
      })
  )
  where
    open import Data.Nat.DivMod using (_mod_)

-- Parse top-level DBC file
parseDBC : Parser DBC
parseDBC =
  keyValue "version" quotedString >>= λ ver →
  newline *> newline *>
  string "messages:" *>
  many (parseMessage 2) >>= λ msgs →
  pure (record { version = ver ; messages = msgs })
