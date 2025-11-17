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
-- Converts decimal notation to rational: "0.25" → 1/4, "1.5" → 3/2
rational : Parser ℚ
rational =
  parseRational <$> integer <*> optional (char '.' *> some digit)
  where
    open import Data.Rational using (_/_)
    open import Data.List using (foldl; length)
    open import Data.Char using (toℕ)
    open import Data.Nat using (_∸_)

    -- Compute 10^n. Returns suc of (10^n - 1), proving result is always ≥ 1
    -- This allows Agda to automatically find the NonZero instance
    power10 : ℕ → ℕ
    power10 zero = suc 0  -- 1
    power10 (suc n) with power10 n
    ... | zero = suc 0  -- Impossible case (power10 always returns suc), but needed for coverage
    ... | suc m = suc (9 + 10 * m)  -- 10 * (suc m) = 10m + 10 = suc (9 + 10m)

    -- Check if integer is non-negative
    isNonNegative : ℤ → Bool
    isNonNegative (+ _) = true
    isNonNegative -[1+ _ ] = false

    -- Parse list of digit chars to natural number
    charToDigit : Char → ℕ
    charToDigit c = toℕ c ∸ 48

    parseDigitList : List Char → ℕ
    parseDigitList = foldl (λ acc d → acc * 10 + charToDigit d) 0

    parseRational : ℤ → Maybe (List Char) → ℚ
    parseRational intPart nothing = intPart / 1
    parseRational intPart (just fracChars) =
      buildRational fracChars
      where
        -- Helper that pattern matches on power10 result to expose suc constructor
        buildRational : List Char → ℚ
        buildRational chars with power10 (length chars)
        ... | zero = intPart / 1  -- Impossible case (power10 always returns suc), but needed for coverage
        ... | suc denomMinus1 =  -- Now Agda sees suc pattern, NonZero instance available!
          let fracDigits = parseDigitList chars
              denom = suc denomMinus1
              -- For positive numbers: numerator = intPart * 10^n + fracDigits
              -- For negative numbers: numerator = intPart * 10^n - fracDigits
              -- (fractional part is always subtracted for negatives)
              numer = if isNonNegative intPart
                      then intPart ℤ.* (+ denom) ℤ.+ (+ fracDigits)
                      else intPart ℤ.* (+ denom) ℤ.- (+ fracDigits)
          in numer / denom

-- ============================================================================
-- YAML STRUCTURE PARSERS (using block-based combinators)
-- ============================================================================

-- Parse newline
newline : Parser Char
newline = char '\n'

-- Parse "key: value" pair (no indentation)
keyValue : ∀ {A : Set} → String → Parser A → Parser A
keyValue key valueParser =
  string key *> spaces *> char ':' *> spaces *> valueParser

-- ============================================================================
-- DBC-SPECIFIC PARSERS
-- ============================================================================

-- Parse ByteOrder from string
parseByteOrder : Parser ByteOrder
parseByteOrder =
  (string "little_endian" *> pure LittleEndian) <|>
  (string "big_endian" *> pure BigEndian)

-- Validate ByteOrder from parsed quoted string
validateByteOrder : String → Parser ByteOrder
validateByteOrder "little_endian" = pure LittleEndian
validateByteOrder "big_endian" = pure BigEndian
validateByteOrder _ = λ _ → nothing

-- Parse boolean from unsigned/signed
parseSigned : Parser Bool
parseSigned =
  (string "unsigned" *> pure false) <|>
  (string "signed" *> pure true)

-- Validate signedness from parsed quoted string
validateSigned : String → Parser Bool
validateSigned "unsigned" = pure false
validateSigned "signed" = pure true
validateSigned _ = λ _ → nothing

-- Parse a signal definition at given base indentation
-- First field (name) is on same line as "- ", rest are indented on new lines
parseSignalDef : ℕ → Parser DBCSignal
parseSignalDef base =
  let fieldIndent = base + 2  -- Subsequent fields indented 2 more than the "-"
  in
    keyValue "name" quotedString >>= λ n →   -- First field on same line as "- "
    newline *>
    yamlKeyValue fieldIndent "start_bit" natural >>= λ sb →
    newline *>
    yamlKeyValue fieldIndent "bit_length" natural >>= λ bl →
    newline *>
    yamlKeyValue fieldIndent "byte_order" quotedString >>= λ boStr →
    validateByteOrder boStr >>= λ bo →
    newline *>
    yamlKeyValue fieldIndent "value_type" quotedString >>= λ vtStr →
    validateSigned vtStr >>= λ vs →
    newline *>
    yamlKeyValue fieldIndent "factor" rational >>= λ f →
    newline *>
    yamlKeyValue fieldIndent "offset" rational >>= λ o →
    newline *>
    yamlKeyValue fieldIndent "minimum" rational >>= λ minV →
    newline *>
    yamlKeyValue fieldIndent "maximum" rational >>= λ maxV →
    newline *>
    yamlKeyValue fieldIndent "unit" quotedString >>= λ u →
    -- Optional multiplexing fields
    parsePresence fieldIndent >>= λ pres →
    pure (mkSignal n (sb mod 64) (bl mod 65) bo vs f o minV maxV u pres)
  where
    open import Data.Nat.DivMod using (_mod_)
    open import Data.Fin using (zero)
    open import Data.Rational using (_/_)
    open import Data.Maybe using (Maybe; just; nothing)

    -- Parse optional multiplexing fields
    parsePresence : ℕ → Parser SignalPresence
    parsePresence indent =
      -- Try to parse "multiplexor: ..." and "multiplex_value: ..."
      (newline *>
       yamlKeyValue indent "multiplexor" quotedString >>= λ muxName →
       newline *>
       yamlKeyValue indent "multiplex_value" natural >>= λ muxVal →
       pure (When muxName muxVal))
      <|>
      -- If no multiplexing fields, signal is always present
      pure Always

    -- Helper to build signal record
    mkSignal : String → Fin 64 → Fin 65 → ByteOrder → Bool → ℚ → ℚ → ℚ → ℚ → String → SignalPresence → DBCSignal
    mkSignal name startBit bitLen byteOrd isSig fac off minVal maxVal unit pres =
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
        ; presence = pres
        }

-- Parse CAN ID (standard or extended)
-- Standard: id: 0x100
-- Extended: id: 0x18FF1234
--           extended: true
parseCANId : ℕ → ℕ → Parser CANId
parseCANId fieldIndent rawId =
  -- Try to parse "extended: true" field
  (newline *> yamlKeyValue fieldIndent "extended" yamlString >>= λ extStr →
    if extStr String.== "true"
    then pure (Extended (rawId mod 536870912))
    else pure (Standard (rawId mod 2048)))
  <|>
  -- If no "extended" field, assume standard ID
  pure (Standard (rawId mod 2048))
  where
    open import Data.String using (_==_)
    open import Data.Nat.DivMod using (_mod_)

-- Parse a message definition at given base indentation
-- Messages are list items: "  - id: 0x100"
-- Message fields are indented 2 more: "    name: ..."
parseMessage : ℕ → Parser DBCMessage
parseMessage base =
  let fieldIndent = base + 2  -- Fields indented 2 more than the "- " marker
      signalIndent = base + 4  -- Signal list items indented 4 more (2 for "- ", 2 for nesting)
  in
    yamlListItem base (keyValue "id" hexNumber) >>= λ rawId →
    parseCANId fieldIndent rawId >>= λ msgId →
    newline *>
    yamlKeyValue fieldIndent "name" quotedString >>= λ msgName →
    newline *>
    yamlKeyValue fieldIndent "dlc" natural >>= λ msgDlc →
    newline *>
    yamlKeyValue fieldIndent "sender" quotedString >>= λ sender →
    newline *>
    atIndent fieldIndent (string "signals:") *>
    newline *>
    yamlListItem signalIndent (parseSignalDef signalIndent) >>= λ firstSig →
    many (newline *> yamlListItem signalIndent (parseSignalDef signalIndent)) >>= λ restSigs →
    pure (record
      { id = msgId
      ; name = msgName
      ; dlc = msgDlc mod 9
      ; sender = sender
      ; signals = firstSig ∷ restSigs
      })
  where
    open import Data.Nat.DivMod using (_mod_)

-- Parse top-level DBC file with automatic base indentation detection
-- Works regardless of whether content starts at column 0 or has leading spaces
-- Example: Handles both "version: ..." and "  version: ..." automatically
parseDBC : Parser DBC
parseDBC =
  withBaseIndent λ base →
    atIndent base (keyValue "version" quotedString) >>= λ ver →
    newline *> newline *>
    atIndent base (string "messages:") *>
    newline *>
    parseMessage (base + 2) >>= λ firstMsg →
    many (newline *> parseMessage (base + 2)) >>= λ restMsgs →
    pure (record { version = ver ; messages = firstMsg ∷ restMsgs })
