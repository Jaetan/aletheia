{-# OPTIONS --safe --without-K --guardedness #-}

module Aletheia.Trace.Parser where

open import Aletheia.Trace.CANTrace
open import Aletheia.CAN.Frame
open import Aletheia.Parser.Combinators
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Nat.DivMod using (_mod_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String; toList)
open import Data.Char using (Char)
open import Data.Vec using (Vec)
open import Data.Bool using (Bool; true; false; if_then_else_)

-- ============================================================================
-- YAML TRACE PARSER
-- ============================================================================

-- Parse a hex byte (0xNN format, returns Fin 256)
hexByte : Parser (Fin 256)
hexByte =
  string "0x" *>
  (mkByte <$> hexDigit <*> hexDigit)
  where
    hexDigit : Parser ℕ
    hexDigit = hexCharToNat <$> satisfy isHexChar
      where
        isHexChar : Char → Bool
        isHexChar c =
          let n = Data.Char.toℕ c
          in ((48 Data.Nat.≤ᵇ n) Data.Bool.∧ (n Data.Nat.≤ᵇ 57)) Data.Bool.∨  -- '0'-'9'
             ((65 Data.Nat.≤ᵇ n) Data.Bool.∧ (n Data.Nat.≤ᵇ 70)) Data.Bool.∨  -- 'A'-'F'
             ((97 Data.Nat.≤ᵇ n) Data.Bool.∧ (n Data.Nat.≤ᵇ 102))              -- 'a'-'f'
          where
            open import Data.Char using (toℕ)
            open import Data.Nat using (_≤ᵇ_)
            open import Data.Bool using (_∧_; _∨_)

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

    mkByte : ℕ → ℕ → Fin 256
    mkByte hi lo = (hi Data.Nat.* 16 Data.Nat.+ lo) mod 256
      where open import Data.Nat using (_+_; _*_)

-- Parse 8 hex bytes separated by commas: [0x12, 0x34, ..., 0xF0]
byteArray8 : Parser (Vec (Fin 256) 8)
byteArray8 =
  char '[' *> spaces *>
  (Data.Vec._∷_ <$> hexByte <* char ',' <* spaces <*>
   (Data.Vec._∷_ <$> hexByte <* char ',' <* spaces <*>
    (Data.Vec._∷_ <$> hexByte <* char ',' <* spaces <*>
     (Data.Vec._∷_ <$> hexByte <* char ',' <* spaces <*>
      (Data.Vec._∷_ <$> hexByte <* char ',' <* spaces <*>
       (Data.Vec._∷_ <$> hexByte <* char ',' <* spaces <*>
        (Data.Vec._∷_ <$> hexByte <* char ',' <* spaces <*>
         (Data.Vec._∷_ <$> hexByte <*>
          pure Data.Vec.[]))))))))
  <* spaces <* char ']'

-- Parse CAN ID (hex number)
parseCANId : ℕ → Parser CANId
parseCANId rawId =
  -- Check if ID is standard (11-bit, ≤ 0x7FF) or extended (29-bit)
  if rawId Data.Nat.≤ᵇ 2047
  then pure (Standard (rawId mod 2048))
  else pure (Extended (rawId mod 536870912))
  where open import Data.Nat using (_≤ᵇ_)

-- Parse hex number (0xNNN format)
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
    parseHexDigits = Data.List.foldl (λ acc d → acc Data.Nat.* 16 Data.Nat.+ hexCharToNat d) 0
      where
        open import Data.List using (foldl)
        open import Data.Nat using (_+_; _*_)

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

-- Parse natural number
natural : Parser ℕ
natural = parseDigits <$> some digit
  where
    parseDigits : List Char → ℕ
    parseDigits = Data.List.foldl (λ acc d → acc Data.Nat.* 10 Data.Nat.+ charToDigit d) 0
      where
        open import Data.List using (foldl)
        open import Data.Nat using (_+_; _*_)

        charToDigit : Char → ℕ
        charToDigit c = Data.Char.toℕ c Data.Nat.∸ 48
          where
            open import Data.Char using (toℕ)
            open import Data.Nat using (_∸_)

-- Parse a single CAN frame entry
parseFrame : ℕ → Parser TimedFrame
parseFrame baseIndent =
  let fieldIndent = baseIndent Data.Nat.+ 2
  in
    yamlListItem baseIndent (yamlKeyValue 0 "timestamp" natural) >>= λ ts →
    newline *>
    yamlKeyValue fieldIndent "id" hexNumber >>= λ rawId →
    parseCANId rawId >>= λ canId →
    newline *>
    yamlKeyValue fieldIndent "dlc" natural >>= λ rawDlc →
    newline *>
    yamlKeyValue fieldIndent "data" byteArray8 >>= λ dataBytes →
    pure (record { timestamp = ts ; frame = record { id = canId ; dlc = rawDlc mod 9 ; payload = dataBytes } })
  where
    open import Data.Nat using (_+_)

-- Parse complete trace (list of frames)
-- Format:
-- frames:
--   - timestamp: 1000
--     id: 0x100
--     dlc: 8
--     data: [0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xF0]
parseCANTrace : Parser (List TimedFrame)
parseCANTrace =
  withBaseIndent λ base →
    atIndent base (string "frames:") *>
    newline *>
    parseFrame (base Data.Nat.+ 2) >>= λ firstFrame →
    many (newline *> parseFrame (base Data.Nat.+ 2)) >>= λ restFrames →
    pure (firstFrame ∷ restFrames)
  where open import Data.Nat using (_+_)

-- User-facing function: parse trace from string
parseTrace : String → Maybe (List TimedFrame)
parseTrace input =
  case runParser parseCANTrace (toList input) of λ where
    nothing → nothing
    (just (trace , _)) → just trace
  where
    open import Data.Product using (proj₁)
