{-# OPTIONS --without-K --guardedness --sized-types #-}

-- Streaming trace parser using Delay for line buffering
-- Colist Char → Colist TimedFrame

module Aletheia.Trace.StreamParser where

open import Size using (Size; Size<_; ∞; ↑_)
open import Codata.Sized.Thunk using (Thunk; force)
open import Codata.Sized.Delay using (Delay; now; later)
open import Codata.Sized.Colist as Colist using (Colist; []; _∷_)
open import Data.List as List using (List; []; _∷_; reverse; null)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤ᵇ_)
open import Data.Nat.DivMod using (_mod_)
open import Data.Fin using (Fin)
open import Data.Char using (Char; toℕ)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Aletheia.Trace.CANTrace using (TimedFrame)
open import Aletheia.CAN.Frame using (CANFrame; CANId; Standard; Extended)
open import Aletheia.Data.DelayedColist using (DelayedColist; later)
open Aletheia.Data.DelayedColist

-- ============================================================================
-- CHARACTER UTILITIES
-- ============================================================================

isDigit : Char → Bool
isDigit c = let n = toℕ c in (48 ≤ᵇ n) ∧ (n ≤ᵇ 57)

isHexDigit : Char → Bool
isHexDigit c =
  let n = toℕ c
  in ((48 ≤ᵇ n) ∧ (n ≤ᵇ 57)) ∨
     ((65 ≤ᵇ n) ∧ (n ≤ᵇ 70)) ∨
     ((97 ≤ᵇ n) ∧ (n ≤ᵇ 102))

isSpace : Char → Bool
isSpace c = (c Data.Char.== ' ') ∨ (c Data.Char.== '\t')
  where open import Data.Char using (_==_)

isNewline : Char → Bool
isNewline c = c Data.Char.== '\n'
  where open import Data.Char using (_==_)

digitToℕ : Char → ℕ
digitToℕ c = toℕ c ∸ 48

hexDigitToℕ : Char → ℕ
hexDigitToℕ c =
  let n = toℕ c
  in if (48 ≤ᵇ n) ∧ (n ≤ᵇ 57)
     then n ∸ 48
     else if (97 ≤ᵇ n) ∧ (n ≤ᵇ 102)
          then n ∸ 87
          else n ∸ 55

-- Read characters into delayed lines
-- Every recursive call is under a constructor (properly guarded)
readLines : ∀ {i : Size} → List Char → Colist Char i → DelayedColist (List Char) i
readLines buf [] = if null buf then [] else (reverse buf ∷ λ where .force → [])
readLines buf (c ∷ rest) with isNewline c
... | true = reverse buf ∷ λ where .force → readLines [] (rest .force)
... | false = later λ where .force → readLines (c ∷ buf) (rest .force)

-- ============================================================================
-- LINE PARSING UTILITIES
-- ============================================================================

-- Skip leading spaces
skipSpaces : List Char → List Char
skipSpaces [] = []
skipSpaces (c ∷ cs) = if isSpace c then skipSpaces cs else c ∷ cs

-- Parse natural number from chars
parseNat : List Char → ℕ
parseNat = List.foldl (λ acc c → acc * 10 + digitToℕ c) 0

-- Parse hex number from chars
parseHex : List Char → ℕ
parseHex = List.foldl (λ acc c → acc * 16 + hexDigitToℕ c) 0

-- Take while predicate holds
takeWhile : (Char → Bool) → List Char → List Char × List Char
takeWhile p [] = [] , []
takeWhile p (c ∷ cs) =
  if p c
  then (let (taken , rest) = takeWhile p cs in (c ∷ taken , rest))
  else ([] , c ∷ cs)

-- Drop while predicate holds
dropWhile : (Char → Bool) → List Char → List Char
dropWhile p [] = []
dropWhile p (c ∷ cs) = if p c then dropWhile p cs else c ∷ cs

-- Check if list starts with prefix
hasPrefix : List Char → List Char → Bool
hasPrefix [] _ = true
hasPrefix (_ ∷ _) [] = false
hasPrefix (p ∷ ps) (c ∷ cs) =
  if p Data.Char.== c then hasPrefix ps cs else false
  where open import Data.Char using (_==_)

-- Drop prefix if present
dropPrefix : List Char → List Char → Maybe (List Char)
dropPrefix [] cs = just cs
dropPrefix (p ∷ ps) [] = nothing
dropPrefix (p ∷ ps) (c ∷ cs) =
  if p Data.Char.== c then dropPrefix ps cs else nothing
  where open import Data.Char using (_==_)

-- ============================================================================
-- FRAME FIELD PARSERS
-- ============================================================================

-- Parse "- timestamp: N" and return N
parseTimestamp : List Char → Maybe ℕ
parseTimestamp line =
  let trimmed = skipSpaces line
  in case dropPrefix ('-' ∷ ' ' ∷ 't' ∷ 'i' ∷ 'm' ∷ 'e' ∷ 's' ∷ 't' ∷ 'a' ∷ 'm' ∷ 'p' ∷ ':' ∷ []) trimmed of λ where
       nothing → nothing
       (just rest) → just (parseNat (dropWhile isSpace rest))
  where
    case_of_ : ∀ {A B : Set} → A → (A → B) → B
    case x of f = f x

-- Parse "  id: 0xNNN" and return CANId
parseId : List Char → Maybe CANId
parseId line =
  let trimmed = skipSpaces line
  in case dropPrefix ('i' ∷ 'd' ∷ ':' ∷ []) trimmed of λ where
       nothing → nothing
       (just rest) →
         case dropPrefix ('0' ∷ 'x' ∷ []) (dropWhile isSpace rest) of λ where
           nothing → nothing
           (just hexChars) →
             let (digits , _) = takeWhile isHexDigit hexChars
                 rawId = parseHex digits
             in if rawId ≤ᵇ 2047
                then just (Standard (rawId mod 2048))
                else just (Extended (rawId mod 536870912))
  where
    case_of_ : ∀ {A B : Set} → A → (A → B) → B
    case x of f = f x

-- Parse "  dlc: N" and return N mod 9
parseDlc : List Char → Maybe (Fin 9)
parseDlc line =
  let trimmed = skipSpaces line
  in case dropPrefix ('d' ∷ 'l' ∷ 'c' ∷ ':' ∷ []) trimmed of λ where
       nothing → nothing
       (just rest) →
         let (digits , _) = takeWhile isDigit (dropWhile isSpace rest)
         in just (parseNat digits mod 9)
  where
    case_of_ : ∀ {A B : Set} → A → (A → B) → B
    case x of f = f x

-- Parse single hex byte "0xNN"
parseHexByte : List Char → Maybe (Fin 256 × List Char)
parseHexByte chars =
  case dropPrefix ('0' ∷ 'x' ∷ []) chars of λ where
    nothing → nothing
    (just rest) →
      case rest of λ where
        [] → nothing
        (c1 ∷ []) → nothing
        (c1 ∷ c2 ∷ remaining) →
          if isHexDigit c1 ∧ isHexDigit c2
          then just ((hexDigitToℕ c1 * 16 + hexDigitToℕ c2) mod 256 , remaining)
          else nothing
  where
    case_of_ : ∀ {A B : Set} → A → (A → B) → B
    case x of f = f x

-- Parse "  data: [0x.., ..]" and return 8 bytes
parseData : List Char → Maybe (Vec (Fin 256) 8)
parseData line =
  let trimmed = skipSpaces line
  in case dropPrefix ('d' ∷ 'a' ∷ 't' ∷ 'a' ∷ ':' ∷ []) trimmed of λ where
       nothing → nothing
       (just rest) →
         let afterBracket = dropWhile (λ c → isSpace c ∨ (c Data.Char.== '[')) rest
         in parse8Bytes afterBracket
  where
    open import Data.Char using (_==_)
    open import Data.Maybe as Maybe using (_>>=_)

    case_of_ : ∀ {A B : Set} → A → (A → B) → B
    case x of f = f x

    skipComma : List Char → List Char
    skipComma cs = dropWhile (λ c → isSpace c ∨ (c == ',')) cs

    parse8Bytes : List Char → Maybe (Vec (Fin 256) 8)
    parse8Bytes cs0 =
      parseHexByte cs0 Maybe.>>= λ { (b0 , cs1) →
      parseHexByte (skipComma cs1) Maybe.>>= λ { (b1 , cs2) →
      parseHexByte (skipComma cs2) Maybe.>>= λ { (b2 , cs3) →
      parseHexByte (skipComma cs3) Maybe.>>= λ { (b3 , cs4) →
      parseHexByte (skipComma cs4) Maybe.>>= λ { (b4 , cs5) →
      parseHexByte (skipComma cs5) Maybe.>>= λ { (b5 , cs6) →
      parseHexByte (skipComma cs6) Maybe.>>= λ { (b6 , cs7) →
      parseHexByte (skipComma cs7) Maybe.>>= λ { (b7 , _) →
      just (b0 ∷ b1 ∷ b2 ∷ b3 ∷ b4 ∷ b5 ∷ b6 ∷ b7 ∷ [])
      }}}}}}}}

-- Parse a complete frame from 4 lines
parseFrameLines : List Char → List Char → List Char → List Char → Maybe TimedFrame
parseFrameLines tsLine idLine dlcLine dataLine =
  parseTimestamp tsLine Maybe.>>= λ ts →
  parseId idLine Maybe.>>= λ canId →
  parseDlc dlcLine Maybe.>>= λ dlc →
  parseData dataLine Maybe.>>= λ payload →
  just (record { timestamp = ts ; frame = record { id = canId ; dlc = dlc ; payload = payload } })
  where open import Data.Maybe as Maybe using (_>>=_)

-- ============================================================================
-- STREAMING FRAME PARSER
-- ============================================================================

-- Helper predicates
containsFrames : List Char → Bool
containsFrames cs = hasPrefix ('f' ∷ 'r' ∷ 'a' ∷ 'm' ∷ 'e' ∷ 's' ∷ ':' ∷ []) (skipSpaces cs)

isFrameStart : List Char → Bool
isFrameStart cs = hasPrefix ('-' ∷ ' ' ∷ 't' ∷ 'i' ∷ 'm' ∷ 'e' ∷ []) (skipSpaces cs)

isEndStream : List Char → Bool
isEndStream cs = hasPrefix ('c' ∷ 'o' ∷ 'm' ∷ 'm' ∷ 'a' ∷ 'n' ∷ 'd' ∷ ':' ∷ ' ' ∷ 'E' ∷ 'n' ∷ 'd' ∷ 'S' ∷ 't' ∷ 'r' ∷ 'e' ∷ 'a' ∷ 'm' ∷ []) (skipSpaces cs)

-- Parse frames from delayed line stream
-- The 'later' constructors pass through
mutual
  parseLinesStream : ∀ {i : Size} → DelayedColist (List Char) i → DelayedColist TimedFrame i
  parseLinesStream = skipToFrames

  -- Skip until "frames:" header
  skipToFrames : ∀ {i : Size} → DelayedColist (List Char) i → DelayedColist TimedFrame i
  skipToFrames [] = []
  skipToFrames (later rest) = later λ where .force → skipToFrames (rest .force)
  skipToFrames (line ∷ rest) =
    if containsFrames line
    then (later λ where .force → parseEntries (rest .force))
    else (later λ where .force → skipToFrames (rest .force))

  -- Parse frame entries
  parseEntries : ∀ {i : Size} → DelayedColist (List Char) i → DelayedColist TimedFrame i
  parseEntries [] = []
  parseEntries (later rest) = later λ where .force → parseEntries (rest .force)
  parseEntries (line1 ∷ rest1) =
    -- Check for EndStream marker first
    if isEndStream line1
    then []  -- Stop parsing - triggers property finalization
    else (if isFrameStart line1
          then (later λ where .force → parseWith3More line1 (rest1 .force))
          else (later λ where .force → parseEntries (rest1 .force)))

  parseWith3More : ∀ {i : Size} → List Char → DelayedColist (List Char) i → DelayedColist TimedFrame i
  parseWith3More _ [] = []
  parseWith3More l1 (later rest) = later λ where .force → parseWith3More l1 (rest .force)
  parseWith3More l1 (line2 ∷ rest2) = later λ where .force → parseWith2More l1 line2 (rest2 .force)

  parseWith2More : ∀ {i : Size} → List Char → List Char → DelayedColist (List Char) i → DelayedColist TimedFrame i
  parseWith2More _ _ [] = []
  parseWith2More l1 l2 (later rest) = later λ where .force → parseWith2More l1 l2 (rest .force)
  parseWith2More l1 l2 (line3 ∷ rest3) = later λ where .force → parseWith1More l1 l2 line3 (rest3 .force)

  parseWith1More : ∀ {i : Size} → List Char → List Char → List Char → DelayedColist (List Char) i → DelayedColist TimedFrame i
  parseWith1More _ _ _ [] = []
  parseWith1More l1 l2 l3 (later rest) = later λ where .force → parseWith1More l1 l2 l3 (rest .force)
  parseWith1More l1 l2 l3 (line4 ∷ rest4) =
    case parseFrameLines l1 l2 l3 line4 of λ where
      nothing → later λ where .force → parseEntries (rest4 .force)
      (just frame) → frame ∷ λ where .force → parseEntries (rest4 .force)
    where
      case_of_ : ∀ {A B : Set} → A → (A → B) → B
      case x of f = f x

-- Main entry point: Colist Char → DelayedColist TimedFrame
-- Composes line reader with frame parser
parseFrameStream : ∀ {i : Size} → Colist Char i → DelayedColist TimedFrame i
parseFrameStream = parseLinesStream ∘ readLines []
  where
    open import Function using (_∘_)
