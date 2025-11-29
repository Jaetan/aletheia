{-# OPTIONS --safe --without-K #-}

module Aletheia.Protocol.Response where

open import Data.String using (String; _++_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Rational using (ℚ)
open import Data.Rational.Show as ℚShow using (show)
open import Data.Vec using (Vec; []; _∷_; foldr)
open import Data.Nat using (ℕ; _/_; _%_)
open import Data.Fin using (Fin; toℕ)
open import Data.List using (List)
open import Data.Char using (Char)
open import Aletheia.CAN.Frame using (Byte)
open import Aletheia.DBC.Types using (DBC)

-- Counterexample data for LTL violations
record CounterexampleData : Set where
  constructor mkCounterexampleData
  field
    timestamp : ℕ       -- Timestamp (microseconds) of violating frame
    reason : String     -- Human-readable reason

-- Property checking result for streaming protocol
-- Emitted when a property is decided (early termination or at EndStream)
data PropertyResult : Set where
  -- Property violated (failed early or at EndStream)
  Violation    : ℕ → CounterexampleData → PropertyResult
  -- Property satisfied (succeeded early or at EndStream)
  Satisfaction : ℕ → PropertyResult
  -- At EndStream: property still pending (neither proved nor violated)
  Pending      : ℕ → Bool → PropertyResult
  -- Stream complete marker (all properties decided)
  StreamComplete : PropertyResult

-- Response payload types
data ResponseData : Set where
  NoData : ResponseData
  DBCData : DBC → ResponseData
  SignalValueData : ℚ → ResponseData
  FrameData : Vec Byte 8 → ResponseData
  -- LTL check result: holds? and optional counterexample
  LTLResultData : Bool → Maybe CounterexampleData → ResponseData

-- Complete response with success/error and optional data
record Response : Set where
  constructor mkResponse
  field
    success : Bool
    message : String
    payload : ResponseData

-- Helper constructors for common response patterns
successResponse : String → ResponseData → Response
successResponse msg dat = mkResponse true msg dat

errorResponse : String → Response
errorResponse msg = mkResponse false msg NoData

-- Convert a single hex digit (0-15) to a character ('0'-'9', 'A'-'F')
hexDigit : ℕ → Char
hexDigit 0 = '0'
hexDigit 1 = '1'
hexDigit 2 = '2'
hexDigit 3 = '3'
hexDigit 4 = '4'
hexDigit 5 = '5'
hexDigit 6 = '6'
hexDigit 7 = '7'
hexDigit 8 = '8'
hexDigit 9 = '9'
hexDigit 10 = 'A'
hexDigit 11 = 'B'
hexDigit 12 = 'C'
hexDigit 13 = 'D'
hexDigit 14 = 'E'
hexDigit 15 = 'F'
hexDigit _ = 'X'  -- Should never happen for valid input

-- Convert a byte (Fin 256) to hex string "0xNN"
byteToHex : Byte → String
byteToHex b =
  let n = toℕ b
      hi = n / 16
      lo = n % 16
  in fromList ('0' L.∷ 'x' L.∷ hexDigit hi L.∷ hexDigit lo L.∷ L.[])
  where
    open import Data.String using (fromList)
    module L = Data.List

-- Convert Vec Byte 8 to space-separated hex string "0x12 0x34 0x56 ..."
bytesToHex : Vec Byte 8 → String
bytesToHex bytes =
  foldr (λ _ → String) (λ b acc → if isEmptyString acc then byteToHex b else byteToHex b ++ " " ++ acc) "" bytes
  where
    open import Data.String using (length)
    open import Data.Nat.Base using (_≡ᵇ_)
    isEmptyString : String → Bool
    isEmptyString s = Data.String.length s ≡ᵇ 0

-- Format response as YAML for output
formatResponse : Response → String
formatResponse resp =
  "success: " ++ (if Response.success resp then "true" else "false") ++ "\n" ++
  "message: \"" ++ Response.message resp ++ "\"\n" ++
  formatData (Response.payload resp)
  where
    formatData : ResponseData → String
    formatData NoData = ""
    formatData (DBCData dbc) = "dbc: <parsed>\n"  -- TODO Phase 5: Implement DBC serialization (pretty-printer)
    formatData (SignalValueData val) = "value: " ++ ℚShow.show val ++ "\n"
    formatData (FrameData bytes) = "frame: " ++ bytesToHex bytes ++ "\n"
    formatData (LTLResultData holds counterex) =
      "property_holds: " ++ (if holds then "true" else "false") ++ "\n" ++
      formatCounterex counterex
      where
        open import Data.Nat.Show as ℕShow using (show)
        formatCounterex : Maybe CounterexampleData → String
        formatCounterex nothing = ""
        formatCounterex (just ce) =
          "counterexample:\n" ++
          "  timestamp: " ++ ℕShow.show (CounterexampleData.timestamp ce) ++ "\n" ++
          "  reason: \"" ++ CounterexampleData.reason ce ++ "\"\n"

-- Format PropertyResult as YAML for streaming output
formatPropertyResult : PropertyResult → String
formatPropertyResult (Violation idx counterex) =
  "status: violation\n" ++
  "property_index: " ++ ℕShow.show idx ++ "\n" ++
  "result: false\n" ++
  "counterexample:\n" ++
  "  timestamp: " ++ ℕShow.show (CounterexampleData.timestamp counterex) ++ "\n" ++
  "  reason: \"" ++ CounterexampleData.reason counterex ++ "\"\n"
  where open import Data.Nat.Show as ℕShow using (show)
formatPropertyResult (Satisfaction idx) =
  "status: satisfaction\n" ++
  "property_index: " ++ ℕShow.show idx ++ "\n" ++
  "result: true\n"
  where open import Data.Nat.Show as ℕShow using (show)
formatPropertyResult (Pending idx result) =
  "status: pending\n" ++
  "property_index: " ++ ℕShow.show idx ++ "\n" ++
  "result: " ++ (if result then "true" else "false") ++ "\n"
  where open import Data.Nat.Show as ℕShow using (show)
formatPropertyResult StreamComplete =
  "status: complete\n"
