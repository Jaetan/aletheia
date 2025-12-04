{-# OPTIONS --safe --without-K #-}

-- Protocol response types and JSON formatters.
--
-- Purpose: Define response types and convert them to JSON for output.
-- Types: Success, Error, Ack, PropertyResponse (violation/satisfaction), Complete.
-- Operations: formatResponse (Response → JSON), includes rational formatting.
-- Role: Used by Protocol.Routing and Main to generate JSON responses.
--
-- Design: Each response type has corresponding JSON structure matching protocol spec.
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

-- Convert a byte (Fin 256) to hex string "0xNN"
-- Uses stdlib's showInBase for proper hex conversion
byteToHex : Byte → String
byteToHex b = "0x" Data.String.++ padLeft '0' 2 (showInBase 16 (toℕ b))
  where
    open import Data.Nat.Show using (showInBase)
    open import Data.Nat.Base using (_<ᵇ_; _∸_)
    open import Data.String using (length; fromList; toList)
    open import Data.List as L using (replicate)

    -- Pad string on left with given character to reach minimum length
    padLeft : Char → ℕ → String → String
    padLeft c minLen s =
      let len = length s
          padding = if len <ᵇ minLen then minLen ∸ len else 0
      in fromList (L.replicate padding c L.++ toList s)

-- Convert Vec Byte 8 to space-separated hex string "0x12 0x34 0x56 ..."
bytesToHex : Vec Byte 8 → String
bytesToHex bytes =
  foldr (λ _ → String) combineBytes "" bytes
  where
    open import Data.String using (length; _++_)
    open import Data.Nat.Base using (_≡ᵇ_)

    isEmptyString : String → Bool
    isEmptyString s = Data.String.length s ≡ᵇ 0

    combineBytes : Byte → String → String
    combineBytes b acc = if isEmptyString acc then byteToHex b else byteToHex b ++ " " ++ acc

