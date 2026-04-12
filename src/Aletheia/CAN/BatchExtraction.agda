{-# OPTIONS --safe --without-K #-}

-- Batch signal extraction operations.
--
-- Purpose: Extract all signals from a CAN frame at once with rich error reporting.
-- Operations: extractAllSignals, extractAllSignalsIndexed, categorizeIndexed.
-- Role: Batch operations for language bindings (Python, C++, Go).
--
-- Design: Returns structured results partitioning signals into: successful extractions,
--         errors (with reasons), and absent signals (multiplexing).
--         Both string-keyed and index-keyed variants share the parameterized
--         PartitionedResults record.
module Aletheia.CAN.BatchExtraction where

open import Aletheia.CAN.Frame using (CANFrame)
open import Aletheia.CAN.ExtractionResult using (ExtractionResult; Success; SignalNotInDBC; SignalNotPresent; ValueOutOfBounds; ExtractionFailed)
open import Aletheia.CAN.SignalExtraction using (extractSignalDirect)
open import Aletheia.CAN.DBCHelpers using (findMessageById)
open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal)
open import Data.String using (String) renaming (_++_ to _++ₛ_)
open import Data.Rational using (ℚ)
open import Data.Rational.Show using () renaming (show to showℚ)
open import Data.List using (List; []; _∷_; map; foldr) renaming (_++_ to _++ₗ_)
open import Data.Nat using (ℕ; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (just; nothing)
open import Aletheia.Error using (FrameError; CANIdNotFound; SignalNotFound; formatFrameError; Error; ExtractionErr; MuxValueMismatch; formatError)

-- ============================================================================
-- PARAMETERIZED RESULT TYPE
-- ============================================================================

-- Partitioned extraction results, parameterized by key type K and error type E.
-- K = String for named results (JSON API), K = ℕ for indexed results (binary API).
-- E = String for human-readable errors, E = ExtractionErrorCode for binary wire format.
record PartitionedResults (K : Set) (E : Set) : Set where
  constructor mkPartitionedResults
  field
    values : List (K × ℚ)
    errors : List (K × E)
    absent : List K

emptyPartitioned : ∀ {K E} → PartitionedResults K E
emptyPartitioned = mkPartitionedResults [] [] []

combinePartitioned : ∀ {K E} → PartitionedResults K E → PartitionedResults K E → PartitionedResults K E
combinePartitioned (mkPartitionedResults v1 e1 a1) (mkPartitionedResults v2 e2 a2) =
  mkPartitionedResults (v1 ++ₗ v2) (e1 ++ₗ e2) (a1 ++ₗ a2)

-- ============================================================================
-- STRING-KEYED EXTRACTION (JSON output)
-- ============================================================================

ExtractionResults : Set
ExtractionResults = PartitionedResults String String

-- Categorize a single extraction result into the appropriate partition
categorizeResult : String → ExtractionResult → ExtractionResults
categorizeResult sigName (Success value) =
  mkPartitionedResults ((sigName , value) ∷ []) [] []
categorizeResult sigName SignalNotInDBC =
  mkPartitionedResults [] ((sigName , formatFrameError (SignalNotFound sigName)) ∷ []) []
-- Mux value mismatch is genuine absence (multiplexed out for this frame).
categorizeResult sigName (SignalNotPresent MuxValueMismatch) =
  mkPartitionedResults [] [] (sigName ∷ [])
-- Other ExtractionError variants indicate structural DBC problems
-- (missing mux signal, cycle, extraction failure) — report as errors.
categorizeResult sigName (SignalNotPresent reason) =
  mkPartitionedResults [] ((sigName , formatError (ExtractionErr reason)) ∷ []) []
categorizeResult sigName (ValueOutOfBounds value min max) =
  mkPartitionedResults [] ((sigName , "value out of bounds: " ++ₛ formatBounds value min max) ∷ []) []
  where
    formatBounds : ℚ → ℚ → ℚ → String
    formatBounds v mn mx = showℚ v ++ₛ " not in [" ++ₛ showℚ mn ++ₛ ", " ++ₛ showℚ mx ++ₛ "]"
-- Dead branch on the batch extraction path: extractSignalDirect (the sole
-- upstream producer) never constructs ExtractionFailed — it produces
-- SignalNotPresent, Success, or ValueOutOfBounds. Kept for completeness
-- since ExtractionResult is a public type. Routed through the typed Error
-- sum so the reason is formatted the same way as every other error.
categorizeResult sigName (ExtractionFailed reason) =
  mkPartitionedResults [] ((sigName , formatError (ExtractionErr reason)) ∷ []) []

-- Extract all signals from a message
extractAllSignalsFromMessage : ∀ {n} → CANFrame n → DBCMessage → ExtractionResults
extractAllSignalsFromMessage frame msg =
  foldr combinePartitioned emptyPartitioned (map extractOne (DBCMessage.signals msg))
  where
    extractOne : DBCSignal → ExtractionResults
    extractOne sig =
      let sigName = DBCSignal.name sig
          result = extractSignalDirect msg frame sig
      in categorizeResult sigName result

-- Extract all signals from a frame
-- Returns structured results with success/error/absent partitioning
extractAllSignals : ∀ {n} → DBC → CANFrame n → ExtractionResults
extractAllSignals dbc frame with findMessageById (CANFrame.id frame) dbc
... | nothing =
    mkPartitionedResults [] (("message" , formatFrameError CANIdNotFound) ∷ []) []
... | just msg =
    extractAllSignalsFromMessage frame msg

-- ============================================================================
-- INDEXED EXTRACTION (binary output — no strings on success path)
-- ============================================================================

-- Extraction error codes for the binary wire format.
-- Constructors map 1:1 to u8 wire values via extractionErrorCodeToℕ.
data ExtractionErrorCode : Set where
  NotInDBC          : ExtractionErrorCode  -- 0: signal name not found in DBC message
  OutOfBounds       : ExtractionErrorCode  -- 1: extracted value outside min/max range
  ExtractionFailed  : ExtractionErrorCode  -- 2: bit extraction or scaling failed

-- Encode ExtractionErrorCode as ℕ for binary wire format serialization.
-- Must match Main.agda binary output documentation and AletheiaFFI.hs.
extractionErrorCodeToℕ : ExtractionErrorCode → ℕ
extractionErrorCodeToℕ NotInDBC         = 0
extractionErrorCodeToℕ OutOfBounds      = 1
extractionErrorCodeToℕ ExtractionFailed = 2

IndexedExtractionResults : Set
IndexedExtractionResults = PartitionedResults ℕ ExtractionErrorCode

categorizeIndexed : ℕ → ExtractionResult → IndexedExtractionResults
categorizeIndexed idx (Success value) =
  mkPartitionedResults ((idx , value) ∷ []) [] []
categorizeIndexed idx SignalNotInDBC =
  mkPartitionedResults [] ((idx , NotInDBC) ∷ []) []
categorizeIndexed idx (SignalNotPresent MuxValueMismatch) =
  mkPartitionedResults [] [] (idx ∷ [])
categorizeIndexed idx (SignalNotPresent _) =
  mkPartitionedResults [] ((idx , ExtractionFailed) ∷ []) []
categorizeIndexed idx (ValueOutOfBounds _ _ _) =
  mkPartitionedResults [] ((idx , OutOfBounds) ∷ []) []
categorizeIndexed idx (ExtractionFailed _) =
  mkPartitionedResults [] ((idx , ExtractionFailed) ∷ []) []

-- Extract all signals from a message, returning indexed results.
extractAllSignalsIndexedFromMessage : ∀ {n} → CANFrame n → DBCMessage → IndexedExtractionResults
extractAllSignalsIndexedFromMessage frame msg = go 0 (DBCMessage.signals msg)
  where
    go : ℕ → List DBCSignal → IndexedExtractionResults
    go _ [] = emptyPartitioned
    go idx (sig ∷ sigs) =
      combinePartitioned (categorizeIndexed idx (extractSignalDirect msg frame sig))
                         (go (suc idx) sigs)

extractAllSignalsIndexed : ∀ {n} → DBC → CANFrame n → FrameError ⊎ IndexedExtractionResults
extractAllSignalsIndexed dbc frame with findMessageById (CANFrame.id frame) dbc
... | nothing = inj₁ CANIdNotFound
... | just msg = inj₂ (extractAllSignalsIndexedFromMessage frame msg)
