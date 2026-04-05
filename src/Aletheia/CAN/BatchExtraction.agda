{-# OPTIONS --safe --without-K #-}

-- Batch signal extraction operations.
--
-- Purpose: Extract all signals from a CAN frame at once with rich error reporting.
-- Operations: extractAllSignals (DBC + frame → ExtractionResults).
-- Role: Batch operations for Python API (Phase 2B.1).
--
-- Design: Returns structured results partitioning signals into: successful extractions,
--         errors (with reasons), and absent signals (multiplexing).
module Aletheia.CAN.BatchExtraction where

open import Aletheia.CAN.Frame using (CANFrame)
open import Aletheia.CAN.ExtractionResult using (ExtractionResult; Success; SignalNotInDBC; SignalNotPresent; ValueOutOfBounds; ExtractionFailed)
open import Aletheia.CAN.SignalExtraction using (extractSignalDirect)
open import Aletheia.CAN.DBCHelpers using (findMessageById)
open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal)
open import Data.String using (String) renaming (_++_ to _++ₛ_)
open import Data.Rational using (ℚ)
open import Data.Rational.Show using (show)
open import Data.List using (List; []; _∷_; map; foldr) renaming (_++_ to _++ₗ_)
open import Data.Nat using (ℕ; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (just; nothing)
open import Aletheia.Prelude using (errCanIdNotFound)

-- ============================================================================
-- BATCH EXTRACTION RESULT TYPE
-- ============================================================================

-- Results of extracting all signals from a frame
-- Partitions signals into three categories: success, errors, absent
record ExtractionResults : Set where
  constructor mkExtractionResults
  field
    -- Successfully extracted signal values (name, value)
    values : List (String × ℚ)

    -- Extraction errors (signal name, error message)
    errors : List (String × String)

    -- Multiplexed signals not present in this frame (signal name)
    absent : List String

-- ============================================================================
-- BATCH EXTRACTION
-- ============================================================================

-- Categorize a single extraction result into the appropriate partition
categorizeResult : String → ExtractionResult → ExtractionResults
categorizeResult sigName (Success value) =
  mkExtractionResults ((sigName , value) ∷ []) [] []
categorizeResult sigName SignalNotInDBC =
  mkExtractionResults [] ((sigName , "signal not found in DBC") ∷ []) []
categorizeResult sigName (SignalNotPresent reason) =
  -- Multiplexed signal not present
  mkExtractionResults [] [] (sigName ∷ [])
categorizeResult sigName (ValueOutOfBounds value min max) =
  mkExtractionResults [] ((sigName , "value out of bounds: " ++ₛ formatBounds value min max) ∷ []) []
  where
    formatBounds : ℚ → ℚ → ℚ → String
    formatBounds v mn mx = show v ++ₛ " not in [" ++ₛ show mn ++ₛ ", " ++ₛ show mx ++ₛ "]"
categorizeResult sigName (ExtractionFailed reason) =
  mkExtractionResults [] ((sigName , reason) ∷ []) []

-- Combine two extraction results
combineResults : ExtractionResults → ExtractionResults → ExtractionResults
combineResults (mkExtractionResults v1 e1 a1) (mkExtractionResults v2 e2 a2) =
  mkExtractionResults (v1 ++ₗ v2) (e1 ++ₗ e2) (a1 ++ₗ a2)

-- Empty extraction results
emptyResults : ExtractionResults
emptyResults = mkExtractionResults [] [] []

-- Extract all signals from a message
extractAllSignalsFromMessage : ∀ {n} → CANFrame n → DBCMessage → ExtractionResults
extractAllSignalsFromMessage frame msg =
  foldr combineResults emptyResults (map extractOne (DBCMessage.signals msg))
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
    -- Message not found in DBC - return error
    mkExtractionResults [] (("message" , errCanIdNotFound) ∷ []) []
... | just msg =
    -- Extract all signals from this message
    extractAllSignalsFromMessage frame msg

-- ============================================================================
-- INDEXED EXTRACTION (binary output — no strings on success path)
-- ============================================================================

-- Results with signal indices instead of names.
-- Error codes: 0 = not_in_dbc, 1 = out_of_bounds, 2 = extraction_failed
record IndexedExtractionResults : Set where
  constructor mkIndexedExtractionResults
  field
    values : List (ℕ × ℚ)       -- (signal_index, value)
    errors : List (ℕ × ℕ)       -- (signal_index, error_code)
    absent : List ℕ              -- signal_index

emptyIndexedResults : IndexedExtractionResults
emptyIndexedResults = mkIndexedExtractionResults [] [] []

combineIndexedResults : IndexedExtractionResults → IndexedExtractionResults → IndexedExtractionResults
combineIndexedResults (mkIndexedExtractionResults v1 e1 a1) (mkIndexedExtractionResults v2 e2 a2) =
  mkIndexedExtractionResults (v1 ++ₗ v2) (e1 ++ₗ e2) (a1 ++ₗ a2)

-- Wire-format error codes (must match Main.agda binary output documentation)
errCodeNotInDBC : ℕ
errCodeNotInDBC = 0

errCodeOutOfBounds : ℕ
errCodeOutOfBounds = 1

errCodeExtractionFailed : ℕ
errCodeExtractionFailed = 2

categorizeIndexed : ℕ → ExtractionResult → IndexedExtractionResults
categorizeIndexed idx (Success value) =
  mkIndexedExtractionResults ((idx , value) ∷ []) [] []
categorizeIndexed idx SignalNotInDBC =
  mkIndexedExtractionResults [] ((idx , errCodeNotInDBC) ∷ []) []
categorizeIndexed idx (SignalNotPresent _) =
  mkIndexedExtractionResults [] [] (idx ∷ [])
categorizeIndexed idx (ValueOutOfBounds _ _ _) =
  mkIndexedExtractionResults [] ((idx , errCodeOutOfBounds) ∷ []) []
categorizeIndexed idx (ExtractionFailed _) =
  mkIndexedExtractionResults [] ((idx , errCodeExtractionFailed) ∷ []) []

-- Extract all signals from a message, returning indexed results.
extractAllSignalsIndexedFromMessage : ∀ {n} → CANFrame n → DBCMessage → IndexedExtractionResults
extractAllSignalsIndexedFromMessage frame msg = go 0 (DBCMessage.signals msg)
  where
    go : ℕ → List DBCSignal → IndexedExtractionResults
    go _ [] = emptyIndexedResults
    go idx (sig ∷ sigs) =
      combineIndexedResults (categorizeIndexed idx (extractSignalDirect msg frame sig))
                            (go (suc idx) sigs)

extractAllSignalsIndexed : ∀ {n} → DBC → CANFrame n → String ⊎ IndexedExtractionResults
extractAllSignalsIndexed dbc frame with findMessageById (CANFrame.id frame) dbc
... | nothing = inj₁ errCanIdNotFound
... | just msg = inj₂ (extractAllSignalsIndexedFromMessage frame msg)
