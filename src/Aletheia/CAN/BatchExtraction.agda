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

open import Aletheia.CAN.Frame
open import Aletheia.CAN.Signal
open import Aletheia.CAN.ExtractionResult
open import Aletheia.CAN.SignalExtraction
open import Aletheia.DBC.Types
open import Data.String using (String) renaming (_++_ to _++ₛ_)
open import Data.Rational using (ℚ)
open import Data.List using (List; []; _∷_; map; foldr) renaming (_++_ to _++ₗ_)
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (Maybe; just; nothing)

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
categorizeResult sigName (SignalNotInDBC _) =
  mkExtractionResults [] ((sigName , "Signal not found in DBC") ∷ []) []
categorizeResult sigName (SignalNotPresent _ reason) =
  -- Multiplexed signal not present
  mkExtractionResults [] [] (sigName ∷ [])
categorizeResult sigName (ValueOutOfBounds _ value min max) =
  mkExtractionResults [] ((sigName , "Value out of bounds: " ++ₛ formatBounds value min max) ∷ []) []
  where
    open import Data.Rational.Show using (show)
    formatBounds : ℚ → ℚ → ℚ → String
    formatBounds v mn mx = show v ++ₛ " not in [" ++ₛ show mn ++ₛ ", " ++ₛ show mx ++ₛ "]"
categorizeResult sigName (ExtractionFailed _ reason) =
  mkExtractionResults [] ((sigName , reason) ∷ []) []

-- Combine two extraction results
combineResults : ExtractionResults → ExtractionResults → ExtractionResults
combineResults (mkExtractionResults v1 e1 a1) (mkExtractionResults v2 e2 a2) =
  mkExtractionResults (v1 ++ₗ v2) (e1 ++ₗ e2) (a1 ++ₗ a2)

-- Empty extraction results
emptyResults : ExtractionResults
emptyResults = mkExtractionResults [] [] []

-- Extract all signals from a message
extractAllSignalsFromMessage : DBC → CANFrame → DBCMessage → ExtractionResults
extractAllSignalsFromMessage dbc frame msg =
  foldr combineResults emptyResults (map extractOne (DBCMessage.signals msg))
  where
    extractOne : DBCSignal → ExtractionResults
    extractOne sig =
      let sigName = DBCSignal.name sig
          result = extractSignalWithContext dbc frame sigName
      in categorizeResult sigName result

-- Extract all signals from a frame
-- Returns structured results with success/error/absent partitioning
extractAllSignals : DBC → CANFrame → ExtractionResults
extractAllSignals dbc frame with findMessageById (CANFrame.id frame) dbc
  where
    open import Aletheia.CAN.SignalExtraction using (findMessageById)
... | nothing =
    -- Message not found in DBC - return error
    mkExtractionResults [] (("message" , "CAN ID not found in DBC") ∷ []) []
... | just msg =
    -- Extract all signals from this message
    extractAllSignalsFromMessage dbc frame msg
