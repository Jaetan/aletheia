-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
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
open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal; signalNameStr)
open import Data.String using (String) renaming (_++_ to _++ₛ_)
open import Data.Rational using (ℚ)
open import Aletheia.DBC.RationalRenderer using (formatℚ)
open import Data.List using (List; []; _∷_; map; foldr) renaming (_++_ to _++ₗ_)
open import Data.Bool using (Bool; true; false)
open import Data.Integer using (∣_∣)
-- The builtin max and comparison: one comparison whatever the size of the
-- components, where the structural `_⊔_` recurses once per unit of value.
open import Data.Nat using (ℕ; suc; _⊔′_; _≤ᵇ_)
open import Aletheia.Limits using (max-rational-component-magnitude)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (just; nothing)
open import Aletheia.Error using
  ( FrameError; CANIdNotFound; SignalNotFound; SignalValueOutOfBounds
  ; formatFrameError; ExtractionErr; formatError
  ; ExtractionError; MuxValueMismatch; MuxSignalNotFound; MuxChainCycle
  ; MuxExtractionFailed; ValueExceedsWireRange; InContext
  )
-- The error and its wire code share a name for this condition, as they do for
-- the multiplexor ones; the error's is renamed here so the two are distinct
-- where the mapping between them is written.
open import Aletheia.Error using () renaming (SignalPastFrameEnd to PastFrameEndError)

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

-- Whether an extracted value fits the binary wire's rational slots: its
-- reduced numerator magnitude and its denominator are both at most
-- `max-rational-component-magnitude`.  Measured as `jsonMaxComponent`
-- measures a JSON number (Aletheia.Protocol.JSON.Types).
wireFits : ℚ → Bool
wireFits q =
  (∣ ℚ.numerator q ∣ ⊔′ suc (ℚ.denominator-1 q)) ≤ᵇ max-rational-component-magnitude

-- Shared structure for categorizeResult and categorizeIndexed.
-- A Success whose value fits the wire goes to the success partition and one
-- whose value does not is refused as `ExtractionFailed ValueExceedsWireRange`
-- through toErr, so both paths refuse it with the same reason and the shim
-- pokes only values the kernel kept (Aletheia.CAN.Batch.Properties.WireFits);
-- MuxValueMismatch goes to the absent partition; the remaining error cases
-- go to toErr.  The fit is a `with`, not `if`, so a proof can abstract it.
categorizeWith : ∀ {K E}
  → (K → ExtractionResult → E)
  → K → ExtractionResult → PartitionedResults K E
categorizeWith toErr key (Success value) with wireFits value
... | true  = mkPartitionedResults ((key , value) ∷ []) [] []
... | false =
  mkPartitionedResults [] ((key , toErr key (ExtractionFailed ValueExceedsWireRange)) ∷ []) []
-- Mux value mismatch is genuine absence (multiplexed out for this frame).
categorizeWith _ key (SignalNotPresent MuxValueMismatch) =
  mkPartitionedResults [] [] (key ∷ [])
-- Other ExtractionError variants, SignalNotInDBC, ValueOutOfBounds and
-- ExtractionFailed go to toErr.
categorizeWith toErr key result =
  mkPartitionedResults [] ((key , toErr key result) ∷ []) []

ExtractionResults : Set
ExtractionResults = PartitionedResults String String

private
  formatBounds : ℚ → ℚ → ℚ → String
  formatBounds v mn mx = formatℚ v ++ₛ " not in [" ++ₛ formatℚ mn ++ₛ ", " ++ₛ formatℚ mx ++ₛ "]"

-- The single reason formatter for BOTH extraction surfaces: the string-keyed
-- (JSON) categorizer and the indexed (binary-wire) categorizer each derive
-- their error reason from this function, so the two paths agree on reason
-- text by construction (machine-checked: reason-parity in
-- Aletheia.CAN.Batch.Properties.ReasonParity).
resultToString : String → ExtractionResult → String
resultToString name SignalNotInDBC = formatFrameError (SignalNotFound name)
resultToString _ (SignalNotPresent reason) = formatError (ExtractionErr reason)
resultToString _ (ValueOutOfBounds value mn mx) =
  formatFrameError (SignalValueOutOfBounds (formatBounds value mn mx))
resultToString _ (ExtractionFailed reason) = formatError (ExtractionErr reason)
-- Unreachable: `categorizeWith` never applies `toErr` to a `Success`, keeping
-- a fitting value and refusing the other as an `ExtractionFailed`, so
-- `resultToString` is never called on a `Success` value.  Empty string is a
-- totality-only sentinel.
resultToString _ (Success _) = ""

categorizeResult : String → ExtractionResult → ExtractionResults
categorizeResult = categorizeWith resultToString

-- Extract all signals from a message
extractAllSignalsFromMessage : ∀ {n} → CANFrame n → DBCMessage → ExtractionResults
extractAllSignalsFromMessage frame msg =
  foldr combinePartitioned emptyPartitioned (map extractOne (DBCMessage.signals msg))
  where
    extractOne : DBCSignal → ExtractionResults
    extractOne sig =
      let sigName = signalNameStr sig
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
-- Constructors map 1:1 to u8 wire values via extractionErrorCodeToℕ, and no
-- two distinguishable error conditions share a code (machine-checked:
-- fromℕ∘toℕ in Aletheia.CAN.Batch.Properties.ReasonParity).  The code is the
-- machine-readable discriminant; the human-readable reason STRING travels the
-- wire alongside it (offsets-table segment — layout in Aletheia.Main.Binary).
data ExtractionErrorCode : Set where
  NotInDBC            : ExtractionErrorCode  -- 0: signal name not found in DBC message
  OutOfBounds         : ExtractionErrorCode  -- 1: extracted value outside min/max range
  BitExtractionFailed : ExtractionErrorCode  -- 2: bit-level read or scaling step failed
  -- 3: the exact value's reduced numerator magnitude or denominator exceeds
  -- `max-rational-component-magnitude`, the signed 64-bit range of the
  -- binary wire's rational slots.  Minted by categorizeWith on both paths
  -- when `wireFits` refuses a Success, so the shim's encoder pokes only
  -- values the kernel proved fit (string twin:
  -- `extraction_value_exceeds_wire_range`).
  ValueExceedsWireRange : ExtractionErrorCode
  MuxSignalNotFound   : ExtractionErrorCode  -- 4: multiplexor signal missing from message
  MuxChainCycle       : ExtractionErrorCode  -- 5: multiplexor chain depth exceeded (cycle?)
  MuxExtractionFailed : ExtractionErrorCode  -- 6: reading the multiplexor's own bits failed
  -- 7: the frame's multiplexor value does not select this signal.  Never on
  -- the wire: categorizeWith routes MuxValueMismatch to the absent partition
  -- before any error code is minted.  Listed so every ExtractionError
  -- constructor owns a distinct code (totality of extractionErrorToCode
  -- without code sharing).
  MuxValueMismatch    : ExtractionErrorCode
  -- 8: the signal's last bit lies past the end of the frame that arrived,
  -- so the bits it names are not there to read.
  SignalPastFrameEnd  : ExtractionErrorCode

-- Encode ExtractionErrorCode as ℕ for binary wire format serialization.
-- Must match Main.agda binary output documentation and AletheiaFFI.hs.
extractionErrorCodeToℕ : ExtractionErrorCode → ℕ
extractionErrorCodeToℕ NotInDBC              = 0
extractionErrorCodeToℕ OutOfBounds           = 1
extractionErrorCodeToℕ BitExtractionFailed   = 2
extractionErrorCodeToℕ ValueExceedsWireRange = 3
extractionErrorCodeToℕ MuxSignalNotFound     = 4
extractionErrorCodeToℕ MuxChainCycle         = 5
extractionErrorCodeToℕ MuxExtractionFailed   = 6
extractionErrorCodeToℕ MuxValueMismatch      = 7
extractionErrorCodeToℕ SignalPastFrameEnd    = 8

-- Map a kernel ExtractionError to its wire code.  InContext wrappers carry
-- no code of their own — the inner error's code travels (mirrors
-- extractionErrorCode in Aletheia.Error, the string-code SSOT).
extractionErrorToCode : ExtractionError → ExtractionErrorCode
extractionErrorToCode MuxValueMismatch        = MuxValueMismatch
extractionErrorToCode (PastFrameEndError _)   = SignalPastFrameEnd
extractionErrorToCode (MuxSignalNotFound _)   = MuxSignalNotFound
extractionErrorToCode MuxChainCycle           = MuxChainCycle
extractionErrorToCode (MuxExtractionFailed _) = MuxExtractionFailed
extractionErrorToCode ValueExceedsWireRange   = ValueExceedsWireRange
extractionErrorToCode (InContext _ inner)     = extractionErrorToCode inner

-- An indexed error entry carries the wire code AND the same reason string
-- the JSON path formats for that error (shared resultToString) — the binary
-- wire is exactly as informative as the JSON wire.
IndexedExtractionResults : Set
IndexedExtractionResults = PartitionedResults ℕ (ExtractionErrorCode × String)

resultToCode : ExtractionResult → ExtractionErrorCode
resultToCode SignalNotInDBC           = NotInDBC
resultToCode (SignalNotPresent e)     = extractionErrorToCode e
resultToCode (ValueOutOfBounds _ _ _) = OutOfBounds
resultToCode (ExtractionFailed e)     = extractionErrorToCode e
-- Unreachable: see the matching `resultToString` clause above.  The
-- `BitExtractionFailed` sentinel is structurally misleading (Success is not
-- a failure), but ExtractionErrorCode totality requires a value — pick
-- any constructor.  Callers never observe this value.
resultToCode (Success _)              = BitExtractionFailed

-- The signal NAME is threaded in solely for the reason string (resultToString
-- embeds it for SignalNotInDBC); the partition key stays the numeric index.
categorizeIndexed : String → ℕ → ExtractionResult → IndexedExtractionResults
categorizeIndexed name = categorizeWith (λ _ r → resultToCode r , resultToString name r)

-- Extract all signals from a message, returning indexed results.
extractAllSignalsIndexedFromMessage : ∀ {n} → CANFrame n → DBCMessage → IndexedExtractionResults
extractAllSignalsIndexedFromMessage frame msg = go 0 (DBCMessage.signals msg)
  where
    go : ℕ → List DBCSignal → IndexedExtractionResults
    go _ [] = emptyPartitioned
    go idx (sig ∷ sigs) =
      combinePartitioned (categorizeIndexed (signalNameStr sig) idx (extractSignalDirect msg frame sig))
                         (go (suc idx) sigs)

extractAllSignalsIndexed : ∀ {n} → DBC → CANFrame n → FrameError ⊎ IndexedExtractionResults
extractAllSignalsIndexed dbc frame with findMessageById (CANFrame.id frame) dbc
... | nothing = inj₁ CANIdNotFound
... | just msg = inj₂ (extractAllSignalsIndexedFromMessage frame msg)
