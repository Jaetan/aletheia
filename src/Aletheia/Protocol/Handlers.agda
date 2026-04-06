{-# OPTIONS --safe --without-K #-}

-- Command handlers for the streaming protocol.
--
-- Purpose: Implement command-specific business logic (ParseDBC, BuildFrame, etc.).
-- Each handler processes command arguments, calls domain functions, and formats responses.
-- Role: Separated from StreamState to isolate command business logic
--       from state machine transitions, LTL processing, and proof-facing functions.
--
-- StreamState.agda retains: state types, formula indexing, signal cache,
--   and LTL frame processing (classifyStepResult, stepProperty, handleDataFrame).
-- This module also provides processStreamCommand (command dispatch).
module Aletheia.Protocol.Handlers where

open import Data.String using (String) renaming (_++_ to _++ₛ_)
open import Data.List using (List; []; _∷_; map; reverse)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Product using (_×_; _,_)
open import Data.Bool using (if_then_else_)
open import Data.Vec using (Vec)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Rational using (ℚ)
open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal)
open import Aletheia.DBC.JSONParser using (parseDBCWithErrors)
open import Aletheia.DBC.Validator using (validateDBCFull; hasAnyError)
open import Aletheia.DBC.Formatter using (formatDBC)
open import Aletheia.LTL.Syntax using (LTL)
open import Aletheia.LTL.SignalPredicate using (SignalPredicate; SignalCache; emptyCache)
open import Aletheia.LTL.Incremental using (FinalVerdict; Holds; Fails)
open import Aletheia.LTL.Coalgebra using (LTLProc; finalizeL; initProc)
open import Aletheia.LTL.JSON using (parseProperty)
open import Aletheia.Protocol.JSON using (JSON; lookupString; getObject; lookupRational)
open import Aletheia.Protocol.Message using (Response; StreamCommand; ParseDBC; SetProperties; StartStream; EndStream; BuildFrame; UpdateFrame; ExtractAllSignals; ValidateDBC; FormatDBC)
open import Aletheia.Protocol.Response as PR using (mkCounterexampleData; PropertyResult)
open import Aletheia.CAN.Frame using (CANFrame; CANId; Byte)
open import Aletheia.CAN.DLC using (DLC; dlcBytes)
open import Aletheia.CAN.BatchExtraction using (extractAllSignals; ExtractionResults)
open import Aletheia.CAN.BatchFrameBuilding using (buildFrame; updateFrame; buildFrameByIndex; updateFrameByIndex)
open import Aletheia.Prelude using (require)
open import Aletheia.Error as Err using
  ( Error; ParseErr; FrameErr; HandlerErr; WithContext
  ; ParseError; FrameError
  ; HandlerError; NoDBC; AlreadyStreaming; NotStreaming; StreamActive
  ; SignalListParseFailed; PropertyParseFailed; ValidationFailed
  ; WrappedParse; WrappedFrame
  ; formatFrameError
  )

-- Import state types from StreamState (no circular dependency: Handlers → StreamState types only)
open import Aletheia.Protocol.StreamState using
  ( StreamState; WaitingForDBC; ReadyToStream; Streaming
  ; getDBC
  ; PropertyState; mkPropertyState
  ; collectAtoms; indexFormula
  )

-- ============================================================================
-- INTERNAL HELPERS
-- ============================================================================

private
  -- Parse JSON array of signal objects into (name, value) pairs
  parseSignalList : List JSON → Maybe (List (String × ℚ))
  parseSignalList [] = just []
  parseSignalList (obj ∷ rest) = do
    fields ← getObject obj
    name ← lookupString "name" fields
    value ← lookupRational "value" fields
    restParsed ← parseSignalList rest
    just ((name , value) ∷ restParsed)

  -- Create frame from bytes, DLC, and message ID
  makeFrame : ∀ {n} → CANId → DLC → Vec Byte n → CANFrame n
  makeFrame msgId dlc bytes = record
    { id = msgId
    ; dlc = DLC.code dlc
    ; payload = bytes
    }

  -- Check DBC is loaded, returning the DBC or NoDBC error
  withDBC : StreamState → HandlerError ⊎ DBC
  withDBC state = require NoDBC (getDBC state)

-- ============================================================================
-- COMMAND HANDLERS
-- ============================================================================

-- Parse DBC command: parse DBC from JSON, validate, and update state
handleParseDBC : JSON → StreamState → StreamState × Response
handleParseDBC dbcJSON state =
  parseHelper (parseDBCWithErrors dbcJSON)
  where
    parseHelper : ParseError ⊎ DBC → StreamState × Response
    parseHelper (inj₁ parseError) =
      (state , Response.Error (WithContext "ParseDBC" (HandlerErr (WrappedParse parseError))))
    parseHelper (inj₂ dbc) =
      let issues = validateDBCFull dbc
      in if hasAnyError issues
         then (state , Response.Error (WithContext "ParseDBC" (HandlerErr (ValidationFailed issues))))
         else (ReadyToStream dbc [] emptyCache , Response.Success "DBC parsed and validated successfully")

-- Parse property list (extracted from where-block for proof access)
parseAllProperties : StreamState → DBC → List JSON → ℕ → List PropertyState → StreamState × Response
parseAllProperties _ dbc [] idx acc =
  (ReadyToStream dbc (reverse acc) emptyCache , Response.Success "Properties set successfully")
parseAllProperties state dbc (json ∷ rest) idx acc with parseProperty json
... | nothing = (state , Response.Error (WithContext "SetProperties" (HandlerErr (PropertyParseFailed idx))))
... | just prop =
    let atoms = collectAtoms prop
        proc = initProc (indexFormula prop)
        propState = mkPropertyState idx prop atoms proc
    in parseAllProperties state dbc rest (idx + 1) (propState ∷ acc)

-- Set properties command: parse JSON properties to LTL
handleSetProperties : List JSON → StreamState → StreamState × Response
handleSetProperties propJSONs WaitingForDBC =
  (WaitingForDBC , Response.Error (WithContext "SetProperties" (HandlerErr NoDBC)))
handleSetProperties propJSONs state@(ReadyToStream dbc _ _) =
  parseAllProperties state dbc propJSONs 0 []
handleSetProperties propJSONs state@(Streaming _ _ _ _) =
  (state , Response.Error (WithContext "SetProperties" (HandlerErr StreamActive)))

-- Start stream command: transition to streaming mode
handleStartStream : StreamState → StreamState × Response
handleStartStream (ReadyToStream dbc props cache) =
  (Streaming dbc props nothing cache , Response.Success "Streaming started")
handleStartStream WaitingForDBC =
  (WaitingForDBC , Response.Error (WithContext "StartStream" (HandlerErr NoDBC)))
handleStartStream state@(Streaming _ _ _ _) =
  (state , Response.Error (WithContext "StartStream" (HandlerErr AlreadyStreaming)))

-- Convert final verdict to property result (extracted for proof access)
verdictToResult : ℕ → FinalVerdict → PR.PropertyResult
verdictToResult idx Holds = PR.PropertyResult.Satisfaction idx
verdictToResult idx (Fails reason) = PR.PropertyResult.Violation idx (mkCounterexampleData 0 reason)

-- Finalize all properties with verdicts (extracted for proof access)
finalizeProperties : List PropertyState → List PR.PropertyResult
finalizeProperties = map λ ps →
  verdictToResult (PropertyState.index ps) (finalizeL (PropertyState.proc ps))

-- End stream command: finalize all properties and transition back to ready state
handleEndStream : StreamState → StreamState × Response
handleEndStream (Streaming dbc props _ cache) =
  let results = finalizeProperties props
  in (ReadyToStream dbc props cache , Response.Complete results)
handleEndStream state =
  (state , Response.Error (WithContext "EndStream" (HandlerErr NotStreaming)))

-- Build CAN frame from signal values
handleBuildFrame : CANId → (dlc : DLC) → List JSON → StreamState → StreamState × Response
handleBuildFrame canId dlc signalsJSON state with withDBC state
... | inj₁ err = (state , Response.Error (WithContext "BuildFrame" (HandlerErr err)))
... | inj₂ dbc = parseSignals dbc signalsJSON
  where
    parseSignals : DBC → List JSON → StreamState × Response
    parseSignals dbc signals with parseSignalList signals
    ... | nothing = (state , Response.Error (WithContext "BuildFrame" (HandlerErr SignalListParseFailed)))
    ... | just signalPairs with buildFrame dbc canId (DLC.code dlc) signalPairs
    ...   | inj₁ err = (state , Response.Error (WithContext "BuildFrame" (FrameErr err)))
    ...   | inj₂ frameBytes = (state , Response.ByteArray frameBytes)

-- Extract all signals from a CAN frame
handleExtractAllSignals : CANId → (dlc : DLC) → Vec Byte (dlcBytes dlc) → StreamState → StreamState × Response
handleExtractAllSignals canId dlc bytes state with withDBC state
... | inj₁ err = (state , Response.Error (WithContext "ExtractAllSignals" (HandlerErr err)))
... | inj₂ dbc =
    let frame = makeFrame canId dlc bytes
        results = extractAllSignals dbc frame
    in (state , Response.ExtractionResultsResponse
                  (ExtractionResults.values results)
                  (ExtractionResults.errors results)
                  (ExtractionResults.absent results))

-- Update specific signals in a CAN frame
handleUpdateFrame : CANId → (dlc : DLC) → Vec Byte (dlcBytes dlc) → List JSON → StreamState → StreamState × Response
handleUpdateFrame canId dlc bytes signalsJSON state with withDBC state
... | inj₁ err = (state , Response.Error (WithContext "UpdateFrame" (HandlerErr err)))
... | inj₂ dbc =
    let frame = makeFrame canId dlc bytes
    in parseSignals dbc signalsJSON frame
  where
    parseSignals : ∀ {m} → DBC → List JSON → CANFrame m → StreamState × Response
    parseSignals dbc signals frame with parseSignalList signals
    ... | nothing = (state , Response.Error (WithContext "UpdateFrame" (HandlerErr SignalListParseFailed)))
    ... | just signalPairs with updateFrame dbc canId frame signalPairs
    ...   | inj₁ err = (state , Response.Error (WithContext "UpdateFrame" (FrameErr err)))
    ...   | inj₂ updatedFrame = (state , Response.ByteArray (CANFrame.payload updatedFrame))

-- Validate DBC structure: parse JSON, then run comprehensive validator
handleValidateDBC : JSON → StreamState → StreamState × Response
handleValidateDBC dbcJSON state =
  parseHelper (parseDBCWithErrors dbcJSON)
  where
    parseHelper : ParseError ⊎ DBC → StreamState × Response
    parseHelper (inj₁ parseErr) =
      (state , Response.Error (WithContext "ValidateDBC" (HandlerErr (WrappedParse parseErr))))
    parseHelper (inj₂ dbc) =
      (state , Response.ValidationResponse (validateDBCFull dbc))

-- Format DBC: returns currently-loaded DBC as JSON
handleFormatDBC : StreamState → StreamState × Response
handleFormatDBC state with withDBC state
... | inj₁ err = (state , Response.Error (WithContext "FormatDBC" (HandlerErr err)))
... | inj₂ dbc = (state , Response.DBCResponse (formatDBC dbc))

-- ============================================================================
-- INDEX-BASED HANDLERS (Binary FFI — no JSON signal parsing)
-- ============================================================================

-- Build CAN frame from signal index-value pairs (no string allocation)
handleBuildFrameByIndex : CANId → (dlc : DLC) → List (ℕ × ℚ) → StreamState → StreamState × Response
handleBuildFrameByIndex canId dlc signalPairs state with withDBC state
... | inj₁ err = (state , Response.Error (WithContext "BuildFrame" (HandlerErr err)))
... | inj₂ dbc = buildHelper (buildFrameByIndex dbc canId (DLC.code dlc) signalPairs)
  where
    buildHelper : FrameError ⊎ Vec Byte (dlcBytes dlc) → StreamState × Response
    buildHelper (inj₁ err) = (state , Response.Error (WithContext "BuildFrame" (FrameErr err)))
    buildHelper (inj₂ frameBytes) = (state , Response.ByteArray frameBytes)

-- Update CAN frame signals by index (no string allocation)
handleUpdateFrameByIndex : CANId → (dlc : DLC) → Vec Byte (dlcBytes dlc) → List (ℕ × ℚ) → StreamState → StreamState × Response
handleUpdateFrameByIndex canId dlc bytes signalPairs state with withDBC state
... | inj₁ err = (state , Response.Error (WithContext "UpdateFrame" (HandlerErr err)))
... | inj₂ dbc =
    let frame = makeFrame canId dlc bytes
    in (state , formatResult (updateFrameByIndex dbc canId frame signalPairs))
  where
    formatResult : FrameError ⊎ CANFrame (dlcBytes dlc) → Response
    formatResult (inj₁ err) = Response.Error (WithContext "UpdateFrame" (FrameErr err))
    formatResult (inj₂ updatedFrame) = Response.ByteArray (CANFrame.payload updatedFrame)

-- ============================================================================
-- COMMAND DISPATCH
-- ============================================================================

-- Process a stream command and update state
processStreamCommand : StreamCommand → StreamState → StreamState × Response
processStreamCommand (ParseDBC dbcJSON) state = handleParseDBC dbcJSON state
processStreamCommand (SetProperties props) state = handleSetProperties props state
processStreamCommand StartStream state = handleStartStream state
processStreamCommand (BuildFrame canId dlc signalsJSON) state = handleBuildFrame canId dlc signalsJSON state
processStreamCommand (ExtractAllSignals canId dlc bytes) state = handleExtractAllSignals canId dlc bytes state
processStreamCommand (UpdateFrame canId dlc bytes signalsJSON) state = handleUpdateFrame canId dlc bytes signalsJSON state
processStreamCommand EndStream state = handleEndStream state
processStreamCommand (ValidateDBC dbcJSON) state = handleValidateDBC dbcJSON state
processStreamCommand FormatDBC state = handleFormatDBC state
