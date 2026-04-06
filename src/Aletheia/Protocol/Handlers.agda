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
open import Aletheia.Prelude using (errNoDBC)
open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal)
open import Aletheia.DBC.JSONParser using (parseDBCWithErrors)
open import Aletheia.DBC.Validator using (validateDBCFull; hasAnyError; formatIssuesText; errorIssues)
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

-- Import state types from StreamState (no circular dependency: Handlers → StreamState types only)
open import Aletheia.Protocol.StreamState using
  ( StreamState; mkStreamState; StreamPhase; WaitingForDBC; ReadyToStream; Streaming
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

  -- Common preamble: validate DBC loaded (prefixes error with command name)
  withDBC : String → StreamState → (DBC → StreamState × Response) → StreamState × Response
  withDBC cmd state cont with StreamState.dbc state
  ... | nothing  = (state , Response.Error (cmd ++ₛ ": " ++ₛ errNoDBC))
  ... | just dbc = cont dbc

-- ============================================================================
-- COMMAND HANDLERS
-- ============================================================================

-- Parse DBC command: parse DBC from JSON, validate, and update state
handleParseDBC : JSON → StreamState → StreamState × Response
handleParseDBC dbcJSON state =
  parseHelper (parseDBCWithErrors dbcJSON)
  where
    parseHelper : String ⊎ DBC → StreamState × Response
    parseHelper (inj₁ parseError) =
      (state , Response.Error ("ParseDBC: parse error: " ++ₛ parseError))
    parseHelper (inj₂ dbc) =
      let issues = validateDBCFull dbc
      in if hasAnyError issues
         then (state , Response.Error ("ParseDBC: validation failed: "
                ++ₛ formatIssuesText (errorIssues issues)))
         else let newState = mkStreamState ReadyToStream (just dbc) [] nothing emptyCache
              in (newState , Response.Success "DBC parsed and validated successfully")

-- Parse property list (extracted from where-block for proof access)
parseAllProperties : StreamState → List JSON → ℕ → List PropertyState → StreamState × Response
parseAllProperties state [] idx acc =
  let newState = mkStreamState ReadyToStream (StreamState.dbc state) (reverse acc) nothing emptyCache
  in (newState , Response.Success "Properties set successfully")
parseAllProperties state (json ∷ rest) idx acc with parseProperty json
... | nothing = (state , Response.Error ("SetProperties: failed to parse property " ++ₛ showℕ idx))
... | just prop =
    let atoms = collectAtoms prop
        proc = initProc (indexFormula prop)
        propState = mkPropertyState idx prop atoms proc
    in parseAllProperties state rest (idx + 1) (propState ∷ acc)

-- Set properties command: parse JSON properties to LTL
handleSetProperties : List JSON → StreamState → StreamState × Response
handleSetProperties propJSONs state with StreamState.phase state
... | WaitingForDBC = (state , Response.Error ("SetProperties: " ++ₛ errNoDBC))
... | ReadyToStream = parseAllProperties state propJSONs 0 []
... | Streaming = (state , Response.Error "SetProperties: stream is active")

-- Start stream command: transition to streaming mode
handleStartStream : StreamState → StreamState × Response
handleStartStream state with StreamState.phase state
... | WaitingForDBC = (state , Response.Error ("StartStream: " ++ₛ errNoDBC))
... | ReadyToStream =
  let newState = mkStreamState Streaming (StreamState.dbc state) (StreamState.properties state) nothing (StreamState.signalCache state)
  in (newState , Response.Success "Streaming started")
... | Streaming = (state , Response.Error "StartStream: already streaming")

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
handleEndStream state with StreamState.phase state
... | Streaming =
  let newState = mkStreamState ReadyToStream (StreamState.dbc state) (StreamState.properties state) (StreamState.prevFrame state) (StreamState.signalCache state)
      results = finalizeProperties (StreamState.properties state)
  in (newState , Response.Complete results)
... | _ = (state , Response.Error "EndStream: not currently streaming")

-- Build CAN frame from signal values
handleBuildFrame : CANId → (dlc : DLC) → List JSON → StreamState → StreamState × Response
handleBuildFrame canId dlc signalsJSON state =
  withDBC "BuildFrame" state λ dbc → parseSignals dbc signalsJSON
  where
    parseSignals : DBC → List JSON → StreamState × Response
    parseSignals dbc signals with parseSignalList signals
    ... | nothing = (state , Response.Error "BuildFrame: failed to parse signal list")
    ... | just signalPairs with buildFrame dbc canId (DLC.code dlc) signalPairs
    ...   | inj₁ err = (state , Response.Error ("BuildFrame: " ++ₛ err))
    ...   | inj₂ frameBytes = (state , Response.ByteArray frameBytes)

-- Extract all signals from a CAN frame
handleExtractAllSignals : CANId → (dlc : DLC) → Vec Byte (dlcBytes dlc) → StreamState → StreamState × Response
handleExtractAllSignals canId dlc bytes state =
  withDBC "ExtractAllSignals" state λ dbc →
    let frame = makeFrame canId dlc bytes
        results = extractAllSignals dbc frame
    in (state , Response.ExtractionResultsResponse
                  (ExtractionResults.values results)
                  (ExtractionResults.errors results)
                  (ExtractionResults.absent results))

-- Update specific signals in a CAN frame
handleUpdateFrame : CANId → (dlc : DLC) → Vec Byte (dlcBytes dlc) → List JSON → StreamState → StreamState × Response
handleUpdateFrame canId dlc bytes signalsJSON state =
  withDBC "UpdateFrame" state λ dbc →
    let frame = makeFrame canId dlc bytes
    in parseSignals dbc signalsJSON frame
  where
    parseSignals : ∀ {m} → DBC → List JSON → CANFrame m → StreamState × Response
    parseSignals dbc signals frame with parseSignalList signals
    ... | nothing = (state , Response.Error "UpdateFrame: failed to parse signal list")
    ... | just signalPairs with updateFrame dbc canId frame signalPairs
    ...   | inj₁ err = (state , Response.Error ("UpdateFrame: " ++ₛ err))
    ...   | inj₂ updatedFrame = (state , Response.ByteArray (CANFrame.payload updatedFrame))

-- Validate DBC structure: parse JSON, then run comprehensive validator
handleValidateDBC : JSON → StreamState → StreamState × Response
handleValidateDBC dbcJSON state =
  parseHelper (parseDBCWithErrors dbcJSON)
  where
    parseHelper : String ⊎ DBC → StreamState × Response
    parseHelper (inj₁ parseErr) =
      (state , Response.Error ("ValidateDBC: parse error: " ++ₛ parseErr))
    parseHelper (inj₂ dbc) =
      (state , Response.ValidationResponse (validateDBCFull dbc))

-- Format DBC: returns currently-loaded DBC as JSON
handleFormatDBC : StreamState → StreamState × Response
handleFormatDBC state =
  withDBC "FormatDBC" state λ dbc → (state , Response.DBCResponse (formatDBC dbc))

-- ============================================================================
-- INDEX-BASED HANDLERS (Binary FFI — no JSON signal parsing)
-- ============================================================================

-- Build CAN frame from signal index-value pairs (no string allocation)
handleBuildFrameByIndex : CANId → (dlc : DLC) → List (ℕ × ℚ) → StreamState → StreamState × Response
handleBuildFrameByIndex canId dlc signalPairs state =
  withDBC "BuildFrame" state λ dbc →
    buildHelper (buildFrameByIndex dbc canId (DLC.code dlc) signalPairs)
  where
    buildHelper : String ⊎ Vec Byte (dlcBytes dlc) → StreamState × Response
    buildHelper (inj₁ err) = (state , Response.Error ("BuildFrame: " ++ₛ err))
    buildHelper (inj₂ frameBytes) = (state , Response.ByteArray frameBytes)

-- Update CAN frame signals by index (no string allocation)
handleUpdateFrameByIndex : CANId → (dlc : DLC) → Vec Byte (dlcBytes dlc) → List (ℕ × ℚ) → StreamState → StreamState × Response
handleUpdateFrameByIndex canId dlc bytes signalPairs state =
  withDBC "UpdateFrame" state λ dbc →
    let frame = makeFrame canId dlc bytes
    in (state , formatResult (updateFrameByIndex dbc canId frame signalPairs))
  where
    formatResult : String ⊎ CANFrame (dlcBytes dlc) → Response
    formatResult (inj₁ err) = Response.Error ("UpdateFrame: " ++ₛ err)
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
