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
open import Data.List using (List; []; _∷_; reverse)
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
open import Aletheia.CAN.DLC using (dlcToBytes)
open import Aletheia.CAN.BatchExtraction using (extractAllSignals; ExtractionResults)
open import Aletheia.CAN.BatchFrameBuilding using (buildFrame; updateFrame)

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
  makeFrame : ∀ {n} → CANId → ℕ → Vec Byte n → CANFrame n
  makeFrame msgId dlc bytes = record
    { id = msgId
    ; dlc = dlc
    ; payload = bytes
    }

  -- Common preamble: validate DBC loaded (prefixes error with command name)
  withDBC : String → StreamState → (DBC → StreamState × Response) → StreamState × Response
  withDBC cmd state cont with StreamState.dbc state
  ... | nothing  = (state , Response.Error (cmd ++ₛ ": DBC not loaded"))
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

-- Set properties command: parse JSON properties to LTL
handleSetProperties : List JSON → StreamState → StreamState × Response
handleSetProperties propJSONs state with StreamState.phase state
... | WaitingForDBC = (state , Response.Error "SetProperties: DBC not loaded")
... | ReadyToStream = parseAllProperties propJSONs 0 []
  where
    parseAllProperties : List JSON → ℕ → List PropertyState → StreamState × Response
    parseAllProperties [] idx acc =
      let newState = mkStreamState ReadyToStream (StreamState.dbc state) (reverse acc) nothing emptyCache
      in (newState , Response.Success "Properties set successfully")
    parseAllProperties (json ∷ rest) idx acc with parseProperty json
    ... | nothing = (state , Response.Error ("SetProperties: failed to parse property " ++ₛ showℕ idx))
    ... | just prop =
        let atoms = collectAtoms prop
            proc = initProc (indexFormula prop)
            propState = mkPropertyState idx prop atoms proc
        in parseAllProperties rest (idx + 1) (propState ∷ acc)
... | Streaming = (state , Response.Error "SetProperties: stream is active")

-- Start stream command: transition to streaming mode
handleStartStream : StreamState → StreamState × Response
handleStartStream state with StreamState.phase state
... | WaitingForDBC = (state , Response.Error "StartStream: DBC not loaded")
... | ReadyToStream =
  let newState = mkStreamState Streaming (StreamState.dbc state) (StreamState.properties state) nothing (StreamState.signalCache state)
  in (newState , Response.Success "Streaming started")
... | Streaming = (state , Response.Error "StartStream: already streaming")

-- End stream command: finalize all properties and transition back to ready state
handleEndStream : StreamState → StreamState × Response
handleEndStream state with StreamState.phase state
... | Streaming =
  let newState = mkStreamState ReadyToStream (StreamState.dbc state) (StreamState.properties state) (StreamState.prevFrame state) (StreamState.signalCache state)
      results = finalizeProperties (StreamState.properties state)
  in (newState , Response.Complete results)
  where
    verdictToResult : ℕ → FinalVerdict → PR.PropertyResult
    verdictToResult idx Holds = PR.PropertyResult.Satisfaction idx
    verdictToResult idx (Fails reason) = PR.PropertyResult.Violation idx (mkCounterexampleData 0 reason)
    finalizeProperties : List PropertyState → List PR.PropertyResult
    finalizeProperties [] = []
    finalizeProperties (propState ∷ rest) =
      verdictToResult (PropertyState.index propState) (finalizeL (PropertyState.proc propState))
      ∷ finalizeProperties rest
... | _ = (state , Response.Error "EndStream: not currently streaming")

-- Build CAN frame from signal values
handleBuildFrame : CANId → (dlc : ℕ) → List JSON → StreamState → StreamState × Response
handleBuildFrame canId dlc signalsJSON state =
  withDBC "BuildFrame" state λ dbc → parseSignals dbc signalsJSON
  where
    parseSignals : DBC → List JSON → StreamState × Response
    parseSignals dbc signals with parseSignalList signals
    ... | nothing = (state , Response.Error "BuildFrame: failed to parse signal list")
    ... | just signalPairs with buildFrame dbc canId dlc signalPairs
    ...   | inj₁ err = (state , Response.Error ("BuildFrame: " ++ₛ err))
    ...   | inj₂ frameBytes = (state , Response.ByteArray frameBytes)

-- Extract all signals from a CAN frame
handleExtractAllSignals : CANId → (dlc : ℕ) → Vec Byte (dlcToBytes dlc) → StreamState → StreamState × Response
handleExtractAllSignals canId dlc bytes state =
  withDBC "ExtractAllSignals" state λ dbc →
    let frame = makeFrame canId dlc bytes
        results = extractAllSignals dbc frame
    in (state , Response.ExtractionResultsResponse
                  (ExtractionResults.values results)
                  (ExtractionResults.errors results)
                  (ExtractionResults.absent results))

-- Update specific signals in a CAN frame
handleUpdateFrame : CANId → (dlc : ℕ) → Vec Byte (dlcToBytes dlc) → List JSON → StreamState → StreamState × Response
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
