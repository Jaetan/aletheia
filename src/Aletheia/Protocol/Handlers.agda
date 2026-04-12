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
open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Product using (_×_; _,_)
open import Data.Bool using (if_then_else_)
open import Data.Vec using (Vec)
open import Data.Sum using (_⊎_; inj₁; inj₂; map₂)
open import Data.Rational using (ℚ)
open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal)
open import Aletheia.DBC.JSONParser using (parseDBCWithErrors)
open import Aletheia.DBC.Validator using (validateDBCFull; hasAnyError; formatIssuesText; errorIssues)
open import Aletheia.DBC.Formatter using (formatDBC)
open import Aletheia.LTL.Syntax using (LTL)
open import Aletheia.LTL.SignalPredicate using (SignalPredicate; SignalCache; emptyCache)
open import Aletheia.LTL.Incremental using (FinalVerdict; Holds; Fails; Unsure)
open import Aletheia.LTL.Coalgebra using (LTLProc; finalizeL; initProc)
open import Aletheia.LTL.JSON using (parseProperty)
open import Aletheia.Protocol.JSON using (JSON; lookupString; getObject; lookupRational)
open import Aletheia.Protocol.Message using (Response; StreamCommand; ParseDBC; SetProperties; StartStream; EndStream; BuildFrame; UpdateFrame; ExtractAllSignals; ValidateDBC; FormatDBC)
open import Aletheia.Protocol.Response as PR using (mkCounterexampleData; PropertyResult)
open import Aletheia.Trace.Time using (Timestamp; μs; mkTs)
open import Aletheia.CAN.Frame using (CANFrame; CANId; Byte)
open import Aletheia.CAN.DLC using (DLC; dlcBytes)
open import Aletheia.CAN.BatchExtraction using (extractAllSignals; ExtractionResults; PartitionedResults)
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
  )
open import Aletheia.Protocol.StreamState.Internals using (collectAtoms; indexFormula)

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
    ; dlc = dlc
    ; payload = bytes
    }

  -- Check DBC is loaded, returning the DBC or NoDBC error
  withDBC : StreamState → HandlerError ⊎ DBC
  withDBC state = require NoDBC (getDBC state)

  -- Require DBC loaded, wrapping NoDBC with command context
  withDBCContext : String → StreamState → (DBC → StreamState × Response) → StreamState × Response
  withDBCContext ctx state f with withDBC state
  ... | inj₁ err = (state , Response.Error (WithContext ctx (HandlerErr err)))
  ... | inj₂ dbc = f dbc

  -- Parse DBC from JSON, wrapping parse errors with command context
  withParsedDBC : String → JSON → StreamState → (DBC → StreamState × Response) → StreamState × Response
  withParsedDBC ctx dbcJSON state f with parseDBCWithErrors dbcJSON
  ... | inj₁ parseErr = (state , Response.Error (WithContext ctx (HandlerErr (WrappedParse parseErr))))
  ... | inj₂ dbc = f dbc

  -- Parse signal list from JSON, wrapping failure with command context
  withParsedSignals : String → StreamState → List JSON → (List (String × ℚ) → StreamState × Response) → StreamState × Response
  withParsedSignals ctx state signals f with parseSignalList signals
  ... | nothing = (state , Response.Error (WithContext ctx (HandlerErr SignalListParseFailed)))
  ... | just pairs = f pairs

  -- Canonical frame-result response: wrap FrameError with context or return
  -- the byte payload. All four frame handlers (build, buildByIndex, update,
  -- updateByIndex) route through this single function — update handlers
  -- pre-apply `CANFrame.payload` via `map₂` from `Data.Sum`. Previously each
  -- handler had its own `buildResult`/`updateResult`/`formatResult` local
  -- helper repeating the same error-wrapping lines; consolidating them here
  -- removes D1/D2/D3 duplication and matches the `withDBCContext` /
  -- `withParsedSignals` / `withParsedDBC` helper-naming convention above.
  frameResponse : String → ∀ {n} → FrameError ⊎ Vec Byte n → Response
  frameResponse ctx (inj₁ err)   = Response.Error (WithContext ctx (FrameErr err))
  frameResponse ctx (inj₂ bytes) = Response.ByteArray bytes

-- ============================================================================
-- COMMAND HANDLERS
-- ============================================================================

-- Parse DBC command: parse DBC from JSON, validate, and update state
handleParseDBC : JSON → StreamState → StreamState × Response
handleParseDBC dbcJSON state = withParsedDBC "ParseDBC" dbcJSON state λ dbc →
  let issues = validateDBCFull dbc
  in if hasAnyError issues
     then (state , Response.Error (WithContext "ParseDBC" (HandlerErr (ValidationFailed ("validation failed: " ++ₛ formatIssuesText (errorIssues issues))))))
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
  (Streaming dbc props nothing cache , Response.Success "Streaming started successfully")
handleStartStream WaitingForDBC =
  (WaitingForDBC , Response.Error (WithContext "StartStream" (HandlerErr NoDBC)))
handleStartStream state@(Streaming _ _ _ _) =
  (state , Response.Error (WithContext "StartStream" (HandlerErr AlreadyStreaming)))

-- Convert final verdict to property result (extracted for proof access).
-- Three verdicts map 1:1:
--   Holds   → Satisfaction
--   Fails   → Violation  (with reason in synthetic counterexample)
--   Unsure  → Unresolved (three-valued Kleene Unknown, e.g. Always(p)
--             where p's signal was never observed)
verdictToResult : ℕ → FinalVerdict → PR.PropertyResult
verdictToResult idx Holds            = PR.PropertyResult.Satisfaction idx
-- EOS Fails uses synthetic timestamp 0: the violation is the absence of
-- satisfaction over the entire trace (e.g. Eventually(p) never saw p),
-- so no single violating frame exists to timestamp.
verdictToResult idx (Fails reason)   = PR.PropertyResult.Violation idx (mkCounterexampleData (mkTs {u = μs} 0) reason)
verdictToResult idx (Unsure reason)  = PR.PropertyResult.Unresolved idx reason

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
handleBuildFrame canId dlc signalsJSON state = withDBCContext "BuildFrame" state λ dbc →
  withParsedSignals "BuildFrame" state signalsJSON λ signalPairs →
    (state , frameResponse "BuildFrame" (buildFrame dbc canId dlc signalPairs))

-- Extract all signals from a CAN frame
handleExtractAllSignals : CANId → (dlc : DLC) → Vec Byte (dlcBytes dlc) → StreamState → StreamState × Response
handleExtractAllSignals canId dlc bytes state = withDBCContext "ExtractAllSignals" state λ dbc →
  let frame = makeFrame canId dlc bytes
      results = extractAllSignals dbc frame
  in (state , Response.ExtractionResultsResponse
                (PartitionedResults.values results)
                (PartitionedResults.errors results)
                (PartitionedResults.absent results))

-- Update specific signals in a CAN frame
handleUpdateFrame : CANId → (dlc : DLC) → Vec Byte (dlcBytes dlc) → List JSON → StreamState → StreamState × Response
handleUpdateFrame canId dlc bytes signalsJSON state = withDBCContext "UpdateFrame" state λ dbc →
  let frame = makeFrame canId dlc bytes
  in withParsedSignals "UpdateFrame" state signalsJSON λ signalPairs →
    (state , frameResponse "UpdateFrame" (map₂ CANFrame.payload (updateFrame dbc canId frame signalPairs)))

-- Validate DBC structure: parse JSON, then run comprehensive validator
handleValidateDBC : JSON → StreamState → StreamState × Response
handleValidateDBC dbcJSON state = withParsedDBC "ValidateDBC" dbcJSON state λ dbc →
  (state , Response.ValidationResponse (validateDBCFull dbc))

-- Format DBC: returns currently-loaded DBC as JSON
handleFormatDBC : StreamState → StreamState × Response
handleFormatDBC state = withDBCContext "FormatDBC" state λ dbc →
  (state , Response.DBCResponse (formatDBC dbc))

-- ============================================================================
-- INDEX-BASED HANDLERS (Binary FFI — no JSON signal parsing)
-- ============================================================================

-- Build CAN frame from signal index-value pairs (no string allocation)
handleBuildFrameByIndex : CANId → (dlc : DLC) → List (ℕ × ℚ) → StreamState → StreamState × Response
handleBuildFrameByIndex canId dlc signalPairs state = withDBCContext "BuildFrame" state λ dbc →
  (state , frameResponse "BuildFrame" (buildFrameByIndex dbc canId dlc signalPairs))

-- Update CAN frame signals by index (no string allocation)
handleUpdateFrameByIndex : CANId → (dlc : DLC) → Vec Byte (dlcBytes dlc) → List (ℕ × ℚ) → StreamState → StreamState × Response
handleUpdateFrameByIndex canId dlc bytes signalPairs state = withDBCContext "UpdateFrame" state λ dbc →
  let frame = makeFrame canId dlc bytes
  in (state , frameResponse "UpdateFrame" (map₂ CANFrame.payload (updateFrameByIndex dbc canId frame signalPairs)))

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
