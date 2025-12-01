{-# OPTIONS --safe --without-K --guardedness #-}

-- Streaming protocol state machine and command handlers.
-- Manages state transitions: WaitingForDBC → ReadyToStream → Streaming.
-- Accumulates frames and checks LTL properties incrementally.
module Aletheia.Protocol.StreamState where

open import Data.String using (String; toList) renaming (_++_ to _++S_)
open import Data.List using (List; []; _∷_; length; _++_)
open import Data.List as L using (map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe as M using (map)
open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Char using (Char)
open import Aletheia.DBC.Types using (DBC)
open import Aletheia.DBC.JSONParser using (parseDBC)
open import Aletheia.LTL.Syntax using (LTL)
open import Aletheia.LTL.SignalPredicate using (SignalPredicate)
open import Aletheia.Protocol.JSON using (JSON; JObject; lookupString; lookupObject; lookup; formatJSON; getRational)
open import Data.Rational using (ℚ)
open import Data.Rational.Show as RatShow using ()
open import Aletheia.LTL.JSON using (parseProperty; dispatchPredicate; parseSignalPredicate; parseAtomic; parseLTL; parseLTLDispatch; parseLTLObject; dispatchOperator; parseLTLObjectHelper)
open import Aletheia.LTL.SignalPredicate using (SignalPredicate)
open import Aletheia.Data.Message  -- Includes Response, StreamCommand, etc.
open import Aletheia.Trace.CANTrace using (TimedFrame)
open import Aletheia.CAN.Frame using (CANFrame)
-- Note: Not importing Response from Protocol.Response to avoid name clash

-- ============================================================================
-- STREAM STATE
-- ============================================================================

-- State machine for streaming protocol
data StreamPhase : Set where
  WaitingForDBC : StreamPhase      -- Initial state, waiting for ParseDBC
  ReadyToStream : StreamPhase      -- DBC parsed, waiting for SetProperties or StartStream
  Streaming : StreamPhase          -- Active streaming mode

-- Complete stream state
record StreamState : Set where
  constructor mkStreamState
  field
    phase : StreamPhase
    dbc : Maybe DBC
    properties : List (ℕ × LTL SignalPredicate)  -- Indexed properties
    accumulatedFrames : List TimedFrame           -- Frames seen so far (for incremental checking)

-- Initial empty state
initialState : StreamState
initialState = mkStreamState WaitingForDBC nothing [] []

-- ============================================================================
-- STATE TRANSITIONS (Command Handlers)
-- ============================================================================

-- Parse DBC command: reset state and parse DBC from JSON
handleParseDBC-State : JSON → StreamState → StreamState × Response
handleParseDBC-State dbcJSON state =
  parseHelper (parseDBC dbcJSON)
  where
    parseHelper : Maybe DBC → StreamState × Response
    parseHelper nothing =
      (state , Response.Error "Failed to parse DBC JSON")
    parseHelper (just dbc) =
      let newState = mkStreamState ReadyToStream (just dbc) [] []  -- Reset properties and frames
      in (newState , Response.Success "DBC parsed successfully")

-- Set properties command: parse JSON properties to LTL
handleSetProperties-State : List JSON → StreamState → StreamState × Response
handleSetProperties-State propJSONs state with StreamState.phase state
... | WaitingForDBC = (state , Response.Error "Must call ParseDBC before SetProperties")
... | ReadyToStream = parseAllProperties propJSONs 0 []
  where
    -- Parse all properties and index them
    parseAllProperties : List JSON → ℕ → List (ℕ × LTL SignalPredicate) → StreamState × Response
    parseAllProperties [] idx acc =
      let newState = mkStreamState ReadyToStream (StreamState.dbc state) acc []  -- Reset accumulated frames when setting properties
      in (newState , Response.Success "Properties set successfully")
    parseAllProperties (json ∷ rest) idx acc with parseProperty json
    ... | nothing = (state , Response.Error ("Failed to parse property " ++S showℕ idx))
    ... | just prop = parseAllProperties rest (idx + 1) (acc ++ ((idx , prop) ∷ []))
... | Streaming = (state , Response.Error "Cannot set properties while streaming")

-- Start stream command: transition to streaming mode
handleStartStream-State : StreamState → StreamState × Response
handleStartStream-State state with StreamState.phase state
... | WaitingForDBC = (state , Response.Error "Must call ParseDBC before StartStream")
... | ReadyToStream =
  let newState = mkStreamState Streaming (StreamState.dbc state) (StreamState.properties state) (StreamState.accumulatedFrames state)
  in (newState , Response.Success "Streaming started")
... | Streaming = (state , Response.Error "Already streaming")

-- End stream command: transition back to ready state
handleEndStream-State : StreamState → StreamState × Response
handleEndStream-State state with StreamState.phase state
... | Streaming =
  let newState = mkStreamState ReadyToStream (StreamState.dbc state) (StreamState.properties state) (StreamState.accumulatedFrames state)
  in (newState , Response.Complete)
... | _ = (state , Response.Error "Not currently streaming")

-- ============================================================================
-- FRAME PROCESSING (LTL Checking)
-- ============================================================================

-- Process incoming CAN frame: accumulate and check all properties
handleDataFrame : StreamState → ℕ → CANFrame → StreamState × Response
handleDataFrame state timestamp frame with StreamState.phase state
... | WaitingForDBC = (state , Response.Error "Must call ParseDBC before sending frames")
... | ReadyToStream = (state , Response.Error "Must call StartStream before sending frames")
... | Streaming with StreamState.dbc state
...   | nothing = (state , Response.Error "No DBC loaded")
...   | just dbc = processFrame dbc
  where
    open import Aletheia.CAN.Frame using (CANFrame)
    open import Aletheia.LTL.Incremental using (checkWithCounterexample; CheckResult; Pass; Fail; Counterexample)
    open import Aletheia.LTL.SignalPredicate using (evalOnFrameWithTrace)
    open import Aletheia.LTL.Syntax using (mapLTL)
    open import Aletheia.Protocol.Response as PR using (mkCounterexampleData; PropertyResult)

    processFrame : DBC → StreamState × Response
    processFrame dbc =
      let timedFrame = record { timestamp = timestamp ; frame = frame }
          newFrames = StreamState.accumulatedFrames state ++ (timedFrame ∷ [])
          newState = mkStreamState Streaming (just dbc) (StreamState.properties state) newFrames
      in checkProps newState dbc newFrames (StreamState.properties newState)
      where
        -- Check all properties and return first violation or Ack
        checkProps : StreamState → DBC → List TimedFrame → List (ℕ × LTL SignalPredicate) → StreamState × Response
        checkProps st dbc frames [] = (st , Response.Ack)  -- No violations
        checkProps st dbc frames ((idx , prop) ∷ rest) with mapLTL (evalOnFrameWithTrace dbc frames) prop | checkWithCounterexample frames (mapLTL (evalOnFrameWithTrace dbc frames) prop)
        ... | ltlFormula | Pass = checkProps st dbc frames rest  -- Property holds, check next
        ... | ltlFormula | Fail ce =
          let open Counterexample ce
              ceData = mkCounterexampleData (TimedFrame.timestamp violatingFrame) reason
              violation = PR.PropertyResult.Violation idx ceData
          in (st , Response.PropertyResponse violation)

-- Process a stream command and update state
processStreamCommand : StreamCommand → StreamState → StreamState × Response
processStreamCommand (ParseDBC dbcJSON) state = handleParseDBC-State dbcJSON state
processStreamCommand (SetProperties props) state = handleSetProperties-State props state
processStreamCommand StartStream state = handleStartStream-State state
processStreamCommand (Encode msgName sigName value) state =
  -- Service command, doesn't change state
  (state , Response.Error "Encode not yet implemented")
processStreamCommand (Decode msgName sigName bytes) state =
  -- Service command, doesn't change state
  (state , Response.Error "Decode not yet implemented")
processStreamCommand EndStream state = handleEndStream-State state
