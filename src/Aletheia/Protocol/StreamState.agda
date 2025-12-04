{-# OPTIONS --without-K --guardedness --sized-types #-}

-- Streaming protocol state machine and command handlers.
--
-- Purpose: Manage state transitions and process commands/data frames.
-- States: WaitingForDBC → ReadyToStream → Streaming.
-- Handlers: processStreamCommand (parseDBC, setProperties, startStream, endStream),
--           processDataFrame (extract signals, check LTL, emit violations).
-- Role: Core protocol logic used by Main to maintain session state.
--
-- State machine enforces: DBC must be loaded before properties, properties before streaming.
-- LTL checking: Coinductive evaluation over infinite traces with immediate violation reporting.
--
-- NOTE: Uses --sized-types for coinductive LTL checking (required for productivity/termination).
--       This makes the module incompatible with --safe, but is necessary for infinite trace semantics.
module Aletheia.Protocol.StreamState where

open import Size using (Size; ∞)
open import Codata.Sized.Thunk using (Thunk; force)
open import Codata.Sized.Delay using (Delay; now; later)
open import Codata.Sized.Colist as Colist using (Colist; []; _∷_)
open import Data.String using (String; toList) renaming (_++_ to _++S_)
open import Data.String.Properties renaming (_≟_ to _≟ₛ_)
open import Data.List using (List; []; _∷_; length) renaming (_++_ to _++L_)
open import Data.List as L using (map)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Maybe as M using (map)
open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Char using (Char)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Vec using (Vec; _∷_; [])
open import Data.Fin using (Fin; toℕ; fromℕ<; #_)
open import Data.Integer using (ℤ; +_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Aletheia.Prelude using (findByPredicate)
open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal)
open import Aletheia.DBC.JSONParser using (parseDBC)
open import Aletheia.LTL.Syntax using (LTL)
open import Aletheia.LTL.SignalPredicate using (SignalPredicate)
open import Aletheia.Protocol.JSON using (JSON; JObject; lookupString; lookupObject; formatJSON; getRational)
open import Data.Rational using (ℚ; _/_)
open import Data.Rational.Show as RatShow using ()
open import Aletheia.LTL.JSON using (parseProperty; dispatchPredicate; parseSignalPredicate; parseAtomic; parseLTL; parseLTLDispatch; parseLTLObject; dispatchOperator; parseLTLObjectHelper)
open import Aletheia.Data.Message  -- Includes Response, StreamCommand, etc.
open import Aletheia.Trace.CANTrace using (TimedFrame)
open import Aletheia.CAN.Frame using (CANFrame; CANId; Byte)
open import Aletheia.CAN.SignalExtraction using (findSignalByName; extractSignalWithContext)
open import Aletheia.CAN.Encoding using (injectSignal; extractSignal)
open import Aletheia.CAN.ExtractionResult using (ExtractionResult; Success; SignalNotInDBC; SignalNotPresent; ExtractionFailed; ValueOutOfBounds; getValue)
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
-- HELPER FUNCTIONS
-- ============================================================================

-- Find message by name in DBC
findMessageByName : String → DBC → Maybe DBCMessage
findMessageByName name dbc = findByPredicate matchesName (DBC.messages dbc)
  where
    matchesName : DBCMessage → Bool
    matchesName msg = ⌊ DBCMessage.name msg ≟ₛ name ⌋

-- ============================================================================
-- COINDUCTIVE STREAM CONVERSION
-- ============================================================================

-- Convert finite list to coinductive colist
-- This allows us to use coinductive LTL checking on accumulated frames
listToColist : ∀ {A : Set} {i : Size} → List A → Colist A i
listToColist [] = []
listToColist (x ∷ xs) = x ∷ λ where .force → listToColist xs

-- Force a delayed computation to get immediate result
-- Used to extract CheckResult from Delay
-- NOTE: Marked TERMINATING because Delay is productive by construction
{-# TERMINATING #-}
forceDelay : ∀ {A : Set} → Delay A ∞ → A
forceDelay (now x) = x
forceDelay (later thunk) = forceDelay (thunk .force)

-- Create zero-filled frame with given message ID
makeZeroFrame : CANId → CANFrame
makeZeroFrame msgId =
  let zero : Byte
      zero = # 0
      zeros : Vec Byte 8
      zeros = zero ∷ zero ∷ zero ∷ zero ∷ zero ∷ zero ∷ zero ∷ zero ∷ []
  in record
    { id = msgId
    ; dlc = # 8
    ; payload = zeros
    }

-- Create frame from bytes and message ID
makeFrame : CANId → Vec Byte 8 → CANFrame
makeFrame msgId bytes = record
  { id = msgId
  ; dlc = # 8
  ; payload = bytes
  }

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
    ... | just prop = parseAllProperties rest (idx + 1) (acc ++L ((idx , prop) ∷ []))
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
    open import Aletheia.LTL.Coinductive using (checkColistCE)
    open import Aletheia.LTL.Incremental using (CheckResult; Pass; Fail; Counterexample)
    open import Aletheia.LTL.SignalPredicate using (evalOnFrameWithTrace)
    open import Aletheia.LTL.Syntax using (mapLTL)
    open import Aletheia.Protocol.Response as PR using (mkCounterexampleData; PropertyResult)

    processFrame : DBC → StreamState × Response
    processFrame dbc =
      let timedFrame = record { timestamp = timestamp ; frame = frame }
          newFrames = StreamState.accumulatedFrames state ++L (timedFrame ∷ [])
          newState = mkStreamState Streaming (just dbc) (StreamState.properties state) newFrames
      in checkProps newState dbc newFrames (StreamState.properties newState)
      where
        -- Check all properties and return first violation or Ack
        checkProps : StreamState → DBC → List TimedFrame → List (ℕ × LTL SignalPredicate) → StreamState × Response
        checkProps st dbc frames [] = (st , Response.Ack)  -- No violations
        checkProps st dbc frames ((idx , prop) ∷ rest) =
          let ltlFormula = mapLTL (evalOnFrameWithTrace dbc frames) prop
              colistFrames = listToColist frames
              delayedResult = checkColistCE ltlFormula colistFrames
              result = forceDelay delayedResult
          in handleResult result
          where
            handleResult : CheckResult → StreamState × Response
            handleResult Pass = checkProps st dbc frames rest  -- Property holds, check next
            handleResult (Fail ce) =
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
  encodeHelper (StreamState.dbc state)
  where
    encodeHelper : Maybe DBC → StreamState × Response
    encodeHelper nothing = (state , Response.Error "DBC not loaded")
    encodeHelper (just dbc) with findMessageByName msgName dbc
    ... | nothing = (state , Response.Error ("Message '" ++S msgName ++S "' not found"))
    ... | just msg with findSignalByName sigName msg
    ...   | nothing = (state , Response.Error ("Signal '" ++S sigName ++S "' not found"))
    ...   | just sig =
          let signalValue = (value / 1)  -- Convert ℤ to ℚ
              zeroFrame = makeZeroFrame (DBCMessage.id msg)
          in injectHelper (injectSignal signalValue (DBCSignal.signalDef sig) (DBCSignal.byteOrder sig) zeroFrame)
      where
        injectHelper : Maybe CANFrame → StreamState × Response
        injectHelper nothing = (state , Response.Error "Signal injection failed (value out of bounds)")
        injectHelper (just frame) = (state , Response.ByteArray (CANFrame.payload frame))

processStreamCommand (Decode msgName sigName bytes) state =
  -- Service command, doesn't change state
  decodeHelper (StreamState.dbc state)
  where
    decodeHelper : Maybe DBC → StreamState × Response
    decodeHelper nothing = (state , Response.Error "DBC not loaded")
    decodeHelper (just dbc) with findMessageByName msgName dbc
    ... | nothing = (state , Response.Error ("Message '" ++S msgName ++S "' not found"))
    ... | just msg =
          let frame = makeFrame (DBCMessage.id msg) bytes
          in extractHelper (extractSignalWithContext dbc frame sigName)
      where
        extractHelper : ExtractionResult → StreamState × Response
        extractHelper (Success value) = (state , Response.SignalValue value)
        extractHelper (SignalNotInDBC name) = (state , Response.Error ("Signal '" ++S name ++S "' not in DBC"))
        extractHelper (SignalNotPresent name reason) = (state , Response.Error ("Signal not present: " ++S reason))
        extractHelper (ValueOutOfBounds name val minVal maxVal) =
          (state , Response.Error ("Value out of bounds: " ++S RatShow.show val ++S " not in [" ++S RatShow.show minVal ++S ", " ++S RatShow.show maxVal ++S "]"))
        extractHelper (ExtractionFailed name reason) = (state , Response.Error ("Extraction failed: " ++S reason))

processStreamCommand EndStream state = handleEndStream-State state
