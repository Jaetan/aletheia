{-# OPTIONS --sized-types --without-K #-}

-- Streaming protocol state machine and command handlers.
--
-- Purpose: Manage state transitions and process commands/data frames.
-- States: WaitingForDBC → ReadyToStream → Streaming.
-- Handlers: processStreamCommand (parseDBC, setProperties, startStream, endStream),
--           handleDataFrame (extract signals, check LTL incrementally, emit violations).
-- Role: Core protocol logic used by Main to maintain session state.
--
-- State machine enforces: DBC must be loaded before properties, properties before streaming.
-- LTL checking: Incremental stateful evaluation (O(1) memory) with immediate violation reporting.
--
-- NOTE: Uses --sized-types for compatibility with coinductive stream interface in Main.
--       This makes the module incompatible with --safe.
module Aletheia.Protocol.StreamState where

open import Data.String using (String; toList) renaming (_++_ to _++ₛ_)
open import Data.String.Properties renaming (_≟_ to _≟ₛ_)
open import Data.List using (List; []; _∷_; length; reverse) renaming (_++_ to _++ₗ_)
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
open import Data.Sum using (_⊎_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Aletheia.Prelude using (findByPredicate)
open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal)
open import Aletheia.DBC.JSONParser using (parseDBCWithErrors)
open import Aletheia.DBC.Properties using (validateDBC)
open import Aletheia.LTL.Syntax using (LTL)
open import Aletheia.LTL.SignalPredicate using (SignalPredicate; evalPredicateWithPrev)
open import Aletheia.LTL.Incremental using (LTLEvalState; StepResult; initState; stepEval; Continue; Violated; Satisfied)
open import Aletheia.Protocol.JSON using (JSON; JObject; lookupString; lookupObject; formatJSON; getRational; getObject; lookupRational)
open import Data.Rational using (ℚ; _/_)
open import Data.Rational.Show as RatShow using ()
open import Aletheia.LTL.JSON using (parseProperty; dispatchPredicate; parseSignalPredicate; parseAtomic; parseLTL; parseLTLDispatch; parseLTLObject; dispatchOperator; parseLTLObjectHelper)
open import Aletheia.Data.Message  -- Includes Response, StreamCommand, etc.
open import Aletheia.Trace.CANTrace using (TimedFrame)
open import Aletheia.CAN.Frame using (CANFrame; CANId; Byte)
open import Aletheia.CAN.DBCHelpers using (findSignalByName; findMessageById)
open import Aletheia.CAN.SignalExtraction using (extractSignalWithContext)
open import Aletheia.CAN.Encoding using (injectSignal; extractSignal)
open import Aletheia.CAN.ExtractionResult using (ExtractionResult; Success; SignalNotInDBC; SignalNotPresent; ExtractionFailed; ValueOutOfBounds; getValue)
open import Aletheia.CAN.BatchExtraction using (extractAllSignals; ExtractionResults)
open import Aletheia.CAN.BatchFrameBuilding using (buildFrame; updateFrame)
-- Note: Not importing Response from Protocol.Response to avoid name clash

-- ============================================================================
-- STREAM STATE
-- ============================================================================

-- State machine for streaming protocol
data StreamPhase : Set where
  WaitingForDBC : StreamPhase      -- Initial state, waiting for ParseDBC
  ReadyToStream : StreamPhase      -- DBC parsed, waiting for SetProperties or StartStream
  Streaming : StreamPhase          -- Active streaming mode

-- Property with evaluation state for incremental checking
record PropertyState : Set where
  constructor mkPropertyState
  field
    index : ℕ
    formula : LTL SignalPredicate
    evalState : LTLEvalState  -- Incremental evaluation state

-- Complete stream state
record StreamState : Set where
  constructor mkStreamState
  field
    phase : StreamPhase
    dbc : Maybe DBC
    properties : List PropertyState    -- Properties with incremental eval state
    prevFrame : Maybe TimedFrame       -- Previous frame for ChangedBy predicate

-- Initial empty state
initialState : StreamState
initialState = mkStreamState WaitingForDBC nothing [] nothing

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
-- HELPER FUNCTIONS FOR FRAME CONSTRUCTION
-- ============================================================================

-- Parse JSON array of signal objects into (name, value) pairs
-- Used by BuildFrame and UpdateFrame commands
parseSignalList : List JSON → Maybe (List (String × ℚ))
parseSignalList [] = just []
parseSignalList (obj ∷ rest) = do
  fields ← getObject obj
  name ← lookupString "name" fields
  value ← lookupRational "value" fields
  restParsed ← parseSignalList rest
  just ((name , value) ∷ restParsed)

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

-- Parse DBC command: reset state, parse DBC from JSON, and validate
handleParseDBC-State : JSON → StreamState → StreamState × Response
handleParseDBC-State dbcJSON state =
  parseHelper (parseDBCWithErrors dbcJSON)
  where
    open import Data.Sum using (inj₁; inj₂)

    parseHelper : String ⊎ DBC → StreamState × Response
    parseHelper (inj₁ parseError) =
      (state , Response.Error ("DBC parse error: " ++ₛ parseError))
    parseHelper (inj₂ dbc) with validateDBC dbc
    ... | inj₁ validationError =
      (state , Response.Error ("DBC validation failed: " ++ₛ validationError))
    ... | inj₂ _ =
      let newState = mkStreamState ReadyToStream (just dbc) [] nothing  -- Reset properties and prevFrame
      in (newState , Response.Success "DBC parsed and validated successfully")

-- Set properties command: parse JSON properties to LTL
handleSetProperties-State : List JSON → StreamState → StreamState × Response
handleSetProperties-State propJSONs state with StreamState.phase state
... | WaitingForDBC = (state , Response.Error "Must call ParseDBC before SetProperties")
... | ReadyToStream = parseAllProperties propJSONs 0 []
  where
    -- Parse all properties and index them with initialized eval state
    parseAllProperties : List JSON → ℕ → List PropertyState → StreamState × Response
    parseAllProperties [] idx acc =
      let newState = mkStreamState ReadyToStream (StreamState.dbc state) acc nothing  -- Reset prevFrame when setting properties
      in (newState , Response.Success "Properties set successfully")
    parseAllProperties (json ∷ rest) idx acc with parseProperty json
    ... | nothing = (state , Response.Error ("Failed to parse property " ++ₛ showℕ idx))
    ... | just prop =
        let propState = mkPropertyState idx prop (initState prop)  -- Initialize eval state
        in parseAllProperties rest (idx + 1) (acc ++ₗ (propState ∷ []))
... | Streaming = (state , Response.Error "Cannot set properties while streaming")

-- Start stream command: transition to streaming mode
handleStartStream-State : StreamState → StreamState × Response
handleStartStream-State state with StreamState.phase state
... | WaitingForDBC = (state , Response.Error "Must call ParseDBC before StartStream")
... | ReadyToStream =
  let newState = mkStreamState Streaming (StreamState.dbc state) (StreamState.properties state) nothing
  in (newState , Response.Success "Streaming started")
... | Streaming = (state , Response.Error "Already streaming")

-- End stream command: transition back to ready state
handleEndStream-State : StreamState → StreamState × Response
handleEndStream-State state with StreamState.phase state
... | Streaming =
  let newState = mkStreamState ReadyToStream (StreamState.dbc state) (StreamState.properties state) (StreamState.prevFrame state)
  in (newState , Response.Complete)
... | _ = (state , Response.Error "Not currently streaming")

-- ============================================================================
-- FRAME PROCESSING (LTL Checking)
-- ============================================================================

-- Process incoming CAN frame with incremental LTL property checking
--
-- Algorithm:
--   1. Validate state machine: must be in Streaming phase with DBC loaded
--   2. Create TimedFrame from timestamp and frame
--   3. For each property: call stepEval with (prevFrame, currFrame, evalState)
--   4. Update property eval states and detect violations/satisfactions
--   5. Return immediately on first violation, otherwise continue checking
--   6. Update prevFrame to current frame for next iteration
--
-- O(1) Memory Guarantee:
--   - Properties maintain fixed-size eval state (no trace accumulation)
--   - Only prevFrame stored (for ChangedBy predicate support)
--   - LTL.Incremental.stepEval processes one frame at a time
--   - No history lists, no unbounded growth
--
-- Incremental Checking:
--   - stepEval: LTLEvalState → Frame → StepResult
--   - Result types: Continue (keep checking), Violated (stop), Satisfied (terminal)
--   - Eval state encodes LTL automaton position (finite state machine)
--   - Always/Eventually: track whether seen violation/satisfaction so far
--   - Until: track left/right satisfaction status
--   - Next: defer to next frame
--
-- Violation Reporting:
--   - First violation detected → PropertyResponse with counterexample
--   - Counterexample includes: timestamp, reason, property index
--   - Violated property keeps old eval state (frozen at violation point)
--   - Other properties continue checking on subsequent frames
--
-- State Updates:
--   - prevFrame: updated to current frame after all properties checked
--   - properties: eval states updated with stepEval results
--   - phase: remains Streaming (only EndStream changes phase)
--
handleDataFrame : StreamState → ℕ → CANFrame → StreamState × Response
handleDataFrame state timestamp frame with StreamState.phase state
... | WaitingForDBC = (state , Response.Error "Must call ParseDBC before sending frames")
... | ReadyToStream = (state , Response.Error "Must call StartStream before sending frames")
... | Streaming with StreamState.dbc state
...   | nothing = (state , Response.Error "No DBC loaded")
...   | just dbc = processFrame dbc
  where
    open import Aletheia.CAN.Frame using (CANFrame)
    open import Aletheia.Protocol.Response as PR using (mkCounterexampleData; PropertyResult)
    open import Aletheia.LTL.Incremental using (Counterexample)

    -- Evaluator function for stepEval (uses evalPredicateWithPrev)
    evalPred : Maybe TimedFrame → TimedFrame → SignalPredicate → Bool
    evalPred prev curr pred = evalPredicateWithPrev dbc prev pred curr

    processFrame : DBC → StreamState × Response
    processFrame dbc =
      let timedFrame = record { timestamp = timestamp ; frame = frame }
          prev = StreamState.prevFrame state
      in checkPropsIncremental (StreamState.properties state) [] prev timedFrame
      where
        -- Incrementally check all properties and update their states
        -- acc: accumulator for updated properties (reversed order)
        checkPropsIncremental : List PropertyState → List PropertyState → Maybe TimedFrame → TimedFrame → StreamState × Response
        checkPropsIncremental [] acc prev curr =
          -- All properties checked, no violations
          let updatedProps = reverse acc
              newState = mkStreamState Streaming (just dbc) updatedProps (just curr)
          in (newState , Response.Ack)
        checkPropsIncremental (propState ∷ rest) acc prev curr =
          let formula = PropertyState.formula propState
              evalState = PropertyState.evalState propState
              idx = PropertyState.index propState
              result = stepEval formula evalPred evalState prev curr
          in handleStepResult result propState rest acc prev curr
          where
            handleStepResult : StepResult LTLEvalState → PropertyState → List PropertyState → List PropertyState → Maybe TimedFrame → TimedFrame → StreamState × Response
            handleStepResult (Continue _ newEvalState) prop remaining accum p c =
              let updatedProp = mkPropertyState (PropertyState.index prop) (PropertyState.formula prop) newEvalState
              in checkPropsIncremental remaining (updatedProp ∷ accum) p c
            handleStepResult (Violated ce) prop remaining accum p c =
              -- Property violated, return immediately with current state
              let open Counterexample ce
                  ceData = mkCounterexampleData (TimedFrame.timestamp violatingFrame) reason
                  violation = PR.PropertyResult.Violation (PropertyState.index prop) ceData
                  -- Reconstruct properties list (violated property keeps old state)
                  allProps = reverse accum ++ₗ (prop ∷ remaining)
                  newState = mkStreamState Streaming (just dbc) allProps (just c)
              in (newState , Response.PropertyResponse violation)
            handleStepResult Satisfied prop remaining accum p c =
              -- Eventually satisfied, keep checking other properties
              let updatedProp = prop  -- Keep same state (satisfied terminal state)
              in checkPropsIncremental remaining (updatedProp ∷ accum) p c

-- ============================================================================
-- BATCH SIGNAL OPERATIONS HANDLERS (Phase 2B.1)
-- ============================================================================

-- Build CAN frame from signal values
handleBuildFrame-State : JSON → List JSON → StreamState → StreamState × Response
handleBuildFrame-State canIdJSON signalsJSON state =
  buildHelper (StreamState.dbc state)
  where
    open import Aletheia.Protocol.JSON using (getNat)
    open import Aletheia.Prelude using (standard-can-id-max)
    open import Data.Nat.DivMod using (_mod_)

    buildHelper : Maybe DBC → StreamState × Response
    buildHelper nothing = (state , Response.Error "DBC not loaded")
    buildHelper (just dbc) with getNat canIdJSON
    ... | nothing = (state , Response.Error "Invalid CAN ID")
    ... | just canIdNat =
          let canId = CANId.Standard (canIdNat mod standard-can-id-max)
          in parseSignals canId signalsJSON
      where
        parseSignals : CANId → List JSON → StreamState × Response
        parseSignals canId signals with parseSignalList signals
        ... | nothing = (state , Response.Error "Failed to parse signal list")
        ... | just signalPairs with buildFrame dbc canId signalPairs
        ...   | nothing = (state , Response.Error "Frame building failed (signals overlap, not found, or values out of bounds)")
        ...   | just frameBytes = (state , Response.ByteArray frameBytes)

-- Extract all signals from a CAN frame
handleExtractAllSignals-State : JSON → Vec Byte 8 → StreamState → StreamState × Response
handleExtractAllSignals-State canIdJSON bytes state =
  extractHelper (StreamState.dbc state)
  where
    open import Aletheia.Protocol.JSON using (getNat)
    open import Aletheia.Prelude using (standard-can-id-max)
    open import Data.Nat.DivMod using (_mod_)

    extractHelper : Maybe DBC → StreamState × Response
    extractHelper nothing = (state , Response.Error "DBC not loaded")
    extractHelper (just dbc) with getNat canIdJSON
    ... | nothing = (state , Response.Error "Invalid CAN ID")
    ... | just canIdNat =
          let canId = CANId.Standard (canIdNat mod standard-can-id-max)
              frame = makeFrame canId bytes
              results = extractAllSignals dbc frame
          in (state , Response.ExtractionResultsResponse
                        (ExtractionResults.values results)
                        (ExtractionResults.errors results)
                        (ExtractionResults.absent results))

-- Update specific signals in a CAN frame
handleUpdateFrame-State : JSON → Vec Byte 8 → List JSON → StreamState → StreamState × Response
handleUpdateFrame-State canIdJSON bytes signalsJSON state =
  updateHelper (StreamState.dbc state)
  where
    open import Aletheia.Protocol.JSON using (getNat)
    open import Aletheia.Prelude using (standard-can-id-max)
    open import Data.Nat.DivMod using (_mod_)

    updateHelper : Maybe DBC → StreamState × Response
    updateHelper nothing = (state , Response.Error "DBC not loaded")
    updateHelper (just dbc) with getNat canIdJSON
    ... | nothing = (state , Response.Error "Invalid CAN ID")
    ... | just canIdNat =
          let canId = CANId.Standard (canIdNat mod standard-can-id-max)
              frame = makeFrame canId bytes
          in parseSignals canId signalsJSON frame
      where
        parseSignals : CANId → List JSON → CANFrame → StreamState × Response
        parseSignals canId signals frame with parseSignalList signals
        ... | nothing = (state , Response.Error "Failed to parse signal list")
        ... | just signalPairs with updateFrame dbc canId frame signalPairs
        ...   | nothing = (state , Response.Error "Frame update failed (signals not found or values out of bounds)")
        ...   | just updatedFrame = (state , Response.ByteArray (CANFrame.payload updatedFrame))

-- ============================================================================
-- STREAM COMMAND DISPATCHER
-- ============================================================================

-- Process a stream command and update state
processStreamCommand : StreamCommand → StreamState → StreamState × Response
processStreamCommand (ParseDBC dbcJSON) state = handleParseDBC-State dbcJSON state
processStreamCommand (SetProperties props) state = handleSetProperties-State props state
processStreamCommand StartStream state = handleStartStream-State state
processStreamCommand (BuildFrame canIdJSON signalsJSON) state = handleBuildFrame-State canIdJSON signalsJSON state
processStreamCommand (ExtractAllSignals canIdJSON bytes) state = handleExtractAllSignals-State canIdJSON bytes state
processStreamCommand (UpdateFrame canIdJSON bytes signalsJSON) state = handleUpdateFrame-State canIdJSON bytes signalsJSON state
processStreamCommand EndStream state = handleEndStream-State state
