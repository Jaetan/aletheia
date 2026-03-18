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

open import Data.String using (String) renaming (_++_ to _++ₛ_)
import Data.String.Properties as String-Props
open import Data.List using (List; []; _∷_) renaming (_++_ to _++ₗ_)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Nat using (ℕ; zero; suc; _+_; _%_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Vec using (Vec; _∷_; [])
open import Data.Sum using (_⊎_)
open import Function using (case_of_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Aletheia.Prelude using (findByPredicate; standard-can-id-max)
open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal)
open import Aletheia.DBC.JSONParser using (parseDBCWithErrors)
open import Aletheia.DBC.Validator using (validateDBCFull; hasAnyError; formatIssuesText; errorIssues)
open import Aletheia.LTL.Syntax using (LTL; Atomic; Not; And; Or; Next; Always; Eventually; Until; Release; MetricEventually; MetricAlways; MetricUntil; MetricRelease)
open import Aletheia.LTL.SignalPredicate using (SignalPredicate; SignalVal; True; False; Unknown; SignalCache; emptyCache; updateCache; evalPredicateTV)
open import Aletheia.LTL.Incremental using (StepResult; Continue; Violated; Satisfied; FinalVerdict; Holds; Fails; Counterexample)
open import Aletheia.LTL.Coalgebra using (LTLProc; PredTable; stepL; finalizeL; initProc; simplify)
open import Aletheia.Protocol.JSON using (JSON; lookupString; getObject; lookupRational; getNat)
open import Data.Rational using (ℚ)
open import Aletheia.LTL.JSON using (parseProperty)
open import Aletheia.Data.Message  -- Includes Response, StreamCommand, etc.
open import Aletheia.Trace.CANTrace using (TimedFrame)
open import Aletheia.CAN.Frame using (CANFrame; CANId; Byte)
open import Aletheia.CAN.DBCHelpers using (findMessageById)
open import Aletheia.Protocol.Iteration using (StepOutcome; advance; halt; iterate)
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
    formula : LTL SignalPredicate    -- Original formula (for display/JSON)
    atoms : List SignalPredicate     -- Collected atomic predicates (for PredTable)
    proc : LTLProc                   -- ℕ-indexed formula state (for stepL)

-- Complete stream state
record StreamState : Set where
  constructor mkStreamState
  field
    phase : StreamPhase
    dbc : Maybe DBC
    properties : List PropertyState    -- Properties with incremental eval state
    prevFrame : Maybe TimedFrame       -- Previous frame for ChangedBy predicate
    signalCache : SignalCache          -- Last-known signal values for three-valued semantics

-- Initial empty state
initialState : StreamState
initialState = mkStreamState WaitingForDBC nothing [] nothing emptyCache

-- ============================================================================
-- HELPER FUNCTIONS
-- ============================================================================

-- Find message by name in DBC
findMessageByName : String → DBC → Maybe DBCMessage
findMessageByName name dbc = findByPredicate matchesName (DBC.messages dbc)
  where
    matchesName : DBCMessage → Bool
    matchesName msg = ⌊ String-Props._≟_ (DBCMessage.name msg) name ⌋

-- ============================================================================
-- FORMULA INDEXING (LTL SignalPredicate → LTLProc + atom list)
-- ============================================================================

-- Collect all atomic predicates in left-to-right tree order.
-- The resulting list maps ℕ indices to predicates for PredTable construction.
collectAtoms : LTL SignalPredicate → List SignalPredicate
collectAtoms (Atomic a)            = a ∷ []
collectAtoms (Not φ)               = collectAtoms φ
collectAtoms (And φ ψ)             = collectAtoms φ ++ₗ collectAtoms ψ
collectAtoms (Or φ ψ)              = collectAtoms φ ++ₗ collectAtoms ψ
collectAtoms (Next φ)              = collectAtoms φ
collectAtoms (Always φ)            = collectAtoms φ
collectAtoms (Eventually φ)        = collectAtoms φ
collectAtoms (Until φ ψ)           = collectAtoms φ ++ₗ collectAtoms ψ
collectAtoms (Release φ ψ)         = collectAtoms φ ++ₗ collectAtoms ψ
collectAtoms (MetricEventually _ _ φ)    = collectAtoms φ
collectAtoms (MetricAlways _ _ φ)        = collectAtoms φ
collectAtoms (MetricUntil _ _ φ ψ)      = collectAtoms φ ++ₗ collectAtoms ψ
collectAtoms (MetricRelease _ _ φ ψ)    = collectAtoms φ ++ₗ collectAtoms ψ

-- Replace each atom with its position index (counter-based, matches collectAtoms order)
private
  indexHelper : LTL SignalPredicate → ℕ → LTL ℕ × ℕ
  indexHelper (Atomic _) n            = (Atomic n , suc n)
  indexHelper (Not φ) n               = let (φ' , n') = indexHelper φ n in (Not φ' , n')
  indexHelper (And φ ψ) n             = let (φ' , n') = indexHelper φ n ; (ψ' , n'') = indexHelper ψ n' in (And φ' ψ' , n'')
  indexHelper (Or φ ψ) n              = let (φ' , n') = indexHelper φ n ; (ψ' , n'') = indexHelper ψ n' in (Or φ' ψ' , n'')
  indexHelper (Next φ) n              = let (φ' , n') = indexHelper φ n in (Next φ' , n')
  indexHelper (Always φ) n            = let (φ' , n') = indexHelper φ n in (Always φ' , n')
  indexHelper (Eventually φ) n        = let (φ' , n') = indexHelper φ n in (Eventually φ' , n')
  indexHelper (Until φ ψ) n           = let (φ' , n') = indexHelper φ n ; (ψ' , n'') = indexHelper ψ n' in (Until φ' ψ' , n'')
  indexHelper (Release φ ψ) n         = let (φ' , n') = indexHelper φ n ; (ψ' , n'') = indexHelper ψ n' in (Release φ' ψ' , n'')
  indexHelper (MetricEventually w s φ) n    = let (φ' , n') = indexHelper φ n in (MetricEventually w s φ' , n')
  indexHelper (MetricAlways w s φ) n        = let (φ' , n') = indexHelper φ n in (MetricAlways w s φ' , n')
  indexHelper (MetricUntil w s φ ψ) n      = let (φ' , n') = indexHelper φ n ; (ψ' , n'') = indexHelper ψ n' in (MetricUntil w s φ' ψ' , n'')
  indexHelper (MetricRelease w s φ ψ) n    = let (φ' , n') = indexHelper φ n ; (ψ' , n'') = indexHelper ψ n' in (MetricRelease w s φ' ψ' , n'')

indexFormula : LTL SignalPredicate → LTL ℕ
indexFormula φ = proj₁ (indexHelper φ 0)

-- Safe list indexing by ℕ
lookupAtom : List SignalPredicate → ℕ → Maybe SignalPredicate
lookupAtom []       _       = nothing
lookupAtom (x ∷ _)  zero    = just x
lookupAtom (_ ∷ xs) (suc n) = lookupAtom xs n

-- Build PredTable from atom list + DBC + SignalCache
-- The table maps predicate indices to evaluation functions.
mkPredTable : DBC → SignalCache → List SignalPredicate → PredTable
mkPredTable dbc cache atoms n frame =
  case lookupAtom atoms n of λ where
    nothing     → Unknown
    (just pred) → evalPredicateTV dbc cache pred (TimedFrame.frame frame)
  where open import Aletheia.Trace.CANTrace using (TimedFrame)

-- ============================================================================
-- SIGNAL CACHE UPDATES
-- ============================================================================

-- Update cache with all signals extractable from a frame
-- Iterates through all messages in DBC, finds matching message by ID,
-- then extracts and caches all its signals
updateCacheFromFrame : DBC → SignalCache → ℕ → CANFrame → SignalCache
updateCacheFromFrame dbc cache ts frame =
  updateFromMessage (findMessageById (CANFrame.id frame) dbc)
  where
    open import Aletheia.LTL.SignalPredicate using (extractSignalValue)

    -- Update cache with all signals from a message
    updateSignals : List DBCSignal → SignalCache → SignalCache
    updateSignals [] c = c
    updateSignals (sig ∷ sigs) c =
      let sigName = DBCSignal.name sig
      in case extractSignalValue sigName dbc frame of λ where
        nothing  → updateSignals sigs c
        (just v) → updateSignals sigs (updateCache sigName v ts c)

    updateFromMessage : Maybe DBCMessage → SignalCache
    updateFromMessage nothing = cache  -- No matching message, keep cache unchanged
    updateFromMessage (just msg) = updateSignals (DBCMessage.signals msg) cache

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
  let zeros : Vec Byte 8
      zeros = 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
  in record
    { id = msgId
    ; dlc = 8
    ; payload = zeros
    }

-- Create frame from bytes and message ID
makeFrame : CANId → Vec Byte 8 → CANFrame
makeFrame msgId bytes = record
  { id = msgId
  ; dlc = 8
  ; payload = bytes
  }

-- ============================================================================
-- STATE TRANSITIONS (Command Handlers)
-- ============================================================================

-- Parse DBC command: reset state, parse DBC from JSON, and validate
-- Validation: DBC/Validator.validateDBCFull — all 16 structural checks (formally proven sound+complete)
handleParseDBC-State : JSON → StreamState → StreamState × Response
handleParseDBC-State dbcJSON state =
  parseHelper (parseDBCWithErrors dbcJSON)
  where
    open import Data.Sum using (inj₁; inj₂)

    parseHelper : String ⊎ DBC → StreamState × Response
    parseHelper (inj₁ parseError) =
      (state , Response.Error ("DBC parse error: " ++ₛ parseError))
    parseHelper (inj₂ dbc) =
      let issues = validateDBCFull dbc
      in if hasAnyError issues
         then (state , Response.Error ("DBC validation failed: "
                ++ₛ formatIssuesText (errorIssues issues)))
         else let newState = mkStreamState ReadyToStream (just dbc) [] nothing emptyCache
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
      let newState = mkStreamState ReadyToStream (StreamState.dbc state) acc nothing emptyCache  -- Reset prevFrame and cache when setting properties
      in (newState , Response.Success "Properties set successfully")
    parseAllProperties (json ∷ rest) idx acc with parseProperty json
    ... | nothing = (state , Response.Error ("Failed to parse property " ++ₛ showℕ idx))
    ... | just prop =
        let atoms = collectAtoms prop
            proc = initProc (indexFormula prop)
            propState = mkPropertyState idx prop atoms proc
        in parseAllProperties rest (idx + 1) (acc ++ₗ (propState ∷ []))
... | Streaming = (state , Response.Error "Cannot set properties while streaming")

-- Start stream command: transition to streaming mode
handleStartStream-State : StreamState → StreamState × Response
handleStartStream-State state with StreamState.phase state
... | WaitingForDBC = (state , Response.Error "Must call ParseDBC before StartStream")
... | ReadyToStream =
  let newState = mkStreamState Streaming (StreamState.dbc state) (StreamState.properties state) nothing (StreamState.signalCache state)
  in (newState , Response.Success "Streaming started")
... | Streaming = (state , Response.Error "Already streaming")

-- End stream command: finalize all properties and transition back to ready state
handleEndStream-State : StreamState → StreamState × Response
handleEndStream-State state with StreamState.phase state
... | Streaming =
  let newState = mkStreamState ReadyToStream (StreamState.dbc state) (StreamState.properties state) (StreamState.prevFrame state) (StreamState.signalCache state)
      results = finalizeProperties (StreamState.properties state)
  in (newState , Response.Complete results)
  where
    open import Aletheia.Protocol.Response as PR using (mkCounterexampleData; PropertyResult)
    -- Convert FinalVerdict to PropertyResult
    verdictToResult : ℕ → FinalVerdict → PR.PropertyResult
    verdictToResult idx Holds = PR.PropertyResult.Satisfaction idx
    verdictToResult idx (Fails reason) = PR.PropertyResult.Violation idx (mkCounterexampleData 0 reason)

    -- Finalize each property: Holds → Satisfaction, Fails → Violation
    finalizeProperties : List PropertyState → List PR.PropertyResult
    finalizeProperties [] = []
    finalizeProperties (propState ∷ rest) =
      verdictToResult (PropertyState.index propState) (finalizeL (PropertyState.proc propState))
      ∷ finalizeProperties rest
... | _ = (state , Response.Error "Not currently streaming")

-- ============================================================================
-- FRAME PROCESSING (LTL Checking)
-- ============================================================================

-- Process incoming CAN frame with incremental LTL property checking.
--
-- Algorithm:
--   1. Validate state machine: must be in Streaming phase with DBC loaded
--   2. Create TimedFrame from timestamp and frame
--   3. For each property: build PredTable from SignalCache, call stepL (Havelund-Rosu)
--   4. Classify StepResult: Continue → simplify and advance, Violated → halt, Satisfied → keep
--   5. Update SignalCache with newly extracted signal values
--   6. Update prevFrame to current frame for next iteration
--
-- O(1) Memory Guarantee:
--   - Properties maintain fixed-size LTLProc state (no trace accumulation)
--   - Only prevFrame stored (for ChangedBy predicate support)
--   - stepL processes one frame at a time via formula progression
--   - Rosu simplification prevents tree growth (absorb idempotent subformulas)
--
-- Violation Reporting:
--   - First violation detected → PropertyResponse with counterexample
--   - Counterexample includes: timestamp, reason, property index
--   - Violated property halts iteration (remaining properties unchanged)
--   - Other properties continue checking on subsequent frames
--
handleDataFrame : StreamState → ℕ → CANFrame → StreamState × Response
handleDataFrame state timestamp frame with StreamState.phase state
... | WaitingForDBC = (state , Response.Error "Must call ParseDBC before sending frames")
... | ReadyToStream = (state , Response.Error "Must call StartStream before sending frames")
... | Streaming with StreamState.dbc state
...   | nothing = (state , Response.Error "No DBC loaded")
...   | just dbc = processFrame dbc
  where
    open import Aletheia.Protocol.Response as PR using (mkCounterexampleData; PropertyResult)
    open import Aletheia.LTL.Incremental using (Counterexample)

    -- Current cache from state (before this frame's signals are extracted)
    currentCache : SignalCache
    currentCache = StreamState.signalCache state

    processFrame : DBC → StreamState × Response
    processFrame dbc =
      let timedFrame = record { timestamp = timestamp ; frame = frame }
          updatedCache = updateCacheFromFrame dbc currentCache timestamp frame
      in dispatchResult (iterate (propStep timedFrame) (StreamState.properties state)) timedFrame updatedCache
      where
        -- Step one property using stepL with PredTable.
        -- Advance: updated property state (Continue, Satisfied)
        -- Halt: violation evidence (property index + counterexample)
        propStep : TimedFrame → PropertyState → StepOutcome PropertyState (ℕ × Counterexample)
        propStep curr prop =
          let table = mkPredTable dbc currentCache (PropertyState.atoms prop)
              result = stepL table (PropertyState.proc prop) curr
          in classifyResult result prop
          where
            classifyResult : StepResult LTLProc → PropertyState → StepOutcome PropertyState (ℕ × Counterexample)
            classifyResult (Continue _ newProc) prop =
              advance (mkPropertyState (PropertyState.index prop) (PropertyState.formula prop) (PropertyState.atoms prop) (simplify newProc))
            classifyResult (Violated ce) prop = halt (PropertyState.index prop , ce)
            classifyResult Satisfied prop = advance prop

        -- Dispatch on iteration result: build StreamState × Response
        dispatchResult : List PropertyState × Maybe (ℕ × Counterexample) → TimedFrame → SignalCache → StreamState × Response
        dispatchResult (updatedProps , nothing) curr cache =
          (mkStreamState Streaming (just dbc) updatedProps (just curr) cache , Response.Ack)
        dispatchResult (allProps , just (idx , ce)) curr cache =
          let open Counterexample ce
              ceData = mkCounterexampleData (TimedFrame.timestamp violatingFrame) reason
              violation = PR.PropertyResult.Violation idx ceData
          in (mkStreamState Streaming (just dbc) allProps (just curr) cache , Response.PropertyResponse violation)

-- ============================================================================
-- BATCH SIGNAL OPERATIONS HANDLERS (Phase 2B.1)
-- ============================================================================

-- Build CAN frame from signal values
handleBuildFrame-State : JSON → List JSON → StreamState → StreamState × Response
handleBuildFrame-State canIdJSON signalsJSON state =
  buildHelper (StreamState.dbc state)
  where
    buildHelper : Maybe DBC → StreamState × Response
    buildHelper nothing = (state , Response.Error "DBC not loaded")
    buildHelper (just dbc) with getNat canIdJSON
    ... | nothing = (state , Response.Error "Invalid CAN ID")
    ... | just canIdNat =
          let canId = CANId.Standard (canIdNat % standard-can-id-max)
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
    extractHelper : Maybe DBC → StreamState × Response
    extractHelper nothing = (state , Response.Error "DBC not loaded")
    extractHelper (just dbc) with getNat canIdJSON
    ... | nothing = (state , Response.Error "Invalid CAN ID")
    ... | just canIdNat =
          let canId = CANId.Standard (canIdNat % standard-can-id-max)
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
    updateHelper : Maybe DBC → StreamState × Response
    updateHelper nothing = (state , Response.Error "DBC not loaded")
    updateHelper (just dbc) with getNat canIdJSON
    ... | nothing = (state , Response.Error "Invalid CAN ID")
    ... | just canIdNat =
          let canId = CANId.Standard (canIdNat % standard-can-id-max)
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
-- VALIDATE DBC HANDLER (read-only probe, does NOT update state)
-- ============================================================================

-- Validate DBC structure: parse JSON, then run comprehensive validator
handleValidateDBC-State : JSON → StreamState → StreamState × Response
handleValidateDBC-State dbcJSON state =
  parseHelper (parseDBCWithErrors dbcJSON)
  where
    open import Data.Sum using (inj₁; inj₂)

    parseHelper : String ⊎ DBC → StreamState × Response
    parseHelper (inj₁ parseErr) =
      (state , Response.Error ("DBC parse error: " ++ₛ parseErr))
    parseHelper (inj₂ dbc) =
      (state , Response.ValidationResponse (validateDBCFull dbc))

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
processStreamCommand (ValidateDBC dbcJSON) state = handleValidateDBC-State dbcJSON state
