{-# OPTIONS --safe --without-K #-}

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
module Aletheia.Protocol.StreamState where

open import Data.String using (String) renaming (_++_ to _++ₛ_)
open import Data.List using (List; []; _∷_; reverse) renaming (_++_ to _++ₗ_)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Vec using (Vec)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (case_of_)
open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal)
open import Aletheia.DBC.JSONParser using (parseDBCWithErrors)
open import Aletheia.DBC.Validator using (validateDBCFull; hasAnyError; formatIssuesText; errorIssues)
open import Aletheia.LTL.Syntax using (LTL; Atomic; Not; And; Or; Next; Always; Eventually; Until; Release; MetricEventually; MetricAlways; MetricUntil; MetricRelease)
open import Aletheia.LTL.SignalPredicate using (SignalPredicate; TruthVal; True; False; Unknown; SignalCache; emptyCache; updateCache; evalPredicateTV; extractTruthValue)
open import Aletheia.LTL.Incremental using (StepResult; Continue; Violated; Satisfied; FinalVerdict; Holds; Fails; Counterexample)
open import Aletheia.LTL.Coalgebra using (LTLProc; PredTable; stepL; finalizeL; initProc; simplify)
open import Aletheia.Protocol.JSON using (JSON; lookupString; getObject; lookupRational)
open import Data.Rational using (ℚ)
open import Aletheia.LTL.JSON using (parseProperty)
open import Aletheia.Protocol.Message using (Response; StreamCommand; ParseDBC; SetProperties; StartStream; EndStream; BuildFrame; UpdateFrame; ExtractAllSignals; ValidateDBC; FormatDBC)
open import Aletheia.DBC.Formatter using (formatDBC)
open import Aletheia.Trace.CANTrace using (TimedFrame)
open import Aletheia.CAN.Frame using (CANFrame; CANId; Byte)
open import Aletheia.CAN.DLC using (dlcToBytes)
open import Aletheia.CAN.DBCHelpers using (findMessageById)
open import Aletheia.Protocol.Iteration using (StepOutcome; advance; halt; iterate)
open import Aletheia.CAN.BatchExtraction using (extractAllSignals; ExtractionResults)
open import Aletheia.CAN.BatchFrameBuilding using (buildFrame; updateFrame)
open import Aletheia.Protocol.Response as PR using (mkCounterexampleData; PropertyResult)

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

-- ============================================================================
-- FORMULA INDEXING (LTL SignalPredicate → LTLProc + atom list)
-- ============================================================================

-- Collect all atomic predicates in left-to-right tree order (O(n) via accumulator).
-- Factored to module level for proof access.
collectAtomsAcc : LTL SignalPredicate → List SignalPredicate → List SignalPredicate
collectAtomsAcc (Atomic a)                 acc = a ∷ acc
collectAtomsAcc (Not φ)                    acc = collectAtomsAcc φ acc
collectAtomsAcc (And φ ψ)                  acc = collectAtomsAcc φ (collectAtomsAcc ψ acc)
collectAtomsAcc (Or φ ψ)                   acc = collectAtomsAcc φ (collectAtomsAcc ψ acc)
collectAtomsAcc (Next φ)                   acc = collectAtomsAcc φ acc
collectAtomsAcc (Always φ)                 acc = collectAtomsAcc φ acc
collectAtomsAcc (Eventually φ)             acc = collectAtomsAcc φ acc
collectAtomsAcc (Until φ ψ)                acc = collectAtomsAcc φ (collectAtomsAcc ψ acc)
collectAtomsAcc (Release φ ψ)              acc = collectAtomsAcc φ (collectAtomsAcc ψ acc)
collectAtomsAcc (MetricEventually _ _ φ)   acc = collectAtomsAcc φ acc
collectAtomsAcc (MetricAlways _ _ φ)       acc = collectAtomsAcc φ acc
collectAtomsAcc (MetricUntil _ _ φ ψ)      acc = collectAtomsAcc φ (collectAtomsAcc ψ acc)
collectAtomsAcc (MetricRelease _ _ φ ψ)    acc = collectAtomsAcc φ (collectAtomsAcc ψ acc)

-- The resulting list maps ℕ indices to predicates for PredTable construction.
collectAtoms : LTL SignalPredicate → List SignalPredicate
collectAtoms formula = collectAtomsAcc formula []

-- Replace each atom with its position index (counter-based, matches collectAtoms order)
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

-- ============================================================================
-- SIGNAL CACHE UPDATES
-- ============================================================================

-- Update cache with all signals from a signal list.
-- Factored to module level for proof access.
updateSignals : ∀ {n} → DBC → CANFrame n → ℕ → List DBCSignal → SignalCache → SignalCache
updateSignals dbc frame ts [] c = c
updateSignals dbc frame ts (sig ∷ sigs) c =
  let sigName = DBCSignal.name sig
  in case extractTruthValue sigName dbc frame of λ where
    nothing  → updateSignals dbc frame ts sigs c
    (just v) → updateSignals dbc frame ts sigs (updateCache sigName v ts c)

-- Update cache with all signals extractable from a frame
-- Iterates through all messages in DBC, finds matching message by ID,
-- then extracts and caches all its signals
updateCacheFromFrame : ∀ {n} → DBC → SignalCache → ℕ → CANFrame n → SignalCache
updateCacheFromFrame dbc cache ts frame =
  case findMessageById (CANFrame.id frame) dbc of λ where
    nothing    → cache
    (just msg) → updateSignals dbc frame ts (DBCMessage.signals msg) cache

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

-- Create frame from bytes, DLC, and message ID
makeFrame : ∀ {n} → CANId → ℕ → Vec Byte n → CANFrame n
makeFrame msgId dlc bytes = record
  { id = msgId
  ; dlc = dlc
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
      let newState = mkStreamState ReadyToStream (StreamState.dbc state) (reverse acc) nothing emptyCache  -- Reset prevFrame and cache when setting properties
      in (newState , Response.Success "Properties set successfully")
    parseAllProperties (json ∷ rest) idx acc with parseProperty json
    ... | nothing = (state , Response.Error ("Failed to parse property " ++ₛ showℕ idx))
    ... | just prop =
        let atoms = collectAtoms prop
            proc = initProc (indexFormula prop)
            propState = mkPropertyState idx prop atoms proc
        in parseAllProperties rest (idx + 1) (propState ∷ acc)
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
-- FRAME PROCESSING HELPERS (factored to module level for proof access)
-- ============================================================================

-- Classify a single stepL result into a StepOutcome.
-- Continue/Satisfied → advance (property continues checking)
-- Violated → halt (property failed, halt iteration)
classifyStepResult : StepResult LTLProc → PropertyState → StepOutcome PropertyState (ℕ × Counterexample)
classifyStepResult (Continue _ newProc) prop =
  advance (mkPropertyState (PropertyState.index prop) (PropertyState.formula prop) (PropertyState.atoms prop) (simplify newProc))
classifyStepResult (Violated ce) prop = halt (PropertyState.index prop , ce)
classifyStepResult Satisfied prop = advance prop

-- Step one property: build PredTable, call stepL, classify result.
stepProperty : DBC → SignalCache → TimedFrame → PropertyState → StepOutcome PropertyState (ℕ × Counterexample)
stepProperty dbc cache tf prop =
  let table = mkPredTable dbc cache (PropertyState.atoms prop)
      result = stepL table (PropertyState.proc prop) tf
  in classifyStepResult result prop

-- Dispatch iteration result to StreamState × Response.
-- nothing → Ack (all properties continued/satisfied)
-- just (idx, ce) → PropertyResponse Violation
dispatchIterResult : DBC → List PropertyState × Maybe (ℕ × Counterexample) → TimedFrame → SignalCache → StreamState × Response
dispatchIterResult dbc (updatedProps , nothing) tf cache =
  (mkStreamState Streaming (just dbc) updatedProps (just tf) cache , Response.Ack)
dispatchIterResult dbc (allProps , just (idx , ce)) tf cache =
  let open Counterexample ce
      ceData = mkCounterexampleData (TimedFrame.timestamp violatingFrame) reason
      violation = PR.PropertyResult.Violation idx ceData
  in (mkStreamState Streaming (just dbc) allProps (just tf) cache , Response.PropertyResponse violation)

-- ============================================================================
-- FRAME PROCESSING (LTL Checking)
-- ============================================================================

-- Process incoming CAN frame with incremental LTL property checking.
--
-- In Streaming phase: updates signal cache, iterates stepProperty over all
-- properties (calling stepL for each), dispatches result to Ack or Violation.
--
-- O(1) Memory: Properties maintain fixed-size LTLProc state (no trace accumulation).
-- Violation Reporting: First violation halts iteration with counterexample evidence.
handleDataFrame : StreamState → TimedFrame → StreamState × Response
handleDataFrame state tf with StreamState.phase state
... | WaitingForDBC = (state , Response.Error "Must call ParseDBC before sending frames")
... | ReadyToStream = (state , Response.Error "Must call StartStream before sending frames")
... | Streaming with StreamState.dbc state
...   | nothing = (state , Response.Error "DBC not loaded")
...   | just dbc =
  let cache = StreamState.signalCache state
      updatedCache = updateCacheFromFrame dbc cache (TimedFrame.timestamp tf) (TimedFrame.frame tf)
  in dispatchIterResult dbc (iterate (stepProperty dbc cache tf) (StreamState.properties state)) tf updatedCache

-- ============================================================================
-- BATCH SIGNAL OPERATIONS HANDLERS (Phase 2B.1)
-- ============================================================================

-- Common preamble: validate DBC loaded
private
  withDBC : StreamState → (DBC → StreamState × Response) → StreamState × Response
  withDBC state cont with StreamState.dbc state
  ... | nothing  = (state , Response.Error "DBC not loaded")
  ... | just dbc = cont dbc

-- Build CAN frame from signal values
handleBuildFrame-State : CANId → (dlc : ℕ) → List JSON → StreamState → StreamState × Response
handleBuildFrame-State canId dlc signalsJSON state =
  withDBC state λ dbc → parseSignals dbc signalsJSON
  where
    parseSignals : DBC → List JSON → StreamState × Response
    parseSignals dbc signals with parseSignalList signals
    ... | nothing = (state , Response.Error "Failed to parse signal list")
    ... | just signalPairs with buildFrame dbc canId dlc signalPairs
    ...   | nothing = (state , Response.Error "Frame building failed (signals overlap, not found, or values out of bounds)")
    ...   | just frameBytes = (state , Response.ByteArray frameBytes)

-- Extract all signals from a CAN frame
handleExtractAllSignals-State : CANId → (dlc : ℕ) → Vec Byte (dlcToBytes dlc) → StreamState → StreamState × Response
handleExtractAllSignals-State canId dlc bytes state =
  withDBC state λ dbc →
    let frame = makeFrame canId dlc bytes
        results = extractAllSignals dbc frame
    in (state , Response.ExtractionResultsResponse
                  (ExtractionResults.values results)
                  (ExtractionResults.errors results)
                  (ExtractionResults.absent results))

-- Update specific signals in a CAN frame
handleUpdateFrame-State : CANId → (dlc : ℕ) → Vec Byte (dlcToBytes dlc) → List JSON → StreamState → StreamState × Response
handleUpdateFrame-State canId dlc bytes signalsJSON state =
  withDBC state λ dbc →
    let frame = makeFrame canId dlc bytes
    in parseSignals dbc signalsJSON frame
  where
    parseSignals : ∀ {m} → DBC → List JSON → CANFrame m → StreamState × Response
    parseSignals dbc signals frame with parseSignalList signals
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
    parseHelper : String ⊎ DBC → StreamState × Response
    parseHelper (inj₁ parseErr) =
      (state , Response.Error ("DBC parse error: " ++ₛ parseErr))
    parseHelper (inj₂ dbc) =
      (state , Response.ValidationResponse (validateDBCFull dbc))

-- ============================================================================
-- FORMAT DBC HANDLER (read-only, returns currently-loaded DBC as JSON)
-- ============================================================================

handleFormatDBC-State : StreamState → StreamState × Response
handleFormatDBC-State state with StreamState.dbc state
... | nothing  = (state , Response.Error "DBC not loaded")
... | just dbc = (state , Response.DBCResponse (formatDBC dbc))

-- ============================================================================
-- STREAM COMMAND DISPATCHER
-- ============================================================================

-- Process a stream command and update state
processStreamCommand : StreamCommand → StreamState → StreamState × Response
processStreamCommand (ParseDBC dbcJSON) state = handleParseDBC-State dbcJSON state
processStreamCommand (SetProperties props) state = handleSetProperties-State props state
processStreamCommand StartStream state = handleStartStream-State state
processStreamCommand (BuildFrame canId dlc signalsJSON) state = handleBuildFrame-State canId dlc signalsJSON state
processStreamCommand (ExtractAllSignals canId dlc bytes) state = handleExtractAllSignals-State canId dlc bytes state
processStreamCommand (UpdateFrame canId dlc bytes signalsJSON) state = handleUpdateFrame-State canId dlc bytes signalsJSON state
processStreamCommand EndStream state = handleEndStream-State state
processStreamCommand (ValidateDBC dbcJSON) state = handleValidateDBC-State dbcJSON state
processStreamCommand FormatDBC state = handleFormatDBC-State state
