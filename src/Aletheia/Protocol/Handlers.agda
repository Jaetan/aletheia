{-# OPTIONS --safe --without-K #-}

-- Command handlers for the streaming protocol.
--
-- Purpose: Implement command-specific business logic (ParseDBC, BuildFrame, etc.).
-- Each handler processes command arguments, calls domain functions, and formats responses.
-- Role: Separated from StreamState to isolate command business logic
--       from state machine transitions, LTL processing, and proof-facing functions.
--
-- StreamState.agda retains: state types, formula indexing, signal cache, and
--   `handleDataFrame` (StreamState.agda:62-72) — the entry point for incoming
--   data frames in the Streaming state.
-- StreamState/Internals.agda retains: LTL frame processing helpers
--   (classifyStepResult, stepProperty, dispatchIterResult).
-- This module also provides processStreamCommand (command dispatch).
module Aletheia.Protocol.Handlers where

open import Data.String using (String) renaming (_++_ to _++ₛ_)
open import Data.List using (List; []; _∷_; map; reverse; length)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Nat using (ℕ; suc; _+_; _<ᵇ_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Product using (_×_; _,_)
open import Data.Bool using (true; false; if_then_else_)
open import Data.Vec using (Vec)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal)
open import Aletheia.DBC.JSONParser using (parseDBCWithErrors)
open import Aletheia.DBC.Validator using (validateDBCFull; hasAnyError; formatIssuesText; errorIssues; warningIssues)
open import Aletheia.DBC.Formatter using (formatDBC)
open import Aletheia.LTL.SignalPredicate using (SignalPredicate; SignalCache; emptyCache)
open import Aletheia.LTL.Incremental using (FinalVerdict; Holds; Fails; Unsure)
open import Aletheia.LTL.Coalgebra using (LTLProc; finalizeL; initProc)
open import Aletheia.LTL.JSON using (parseProperty)
open import Aletheia.LTL.Syntax using (atomCount)
open import Aletheia.Protocol.JSON using (JSON; lookupString; getObject; lookupRational)
open import Aletheia.Protocol.Message using (Response; StreamCommand; ParseDBC; SetProperties; StartStream; EndStream; ExtractAllSignals; ValidateDBC; FormatDBC; ParseDBCText; FormatDBCText)
open import Aletheia.Protocol.Response as PR using (mkCounterexampleData; PropertyResult)
open import Aletheia.Trace.Time using (Timestamp; μs; mkTs)
open import Aletheia.CAN.Frame using (CANFrame; CANId; Byte)
open import Aletheia.CAN.DLC using (DLC; dlcBytes)
open import Aletheia.CAN.BatchExtraction using (extractAllSignals; ExtractionResults; PartitionedResults)
open import Aletheia.CAN.BatchFrameBuilding using (buildFrameByIndex; updateFrameByIndex)
open import Aletheia.Prelude using (require)
open import Aletheia.Error as Err using
  ( Error; ParseErr; HandlerErr; WithContext
  ; ParseError; InContext; InputBoundExceeded
  ; HandlerError; NoDBC; AlreadyStreaming; NotStreaming; StreamActive
  ; PropertyParseFailed; ValidationFailed
  ; WrappedParse
  )
open import Aletheia.Limits using
  ( ArrayCardinality; AtomCount
  ; max-messages-per-file; max-signals-per-message; max-attributes-per-file
  ; max-atom-count-per-property
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

  -- R19 cluster 8 phase e.3: cardinality refinement at the handler boundary.
  -- parseDBCWithErrors / parseText are intentionally left unchanged so the
  -- existing roundtrip proofs (parseMessageList-roundtrip,
  -- parseDBCWithErrors-roundtrip, …) preserve their structural shape.  The
  -- adversarial-input rejection still happens at the wire entry, just one
  -- handler layer up.  Post-parse refinement, NOT fuel — direct length
  -- counts against canonical `Aletheia.Limits` bounds.
  --
  -- Returns nothing if all cardinality bounds OK; else a triple
  -- (context-string, observed, limit) identifying the first violation.
  -- Discovery order: messages array → per-message signals array →
  -- attributes array.  Each `DBCMessage.signals` is checked under the
  -- 1024 signals-per-message bound; the messages array itself is checked
  -- under the 10000 messages-per-file bound; attributes under 10000.

  signalsBound : List DBCMessage → Maybe (String × ℕ × ℕ)
  signalsBound [] = nothing
  signalsBound (msg ∷ rest) with length (DBCMessage.signals msg) <ᵇ suc max-signals-per-message
  ... | true  = signalsBound rest
  ... | false = just ("signals array" , length (DBCMessage.signals msg) , max-signals-per-message)

  firstDBCOverBound : DBC → Maybe (String × ℕ × ℕ)
  firstDBCOverBound dbc with length (DBC.messages dbc) <ᵇ suc max-messages-per-file
  ... | false = just ("messages array" , length (DBC.messages dbc) , max-messages-per-file)
  ... | true  with signalsBound (DBC.messages dbc)
  ...   | just over = just over
  ...   | nothing with length (DBC.attributes dbc) <ᵇ suc max-attributes-per-file
  ...     | true  = nothing
  ...     | false = just ("attributes array" , length (DBC.attributes dbc) , max-attributes-per-file)

  -- Build a typed error response for a cardinality violation.
  cardinalityErrorResponse : String → String → ℕ → ℕ → StreamState → StreamState × Response
  cardinalityErrorResponse cmdCtx arrayCtx observed limit state =
    (state , Response.Error
      (WithContext cmdCtx
        (WithContext arrayCtx (InputBoundExceeded ArrayCardinality observed limit))))

-- ============================================================================
-- COMMAND HANDLERS
-- ============================================================================

-- Parse DBC command: parse DBC from JSON, validate, and update state.
-- Success path emits ParsedDBCResponse carrying the parsed body and any
-- non-error issues (warnings) — option 6b: warnings flow through, never
-- silently dropped.  Same shape as ParseDBCText for binding-side parity.
handleParseDBC : JSON → StreamState → StreamState × Response
handleParseDBC dbcJSON state = withParsedDBC "ParseDBC" dbcJSON state λ dbc →
  -- R19 cluster 8 phase e.3: post-parse cardinality refinement at the
  -- handler boundary (see `firstDBCOverBound` above for rationale).
  case-helper dbc (firstDBCOverBound dbc)
  where
    case-helper : DBC → Maybe (String × ℕ × ℕ) → StreamState × Response
    case-helper dbc (just (ctx , obs , lim)) =
      cardinalityErrorResponse "ParseDBC" ctx obs lim state
    case-helper dbc nothing =
      let issues = validateDBCFull dbc
      in if hasAnyError issues
         then (state , Response.Error (WithContext "ParseDBC" (HandlerErr (ValidationFailed (errorIssues issues)))))
         else (ReadyToStream dbc [] emptyCache , Response.ParsedDBCResponse (formatDBC dbc) (warningIssues issues))

-- ParseDBCText handler isolated in its own submodule to keep parseText's
-- transitive import closure (~30 modules: TopLevel → Attributes → …) out
-- of this module's elaborator state.  Pre-split, importing parseText here
-- exhausted the 16 GiB heap during the StreamCommand → Handlers → Main chain.
open import Aletheia.Protocol.Handlers.ParseDBCText using (handleParseDBCText)

-- FormatDBCText handler isolated for the same reason (TextFormatter
-- transitive closure ~30 modules).  See Handlers/FormatDBCText.agda.
open import Aletheia.Protocol.Handlers.FormatDBCText using (handleFormatDBCText)

-- Parse property list (extracted from where-block for proof access).
--
-- Distinguishes two rejection paths at the handler boundary:
--   * Shape malformed (`parseProperty` → `nothing`): emit untyped
--     `HandlerErr (PropertyParseFailed idx)` (code
--     `handler_property_parse_failed`).
--   * Shape OK but atom count > `max-atom-count-per-property` (1024):
--     emit typed `ParseErr (InputBoundExceeded AtomCount observed limit)`
--     (code `parse_input_bound_exceeded` + structured `bound_kind /
--     observed / limit`).  AGDA-D-13.4 phase 2b — closes R19 cluster 8
--     phase e.2 typed-error half.  Mirrors the handler-boundary
--     placement pattern from cluster 8 e.3 / phase 2a NestingDepth.
parseAllProperties : StreamState → DBC → List JSON → ℕ → List PropertyState → StreamState × Response
parseAllProperties _ dbc [] _ acc =
  (ReadyToStream dbc (reverse acc) emptyCache , Response.Success "Properties set successfully")
parseAllProperties state dbc (json ∷ rest) idx acc with parseProperty json
... | nothing = (state , Response.Error (WithContext "SetProperties" (HandlerErr (PropertyParseFailed idx))))
... | just prop with atomCount prop <ᵇ suc max-atom-count-per-property | atomCount prop
...   | false | observed = (state , Response.Error
                              (WithContext "SetProperties"
                                (InputBoundExceeded AtomCount observed max-atom-count-per-property)))
...   | true  | _        = let atoms = collectAtoms prop
                               proc = initProc (indexFormula prop)
                               propState = mkPropertyState idx prop atoms proc
                           in parseAllProperties state dbc rest (idx + 1) (propState ∷ acc)

-- Set properties command: parse JSON properties to LTL
handleSetProperties : List JSON → StreamState → StreamState × Response
handleSetProperties _ WaitingForDBC =
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

-- Extract all signals from a CAN frame
handleExtractAllSignals : CANId → (dlc : DLC) → Vec Byte (dlcBytes dlc) → StreamState → StreamState × Response
handleExtractAllSignals canId dlc bytes state = withDBCContext "ExtractAllSignals" state λ dbc →
  let frame = makeFrame canId dlc bytes
      results = extractAllSignals dbc frame
  in (state , Response.ExtractionResultsResponse
                (PartitionedResults.values results)
                (PartitionedResults.errors results)
                (PartitionedResults.absent results))

-- Validate DBC structure: parse JSON, then run comprehensive validator
handleValidateDBC : JSON → StreamState → StreamState × Response
handleValidateDBC dbcJSON state = withParsedDBC "ValidateDBC" dbcJSON state λ dbc →
  (state , Response.ValidationResponse (validateDBCFull dbc))

-- Format DBC: returns currently-loaded DBC as JSON
handleFormatDBC : StreamState → StreamState × Response
handleFormatDBC state = withDBCContext "FormatDBC" state λ dbc →
  (state , Response.DBCResponse (formatDBC dbc))

-- ============================================================================
-- COMMAND DISPATCH
-- ============================================================================

-- Process a stream command and update state
processStreamCommand : StreamCommand → StreamState → StreamState × Response
processStreamCommand (ParseDBC dbcJSON) state = handleParseDBC dbcJSON state
processStreamCommand (SetProperties props) state = handleSetProperties props state
processStreamCommand StartStream state = handleStartStream state
processStreamCommand (ExtractAllSignals canId dlc bytes) state = handleExtractAllSignals canId dlc bytes state
processStreamCommand EndStream state = handleEndStream state
processStreamCommand (ValidateDBC dbcJSON) state = handleValidateDBC dbcJSON state
processStreamCommand FormatDBC state = handleFormatDBC state
processStreamCommand (ParseDBCText text) state = handleParseDBCText text state
processStreamCommand (FormatDBCText dbcJSON) state = handleFormatDBCText dbcJSON state
