{-# OPTIONS --safe --without-K #-}

-- Command handlers for the streaming protocol.
--
-- Purpose: Implement command-specific business logic (ParseDBC, BuildFrame, etc.).
-- Each handler processes command arguments, calls domain functions, and formats responses.
-- Role: Separated from StreamState to isolate command business logic
--       from state machine transitions, LTL processing, and proof-facing functions.
--
-- `Aletheia.Protocol.StreamState` retains: state types, formula indexing,
--   signal cache, and `handleDataFrame` — the entry point for incoming data
--   frames in the Streaming state.
-- StreamState/Internals.agda retains: LTL frame processing helpers
--   (classifyStepResult, stepProperty, dispatchIterResult).
-- This module also provides processStreamCommand (command dispatch).
module Aletheia.Protocol.Handlers where

open import Data.String using (String; fromList)
open import Data.List using (List; []; _∷_; map; reverse; length) renaming (_++_ to _++ₗ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _<ᵇ_)
open import Data.Fin using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_×_; _,_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Vec using (Vec)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl)
open import Aletheia.DBC.Types using (DBC; DBCMessage)
open import Aletheia.DBC.BoundWalks using
  ( totalValueDescriptions
  ; firstOverBoundLC; firstOverBoundInMessages; firstOverBoundInComments
  ; firstOverBoundInAttrs; firstOverBoundInValueTables; firstOverBoundInUnresolved
  )
open import Aletheia.DBC.JSONParser using (parseDBCWithErrors)
open import Aletheia.DBC.Validator using (validateDBCFull; hasAnyError; errorIssues; warningIssues)
open import Aletheia.DBC.Formatter using (formatDBC)
open import Aletheia.LTL.SignalPredicate using (SignalPredicate; SignalCache; emptyCache; signalOf; lookupCache)
open import Aletheia.LTL.Incremental using (FinalVerdict; Holds; Fails; Unsure)
open import Aletheia.LTL.Coalgebra using (finalizeL; initProc)
open import Aletheia.LTL.JSON using (parseProperty)
open import Aletheia.LTL.Syntax using (atomCount)
open import Aletheia.Protocol.JSON using (JSON)
open import Aletheia.Protocol.Message using (Response; StreamCommand; ParseDBC; SetProperties; StartStream; SendFrame; EndStream; ExtractAllSignals; ValidateDBC; FormatDBC; ParseDBCText; FormatDBCText)
open import Aletheia.Protocol.Response as PR using (mkCounterexampleData; Warning; mkWarning; UncachedAtom)
open import Aletheia.Trace.Time using (μs; mkTs)
open import Aletheia.CAN.Frame using (CANFrame; CANId; Byte)
open import Aletheia.CAN.DLC using (DLC; dlcBytes)
open import Aletheia.CAN.BatchExtraction using (extractAllSignals; PartitionedResults)
open import Aletheia.Prelude using (require)
open import Aletheia.Error as Err using
  ( Error; HandlerErr; WithContext
  ; InputBoundExceeded
  ; HandlerError; NoDBC; AlreadyStreaming; NotStreaming; StreamActive
  ; PropertyParseFailed; ValidationFailed
  )
open import Aletheia.Limits using
  ( BoundKind; ArrayCardinality; AtomCount; StringLength; PropertyCount; IdentifierLength
  ; max-messages-per-file; max-signals-per-message; max-attributes-per-file
  ; max-comments-per-file; max-nodes-per-file; max-value-tables-per-file
  ; max-value-descriptions-per-file
  ; max-atom-count-per-property
  ; max-properties-per-stream
  ; max-identifier-length
  )
open import Data.Char using (Char)

-- Import state types from StreamState (no circular dependency: Handlers → StreamState types only)
open import Aletheia.Protocol.StreamState using
  ( StreamState; WaitingForDBC; ReadyToStream; Streaming
  ; getDBC; handleDataFrame
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

  -- Parse DBC from JSON, wrapping parse errors with command context.
  -- parseDBCWithErrors returns `Error ⊎ DBC` (R20 cluster I — AGDA-D-32.1
  -- lifted the return type so `Error.InputBoundExceeded IdentifierLength
  -- …` rejections at `validateIdent` surface alongside `ParseErr`
  -- envelopes); the legacy ParseError envelopes arrive pre-wrapped via
  -- `ParseErr`.
  withParsedDBC : String → JSON → StreamState → (DBC → StreamState × Response) → StreamState × Response
  withParsedDBC ctx dbcJSON state f with parseDBCWithErrors dbcJSON
  ... | inj₁ err = (state , Response.Error (WithContext ctx err))
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

  -- R20 cluster H — AGDA-D-11.2 / AGDA-D-32.4.  Total value-description
  -- count is the sum across all three carriers (per-signal `VAL_` entries,
  -- top-level `VAL_TABLE_` definitions, and `unresolvedValueDescs` for
  -- VAL_ lines whose `(canId, signalName)` did not resolve to a signal).
  -- Walked at the handler boundary alongside the other cardinality
  -- checks; one cap closes `max-value-descriptions-per-file` previously
  -- declared in `Aletheia.Limits` but never consulted.  Walks live in
  -- `Aletheia.DBC.BoundWalks` (R20 cluster V — AGDA-A-1.3) shared with
  -- the verified text-parser path in `Handlers.ParseDBCText`.

  firstDBCOverBound : DBC → Maybe (String × ℕ × ℕ)
  firstDBCOverBound dbc with length (DBC.messages dbc) <ᵇ suc max-messages-per-file
  ... | false = just ("messages array" , length (DBC.messages dbc) , max-messages-per-file)
  ... | true  with signalsBound (DBC.messages dbc)
  ...   | just over = just over
  ...   | nothing with length (DBC.attributes dbc) <ᵇ suc max-attributes-per-file
  ...     | false = just ("attributes array" , length (DBC.attributes dbc) , max-attributes-per-file)
  ...     | true  with length (DBC.comments dbc) <ᵇ suc max-comments-per-file
  ...       | false = just ("comments array" , length (DBC.comments dbc) , max-comments-per-file)
  ...       | true  with length (DBC.nodes dbc) <ᵇ suc max-nodes-per-file
  ...         | false = just ("nodes array" , length (DBC.nodes dbc) , max-nodes-per-file)
  ...         | true  with length (DBC.valueTables dbc) <ᵇ suc max-value-tables-per-file
  ...           | false = just ("value tables array" , length (DBC.valueTables dbc) , max-value-tables-per-file)
  ...           | true  with totalValueDescriptions dbc <ᵇ suc max-value-descriptions-per-file
  ...             | false = just ("value descriptions total" , totalValueDescriptions dbc , max-value-descriptions-per-file)
  ...             | true  = nothing

  -- Build a typed error response for an adversarial-bound violation.
  -- BoundKind discriminates ArrayCardinality (cluster H) vs StringLength
  -- (R20 cluster I — AGDA-D-32.2).  Per AGENTS.md universal rule
  -- "Adversarial-input bounds at parser surfaces", rejection is a typed
  -- `Error.InputBoundExceeded kind observed limit` carrying the offending
  -- kind, observed value, and limit — never an OOM, never a stalled stream.
  boundErrorResponse : String → BoundKind → String → ℕ → ℕ → StreamState → StreamState × Response
  boundErrorResponse cmdCtx kind fieldCtx observed limit state =
    (state , Response.Error
      (WithContext cmdCtx
        (WithContext fieldCtx (InputBoundExceeded kind observed limit))))

  -- R20 cluster I — AGDA-D-32.2.  Post-parse walk of every unbounded
  -- `List Char` field in the parsed DBC.  Cluster H closed cardinality
  -- bounds at this same handler boundary; this mirrors the placement for
  -- string-length bounds (comment text, attribute string values, signal
  -- units, value-description labels, attribute names — none of which go
  -- through `validIdentifierᵇ`'s length cap).  Underlying walks live in
  -- `Aletheia.DBC.BoundWalks` (R20 cluster V — AGDA-A-1.3) shared with
  -- the verified text-parser path; this aggregator tags each branch with
  -- a field-name `String` for richer JSON error messages.
  firstStringOverBound : DBC → Maybe (String × ℕ × ℕ)
  firstStringOverBound dbc with firstOverBoundLC (DBC.version dbc)
  ... | just (obs , lim) = just ("version string" , obs , lim)
  ... | nothing with firstOverBoundInMessages (DBC.messages dbc)
  ...   | just (obs , lim) = just ("signal text field" , obs , lim)
  ...   | nothing with firstOverBoundInComments (DBC.comments dbc)
  ...     | just (obs , lim) = just ("comment text" , obs , lim)
  ...     | nothing with firstOverBoundInAttrs (DBC.attributes dbc)
  ...       | just (obs , lim) = just ("attribute text field" , obs , lim)
  ...       | nothing with firstOverBoundInValueTables (DBC.valueTables dbc)
  ...         | just (obs , lim) = just ("value table label" , obs , lim)
  ...         | nothing with firstOverBoundInUnresolved (DBC.unresolvedValueDescs dbc)
  ...           | just (obs , lim) = just ("unresolved value description label" , obs , lim)
  ...           | nothing = nothing

-- ============================================================================
-- COMMAND HANDLERS
-- ============================================================================

-- Parse DBC command: parse DBC from JSON, validate, and update state.
-- Success path emits ParsedDBCResponse carrying the parsed body and any
-- non-error issues (warnings) — option 6b: warnings flow through, never
-- silently dropped.  Same shape as ParseDBCText for binding-side parity.
handleParseDBC : JSON → StreamState → StreamState × Response
handleParseDBC dbcJSON state = withParsedDBC "ParseDBC" dbcJSON state λ dbc →
  -- Post-parse adversarial-bound refinement at the handler boundary.
  --   * ArrayCardinality (cluster 8 phase e.3 / cluster H): list-cardinality
  --     caps on messages / signals / attributes / comments / nodes / value
  --     tables / total value descriptions.
  --   * StringLength (R20 cluster I / AGDA-D-32.2): char-length caps on
  --     `List Char` fields not covered by the Identifier grammar (version,
  --     comments, attribute names + AVString + ATEnum labels, signal units,
  --     value-description labels).
  --   Both walks run on the parsed value; `parseDBCWithErrors` is unchanged
  --   so existing roundtrip proofs preserve their structural shape.
  case-helper dbc (firstDBCOverBound dbc) (firstStringOverBound dbc)
  where
    case-helper : DBC → Maybe (String × ℕ × ℕ) → Maybe (String × ℕ × ℕ) → StreamState × Response
    case-helper dbc (just (ctx , obs , lim)) _ =
      boundErrorResponse "ParseDBC" ArrayCardinality ctx obs lim state
    case-helper dbc nothing (just (ctx , obs , lim)) =
      boundErrorResponse "ParseDBC" StringLength ctx obs lim state
    case-helper dbc nothing nothing =
      let issues = validateDBCFull dbc
      in if hasAnyError issues
         then (state , Response.Error (WithContext "ParseDBC" (HandlerErr (ValidationFailed (errorIssues issues)))))
         else (ReadyToStream 0 dbc [] emptyCache , Response.ParsedDBCResponse (formatDBC dbc) (warningIssues issues))

-- ParseDBCText handler isolated in its own submodule to keep parseText's
-- transitive import closure (~30 modules: TopLevel → Attributes → …) out
-- of this module's elaborator state.  Pre-split, importing parseText here
-- exhausted the 16 GiB heap during the StreamCommand → Handlers → Main chain.
open import Aletheia.Protocol.Handlers.ParseDBCText using (handleParseDBCText)

-- FormatDBCText handler isolated for the same reason (TextFormatter
-- transitive closure ~30 modules).  See Handlers/FormatDBCText.agda.
open import Aletheia.Protocol.Handlers.FormatDBCText using (handleFormatDBCText)

-- Tabulate a list with each element's positional `Fin (length xs)` index.
-- Used by `handleSetProperties` to pair each input JSON with the `Fin n`
-- it will inhabit in the resulting `List (PropertyState n)`, where
-- `n = length propJSONs`.  Keeping the input-position pairing here means
-- `parseAllProperties` never has to thread a counter alongside an
-- arithmetic invariant — every recursive call gets its `Fin n` from the
-- pre-tabulated head, with `length` definitional equality discharging
-- the type.
withIndices : ∀ {A : Set} (xs : List A) → List (Fin (length xs) × A)
withIndices []       = []
withIndices (x ∷ xs) = (fzero , x) ∷ map (λ p → fsuc (Data.Product.proj₁ p) , Data.Product.proj₂ p) (withIndices xs)

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
--
-- The `Fin n` index threaded through the JSON list is the static
-- property identifier; `toℕ` lifts it to `ℕ` only for the wire-side
-- `PropertyParseFailed` envelope (which still carries `ℕ` because the
-- error message reaches the user regardless of `n`).

-- AGDA-D-32.1 (R23): per-atom signal-name length check.  Walks the
-- collected atoms and returns the first (signal-name-length, sentinel)
-- pair whose length exceeds `max-identifier-length`.  Returns `nothing`
-- when every atom's signalOf fits the bound.
firstOverLongSignalName : List SignalPredicate → Maybe ℕ
firstOverLongSignalName [] = nothing
firstOverLongSignalName (sp ∷ rest) with length (signalOf sp) <ᵇ suc max-identifier-length
... | true  = firstOverLongSignalName rest
... | false = just (length (signalOf sp))

parseAllProperties : (n : ℕ) → StreamState → DBC → List (Fin n × JSON) → List (PropertyState n) → StreamState × Response
parseAllProperties n _ dbc [] acc =
  (ReadyToStream n dbc (reverse acc) emptyCache , Response.Success "Properties set successfully")
parseAllProperties n state dbc ((idx , json) ∷ rest) acc with parseProperty json
... | nothing = (state , Response.Error (WithContext "SetProperties" (HandlerErr (PropertyParseFailed (toℕ idx)))))
... | just prop with atomCount prop <ᵇ suc max-atom-count-per-property | atomCount prop
...   | false | observed = (state , Response.Error
                              (WithContext "SetProperties"
                                (InputBoundExceeded AtomCount observed max-atom-count-per-property)))
...   | true  | _        =
       let atoms = collectAtoms prop
       in checkSignalNamesThenContinue atoms
  where
    checkSignalNamesThenContinue : List SignalPredicate → StreamState × Response
    checkSignalNamesThenContinue atoms with firstOverLongSignalName atoms
    ... | just observed = (state , Response.Error
                                      (WithContext "SetProperties"
                                        (InputBoundExceeded IdentifierLength observed max-identifier-length)))
    ... | nothing       =
        let proc = initProc (indexFormula prop)
            propState = mkPropertyState idx prop atoms proc
        in parseAllProperties n state dbc rest (propState ∷ acc)

-- Set properties command: parse JSON properties to LTL
handleSetProperties : List JSON → StreamState → StreamState × Response
handleSetProperties _ WaitingForDBC =
  (WaitingForDBC , Response.Error (WithContext "SetProperties" (HandlerErr NoDBC)))
handleSetProperties propJSONs state@(ReadyToStream _ dbc _ _)
  with length propJSONs <ᵇ suc max-properties-per-stream | length propJSONs
... | false | observed = (state , Response.Error
                            (WithContext "SetProperties"
                              (InputBoundExceeded PropertyCount observed max-properties-per-stream)))
... | true  | _        =
  parseAllProperties (length propJSONs) state dbc (withIndices propJSONs) []
handleSetProperties propJSONs state@(Streaming _ _ _ _ _) =
  (state , Response.Error (WithContext "SetProperties" (HandlerErr StreamActive)))

-- Start stream command: transition to streaming mode
handleStartStream : StreamState → StreamState × Response
handleStartStream (ReadyToStream n dbc props cache) =
  (Streaming n dbc props nothing cache , Response.Success "Streaming started successfully")
handleStartStream WaitingForDBC =
  (WaitingForDBC , Response.Error (WithContext "StartStream" (HandlerErr NoDBC)))
handleStartStream state@(Streaming _ _ _ _ _) =
  (state , Response.Error (WithContext "StartStream" (HandlerErr AlreadyStreaming)))

-- Convert final verdict to property result (extracted for proof access).
-- Three verdicts map 1:1:
--   Holds   → Satisfaction
--   Fails   → Violation  (with reason in synthetic counterexample)
--   Unsure  → Unresolved (three-valued Kleene Unknown, e.g. Always(p)
--             where p's signal was never observed)
--
-- The `Fin n` index is `toℕ`'d only here at the wire boundary — the
-- internal pipeline (`PropertyState n` → `Fin n × Counterexample` →
-- this function) keeps the static `Fin n` throughout.
verdictToResult : ∀ {n} → Fin n → FinalVerdict → PR.PropertyResult
verdictToResult idx Holds            = PR.PropertyResult.Satisfaction (toℕ idx)
-- EOS Fails uses synthetic timestamp 0: the violation is the absence of
-- satisfaction over the entire trace (e.g. Eventually(p) never saw p),
-- so no single violating frame exists to timestamp.
verdictToResult idx (Fails reason)   = PR.PropertyResult.Violation (toℕ idx) (mkCounterexampleData (mkTs {u = μs} 0) reason)
verdictToResult idx (Unsure reason)  = PR.PropertyResult.Unresolved (toℕ idx) reason

-- Finalize all properties with verdicts (extracted for proof access)
finalizeProperties : ∀ {n} → List (PropertyState n) → List PR.PropertyResult
finalizeProperties = map λ ps →
  verdictToResult (PropertyState.index ps) (finalizeL (PropertyState.proc ps))

-- R21 cluster 1 — AGDA-D-12.1 closure (walker landed):
--
-- For one PropertyState, walk its atoms and emit a `UncachedAtom` warning
-- for each atom whose target signal never appears in the cache at
-- EndStream.  Each warning records the property index (so the binding
-- can correlate with the corresponding PropertyResult) and the
-- offending signal name (as a string, lifted from `List Char` via
-- `fromList`).  Multiple atoms in the same property whose signals are
-- ALL missing produce one warning each — callers can deduplicate by
-- (propertyIndex, detail) tuple if desired; the kernel does not, since
-- the diagnostic value is "this many atoms had this many distinct
-- missed signals," not just "one or more missed."
collectUncachedWarnings-one : ∀ {n} → SignalCache → PropertyState n → List Warning
collectUncachedWarnings-one cache ps =
  walkAtoms (PropertyState.atoms ps)
  where
    propIdx : ℕ
    propIdx = toℕ (PropertyState.index ps)

    walkAtoms : List SignalPredicate → List Warning
    walkAtoms [] = []
    walkAtoms (sp ∷ rest) with lookupCache (signalOf sp) cache
    ... | just _  = walkAtoms rest
    ... | nothing = mkWarning UncachedAtom propIdx (fromList (signalOf sp))
                  ∷ walkAtoms rest

-- Walker entrypoint: collect cache-miss warnings across every property.
collectUncachedWarnings : ∀ {n} → SignalCache → List (PropertyState n) → List Warning
collectUncachedWarnings _ [] = []
collectUncachedWarnings cache (ps ∷ rest) =
  collectUncachedWarnings-one cache ps ++ₗ collectUncachedWarnings cache rest

-- End stream command: finalize all properties + emit cache-miss warnings,
-- then transition back to ready state.  R21 cluster 1 — AGDA-D-12.1
-- closure: the walker populates the warnings list via
-- `collectUncachedWarnings` (atom-level lookup against the EndStream
-- signal cache).  Wire shape is unchanged from the scaffold landing in
-- `85623b7`; binding-side parsers see the field they were already
-- decoding, just with concrete entries now.
handleEndStream : StreamState → StreamState × Response
handleEndStream (Streaming n dbc props _ cache) =
  let results  = finalizeProperties props
      warnings = collectUncachedWarnings cache props
  in (ReadyToStream n dbc props cache , Response.Complete results warnings)
handleEndStream state =
  (state , Response.Error (WithContext "EndStream" (HandlerErr NotStreaming)))

-- Submit a CAN data frame via the JSON path — JSON mirror of the binary
-- FFI `aletheia_send_frame` entry point.  Constructs a `TimedFrame`
-- from the command arguments (including CAN-FD BRS / ESI metadata) and
-- delegates to `handleDataFrame`, which enforces timestamp monotonicity
-- and runs incremental LTL property checking.  R19 Phase 2 cluster 18 —
-- AGDA-D-10.1 closure.
handleSendFrame : ℕ → CANId → (dlc : DLC) → Vec Byte (dlcBytes dlc)
                → Maybe Bool → Maybe Bool
                → StreamState → StreamState × Response
handleSendFrame ts canId dlc bytes brs esi state =
  handleDataFrame state (record
    { timestamp   = mkTs ts
    ; payloadSize = dlcBytes dlc
    ; frame       = makeFrame canId dlc bytes
    ; dlcValid    = refl
    ; brs         = brs
    ; esi         = esi
    })

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
processStreamCommand (SendFrame ts canId dlc bytes brs esi) state =
  handleSendFrame ts canId dlc bytes brs esi state
processStreamCommand (ExtractAllSignals canId dlc bytes) state = handleExtractAllSignals canId dlc bytes state
processStreamCommand EndStream state = handleEndStream state
processStreamCommand (ValidateDBC dbcJSON) state = handleValidateDBC dbcJSON state
processStreamCommand FormatDBC state = handleFormatDBC state
processStreamCommand (ParseDBCText text) state = handleParseDBCText text state
processStreamCommand (FormatDBCText dbcJSON) state = handleFormatDBCText dbcJSON state
