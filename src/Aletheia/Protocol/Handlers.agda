-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
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
open import Data.Bool using (Bool; true; false)
open import Data.Vec using (Vec)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Aletheia.DBC.Types using (DBC)
open import Aletheia.DBC.JSONParser using (parseDBCWithErrors)
open import Aletheia.DBC.Validator using (validateDBCFull)
open import Aletheia.DBC.Formatter using (formatDBC)
open import Aletheia.DBC.Identifier using (TooLong; BadChars)
open import Aletheia.LTL.SignalPredicate using (SignalPredicate; SignalCache; emptyCache; signalOf; lookupCache)
open import Aletheia.LTL.Incremental using (FinalVerdict; Holds; Fails; Unsure)
open import Aletheia.LTL.Coalgebra using (finalizeL; initProc)
open import Aletheia.LTL.JSON using (parseProperty; ParseFail; Shape; BadSignal)
open import Aletheia.LTL.Syntax using (atomCount)
open import Aletheia.Protocol.JSON using (JSON)
open import Aletheia.Protocol.Message using (Response; StreamCommand; ParseDBC; SetProperties; ValidateDBC; ParseDBCText; FormatDBCText)
open import Aletheia.Protocol.Response as PR using (mkCounterexampleData; Warning; mkWarning; UncachedAtom)
open import Aletheia.Trace.Time using (μs; mkTs)
open import Aletheia.CAN.Frame using (CANFrame; CANId; Byte)
open import Aletheia.CAN.DLC using (DLC; dlcBytes)
open import Aletheia.CAN.BatchExtraction using (extractAllSignals; PartitionedResults)
open import Aletheia.Prelude using (require)
open import Aletheia.Error as Err using
  ( HandlerErr; WithContext; ParseErr
  ; InputBoundExceeded
  ; HandlerError; NoDBC; AlreadyStreaming; NotStreaming; StreamActive
  ; PropertyParseFailed
  ; InvalidIdentifier
  )
open import Aletheia.Limits using
  ( AtomCount; PropertyCount; IdentifierLength
  ; max-atom-count-per-property
  ; max-properties-per-stream
  ; max-identifier-length
  )
open import Data.Char using ()

-- Import state types from StreamState (no circular dependency: Handlers → StreamState types only)
open import Aletheia.Protocol.StreamState using
  ( StreamState; WaitingForDBC; ReadyToStream; Streaming
  ; getDBC
  ; PropertyState; mkPropertyState
  )
open import Aletheia.Protocol.StreamState.Internals using (collectAtoms; indexFormula)
open import Aletheia.Protocol.Handlers.LoadDBC using (checkDBCBounds; loadValidatedDBC)

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
  -- parseDBCWithErrors returns `Error ⊎ DBC`; the return type is lifted
  -- so `Error.InputBoundExceeded IdentifierLength …` rejections at
  -- `validateIdent` surface alongside `ParseErr` envelopes.  The legacy
  -- ParseError envelopes arrive pre-wrapped via `ParseErr`.
  withParsedDBC : String → JSON → StreamState → (DBC → StreamState × Response) → StreamState × Response
  withParsedDBC ctx dbcJSON state f with parseDBCWithErrors dbcJSON
  ... | inj₁ err = (state , Response.Error (WithContext ctx err))
  ... | inj₂ dbc = f dbc

-- ============================================================================
-- COMMAND HANDLERS
-- ============================================================================

-- Parse DBC command: parse DBC from JSON, validate, and update state.
-- Success path emits ParsedDBCResponse carrying the parsed body and any
-- non-error issues (warnings) — option 6b: warnings flow through, never
-- silently dropped.  Same shape as ParseDBCText for binding-side parity.
handleParseDBC : JSON → StreamState → StreamState × Response
handleParseDBC dbcJSON state = withParsedDBC "ParseDBC" dbcJSON state λ dbc →
  -- Post-parse adversarial-bound cascade + validate-and-load, shared with
  -- ParseDBCText via Handlers.LoadDBC (the two routes differ only in the
  -- command-context literal).  ArrayCardinality caps on messages / signals /
  -- attributes / comments / nodes / value tables / total value descriptions;
  -- StringLength caps on the `List Char` fields not covered by the Identifier
  -- grammar; then validateDBCFull with the ReadyToStream / ParsedDBCResponse
  -- success branch.  `parseDBCWithErrors` is unchanged so the existing
  -- roundtrip proofs preserve their structural shape.
  loadValidatedDBC "ParseDBC" dbc state

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
--   * Shape malformed (`parseProperty` → `inj₁ Shape`): emit untyped
--     `HandlerErr (PropertyParseFailed idx)` (code
--     `handler_property_parse_failed`).
--   * Shape OK but atom count > `max-atom-count-per-property` (1024):
--     emit typed `ParseErr (InputBoundExceeded AtomCount observed limit)`
--     (code `parse_input_bound_exceeded` + structured `bound_kind /
--     observed / limit`).  This mirrors the handler-boundary placement
--     pattern used for NestingDepth.
--
-- The `Fin n` index threaded through the JSON list is the static
-- property identifier; `toℕ` lifts it to `ℕ` only for the wire-side
-- `PropertyParseFailed` envelope (which still carries `ℕ` because the
-- error message reaches the user regardless of `n`).

-- Signal names are `Identifier`-typed and validated on the SINGLE parse
-- path — `parseProperty` carries the typed reason out as `ParseFail`, so
-- there is no second raw-JSON walk to keep in sync.  Map the verdict
-- directly to the wire error:
--   * `Shape`                   — malformed JSON shape → untyped
--                                 `HandlerErr (PropertyParseFailed idx)`.
--   * `BadSignal (TooLong n)`   — name over `max-identifier-length` →
--                                 `InputBoundExceeded IdentifierLength`
--                                 (the old post-parse per-atom length check
--                                 is now unreachable — over-long names fail
--                                 the single parse first).
--   * `BadSignal (BadChars cs)` — bad charset / empty →
--                                 `ParseErr (InvalidIdentifier …)`.
parseFailResponse : StreamState → ℕ → ParseFail → StreamState × Response
parseFailResponse state propIdx Shape =
      (state , Response.Error (WithContext "SetProperties"
                                (HandlerErr (PropertyParseFailed propIdx))))
parseFailResponse state _ (BadSignal (TooLong observed)) =
      (state , Response.Error (WithContext "SetProperties"
                                (InputBoundExceeded IdentifierLength observed max-identifier-length)))
parseFailResponse state _ (BadSignal (BadChars cs)) =
      (state , Response.Error (WithContext "SetProperties"
                                (ParseErr (InvalidIdentifier (fromList cs)))))

parseAllProperties : (n : ℕ) → StreamState → DBC → List (Fin n × JSON) → List (PropertyState n) → StreamState × Response
parseAllProperties n _ dbc [] acc =
  (ReadyToStream n dbc (reverse acc) emptyCache , Response.Success "Properties set successfully")
parseAllProperties n state dbc ((idx , json) ∷ rest) acc with parseProperty json
... | inj₁ pf   = parseFailResponse state (toℕ idx) pf
... | inj₂ prop with atomCount prop <ᵇ suc max-atom-count-per-property | atomCount prop
...   | false | observed = (state , Response.Error
                              (WithContext "SetProperties"
                                (InputBoundExceeded AtomCount observed max-atom-count-per-property)))
...   | true  | _        =
       let atoms = collectAtoms prop
           proc = initProc (indexFormula prop)
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
-- then transition back to ready state.  The walker populates the warnings
-- list via `collectUncachedWarnings` (atom-level lookup against the
-- EndStream signal cache).  Binding-side parsers see the field they were
-- already decoding, just with concrete entries now.
handleEndStream : StreamState → StreamState × Response
handleEndStream (Streaming n dbc props _ cache) =
  let results  = finalizeProperties props
      warnings = collectUncachedWarnings cache props
  in (ReadyToStream n dbc props cache , Response.Complete results warnings)
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
  -- C2 hardening: run the same adversarial bound cascade as the load routes
  -- (shared via Handlers.LoadDBC.checkDBCBounds) before validating, so an
  -- over-cardinality / over-length JSON DBC is rejected with a typed
  -- InputBoundExceeded rather than validated unbounded.  Discovery order and
  -- field-context tags are identical to ParseDBC.
  validateHelper dbc (checkDBCBounds "ValidateDBC" dbc state)
  where
    validateHelper : DBC → Maybe (StreamState × Response) → StreamState × Response
    validateHelper _ (just err) = err
    validateHelper dbc nothing = (state , Response.ValidationResponse (validateDBCFull dbc))

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
processStreamCommand (ValidateDBC dbcJSON) state = handleValidateDBC dbcJSON state
processStreamCommand (ParseDBCText text) state = handleParseDBCText text state
processStreamCommand (FormatDBCText dbcJSON) state = handleFormatDBCText dbcJSON state
