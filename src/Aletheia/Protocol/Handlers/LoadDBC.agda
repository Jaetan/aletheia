-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Shared DBC validate-and-load pipeline for the two DBC-loading command
-- handlers (ParseDBC / ParseDBCText) plus the ValidateDBC bounds cascade.
--
-- Purpose: the JSON route (`Handlers.handleParseDBC`) and the verified text
-- route (`Handlers.ParseDBCText.handleParseDBCTextResult`) ran a
-- byte-identical post-parse pipeline — the adversarial array-cardinality +
-- string-length bound cascade, then `validateDBCFull` with the same
-- `ReadyToStream` / `ParsedDBCResponse` success branch — differing only in
-- the command-context `String` literal.  Each also carried its own copy of
-- the tagged bound aggregators (`firstDBCOverBound` / `firstStringOverBound`
-- over the shared `Aletheia.DBC.BoundWalks` primitives), the text route
-- historically dropping the field-name tag.  This leaf hosts the single
-- tagged implementation, parameterized on the command-context literal, so
-- both routes emit identical field-context bound errors.  `ValidateDBC`
-- reuses just the bounds half (`checkDBCBounds`) since it returns a
-- `ValidationResponse` rather than loading a stream session.
--
-- Heap constraint: this module's import closure is deliberately free of the
-- DBC text-parser closure (`TextParser → TopLevel → ~30 modules`) and of the
-- text formatter's own `TopLevel` aggregation.  It imports the validator /
-- formatter / bound-walk substrate that both consumers already carry — which,
-- through the validator's warning-class mux-coherence mirrors
-- (`Validator/Checks` → `TextParser.WellFormedCheck.Foundations`), includes
-- the two formatter leaves `TextFormatter.Topology`/`Emitter` (for
-- `findMuxMaster`) but nothing further — so `Aletheia.Protocol.Handlers` can
-- import it WITHOUT dragging in the text-parser closure that exhausted the
-- 16 GiB elaborator cap pre-split (see the `Handlers.ParseDBCText` module
-- note).
module Aletheia.Protocol.Handlers.LoadDBC where

open import Data.String using (String)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _<ᵇ_)
open import Data.Product using (_×_; _,_)
open import Data.Bool using (if_then_else_)
open import Aletheia.DBC.Types using (DBC; DBCMessage)
open import Aletheia.DBC.BoundWalks using
  ( totalValueDescriptions
  ; firstOverBoundLC; firstOverBoundInMessages; firstOverBoundInComments
  ; firstOverBoundInAttrs; firstOverBoundInValueTables; firstOverBoundInUnresolved
  )
open import Aletheia.DBC.Validator using (validateDBCFull; hasAnyError; warningIssues)
open import Aletheia.DBC.Formatter using (formatDBC)
open import Aletheia.LTL.SignalPredicate using (emptyCache)
open import Aletheia.Protocol.Message using (Response)
open import Aletheia.Protocol.StreamState using (StreamState; ReadyToStream)
open import Aletheia.Error using
  ( WithContext; HandlerErr; InputBoundExceeded; ValidationFailed )
open import Aletheia.Limits using
  ( BoundKind; ArrayCardinality; StringLength
  ; max-messages-per-file; max-signals-per-message; max-attributes-per-file
  ; max-comments-per-file; max-nodes-per-file; max-value-tables-per-file
  ; max-value-descriptions-per-file
  )

private
  -- Cardinality check for one array field: `nothing` when the observed
  -- length is within the cap, else `just (fieldTag , observed , limit)`.
  -- The observed length is passed in (evaluated once by the caller) and
  -- reused for both the comparison and the payload, so no field is
  -- traversed a second time to build the rejection tuple.
  checkCard : String → ℕ → ℕ → Maybe (String × ℕ × ℕ)
  checkCard fieldTag observed limit =
    if observed <ᵇ suc limit then nothing else just (fieldTag , observed , limit)

  -- Per-message signals-array cardinality, tagged with the field-name
  -- context for richer JSON error messages.  Returns nothing if every
  -- message is under the `max-signals-per-message` cap.
  signalsBound : List DBCMessage → Maybe (String × ℕ × ℕ)
  signalsBound [] = nothing
  signalsBound (msg ∷ rest) with checkCard "signals array" (length (DBCMessage.signals msg)) max-signals-per-message
  ... | just over = just over
  ... | nothing  = signalsBound rest

  -- Array-cardinality cascade over the DBC.  Discovery order: messages →
  -- per-message signals → attributes → comments → nodes → value tables →
  -- total value descriptions.  Each branch tags the offending field; the
  -- first over-bound field wins.
  firstDBCOverBound : DBC → Maybe (String × ℕ × ℕ)
  firstDBCOverBound dbc with checkCard "messages array" (length (DBC.messages dbc)) max-messages-per-file
  ... | just over = just over
  ... | nothing with signalsBound (DBC.messages dbc)
  ...   | just over = just over
  ...   | nothing with checkCard "attributes array" (length (DBC.attributes dbc)) max-attributes-per-file
  ...     | just over = just over
  ...     | nothing with checkCard "comments array" (length (DBC.comments dbc)) max-comments-per-file
  ...       | just over = just over
  ...       | nothing with checkCard "nodes array" (length (DBC.nodes dbc)) max-nodes-per-file
  ...         | just over = just over
  ...         | nothing with checkCard "value tables array" (length (DBC.valueTables dbc)) max-value-tables-per-file
  ...           | just over = just over
  ...           | nothing = checkCard "value descriptions total" (totalValueDescriptions dbc) max-value-descriptions-per-file

  -- String-length cascade over every unbounded `List Char` field, tagging
  -- each branch with its field name.  Underlying per-field walks live in
  -- `Aletheia.DBC.BoundWalks`; this aggregator attaches the tag.
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

  -- Typed error response for an adversarial-bound violation: a
  -- double-`WithContext` envelope (command context outermost, offending
  -- field context inner) wrapping `InputBoundExceeded kind observed limit`.
  boundErrorResponse : String → BoundKind → String → ℕ → ℕ → StreamState → StreamState × Response
  boundErrorResponse cmdCtx kind fieldCtx observed limit state =
    (state , Response.Error
      (WithContext cmdCtx
        (WithContext fieldCtx (InputBoundExceeded kind observed limit))))

  -- The validate-and-load success epilogue (post-bounds): run the full
  -- validator; an error-severity issue becomes a `ValidationFailed`
  -- envelope, a clean parse loads a `ReadyToStream` session and emits
  -- `ParsedDBCResponse` with the (non-error) warnings flowing through.
  loadValidatedEpilogue : String → DBC → StreamState → StreamState × Response
  loadValidatedEpilogue cmdCtx dbc state =
    let issues = validateDBCFull dbc
    in if hasAnyError issues
       then (state , Response.Error (WithContext cmdCtx (HandlerErr (ValidationFailed issues))))
       else (ReadyToStream 0 dbc [] emptyCache , Response.ParsedDBCResponse (formatDBC dbc) (warningIssues issues))

-- The adversarial-bound cascade shared by all three DBC commands: array
-- cardinality first, then string-length.  `nothing` = clean (proceed);
-- `just` = the first violation, already built into a ready-to-return
-- error response for the given command context.
checkDBCBounds : String → DBC → StreamState → Maybe (StreamState × Response)
checkDBCBounds cmdCtx dbc state = cascade (firstDBCOverBound dbc) (firstStringOverBound dbc)
  where
    cascade : Maybe (String × ℕ × ℕ) → Maybe (String × ℕ × ℕ) → Maybe (StreamState × Response)
    cascade (just (ctx , obs , lim)) _ = just (boundErrorResponse cmdCtx ArrayCardinality ctx obs lim state)
    cascade nothing (just (ctx , obs , lim)) = just (boundErrorResponse cmdCtx StringLength ctx obs lim state)
    cascade nothing nothing = nothing

-- The full parse→load pipeline: adversarial bound cascade, then the
-- validate-and-load epilogue.  Shared verbatim by ParseDBC (JSON) and
-- ParseDBCText (verified text); the two differ only in the command-context
-- `String`, so both now emit identical field-context bound errors.
loadValidatedDBC : String → DBC → StreamState → StreamState × Response
loadValidatedDBC cmdCtx dbc state with checkDBCBounds cmdCtx dbc state
... | just err = err
... | nothing  = loadValidatedEpilogue cmdCtx dbc state
