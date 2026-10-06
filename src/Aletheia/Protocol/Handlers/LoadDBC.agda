-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- The validate-and-load pipeline the two DBC-loading commands share
-- (ParseDBC from JSON, ParseDBCText from text): the size bounds
-- (`Aletheia.DBC.Bounds.checkBounds`), then the validator, then a
-- `ReadyToStream` session.  The two differ only in the command context that
-- prefixes a refusal.
--
-- Heap constraint: this module's import closure is deliberately free of the
-- DBC text-parser closure (`TextParser → TopLevel` and its transitive module
-- tree) and of the text formatter's own `TopLevel` aggregation.  It imports
-- the validator / formatter / bound checker that both consumers
-- already carry — which, through the validator's warning-class mux-coherence
-- mirrors (`Validator/Checks` → `TextParser.WellFormedCheck.Foundations`),
-- includes the formatter leaves `TextFormatter.Topology`/`Emitter` (for
-- `findMuxMaster`) but nothing further — so `Aletheia.Protocol.Handlers` can
-- import it WITHOUT dragging in the text-parser closure that exhausted the
-- 16 GiB elaborator cap pre-split (see the `Handlers.ParseDBCText` module
-- note).
module Aletheia.Protocol.Handlers.LoadDBC where

open import Data.String using (String)
open import Data.List using ([])
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Aletheia.DBC.Types using (DBC)
open import Aletheia.DBC.Bounds using (BoundedDBC; checkBounds)
open import Aletheia.DBC.Validated using (validate)
open import Aletheia.DBC.Formatter using (formatDBC)
open import Aletheia.LTL.SignalPredicate using (emptyCache)
open import Aletheia.Protocol.Message using (Response)
open import Aletheia.Protocol.StreamState using (StreamState; ReadyToStream)
open import Aletheia.Error using (WithContext; HandlerErr; ValidationFailed)

private
  -- Validate a DBC within its bounds and load it: an error-severity issue
  -- refuses with `ValidationFailed`; otherwise the session loads the
  -- `ValidDBC` and the response carries the DBC and its warnings.
  loadValidatedEpilogue : String → BoundedDBC → StreamState → StreamState × Response
  loadValidatedEpilogue cmdCtx b state with validate b
  ... | inj₁ issues = (state , Response.Error (WithContext cmdCtx (HandlerErr (ValidationFailed issues))))
  ... | inj₂ (vdbc , warnings) =
    (ReadyToStream 0 vdbc [] emptyCache , Response.ParsedDBCResponse (formatDBC (BoundedDBC.dbc b)) warnings)

loadValidatedDBC : String → DBC → StreamState → StreamState × Response
loadValidatedDBC cmdCtx dbc state with checkBounds dbc
... | inj₁ e = (state , Response.Error (WithContext cmdCtx e))
... | inj₂ b = loadValidatedEpilogue cmdCtx b state
