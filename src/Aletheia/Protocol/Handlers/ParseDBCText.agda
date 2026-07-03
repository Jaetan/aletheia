-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- ParseDBCText command handler — split from Handlers.agda.
--
-- Purpose: Isolate the DBC text parser's transitive import closure
-- (TextParser → TopLevel → Attributes → ~30 modules) from the main
-- Handlers module.  Pre-split, importing `parseText` directly into
-- `Handlers.agda` exhausted the 16 GiB elaborator cap during the
-- StreamCommand → Handlers → Main compile chain.
--
-- Role: Imported by `Aletheia.Protocol.Handlers` for the
-- `processStreamCommand (ParseDBCText _) _` dispatch case.
module Aletheia.Protocol.Handlers.ParseDBCText where

open import Data.Char using ()
open import Data.String using (String; toList)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _≤ᵇ_; _<ᵇ_)
open import Data.Product using (_×_; _,_)
open import Data.Bool using (true; false; if_then_else_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Aletheia.DBC.Types using (DBC; DBCMessage)
open import Aletheia.DBC.BoundWalks using
  ( totalValueDescriptions
  ; firstOverBoundLC; firstOverBoundInMessages; firstOverBoundInComments
  ; firstOverBoundInAttrs; firstOverBoundInValueTables; firstOverBoundInUnresolved
  )
open import Aletheia.DBC.Validator using (validateDBCFull; hasAnyError; warningIssues)
open import Aletheia.DBC.Formatter using (formatDBC)
open import Aletheia.DBC.TextParser using (parseText)
open import Aletheia.LTL.SignalPredicate using (emptyCache)
open import Aletheia.Protocol.Message using (Response)
open import Aletheia.Protocol.StreamState using (StreamState; ReadyToStream)
open import Aletheia.Error using
  ( DBCTextParseError; InputBoundExceeded
  ; WithContext; HandlerErr; DBCTextParseErr
  ; ValidationFailed
  )
open import Aletheia.Limits using
  ( InputLengthBytes; ArrayCardinality; StringLength
  ; max-dbc-text-bytes
  ; max-messages-per-file; max-signals-per-message; max-attributes-per-file
  ; max-comments-per-file; max-nodes-per-file; max-value-tables-per-file
  ; max-value-descriptions-per-file
  )

-- Parse DBC from raw DBC text using the verified Agda text parser.
-- Track B.3.e — composes the proven parseText (DBC/TextParser.agda) with the
-- runtime validator so the success path returns a parsed-AND-validated DBC.
-- Three result categories:
--   • parseText fails        → Error wrapping a typed DBCTextParseError.
--   • parser succeeds, errors → Error wrapping ValidationFailed with the
--     FULL issue list (errors and warnings — ResponseFormat.errorExtras
--     surfaces it structurally; the message flattens errors only).
--   • parser+validator clean  → ParsedDBCResponse with body + warnings.
--
-- Implementation note: pattern-match through a helper (rather than `with
-- parseText text`) so the elaborator does not abstract `parseText text`
-- in the goal type during type-checking — inlining the `with` form here
-- exhausts the 16 GiB heap cap.  See feedback_expose_scrutinee_for_external_rewrite.
-- R19 cluster 8 phase e.3: cardinality refinement at the handler boundary
-- (mirror of the same helpers in `Aletheia.Protocol.Handlers`).  parseText
-- itself is unchanged so existing roundtrip proofs preserve their shape.
-- The check is duplicated here (not imported from Handlers.agda) because
-- Handlers.agda imports this module → no upward dependency.

private
  -- Per-handler signalsBound — the simple form (no field-name tag);
  -- the Handlers.agda twin returns `Maybe (String × ℕ × ℕ)` for richer
  -- JSON error messages.  Kept local because of the return-type split.
  signalsBound : List DBCMessage → Maybe (ℕ × ℕ)
  signalsBound [] = nothing
  signalsBound (msg ∷ rest) with length (DBCMessage.signals msg) <ᵇ suc max-signals-per-message
  ... | true  = signalsBound rest
  ... | false = just (length (DBCMessage.signals msg) , max-signals-per-message)

  -- vds family + string-length walks live in `Aletheia.DBC.BoundWalks`
  -- (R20 cluster V — AGDA-A-1.3); shared with `Handlers.agda` to avoid
  -- the prior in-source duplication that the original cycle-avoidance
  -- rationale forced.

  firstDBCOverBound : DBC → Maybe (ℕ × ℕ)
  firstDBCOverBound dbc with length (DBC.messages dbc) <ᵇ suc max-messages-per-file
  ... | false = just (length (DBC.messages dbc) , max-messages-per-file)
  ... | true  with signalsBound (DBC.messages dbc)
  ...   | just over = just over
  ...   | nothing with length (DBC.attributes dbc) <ᵇ suc max-attributes-per-file
  ...     | false = just (length (DBC.attributes dbc) , max-attributes-per-file)
  ...     | true  with length (DBC.comments dbc) <ᵇ suc max-comments-per-file
  ...       | false = just (length (DBC.comments dbc) , max-comments-per-file)
  ...       | true  with length (DBC.nodes dbc) <ᵇ suc max-nodes-per-file
  ...         | false = just (length (DBC.nodes dbc) , max-nodes-per-file)
  ...         | true  with length (DBC.valueTables dbc) <ᵇ suc max-value-tables-per-file
  ...           | false = just (length (DBC.valueTables dbc) , max-value-tables-per-file)
  ...           | true  with totalValueDescriptions dbc <ᵇ suc max-value-descriptions-per-file
  ...             | false = just (totalValueDescriptions dbc , max-value-descriptions-per-file)
  ...             | true  = nothing

  -- String-length walks live in `Aletheia.DBC.BoundWalks` (R20 cluster V).
  firstStringOverBound : DBC → Maybe (ℕ × ℕ)
  firstStringOverBound dbc with firstOverBoundLC (DBC.version dbc)
  ... | just over = just over
  ... | nothing with firstOverBoundInMessages (DBC.messages dbc)
  ...   | just over = just over
  ...   | nothing with firstOverBoundInComments (DBC.comments dbc)
  ...     | just over = just over
  ...     | nothing with firstOverBoundInAttrs (DBC.attributes dbc)
  ...       | just over = just over
  ...       | nothing with firstOverBoundInValueTables (DBC.valueTables dbc)
  ...         | just over = just over
  ...         | nothing = firstOverBoundInUnresolved (DBC.unresolvedValueDescs dbc)

handleParseDBCTextResult : DBCTextParseError ⊎ DBC → StreamState → StreamState × Response
handleParseDBCTextResult (inj₁ err)  state =
  (state , Response.Error (WithContext "ParseDBCText" (DBCTextParseErr err)))
handleParseDBCTextResult (inj₂ dbc) state =
  helper dbc (firstDBCOverBound dbc) (firstStringOverBound dbc)
  where
    helper : DBC → Maybe (ℕ × ℕ) → Maybe (ℕ × ℕ) → StreamState × Response
    helper dbc (just (obs , lim)) _ =
      (state , Response.Error (WithContext "ParseDBCText"
        (InputBoundExceeded ArrayCardinality obs lim)))
    helper dbc nothing (just (obs , lim)) =
      (state , Response.Error (WithContext "ParseDBCText"
        (InputBoundExceeded StringLength obs lim)))
    helper dbc nothing nothing =
      let issues = validateDBCFull dbc
      in if hasAnyError issues
         then (state , Response.Error (WithContext "ParseDBCText" (HandlerErr (ValidationFailed issues))))
         else (ReadyToStream 0 dbc [] emptyCache , Response.ParsedDBCResponse (formatDBC dbc) (warningIssues issues))

-- Adversarial-input bound: rejects inputs longer than `max-dbc-text-bytes`
-- (`Aletheia.Limits`) with a typed `DBCTextParseError.InputBoundExceeded`
-- before invoking the parser, per AGENTS.md universal rule "Adversarial-input
-- bounds at parser surfaces".
handleParseDBCText : String → StreamState → StreamState × Response
handleParseDBCText text state =
  let inputLen = length (toList text)
  in if inputLen ≤ᵇ max-dbc-text-bytes
     then handleParseDBCTextResult (parseText text) state
     else (state , Response.Error (WithContext "ParseDBCText"
              (InputBoundExceeded InputLengthBytes inputLen max-dbc-text-bytes)))
