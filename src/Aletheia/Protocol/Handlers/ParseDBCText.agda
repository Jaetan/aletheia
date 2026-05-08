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

open import Data.String using (String; toList)
open import Data.List using (List; []; length)
open import Data.Nat using (_≤ᵇ_)
open import Data.Product using (_×_; _,_)
open import Data.Bool using (if_then_else_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Aletheia.DBC.Types using (DBC)
open import Aletheia.DBC.Validator using (validateDBCFull; hasAnyError; errorIssues; warningIssues)
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
open import Aletheia.Limits using (InputLengthBytes; max-dbc-text-bytes)

-- Parse DBC from raw DBC text using the verified Agda text parser.
-- Track B.3.e — composes the proven parseText (DBC/TextParser.agda) with the
-- runtime validator so the success path returns a parsed-AND-validated DBC.
-- Three result categories:
--   • parseText fails        → Error wrapping a typed DBCTextParseError.
--   • parser succeeds, errors → Error wrapping ValidationFailed (errorIssues).
--   • parser+validator clean  → ParsedDBCResponse with body + warnings.
--
-- Implementation note: pattern-match through a helper (rather than `with
-- parseText text`) so the elaborator does not abstract `parseText text`
-- in the goal type during type-checking — inlining the `with` form here
-- exhausts the 16 GiB heap cap.  See feedback_expose_scrutinee_for_external_rewrite.
handleParseDBCTextResult : DBCTextParseError ⊎ DBC → StreamState → StreamState × Response
handleParseDBCTextResult (inj₁ err)  state =
  (state , Response.Error (WithContext "ParseDBCText" (DBCTextParseErr err)))
handleParseDBCTextResult (inj₂ dbc) state =
  let issues = validateDBCFull dbc
  in if hasAnyError issues
     then (state , Response.Error (WithContext "ParseDBCText" (HandlerErr (ValidationFailed (errorIssues issues)))))
     else (ReadyToStream dbc [] emptyCache , Response.ParsedDBCResponse (formatDBC dbc) (warningIssues issues))

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
              (DBCTextParseErr (InputBoundExceeded InputLengthBytes inputLen max-dbc-text-bytes))))
