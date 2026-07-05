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

open import Data.String using (String; toList)
open import Data.List using (length)
open import Data.Nat using (_≤ᵇ_)
open import Data.Product using (_×_; _,_)
open import Data.Bool using (if_then_else_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Aletheia.DBC.Types using (DBC)
open import Aletheia.DBC.TextParser using (parseTextChars)
open import Aletheia.Protocol.Message using (Response)
open import Aletheia.Protocol.StreamState using (StreamState)
open import Aletheia.Protocol.Handlers.LoadDBC using (loadValidatedDBC)
open import Aletheia.Error using
  ( DBCTextParseError; InputBoundExceeded; WithContext; DBCTextParseErr )
open import Aletheia.Limits using (InputLengthBytes; max-dbc-text-bytes)

-- Parse DBC from raw DBC text using the verified Agda text parser.
-- Track B.3.e — composes the proven `parseTextChars` (DBC/TextParser.agda)
-- with the runtime validate-and-load pipeline (shared verbatim with the JSON
-- route via `Aletheia.Protocol.Handlers.LoadDBC`) so the success path returns
-- a parsed-AND-validated DBC.  Three result categories:
--   • parseTextChars fails    → Error wrapping a typed DBCTextParseError.
--   • parser succeeds, errors → Error wrapping ValidationFailed with the
--     FULL issue list (via `loadValidatedDBC` — ResponseFormat.errorExtras
--     surfaces it structurally; the message flattens errors only).
--   • parser+validator clean  → ParsedDBCResponse with body + warnings.
-- The post-parse adversarial bound cascade + validate-and-load epilogue live
-- in `Handlers.LoadDBC` (whose closure is deliberately free of the text
-- parser/formatter); both DBC-loading routes call `loadValidatedDBC`, so the
-- text route now emits the same field-context bound errors as the JSON route.
--
-- Implementation note: pattern-match through the top-level
-- `handleParseDBCTextResult` (rather than `with parseTextChars chars`) so the
-- elaborator does not abstract the parse result in the goal type during
-- type-checking — inlining the `with` form here exhausts the 16 GiB heap cap.
-- See feedback_expose_scrutinee_for_external_rewrite.

handleParseDBCTextResult : DBCTextParseError ⊎ DBC → StreamState → StreamState × Response
handleParseDBCTextResult (inj₁ err)  state =
  (state , Response.Error (WithContext "ParseDBCText" (DBCTextParseErr err)))
handleParseDBCTextResult (inj₂ dbc) state =
  loadValidatedDBC "ParseDBCText" dbc state

-- Adversarial-input bound: rejects inputs longer than `max-dbc-text-bytes`
-- (`Aletheia.Limits`) with a typed `InputBoundExceeded` before invoking the
-- parser, per AGENTS.md universal rule "Adversarial-input bounds at parser
-- surfaces".  `toList text` is materialized ONCE here and fed to the
-- `List Char` entry point `parseTextChars`; the `String` overload `parseText`
-- would walk `toList` a second time (no CSE across the FFI call boundary).
handleParseDBCText : String → StreamState → StreamState × Response
handleParseDBCText text state =
  let chars    = toList text
      inputLen = length chars
  in if inputLen ≤ᵇ max-dbc-text-bytes
     then handleParseDBCTextResult (parseTextChars chars) state
     else (state , Response.Error (WithContext "ParseDBCText"
              (InputBoundExceeded InputLengthBytes inputLen max-dbc-text-bytes)))
