-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K --no-main #-}

-- JSON streaming protocol entry points.
--
-- Purpose: Process line-delimited JSON requests and emit JSON responses.
-- Protocol: parseDBC → setProperties → startStream → data_frames* → endStream,
--   plus extractAllSignals, validateDBC, formatDBC, parseDBCText.
-- Exports: processJSONLine (JSON commands).
module Aletheia.Main.JSON where

open import Data.String using (String; toList; _≟_)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapₘ)
open import Data.Product using (proj₁; _×_; _,_)
open import Data.List using (List; length)
open import Data.Nat using (_≤ᵇ_; _<ᵇ_; suc)
open import Data.Sum using (inj₁; inj₂)
open import Data.Bool using (if_then_else_)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Aletheia.Parser.Combinators using (runParser)
open import Aletheia.Protocol.JSON using (JSON; JObject; parseJSON; lookupString)
open import Aletheia.Protocol.JSON.Types using (jsonDepth)
open import Aletheia.Protocol.Routing using (parseCommand)
open import Aletheia.Protocol.StreamState using (StreamState)
open import Aletheia.Protocol.Handlers using (processStreamCommand)
open import Aletheia.Error using
  ( Error; DispatchErr
  ; InputBoundExceeded
  ; MissingTypeField; UnknownMessageType; InvalidJSON; RequestNotObject
  )
open import Aletheia.Limits using
  ( InputLengthBytes; NestingDepth
  ; max-json-bytes; max-nesting-depth
  )
open import Aletheia.Main.Binary using (wrapJSON)
import Aletheia.Protocol.Message as Msg

private
  -- Try to parse and execute a command from JSON fields.  parseCommand
  -- returns `Error ⊎ StreamCommand` (R20 cluster I — AGDA-D-32.3 lifted
  -- the return type to accommodate the typed `InputBoundExceeded
  -- FrameByteCount …` emit at `parseBytePayload`); the legacy RouteError
  -- branches arrive pre-wrapped via `RouteErr`.
  tryParseCommand : StreamState → List (String × JSON) → StreamState × String
  tryParseCommand state obj with parseCommand obj
  ... | inj₁ err = wrapJSON (state , Msg.Response.Error err)
  ... | inj₂ cmd = wrapJSON (processStreamCommand cmd state)

  -- Dispatch by message type field
  dispatchCommand : StreamState → List (String × JSON) → StreamState × String
  dispatchCommand state obj with lookupString "type" obj
  ... | nothing = wrapJSON (state , Msg.Response.Error (DispatchErr MissingTypeField))
  ... | just msgType =
    if ⌊ msgType ≟ "command" ⌋
    then tryParseCommand state obj
    else wrapJSON (state , Msg.Response.Error (DispatchErr (UnknownMessageType msgType)))

  -- Post-parse nesting-depth check (R19 AGDA-D-13.4 phase 2a — typed wire-
  -- error refinement).  The JSON parser terminates structurally on `length
  -- input`, so deep adversarial inputs parse cleanly; this guard measures
  -- the actual depth of the parsed tree and rejects above `max-nesting-
  -- depth` with `ParseErr (InputBoundExceeded NestingDepth observed limit)`,
  -- exposing the structured `bound_kind / observed / limit` triple via
  -- `errorExtras`.  Pre-2a (R19 cluster 8 phase a) emitted the untyped
  -- `DispatchErr InvalidJSON` from inside `parseJSON`; moving the check
  -- here keeps `parseJSON` a pure inverse of `formatJSON`.
  handleParsedJSON : StreamState → Maybe JSON → StreamState × String
  handleParsedJSON state nothing = wrapJSON (state , Msg.Response.Error (DispatchErr InvalidJSON))
  handleParsedJSON state (just j) =
    let depth = jsonDepth j
    in if depth <ᵇ suc max-nesting-depth
       then handleJSONObject state j
       else wrapJSON (state , Msg.Response.Error
              (InputBoundExceeded NestingDepth depth max-nesting-depth))
    where
      handleJSONObject : StreamState → JSON → StreamState × String
      handleJSONObject state (JObject obj) = dispatchCommand state obj
      handleJSONObject state _ = wrapJSON (state , Msg.Response.Error (DispatchErr RequestNotObject))

-- Process a single JSON line and update stream state.
-- NOINLINE: Required for MAlonzo FFI (ensures symbol is exported to Haskell).
--
-- Adversarial-input bound: rejects inputs longer than `max-json-bytes`
-- (`Aletheia.Limits`) with a typed `ParseError.InputBoundExceeded` before
-- invoking the JSON parser, per AGENTS.md universal rule "Adversarial-input
-- bounds at parser surfaces".  Each binding additionally short-circuits at
-- the FFI entry to avoid marshaling oversize payloads.  Nesting-depth bound
-- enforced at `handleParsedJSON` on the parsed tree (typed `ParseError.
-- InputBoundExceeded NestingDepth …`, AGDA-D-13.4 phase 2a).
processJSONLine : StreamState → String → StreamState × String
{-# NOINLINE processJSONLine #-}
processJSONLine state jsonLine =
  let chars    = toList jsonLine
      inputLen = length chars
  in if inputLen ≤ᵇ max-json-bytes
     then handleParsedJSON state (mapₘ proj₁ (runParser parseJSON chars))
     else wrapJSON (state , Msg.Response.Error
            (InputBoundExceeded InputLengthBytes inputLen max-json-bytes))
