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
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.List using (List; length)
open import Data.Nat using (_≤ᵇ_; _<ᵇ_; suc)
open import Data.Sum using (inj₁; inj₂)
open import Data.Bool using (if_then_else_)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Aletheia.Parser.Combinators using (runParser)
open import Aletheia.Parser.Position using (Position)
open import Aletheia.Protocol.JSON using (JSON; JObject; parseJSON; lookupString)
open import Aletheia.Protocol.JSON.Types using (jsonDepth; jsonMaxComponent)
open import Aletheia.Protocol.Routing using (parseCommand)
open import Aletheia.Protocol.StreamState using (StreamState)
open import Aletheia.Protocol.Handlers using (processStreamCommand)
open import Aletheia.Error using
  ( DispatchErr
  ; InputBoundExceeded
  ; MissingTypeField; UnknownMessageType; InvalidJSON; RequestNotObject
  )
open import Aletheia.Limits using
  ( InputLengthBytes; NestingDepth; RationalComponentMagnitude
  ; max-json-bytes; max-nesting-depth; max-rational-component-magnitude
  )
open import Aletheia.Main.Binary using (wrapJSON)
import Aletheia.Protocol.Message as Msg

private
  -- Try to parse and execute a command from JSON fields.  parseCommand
  -- returns `Error ⊎ StreamCommand` (the return type accommodates the
  -- typed `InputBoundExceeded FrameByteCount …` emit at
  -- `parseBytePayload`); the legacy RouteError
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

  -- Post-parse tree bounds.  The JSON parser terminates structurally on
  -- `length input`, so deep or numerically absurd adversarial inputs
  -- parse cleanly; these guards measure the parsed tree and reject with
  -- typed `InputBoundExceeded` errors exposing the structured
  -- `bound_kind / observed / limit` triple via `errorExtras`:
  --   * nesting depth above `max-nesting-depth` (`jsonDepth`);
  --   * any number whose rational components exceed the Int64 wire
  --     range (`jsonMaxComponent` vs `max-rational-component-magnitude`)
  --     — one bound over every kernel-bound numeric position, matching
  --     the range the decimal SSOT and the binary FFI's rational slots
  --     enforce, so a bare JSON integer cannot carry a component the
  --     wire cannot represent.
  -- The checks live here rather than inside `parseJSON` to keep the
  -- parser a pure inverse of `formatJSON`.
  -- Takes the full `runParser` pair: the failure watermark (proj₁) feeds
  -- the positioned `InvalidJSON` on the nothing arm; the success arm
  -- drops both the watermark and the end position.
  handleParsedJSON : StreamState → Position × Maybe (JSON × Position) → StreamState × String
  handleParsedJSON state (w , nothing) = wrapJSON (state , Msg.Response.Error (DispatchErr (InvalidJSON w)))
  handleParsedJSON state (_ , just (j , _)) =
    let depth = jsonDepth j
        comp  = jsonMaxComponent j
    in if depth <ᵇ suc max-nesting-depth
       then (if comp ≤ᵇ max-rational-component-magnitude
             then handleJSONObject state j
             else wrapJSON (state , Msg.Response.Error
                    (InputBoundExceeded RationalComponentMagnitude comp
                                        max-rational-component-magnitude)))
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
-- InputBoundExceeded NestingDepth …`).
processJSONLine : StreamState → String → StreamState × String
{-# NOINLINE processJSONLine #-}
processJSONLine state jsonLine =
  let chars    = toList jsonLine
      inputLen = length chars
  in if inputLen ≤ᵇ max-json-bytes
     then handleParsedJSON state (runParser parseJSON chars)
     else wrapJSON (state , Msg.Response.Error
            (InputBoundExceeded InputLengthBytes inputLen max-json-bytes))
