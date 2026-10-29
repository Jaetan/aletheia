-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K --no-main #-}

-- JSON streaming protocol entry points.
--
-- Purpose: Process line-delimited JSON requests and emit JSON responses.
-- Protocol: parseDBC → setProperties → startStream → data_frames* → endStream,
--   plus extractAllSignals, validateDBC, formatDBC, parseDBCText.
-- Exports: processJSONLine (JSON commands), checkPropertyText (the build-time
--   property check).
module Aletheia.Main.JSON where

open import Data.String using (String; toList; _≟_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.List using (List)
open import Aletheia.Data.UTF8 using (utf8Length)
open import Data.Nat using (_≤ᵇ_; _<ᵇ_; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (if_then_else_)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Aletheia.Parser.Combinators using (runParser)
open import Aletheia.Parser.Watermark using (Watermark)
open import Aletheia.Parser.Position using (Position)
open import Aletheia.Protocol.JSON using (JSON; JObject; parseJSON; lookupString)
open import Aletheia.Protocol.JSON.Types using (jsonDepth; jsonMaxComponent)
open import Aletheia.Protocol.Routing using (parseCommand)
open import Aletheia.Protocol.StreamState using (StreamState)
open import Aletheia.Protocol.Handlers using (processStreamCommand; checkProperty)
open import Aletheia.Error using
  ( Error; DispatchErr; RouteErr
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
  -- Try to parse and execute a command from JSON fields.
  tryParseCommand : StreamState → List (String × JSON) → StreamState × String
  tryParseCommand state obj with parseCommand obj
  ... | inj₁ err = wrapJSON (state , Msg.Response.Error (RouteErr err))
  ... | inj₂ cmd = wrapJSON (processStreamCommand cmd state)

  -- Dispatch by message type field
  dispatchCommand : StreamState → List (String × JSON) → StreamState × String
  dispatchCommand state obj with lookupString "type" obj
  ... | nothing = wrapJSON (state , Msg.Response.Error (DispatchErr MissingTypeField))
  ... | just msgType =
    if ⌊ msgType ≟ "command" ⌋
    then tryParseCommand state obj
    else wrapJSON (state , Msg.Response.Error (DispatchErr (UnknownMessageType msgType)))

-- A request's text read as every command's is.  Its UTF-8 length is held
-- to `max-json-bytes`, the size of the buffer that crossed the boundary,
-- before the parser runs, per AGENTS.md universal rule "Adversarial-input
-- bounds at parser surfaces".  The JSON parser terminates structurally on the
-- input list, so deep or numerically absurd adversarial inputs parse
-- cleanly; the parsed tree is then measured and refused with typed
-- `InputBoundExceeded` errors exposing the structured
-- `bound_kind / observed / limit` triple via `errorExtras`:
--   * nesting depth above `max-nesting-depth` (`jsonDepth`);
--   * any number whose rational components exceed the 128-bit magnitude
--     range (`jsonMaxComponent` vs `max-rational-component-magnitude`),
--     one bound over every kernel-bound numeric position, matching the range
--     the decimal SSOT and the binary FFI's rational slots enforce, so a bare
--     JSON integer cannot carry a component the wire cannot represent.
-- The checks live here, after the parse, so `parseJSON` is RFC 8259's
-- grammar alone (`parseJSON-sound`) and reads back what `formatJSONChars`
-- writes (`parseJSON-formatJSONChars`).
readRequest : String → Error ⊎ JSON
readRequest line =
  let chars    = toList line
      inputLen = utf8Length chars
  in if inputLen ≤ᵇ max-json-bytes
     then fromParse (runParser parseJSON chars)
     else inj₁ (InputBoundExceeded InputLengthBytes inputLen max-json-bytes)
  where
    -- Takes the full `runParser` pair: the failure watermark (proj₁) feeds
    -- the positioned `InvalidJSON` on the nothing arm; the success arm drops
    -- both the watermark and the end position.
    fromParse : Watermark × Maybe (JSON × Position) → Error ⊎ JSON
    fromParse (w , nothing) = inj₁ (DispatchErr (InvalidJSON (Watermark.position w)))
    fromParse (_ , just (j , _)) =
      let depth = jsonDepth j
          comp  = jsonMaxComponent j
      in if depth <ᵇ suc max-nesting-depth
         then (if comp ≤ᵇ max-rational-component-magnitude
               then inj₂ j
               else inj₁ (InputBoundExceeded RationalComponentMagnitude comp
                                             max-rational-component-magnitude))
         else inj₁ (InputBoundExceeded NestingDepth depth max-nesting-depth)

-- Process a single JSON line and update stream state.
-- NOINLINE: Required for MAlonzo FFI (ensures symbol is exported to Haskell).
-- Each binding additionally short-circuits at the FFI entry to avoid
-- marshaling oversize payloads.
processJSONLine : StreamState → String → StreamState × String
{-# NOINLINE processJSONLine #-}
processJSONLine state jsonLine with readRequest jsonLine
... | inj₁ e             = wrapJSON (state , Msg.Response.Error e)
... | inj₂ (JObject obj) = dispatchCommand state obj
... | inj₂ _             = wrapJSON (state , Msg.Response.Error (DispatchErr RequestNotObject))

-- The build-time property check: one property's text read as a request's
-- is, then as set_properties reads a property, each signal name decided as
-- an identifier and its presence in a DBC left to set_properties.
-- NOINLINE: Required for MAlonzo FFI (ensures symbol is exported to Haskell).
checkPropertyText : String → Error ⊎ ⊤
{-# NOINLINE checkPropertyText #-}
checkPropertyText text with readRequest text
... | inj₁ e = inj₁ e
... | inj₂ j with checkProperty j
...   | inj₁ e = inj₁ e
...   | inj₂ _ = inj₂ tt
