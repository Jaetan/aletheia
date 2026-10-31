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
open import Data.Bool using (true; false; if_then_else_)
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
  ; past-≤ᵇ; past-<ᵇ
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

-- A parsed request: the parse failure at its watermark, or the tree held to
-- its nesting depth and its largest number component.
readParsed : Watermark × Maybe (JSON × Position) → Error ⊎ JSON
readParsed (w , nothing) = inj₁ (DispatchErr (InvalidJSON (Watermark.position w)))
readParsed (_ , just (j , _)) with jsonDepth j <ᵇ suc max-nesting-depth in deq
... | false = inj₁ (InputBoundExceeded NestingDepth (jsonDepth j) max-nesting-depth (tt , past-<ᵇ (jsonDepth j) max-nesting-depth deq))
... | true with jsonMaxComponent j ≤ᵇ max-rational-component-magnitude in ceq
...   | true  = inj₂ j
...   | false = inj₁ (InputBoundExceeded RationalComponentMagnitude (jsonMaxComponent j)
                       max-rational-component-magnitude
                       (tt , past-≤ᵇ (jsonMaxComponent j) max-rational-component-magnitude ceq))

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
readRequest line with utf8Length (toList line) ≤ᵇ max-json-bytes in eq
... | true  = readParsed (runParser parseJSON (toList line))
... | false = inj₁ (InputBoundExceeded InputLengthBytes (utf8Length (toList line)) max-json-bytes
                     (tt , past-≤ᵇ (utf8Length (toList line)) max-json-bytes eq))

-- Process a single JSON line and update stream state.
-- NOINLINE: Required for MAlonzo FFI (ensures symbol is exported to Haskell).
-- The Python, Go and C++ bindings also refuse a command past
-- `max-json-bytes` at the FFI entry, so an oversize payload is not
-- marshaled.
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
