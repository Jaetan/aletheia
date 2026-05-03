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
open import Data.List using (List)
open import Data.Sum using (inj₁; inj₂)
open import Data.Bool using (if_then_else_)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Aletheia.Parser.Combinators using (runParser)
open import Aletheia.Protocol.JSON using (JSON; JObject; parseJSON; lookupString)
open import Aletheia.Protocol.Routing using (parseCommand)
open import Aletheia.Protocol.StreamState using (StreamState)
open import Aletheia.Protocol.Handlers using (processStreamCommand)
open import Aletheia.Error using
  ( Error; RouteErr; DispatchErr
  ; DispatchError; MissingTypeField; UnknownMessageType; InvalidJSON; RequestNotObject
  )
open import Aletheia.Main.Binary using (wrapJSON)
import Aletheia.Protocol.Message as Msg

private
  -- Try to parse and execute a command from JSON fields
  tryParseCommand : StreamState → List (String × JSON) → StreamState × String
  tryParseCommand state obj with parseCommand obj
  ... | inj₁ routeErr = wrapJSON (state , Msg.Response.Error (RouteErr routeErr))
  ... | inj₂ cmd = wrapJSON (processStreamCommand cmd state)

  -- Dispatch by message type field
  dispatchCommand : StreamState → List (String × JSON) → StreamState × String
  dispatchCommand state obj with lookupString "type" obj
  ... | nothing = wrapJSON (state , Msg.Response.Error (DispatchErr MissingTypeField))
  ... | just msgType =
    if ⌊ msgType ≟ "command" ⌋
    then tryParseCommand state obj
    else wrapJSON (state , Msg.Response.Error (DispatchErr (UnknownMessageType msgType)))

  -- Handle parsed JSON result
  handleParsedJSON : StreamState → Maybe JSON → StreamState × String
  handleParsedJSON state nothing = wrapJSON (state , Msg.Response.Error (DispatchErr InvalidJSON))
  handleParsedJSON state (just (JObject obj)) = dispatchCommand state obj
  handleParsedJSON state (just _) = wrapJSON (state , Msg.Response.Error (DispatchErr RequestNotObject))

-- Process a single JSON line and update stream state.
-- NOINLINE: Required for MAlonzo FFI (ensures symbol is exported to Haskell).
processJSONLine : StreamState → String → StreamState × String
{-# NOINLINE processJSONLine #-}
processJSONLine state jsonLine = handleParsedJSON state (mapₘ proj₁ (runParser parseJSON (toList jsonLine)))
