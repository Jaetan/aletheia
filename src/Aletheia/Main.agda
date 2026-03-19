{-# OPTIONS --no-main --sized-types --without-K #-}

-- Main entry point for Aletheia (JSON streaming protocol).
--
-- Purpose: Process line-delimited JSON requests and emit JSON responses.
-- Protocol: parse_dbc → set_properties → start_stream → data_frames* → end_stream
-- State Machine: WaitingForDBC → ReadyToStream → Streaming
--
-- Compilation: Compiled to Haskell via MAlonzo, called from AletheiaFFI.hs.
-- Integration: Python loads libaletheia-ffi.so via ctypes (direct FFI, no subprocess).
--
-- State machine logic delegated to Protocol.StreamState; Main provides processJSONLine only.
--
-- Key design: ALL logic lives in Agda (parsing, validation, state, LTL checking).
-- Haskell FFI shim (AletheiaFFI.hs) only handles C-callable exports and state management.
--
-- NOTE: This module uses --sized-types which is incompatible with --safe.
-- This is required because it imports modules with sized types.
module Aletheia.Main where

open import Data.String using (String; toList; _≟_) renaming (_++_ to _++ₛ_)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Product using (proj₁; _×_; _,_)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (if_then_else_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Size using (Size)
open import Codata.Sized.Colist using (Colist; []; _∷_)
open import Codata.Sized.Thunk using (force)

-- Phase 2B: JSON streaming protocol
open import Aletheia.Parser.Combinators using (runParser)
open import Aletheia.Protocol.JSON using (JSON; JObject; parseJSON; formatJSON; lookupString)
open import Aletheia.Protocol.Routing as Routing using (formatResponse; parseDataFrame; parseCommand)
open import Aletheia.Protocol.StreamState using (StreamState; initialState; processStreamCommand; handleDataFrame)
import Aletheia.Protocol.Message as Msg

-- ============================================================================
-- Phase 2B: JSON Streaming Protocol
-- ============================================================================

-- Process a single JSON line and update stream state
--
-- Algorithm:
--   1. Parse JSON string → Maybe JSON
--   2. Validate JSON is an object with "type" field
--   3. Route by type: "command" → command handler, "data" → data frame handler
--   4. Update state machine and generate response
--   5. Format response as JSON string
--
-- Error Handling:
--   - Graceful degradation: invalid input → error response, state unchanged
--   - Descriptive error messages at each parsing stage (JSON parse, type field, routing)
--   - parseCommand/parseDataFrame return error messages for detailed context
--
-- State Threading:
--   - State flows through: parseJSON_helper → routing → handler → response
--   - On error: original state returned unchanged
--   - On success: new state from handler (DBC parse, properties set, stream update)
--
-- NOINLINE Pragma:
--   - Required for MAlonzo FFI: ensures symbol is exported to Haskell
--   - Without this, Agda might inline the function and break FFI linkage
--   - Haskell shim calls this by mangled name (detected at build time)
--
-- Returns: (new state, JSON response string)
processJSONLine : StreamState → String → StreamState × String
{-# NOINLINE processJSONLine #-}
processJSONLine state jsonLine = parseJSON_helper (map proj₁ (runParser parseJSON (toList jsonLine)))
  where
    -- Try to parse command with detailed tracing
    tryParseCommand : List (String × JSON) → StreamState × String
    tryParseCommand obj with parseCommand obj
    ... | inj₁ errMsg = (state , formatJSON (Routing.formatResponse (Msg.Response.Error errMsg)))
    ... | inj₂ cmd =
          let (newState , response) = processStreamCommand cmd state
          in (newState , formatJSON (Routing.formatResponse response))

    -- Trace all messages
    parseJSON_helperWithTrace : JSON → StreamState × String
    parseJSON_helperWithTrace (JObject obj) =
      let typeField = lookupString "type" obj
      in case_type typeField obj
      where
        case_type : Maybe String → List (String × JSON) → StreamState × String
        case_type nothing obj = (state , formatJSON (Routing.formatResponse (Msg.Response.Error "Missing 'type' field in request")))
        case_type (just msgType) obj =
          if ⌊ msgType ≟ "data" ⌋
          then trace_dataframe obj
          else if ⌊ msgType ≟ "command" ⌋
               then tryParseCommand obj
               else (state , formatJSON (Routing.formatResponse (Msg.Response.Error ("Unknown message type: " ++ₛ msgType))))
          where
            trace_dataframe : List (String × JSON) → StreamState × String
            trace_dataframe obj with parseDataFrame obj
            ... | nothing = (state , formatJSON (Routing.formatResponse (Msg.Response.Error "Failed to parse data frame")))
            ... | just (inj₁ errMsg) = (state , formatJSON (Routing.formatResponse (Msg.Response.Error errMsg)))
            ... | just (inj₂ (timestamp , frame)) =
                  let (newState , response) = handleDataFrame state timestamp frame
                  in (newState , formatJSON (Routing.formatResponse response))
    parseJSON_helperWithTrace json = (state , formatJSON (Routing.formatResponse (Msg.Response.Error "Request must be a JSON object")))

    parseJSON_helper : Maybe JSON → StreamState × String
    parseJSON_helper nothing = (state , formatJSON (Routing.formatResponse (Msg.Response.Error "Invalid JSON")))
    parseJSON_helper (just (JObject obj)) = parseJSON_helperWithTrace (JObject obj)
    parseJSON_helper (just _) = (state , formatJSON (Routing.formatResponse (Msg.Response.Error "Request must be a JSON object")))

-- ============================================================================
-- COINDUCTIVE STREAMING INTERFACE (O(1) Memory)
-- ============================================================================

-- Process a colist of JSON lines and produce a colist of responses
-- This is the O(1) memory interface: processes frames one at a time without accumulation
-- State is threaded through the stream computation
processStream : ∀ {i} → StreamState → Colist String i → Colist String i
{-# NOINLINE processStream #-}
processStream state [] = []
processStream state (line ∷ rest) =
  let (newState , response) = processJSONLine state line
  in response ∷ λ where .force → processStream newState (force rest)