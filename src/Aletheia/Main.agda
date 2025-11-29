{-# OPTIONS --no-main --guardedness --sized-types --without-K #-}

-- NOTE: This module uses --sized-types which is incompatible with --safe.
-- This is required because it imports modules with sized types and guardedness.

module Aletheia.Main where

open import Data.String using (String; toList; _≟_)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Product using (proj₁; _×_; _,_)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (if_then_else_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Sum using (_⊎_; inj₁; inj₂)

-- Phase 2B: JSON streaming protocol
open import Aletheia.Parser.Combinators using (runParser)
open import Aletheia.Protocol.JSON using (JSON; JObject; parseJSON; formatJSON; lookupString)
open import Aletheia.Protocol.Routing using (parseRequest; formatResponse; parseDataFrameWithTrace; parseCommandWithTrace)
open import Aletheia.Protocol.Routing as Routing using ()
open import Aletheia.Protocol.StreamState using (StreamState; initialState; processStreamCommand; handleDataFrame)
open import Aletheia.Data.Message as Msg using (Request; Response)

-- ============================================================================
-- Phase 2B: JSON Streaming Protocol
-- ============================================================================

-- Process a single JSON line and update stream state
-- Returns: (new state, JSON response string)
{-# NOINLINE processJSONLine #-}
processJSONLine : StreamState → String → StreamState × String
processJSONLine state jsonLine = parseJSON_helper (map proj₁ (runParser parseJSON (toList jsonLine)))
  where
    open import Aletheia.Protocol.JSON using (JObject; lookupString)
    open import Data.String using (_≟_) renaming (_++_ to _++S_)
    open import Relation.Nullary.Decidable using (⌊_⌋)
    open import Data.Bool using (if_then_else_)

    -- Try to parse command with detailed tracing
    tryParseCommand : List (String × JSON) → StreamState × String
    tryParseCommand obj with parseCommandWithTrace obj
    ... | inj₁ errMsg = (state , formatJSON (Routing.formatResponse (Msg.Response.Error errMsg)))
    ... | inj₂ cmd =
          let (newState , response) = processStreamCommand cmd state
          in (newState , formatJSON (Routing.formatResponse response))

    parseRequest_helper : Maybe Msg.Request → StreamState × String
    parseRequest_helper nothing = (state , formatJSON (Routing.formatResponse (Msg.Response.Error "Invalid request format")))
    parseRequest_helper (just (Msg.Request.CommandRequest cmd)) =
      let (newState , response) = processStreamCommand cmd state
      in (newState , formatJSON (Routing.formatResponse response))
    parseRequest_helper (just (Msg.Request.DataFrame timestamp frame)) =
      let (newState , response) = handleDataFrame state timestamp frame
      in (newState , formatJSON (Routing.formatResponse response))

    -- Trace all messages
    parseJSON_helperWithTrace : JSON → StreamState × String
    parseJSON_helperWithTrace (JObject obj) =
      let typeField = lookupString "type" obj
      in case_type typeField obj
      where
        case_type : Maybe String → List (String × JSON) → StreamState × String
        case_type nothing obj = (state , formatJSON (Routing.formatResponse (Msg.Response.Error "TRACE: missing type field")))
        case_type (just msgType) obj =
          if ⌊ msgType ≟ "data" ⌋
          then trace_dataframe obj
          else if ⌊ msgType ≟ "command" ⌋
               then tryParseCommand obj  -- Use traced command parser
               else (state , formatJSON (Routing.formatResponse (Msg.Response.Error ("TRACE: unknown type: " ++S msgType))))
          where
            trace_dataframe : List (String × JSON) → StreamState × String
            trace_dataframe obj with parseDataFrameWithTrace obj
            ... | nothing = (state , formatJSON (Routing.formatResponse (Msg.Response.Error "TRACE_DF0: parseDataFrameWithTrace returned nothing")))
            ... | just (inj₁ errMsg) = (state , formatJSON (Routing.formatResponse (Msg.Response.Error errMsg)))
            ... | just (inj₂ (timestamp , frame)) =
                  let (newState , response) = handleDataFrame state timestamp frame
                  in (newState , formatJSON (Routing.formatResponse response))
    parseJSON_helperWithTrace json = (state , formatJSON (Routing.formatResponse (Msg.Response.Error "TRACE: JSON is not an object")))

    parseJSON_helper : Maybe JSON → StreamState × String
    parseJSON_helper nothing = (state , formatJSON (Routing.formatResponse (Msg.Response.Error "TRACE_PARSE: Invalid JSON")))
    parseJSON_helper (just (JObject obj)) = parseJSON_helperWithTrace (JObject obj)
    parseJSON_helper (just _) = (state , formatJSON (Routing.formatResponse (Msg.Response.Error "TRACE_PARSE: JSON is not an object")))
