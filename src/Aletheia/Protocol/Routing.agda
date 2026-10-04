-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Command parsing for the streaming protocol.
--
-- Purpose: Parse JSON commands and dispatch to appropriate handlers.
-- Operations: parseCommand (JSON → RouteError ⊎ StreamCommand).
-- Role: Parses the "command" field from JSON objects, used by Main.processJSONLine.
-- Validation: All required fields checked, typed RouteError on failure.
module Aletheia.Protocol.Routing where

open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Aletheia.Prelude using (lookupByKey)
open import Aletheia.Protocol.JSON using (JSON; lookupString; lookupArray)
open import Aletheia.Protocol.Message using (StreamCommand; ParseDBC; SetProperties; ValidateDBC; ParseDBCText; FormatDBCText)
open import Aletheia.Error using
  ( RouteError
  ; RouteMissingField; UnknownCommand
  ; MissingCommandField; MissingDBCField; MissingPropsField
  ; InContext
  )

-- ============================================================================
-- INTERNAL HELPERS
-- ============================================================================

private
  -- Parse ParseDBC command
  tryParseDBC : List (String × JSON) → RouteError ⊎ StreamCommand
  tryParseDBC obj with lookupByKey "dbc" obj
  ... | nothing = inj₁ (InContext "ParseDBC" MissingDBCField)
  ... | just dbc = inj₂ (ParseDBC dbc)

  -- Parse SetProperties command
  trySetProperties : List (String × JSON) → RouteError ⊎ StreamCommand
  trySetProperties obj with lookupArray "properties" obj
  ... | nothing = inj₁ MissingPropsField
  ... | just props = inj₂ (SetProperties props)

  -- Parse ValidateDBC command
  tryValidateDBC : List (String × JSON) → RouteError ⊎ StreamCommand
  tryValidateDBC obj with lookupByKey "dbc" obj
  ... | nothing = inj₁ (InContext "ValidateDBC" MissingDBCField)
  ... | just dbc = inj₂ (ValidateDBC dbc)

  -- Parse ParseDBCText command (raw DBC text image)
  tryParseDBCText : List (String × JSON) → RouteError ⊎ StreamCommand
  tryParseDBCText obj with lookupString "text" obj
  ... | nothing   = inj₁ (InContext "ParseDBCText" (RouteMissingField "text"))
  ... | just text = inj₂ (ParseDBCText text)

  -- Parse FormatDBCText command (DBC JSON structure → DBC text)
  tryFormatDBCText : List (String × JSON) → RouteError ⊎ StreamCommand
  -- The handler refuses with a typed error rather than emit text that does not
  -- round-trip, so routing only needs the DBC structure.
  tryFormatDBCText obj with lookupByKey "dbc" obj
  ... | nothing  = inj₁ (InContext "FormatDBCText" MissingDBCField)
  ... | just dbc = inj₂ (FormatDBCText dbc)

  -- Dispatch table for command parsers
  commandDispatchTable : List (String × (List (String × JSON) → RouteError ⊎ StreamCommand))
  commandDispatchTable =
    ("parseDBC" , tryParseDBC) ∷
    ("setProperties" , trySetProperties) ∷
    ("validateDBC" , tryValidateDBC) ∷
    ("parseDBCText" , tryParseDBCText) ∷
    ("formatDBCText" , tryFormatDBCText) ∷
    []

  -- Dispatch using table lookup
  dispatchCommand : String → List (String × JSON) → RouteError ⊎ StreamCommand
  dispatchCommand cmdType obj with lookupByKey cmdType commandDispatchTable
  ... | nothing = inj₁ (UnknownCommand cmdType)
  ... | just parser = parser obj

-- Parse StreamCommand from JSON object (returns RouteError on failure).
parseCommand : List (String × JSON) → RouteError ⊎ StreamCommand
parseCommand obj with lookupString "command" obj
... | nothing = inj₁ MissingCommandField
... | just cmdType = dispatchCommand cmdType obj
