{-# OPTIONS --safe --without-K #-}

-- JSON data types, parser, and formatter with rational number support.
--
-- Purpose: Core JSON handling for streaming protocol (parse/format JSON).
-- Types: JSON (JNull, JBool, JNumber, JString, JArray, JObject).
-- Operations: parseJSON (String → JSON), formatJSON (JSON → String).
-- Role: Foundation for all protocol communication (commands, responses, data frames).
--
-- Structure: Implementation split across sub-modules:
--   Types.agda  — JSON data type (~25 lines)
--   Lookup.agda — value extractors and typed lookup helpers (~100 lines)
--   Format.agda — formatJSON and formatRational (~55 lines)
--   Parse.agda  — parseJSON and all parse helpers (~200 lines)
-- This facade re-exports everything for backward compatibility.
module Aletheia.Protocol.JSON where

open import Aletheia.Protocol.JSON.Types public
open import Aletheia.Protocol.JSON.Lookup public
open import Aletheia.Protocol.JSON.Format public
open import Aletheia.Protocol.JSON.Parse public
