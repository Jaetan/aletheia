-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- JSON, the protocol's text: every command is read and every reply written
-- through this module, which re-exports four:
--   Types.agda   the value type `JSON`
--   Lookup.agda  value extractors and typed lookups
--   Format.agda  `formatJSON` and `formatJSONChars`
--   Parse.agda   `parseJSON`, RFC 8259's grammar
module Aletheia.Protocol.JSON where

open import Aletheia.Protocol.JSON.Types public
open import Aletheia.Protocol.JSON.Lookup public
open import Aletheia.Protocol.JSON.Format public
open import Aletheia.Protocol.JSON.Parse public
