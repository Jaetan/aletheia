{-# OPTIONS --safe --without-K #-}

-- Shared JSON types and utilities re-exported from Protocol.JSON.
--
-- Purpose: Provide a layer-neutral import path for JSON types so that
-- non-Protocol modules (e.g. LTL/JSON) can use JSON without depending
-- on the Protocol layer. This eliminates the LTL → Protocol cross-layer
-- dependency that otherwise exists when LTL/JSON.agda imports
-- Protocol.JSON directly.
module Aletheia.JSON where

open import Aletheia.Protocol.JSON public
