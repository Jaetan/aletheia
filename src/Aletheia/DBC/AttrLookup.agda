-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Attribute-definition lookup shared by the DBC text formatter and text
-- parser.  Both `TextFormatter.Attributes` and `TextParser.Attributes`
-- re-export `lookupDef` publicly, so the formatter's emit path and the
-- parser's refinement pass resolve attribute names through the SAME
-- function — proofs relating the two sides need no bridging lemma.
module Aletheia.DBC.AttrLookup where

open import Data.Bool using (if_then_else_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)

open import Aletheia.DBC.Types using (AttrDef)
open import Aletheia.DBC.Identifier using (Identifier; _≡csᵇ_)

-- Look up an attribute definition by name.  Linear scan; fine for the
-- small def counts seen in practice (corpus: single digits).
lookupDef : Identifier → List AttrDef → Maybe AttrDef
lookupDef _ [] = nothing
lookupDef name (d ∷ rest) =
  if Identifier.name name ≡csᵇ Identifier.name (AttrDef.name d)
    then just d
    else lookupDef name rest
