-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- The farthest point a parse reached and, when the identifier decision
-- refused a name there, which name and why.  Every parser result carries
-- one as its first component; the combinators merge them by position, and
-- a driver reads the refusal when the parse fails, so a refused name is
-- reported with its code and the line and column where it starts rather
-- than as a bare position.
module Aletheia.Parser.Watermark where

open import Data.Bool using (true; false)
open import Data.Maybe using (Maybe; just; nothing)

open import Aletheia.Parser.Position using (Position; samePosᵇ; maxₚ)
open import Aletheia.DBC.Identifier using (IdentifierError)

-- A name the identifier decision refused: where it starts, and why.
record Refusal : Set where
  constructor refused
  field
    start  : Position
    reason : IdentifierError

record Watermark : Set where
  constructor mark
  field
    position : Position
    refusal  : Maybe Refusal

-- A point reached with nothing refused there.
at : Position → Watermark
at pos = mark pos nothing

-- The farther of two watermarks, by position as `maxₚ` orders them; at one
-- position, the refusal is kept (the first one when both carry one).
farthest : Watermark → Watermark → Watermark
farthest (mark p r) (mark q s) with samePosᵇ p q
... | true  = mark p (keep r s)
  where
    keep : Maybe Refusal → Maybe Refusal → Maybe Refusal
    keep (just x) _ = just x
    keep nothing  y = y
... | false with samePosᵇ (maxₚ p q) p
...   | true  = mark p r
...   | false = mark q s
