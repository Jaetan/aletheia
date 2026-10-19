-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- A parser run over a whole text has three outcomes: it failed, it stopped
-- before the end, or it consumed the text.  The DBC text route and the
-- decimal entry refuse the first two with the same typed error, carrying
-- the failure watermark `runParserPartial` pairs with its result (the
-- deepest position any parse attempt reached) and, for a stop, where the
-- unconsumed input starts.
module Aletheia.DBC.TextParser.Consumed where

open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Aletheia.Parser.Combinators using (ParseResult; mkResult)
open import Aletheia.Parser.Position using (Position)
open import Aletheia.Error using (DBCTextParseError; ParseFailure; TrailingInput)

consumed : ∀ {A : Set} → Position → Maybe (ParseResult A) → DBCTextParseError ⊎ ParseResult A
consumed w nothing                        = inj₁ (ParseFailure w)
consumed w (just (mkResult _ pos (_ ∷ _))) = inj₁ (TrailingInput w pos)
consumed _ (just res@(mkResult _ _ []))    = inj₂ res
