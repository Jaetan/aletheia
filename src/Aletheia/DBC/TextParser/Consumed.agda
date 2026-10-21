-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- A parser run over a whole text has three outcomes: it failed, it stopped
-- before the end, or it consumed the text.  The DBC text route and the
-- decimal entry refuse the first two with the same typed errors, read from
-- the watermark `runParserPartial` pairs with its result: a name the
-- identifier decision refused, located where it starts; else the deepest
-- position any parse attempt reached and, for a stop, where the unconsumed
-- input starts.
module Aletheia.DBC.TextParser.Consumed where

open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Aletheia.Parser.Combinators using (ParseResult; mkResult)
open import Data.String using (fromList)
open import Aletheia.Parser.Watermark using (Watermark; mark; Refusal; refused)
open import Aletheia.DBC.Identifier using (TooLong; Keyword; BadChars)
open import Aletheia.Limits using (IdentifierLength; max-identifier-length)
open import Aletheia.Error using
  (Error; DBCTextParseErr; ParseFailure; TrailingInput; InputBoundExceededAt; KeywordName; AtText; ParseErr; InvalidIdentifier)

-- The refusals are the JSON route's own errors, located where the name
-- starts: the kernel spells each code once.
refusalError : Refusal → Error
refusalError (refused start (TooLong n)) =
  InputBoundExceededAt (AtText start) IdentifierLength n max-identifier-length
refusalError (refused start (Keyword kw)) = KeywordName (AtText start) (fromList kw)
refusalError (refused start (BadChars cs)) = ParseErr (InvalidIdentifier (AtText start) (fromList cs))

-- A refusal on the watermark stands at the deepest position reached, so a
-- run that failed or stopped there is answered by the refusal; a run that
-- consumed the text passed it on another branch.
consumed : ∀ {A : Set} → Watermark → Maybe (ParseResult A) → Error ⊎ ParseResult A
consumed _                 (just res@(mkResult _ _ []))      = inj₂ res
consumed (mark w nothing)  (just (mkResult _ pos (_ ∷ _)))   = inj₁ (DBCTextParseErr (TrailingInput w pos))
consumed (mark _ (just r)) (just (mkResult _ _ (_ ∷ _)))     = inj₁ (refusalError r)
consumed (mark w nothing)  nothing                           = inj₁ (DBCTextParseErr (ParseFailure w))
consumed (mark _ (just r)) nothing                           = inj₁ (refusalError r)
