-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 4c — TAT TopStmt dispatcher: DBCAttrAssign arm.
--
-- ONE case, no target pattern-match.  Per-target work moved into the
-- propositional `emitAttrAssign-chars-BA-head` lemma (Σ over `rest` with
-- prefix-equality witness; case-splits on target under a small `≡`-typed
-- goal).  The full TopStmt goal type stays abstract over `a` and never
-- gets case-split, so reduction of `liftTopStmt`/`advancePositions`/
-- `mkResult` happens once.
module Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Attribute.TopStmt.Assign where

open import Data.Char  using (Char)
open import Data.List  using (List)
  renaming (_++_ to _++ₗ_)
open import Data.Maybe using (just)
open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong)

open import Aletheia.Parser.Combinators using
  (Position; mkResult; advancePositions)

open import Aletheia.DBC.Types using
  (AttrDef; AttrAssign; DBCAttrAssign)

open import Aletheia.DBC.TextParser.TopLevel using
  (parseTopStmt)

open import Aletheia.DBC.TextParser.Properties.Aggregator.Foundations using
  ( WFAttribute
  ; TAT
  ; emitTopStmt-chars
  ; liftTopStmt
  )
open import Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Attribute.Universal using
  (parseAttrLine-on-emit-Attribute)
open import Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Attribute.PrefixHead using
  ( emitAttrAssign-chars-BA-head
  ; parseTopStmt-on-BA-head-via-prefix
  )

open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (SuffixStops)
open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  (isNewlineStart)

-- ============================================================================
-- DBCAttrAssign ARM  (1 case — target work moved into the prefix lemma)
-- ============================================================================

parseTopStmt-on-emit-typed-TAT-Assign :
    ∀ (defs : List AttrDef) (pos : Position)
      (a : AttrAssign) (outer : List Char)
  → WFAttribute defs (DBCAttrAssign a)
  → SuffixStops isNewlineStart outer
  → parseTopStmt pos (emitTopStmt-chars defs (TAT (DBCAttrAssign a)) ++ₗ outer)
    ≡ just (mkResult
              (liftTopStmt defs (TAT (DBCAttrAssign a)))
              (advancePositions pos
                 (emitTopStmt-chars defs (TAT (DBCAttrAssign a))))
              outer)
parseTopStmt-on-emit-typed-TAT-Assign defs pos a outer wf ss-NL =
  parseTopStmt-on-BA-head-via-prefix pos _ _ _ outer _
    (cong (_++ₗ outer) (proj₂ (emitAttrAssign-chars-BA-head a)))
    (parseAttrLine-on-emit-Attribute defs pos (DBCAttrAssign a) outer wf ss-NL)
