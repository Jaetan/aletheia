{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 4c — TAT TopStmt dispatcher: DBCAttrDef arm.
--
-- ONE case, no scope pattern-match.  The `'B'∷'A'∷` prefix exposure that
-- `parseTopStmt-on-BA-head` needs is supplied by the propositional
-- `emitAttrDef-chars-BA-head` lemma (which case-splits on scope under a
-- small `≡`-typed goal, ~14s / 449 MB) — moved out of the full TopStmt
-- goal type, where forcing the same per-scope reduction inside a goal
-- containing `liftTopStmt`/`advancePositions`/`mkResult` blew through
-- -M16G.
module Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Attribute.TopStmt.Def where

open import Data.Char  using (Char)
open import Data.List  using (List; []; _∷_)
  renaming (_++_ to _++ₗ_)
open import Data.Maybe using (just)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong)

open import Aletheia.Parser.Combinators using
  (Position; ParseResult; mkResult; advancePositions)

open import Aletheia.DBC.Types using
  (AttrDef; DBCAttribute; DBCAttrDef)

open import Aletheia.DBC.TextFormatter.Attributes using
  (emitAttribute-chars; emitAttrDef-chars)

open import Aletheia.DBC.TextParser.Attributes using
  (parseAttrLine)
open import Aletheia.DBC.TextParser.TopLevel using
  (TopStmt; TSAttribute; parseTopStmt)

open import Aletheia.DBC.TextParser.Properties.Aggregator.Foundations using
  ( rawOf; WFAttribute
  ; TopStmtTyped; TAT
  ; emitTopStmt-chars
  ; liftTopStmt
  )
open import Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Attribute.Universal using
  (parseAttrLine-on-emit-Attribute)
open import Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Attribute.PrefixHead using
  ( emitAttrDef-chars-BA-head
  ; parseTopStmt-on-BA-head-via-prefix
  )

open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (SuffixStops)
open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  (isNewlineStart)

-- ============================================================================
-- DBCAttrDef ARM  (1 case — scope work moved into the prefix lemma)
-- ============================================================================

parseTopStmt-on-emit-typed-TAT-Def :
    ∀ (defs : List AttrDef) (pos : Position)
      (d : AttrDef) (outer : List Char)
  → WFAttribute defs (DBCAttrDef d)
  → SuffixStops isNewlineStart outer
  → parseTopStmt pos (emitTopStmt-chars defs (TAT (DBCAttrDef d)) ++ₗ outer)
    ≡ just (mkResult
              (liftTopStmt defs (TAT (DBCAttrDef d)))
              (advancePositions pos
                 (emitTopStmt-chars defs (TAT (DBCAttrDef d))))
              outer)
parseTopStmt-on-emit-typed-TAT-Def defs pos d outer wf ss-NL =
  parseTopStmt-on-BA-head-via-prefix pos _ _ _ outer _
    (cong (_++ₗ outer) (proj₂ (emitAttrDef-chars-BA-head d)))
    (parseAttrLine-on-emit-Attribute defs pos (DBCAttrDef d) outer wf ss-NL)
