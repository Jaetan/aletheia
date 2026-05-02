{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 4c — TAT TopStmt dispatcher: DBCAttrDefault arm.
--
-- ONE case.  Uses `parseTopStmt-on-BA-head-via-prefix` with the explicit
-- prefix witness from `emitAttrDefault-chars-BA-head` (uniform with the
-- Def and Assign arms).
module Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Attribute.TopStmt.Default where

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
  (AttrDef; AttrDefault; DBCAttribute; DBCAttrDefault)

open import Aletheia.DBC.TextFormatter.Attributes using
  (emitAttribute-chars; emitAttrDefault-chars)

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
  ( emitAttrDefault-chars-BA-head
  ; parseTopStmt-on-BA-head-via-prefix
  )

open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (SuffixStops)
open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  (isNewlineStart)

-- ============================================================================
-- DBCAttrDefault ARM
-- ============================================================================

parseTopStmt-on-emit-typed-TAT-Default :
    ∀ (defs : List AttrDef) (pos : Position)
      (d : AttrDefault) (outer : List Char)
  → WFAttribute defs (DBCAttrDefault d)
  → SuffixStops isNewlineStart outer
  → parseTopStmt pos (emitTopStmt-chars defs (TAT (DBCAttrDefault d)) ++ₗ outer)
    ≡ just (mkResult
              (liftTopStmt defs (TAT (DBCAttrDefault d)))
              (advancePositions pos
                 (emitTopStmt-chars defs (TAT (DBCAttrDefault d))))
              outer)
parseTopStmt-on-emit-typed-TAT-Default defs pos d outer wf ss-NL =
  parseTopStmt-on-BA-head-via-prefix pos _ _ _ outer _
    (cong (_++ₗ outer) (proj₂ (emitAttrDefault-chars-BA-head defs d)))
    (parseAttrLine-on-emit-Attribute defs pos (DBCAttrDefault d) outer wf ss-NL)
