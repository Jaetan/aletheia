{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 4c — TopStmt-level dispatcher for the typed-shadow `TAT a`
-- (DBCAttribute payload).
--
-- 3-way façade: dispatches `DBCAttribute` to per-section sub-dispatchers.
-- The deeper per-scope (DBCAttrDef × 7 scopes) and per-target (DBCAttrAssign
-- × 7 targets) pattern-matches live in the sub-modules, where each
-- sub-module's elaboration is bounded.  Splitting was forced after the
-- 15-case monolithic version exceeded the -M16G heap (24min wall, no
-- progress) — same diagnose-and-split pattern that took TVT from 15.7 GB
-- / 273s to 443 MB / 14s in the Layer 4c-(a) checkpoint.
module Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Attribute.TopStmt where

open import Data.Char  using (Char)
open import Data.List  using (List; []; _∷_)
  renaming (_++_ to _++ₗ_)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)

open import Aletheia.Parser.Combinators using
  (Position; ParseResult; mkResult; advancePositions)

open import Aletheia.DBC.Types using
  (AttrDef; DBCAttribute; DBCAttrDef; DBCAttrDefault; DBCAttrAssign)

open import Aletheia.DBC.TextParser.TopLevel using
  (TopStmt; parseTopStmt)

open import Aletheia.DBC.TextParser.Properties.Aggregator.Foundations using
  ( WFAttribute
  ; TopStmtTyped; TAT
  ; emitTopStmt-chars
  ; liftTopStmt
  )
open import Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Attribute.TopStmt.Def using
  (parseTopStmt-on-emit-typed-TAT-Def)
open import Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Attribute.TopStmt.Default using
  (parseTopStmt-on-emit-typed-TAT-Default)
open import Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Attribute.TopStmt.Assign using
  (parseTopStmt-on-emit-typed-TAT-Assign)

open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (SuffixStops)
open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  (isNewlineStart)

-- ============================================================================
-- TOP-LEVEL TAT DISPATCHER  (3-way façade on DBCAttribute)
-- ============================================================================

parseTopStmt-on-emit-typed-TAT :
    ∀ (defs : List AttrDef) (pos : Position)
      (a : DBCAttribute) (outer : List Char)
  → WFAttribute defs a
  → SuffixStops isNewlineStart outer
  → parseTopStmt pos (emitTopStmt-chars defs (TAT a) ++ₗ outer)
    ≡ just (mkResult
              (liftTopStmt defs (TAT a))
              (advancePositions pos (emitTopStmt-chars defs (TAT a)))
              outer)
parseTopStmt-on-emit-typed-TAT defs pos (DBCAttrDef d) outer wf ss-NL =
  parseTopStmt-on-emit-typed-TAT-Def defs pos d outer wf ss-NL
parseTopStmt-on-emit-typed-TAT defs pos (DBCAttrDefault d) outer wf ss-NL =
  parseTopStmt-on-emit-typed-TAT-Default defs pos d outer wf ss-NL
parseTopStmt-on-emit-typed-TAT defs pos (DBCAttrAssign a) outer wf ss-NL =
  parseTopStmt-on-emit-typed-TAT-Assign defs pos a outer wf ss-NL
