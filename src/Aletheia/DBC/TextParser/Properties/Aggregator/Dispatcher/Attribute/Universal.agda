{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 4c — Universal-attribute roundtrip dispatcher.
--
-- 3-way dispatch on `DBCAttribute`:
--   * DBCAttrDef d     → forward to Def.parseAttrLine-on-emit-RawDef.
--   * DBCAttrDefault d → forward to Default.parseAttrLine-on-emit-RawDefault.
--   * DBCAttrAssign a  → forward to Assign.parseAttrLine-on-emit-RawAssign,
--                        with IdentNameStop-of discharged universally via
--                        identifier-name-stop-of.
module Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Attribute.Universal where

open import Data.Char  using (Char)
open import Data.List  using (List; []; _∷_)
  renaming (_++_ to _++ₗ_)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)

open import Aletheia.Parser.Combinators using
  (Position; ParseResult; mkResult; advancePositions)

open import Aletheia.DBC.Types using
  ( AttrDef
  ; AttrAssign; mkAttrAssign
  ; DBCAttribute; DBCAttrDef; DBCAttrDefault; DBCAttrAssign
  )

open import Aletheia.DBC.TextFormatter.Attributes using
  (emitAttribute-chars)

open import Aletheia.DBC.TextParser.Attributes using
  (parseAttrLine)

open import Aletheia.DBC.TextParser.Properties.Aggregator.Foundations using
  (rawOf; WFAttribute)

open import Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Attribute.Foundations using
  (identifier-name-stop-of)

open import Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Attribute.Def using
  (parseAttrLine-on-emit-RawDef)
open import Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Attribute.Default using
  (parseAttrLine-on-emit-RawDefault)
open import Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Attribute.Assign using
  (parseAttrLine-on-emit-RawAssign)

open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (SuffixStops)
open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  (isNewlineStart)

-- ============================================================================
-- TOP-LEVEL UNIVERSAL DISPATCHER  (3-way on DBCAttribute)
-- ============================================================================

parseAttrLine-on-emit-Attribute :
    ∀ (defs : List AttrDef) (pos : Position)
      (a : DBCAttribute) (outer : List Char)
  → WFAttribute defs a
  → SuffixStops isNewlineStart outer
  → parseAttrLine pos (emitAttribute-chars defs a ++ₗ outer)
    ≡ just (mkResult
              (rawOf defs a)
              (advancePositions pos (emitAttribute-chars defs a))
              outer)
parseAttrLine-on-emit-Attribute defs pos (DBCAttrDef d) outer wf ss-NL =
  parseAttrLine-on-emit-RawDef defs pos d outer wf ss-NL
parseAttrLine-on-emit-Attribute defs pos (DBCAttrDefault d) outer wf ss-NL =
  parseAttrLine-on-emit-RawDefault defs pos d outer wf ss-NL
parseAttrLine-on-emit-Attribute defs pos
  (DBCAttrAssign (mkAttrAssign name target value)) outer _ ss-NL =
    parseAttrLine-on-emit-RawAssign defs pos name target value outer
      (identifier-name-stop-of target) ss-NL
